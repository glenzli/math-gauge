"""Execution conditions change permissions, never task obligations or grade weights."""

import copy
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from math_gauge.benchmarks import BenchmarkProfile, build_plan, identity, validate_plan
from math_gauge.catalog import Suite, candidate_message, read_json, write_json
from math_gauge.execution_policy import (
    LOCAL_TOOLS_TRACK, LOCAL_TOOL_IDS, NO_TOOLS_TRACK,
    execution_context, validate_context_policy,
)
from math_gauge.harness import (
    export_harness_bundle, export_simple_release_dataset, freeze_release_runtime, inspect_harness_bundle, inspect_release_run,
    make_release_anchor, reconstruct_release_plan,
)
from math_gauge.harness_answers import issue_answer_request, record_answer_attempt, pack_answer_archive
from math_gauge.harness_import import import_answer_archive
from math_gauge.reliability import inspect_reliability_run
from math_gauge.scoring import render_score, score_runs

ROOT = Path(__file__).resolve().parents[1]
RUNTIME = {"model_label": "synthetic-policy-fixture", "adapter_identity": {"kind": "fixture"},
           "candidate_parameters": {"model": "synthetic-no-model-calls", "reasoning_effort": "max"},
           "budget": {"timeout_seconds": 2}, "fresh_context": True}
LEGACY_CONTEXT = {"independent": "fresh", "followup": "branch-history-only",
                  "external_correctness_feedback": False, "tools_allowed": []}


class ExecutionPolicyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.suite = Suite.load(ROOT / "cases")
        cls.profile = BenchmarkProfile.load(ROOT / "protocol/benchmark-profile.json", cls.suite)
        cls.base_plan = build_plan(cls.profile, cls.suite, ["all"])
        cls.shared_temp = tempfile.TemporaryDirectory()
        cls.addClassCleanup(cls.shared_temp.cleanup)
        cls.shared = Path(cls.shared_temp.name).resolve() / "dataset"
        cls.dataset = export_simple_release_dataset(cls.base_plan, cls.suite, cls.shared,
            release_version="0.2.0", readme=b"# Synthetic policy consumer guide\n",
            extra_files={"LICENSE": (ROOT / "LICENSE").read_bytes(),
                         "THIRD_PARTY_NOTICES.md": b"Synthetic fixture only\n"})
        cls.anchor = make_release_anchor(cls.base_plan, cls.dataset)

    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.download = self.root / "download"
        shutil.copytree(self.shared, self.download)

    def test_omitted_track_preserves_exact_legacy_context_and_only_execution_identity_changes(self):
        self.assertEqual(execution_context(), LEGACY_CONTEXT)
        self.assertEqual(json.dumps(execution_context(RUNTIME)), json.dumps(LEGACY_CONTEXT))
        first = execution_context()
        first["tools_allowed"].append("must-not-persist")
        self.assertEqual(execution_context(), LEGACY_CONTEXT)
        original = build_plan(self.profile, self.suite, ["all"], runtime=RUNTIME)
        runtime = dict(RUNTIME, execution_track=LOCAL_TOOLS_TRACK)
        enabled = build_plan(self.profile, self.suite, ["all"], runtime=runtime)
        self.assertEqual(original["context_policy"], LEGACY_CONTEXT)
        self.assertEqual(enabled["context_policy"], {
            **LEGACY_CONTEXT, "execution_track": LOCAL_TOOLS_TRACK, "tools_allowed": list(LOCAL_TOOL_IDS),
            "tool_network_access": False, "search_allowed": False, "local_tool_feedback_allowed": True})
        for key in ("suite", "profile", "case_index", "slots", "planned", "reliability"):
            self.assertEqual(enabled[key], original[key], key)
        self.assertNotEqual(enabled["plan_sha256"], original["plan_sha256"])
        self.assertEqual(self.base_plan["context_policy"], LEGACY_CONTEXT)
        validate_plan(original)
        validate_plan(enabled)

    def test_unknown_tracks_and_rehashed_context_tool_network_feedback_drift_are_rejected(self):
        for track in (None, True, "", "unknown", "math-gauge.local-tools-no-search/v2"):
            with self.subTest(track=track), self.assertRaisesRegex(ValueError, "Unknown execution track"):
                build_plan(self.profile, self.suite, runtime=dict(RUNTIME, execution_track=track))
        valid = build_plan(self.profile, self.suite, runtime=dict(RUNTIME, execution_track=LOCAL_TOOLS_TRACK))
        for key, value in (("tool_network_access", True), ("tool_network_access", 0), ("search_allowed", True),
                           ("external_correctness_feedback", True), ("local_tool_feedback_allowed", False),
                           ("tools_allowed", [*LOCAL_TOOL_IDS, "web_search"]), ("followup", "shared-history")):
            with self.subTest(key=key, value=value):
                changed = copy.deepcopy(valid)
                changed["context_policy"][key] = value
                changed["plan_sha256"] = identity({k: v for k, v in changed.items() if k != "plan_sha256"})
                with self.assertRaisesRegex(ValueError, "context policy"):
                    validate_plan(changed)
        for field in ("tools_allowed", "tool_network_access", "tool_policy"):
            runtime = dict(RUNTIME, execution_track=LOCAL_TOOLS_TRACK, **{field: True})
            destination = self.root / field
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, "Unsupported fields"):
                freeze_release_runtime(self.download, runtime, destination)
            self.assertFalse(destination.exists())
        with self.assertRaisesRegex(ValueError, "context policy"):
            validate_context_policy(dict(LEGACY_CONTEXT, tool_network_access=True))

    def portable(self, helper, *arguments):
        result = subprocess.run([sys.executable, "-I", "-S", "-B", str(helper), *map(str, arguments)],
                                cwd=self.root, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        return json.loads(result.stdout)

    def create_return(self, runtime, name, *, portable=False):
        run, responses = self.root / (name + "-run"), self.root / (name + "-responses")
        archive, imported = self.root / (name + ".zip"), self.root / (name + "-imported")
        runtime_path = self.root / (name + "-runtime.json")
        write_json(runtime_path, runtime)
        helper = self.download / "tools/benchmark.py"
        if portable:
            self.portable(helper, "prepare", "--runtime", runtime_path, "--target", "lean-construction", "--out", run)
            manifest = inspect_release_run(run)
        else:
            manifest = freeze_release_runtime(self.download, runtime, run, targets=["lean-construction"])
        sid = manifest["selected_slot_ids"][0]
        request, response = self.root / (name + "-request.json"), self.root / (name + "-response.md")
        raw = "Synthetic response; no tool use is required。\r\n".encode()
        response.write_bytes(raw)
        if portable:
            self.portable(helper, "request", "--run", run, "--responses", responses, "--slot", sid, "--out", request)
            self.portable(helper, "record", "--run", run, "--responses", responses, "--slot", sid,
                          "--request", request, "--response", response, "--status", "ok")
            self.portable(helper, "pack", "--run", run, "--responses", responses, "--out", archive)
        else:
            issue_answer_request(run, responses, sid, request)
            record_answer_attempt(run, responses, sid, request, response, status="ok")
            pack_answer_archive(run, responses, archive)
        with patch("subprocess.Popen", side_effect=AssertionError("Import executed code")):
            meta = import_answer_archive(archive, self.anchor, self.suite, imported)
        checked, records = inspect_reliability_run(imported)
        self.assertEqual((imported / records[sid]["response_path"]).read_bytes(), raw)
        self.assertTrue(meta["fixture_only"])
        self.assertFalse(meta["external_origin_verified"])
        self.assertEqual(meta["candidate_calls"], 0)
        return run, imported, sid, read_json(request), checked

    def test_relocated_tool_track_roundtrip_preserves_complete_messages_and_original_lean_obligations(self):
        runtime = dict(RUNTIME, execution_track=LOCAL_TOOLS_TRACK)
        run, imported, sid, request, checked = self.create_return(runtime, "tools", portable=True)
        expected_context = execution_context(runtime)
        self.assertEqual(inspect_release_run(run)["execution"]["context_policy"], expected_context)
        reconstructed = reconstruct_release_plan(run, self.base_plan, suite=self.suite)
        self.assertEqual(reconstructed["context_policy"], expected_context)
        self.assertEqual(checked["plan"], reconstructed)
        self.assertEqual(reconstructed["case_index"], self.base_plan["case_index"])
        self.assertEqual(reconstructed["planned"]["all_slots"], 177)
        cid = sid.split(":")[0]
        self.assertEqual(request, {"schema": "math-gauge.conversation/v1",
            "messages": [{"role": "user", "content": candidate_message(self.suite.request(self.suite.cases[cid]))}],
            "parameters": runtime["candidate_parameters"]})
        self.assertNotIn("execution_track", json.dumps(request))
        self.assertNotIn("local_tool_feedback_allowed", json.dumps(request))
        report = score_runs([imported])
        self.assertEqual(report["execution_condition"]["track"], LOCAL_TOOLS_TRACK)
        self.assertIn("Local tools permitted", render_score(report))
        self.assertEqual(report["result_kind"], "fixture")
        self.assertFalse(report["metrics"]["overall"]["formal_comparison_eligible"])

    def test_generic_controller_embeds_the_same_opt_in_policy_without_repo_imports(self):
        runtime = dict(RUNTIME, execution_track=LOCAL_TOOLS_TRACK)
        plan = build_plan(self.profile, self.suite, runtime=runtime)
        bundle = self.root / "generic-bundle"
        manifest = export_harness_bundle(plan, self.suite, bundle, targets=["chapters"])
        inspect_harness_bundle(bundle, plan=plan, suite=self.suite)
        sid = manifest["selected_slot_ids"][0]
        request = self.portable(bundle / "controller.py", "request", "--bundle", bundle, "--slot", sid)
        self.assertEqual(manifest["execution"]["context_policy"], execution_context(runtime))
        self.assertEqual(request["parameters"], runtime["candidate_parameters"])
        self.assertEqual(request["messages"], [{"role": "user", "content": candidate_message(
            self.suite.request(self.suite.cases[sid.split(":")[0]]))}])

    def test_conditions_receive_same_numeric_scoring_but_cannot_be_merged(self):
        _, old_run, _, _, _ = self.create_return(RUNTIME, "legacy")
        _, tool_run, _, _, _ = self.create_return(dict(RUNTIME, execution_track=LOCAL_TOOLS_TRACK), "tools")
        old_report, new_report = score_runs([old_run]), score_runs([tool_run])
        self.assertEqual(old_report["execution_condition"]["track"], NO_TOOLS_TRACK)
        self.assertEqual(new_report["execution_condition"]["track"], LOCAL_TOOLS_TRACK)
        for name in old_report["metrics"]:
            for field in ("exact", "lower", "upper", "formal_exact", "coverage"):
                self.assertEqual(old_report["metrics"][name][field], new_report["metrics"][name][field], (name, field))
        with self.assertRaisesRegex(ValueError, "Cannot merge different plan"):
            score_runs([old_run, tool_run])


if __name__ == "__main__":
    unittest.main()
