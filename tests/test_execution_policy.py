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

from benchmark_fixtures import legacy_suite, legacy_profile, legacy_root

from math_gauge.benchmarks import BenchmarkProfile, build_plan, identity, select_slots, validate_plan
from math_gauge.catalog import Suite, candidate_message, digest_bytes, read_json, write_json
from math_gauge.execution_policy import (
    FOLLOWUP_PROMPT_PROJECTION, LOCAL_TOOLS_TRACK, LOCAL_TOOL_IDS, NO_TOOLS_TRACK,
    execution_context, project_followup_prompt, validate_context_policy,
)
from math_gauge.harness import (
    export_harness_bundle, export_simple_release_dataset, freeze_release_runtime, inspect_harness_bundle, inspect_release_run,
    make_release_anchor, reconstruct_release_plan, release_candidate_request,
)
from math_gauge.harness_answers import issue_answer_request, record_answer_attempt, pack_answer_archive, skip_answer_slot
from math_gauge.harness_import import import_answer_archive
from math_gauge.reliability import _slot_path, _validate_schedule, execute_reliability_run, inspect_reliability_run
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
        cls.suite = legacy_suite()
        cls.profile = legacy_profile(cls.suite)
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
            "tool_network_access": False, "search_allowed": False, "local_tool_feedback_allowed": True,
            "followup_prompt_projection": FOLLOWUP_PROMPT_PROJECTION})
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
                           ("followup_prompt_projection", "unknown/v2"),
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

    def test_all_source_prompts_are_preserved_and_only_local_permission_suffix_is_projected(self):
        rows = self.base_plan["reliability"]["prompts"]["messages"]
        original = copy.deepcopy(rows)
        self.assertEqual(len(rows), 48)
        local = execution_context(dict(RUNTIME, execution_track=LOCAL_TOOLS_TRACK))
        old_suffix = "本轮不能调用工具或查询外部资料。\n".encode()
        new_suffix = "本轮不得访问网络或进行联网检索。\n".encode()
        for source in rows:
            with self.subTest(sid=source["message_id"]):
                default = project_followup_prompt(source, LEGACY_CONTEXT)
                self.assertEqual(default, source)
                self.assertEqual(default["content"].encode(), source["content"].encode())
                self.assertEqual(default["content_sha256"], digest_bytes(source["content"].encode()))
                projected = project_followup_prompt(source, local)
                raw, effective = source["content"].encode(), projected["content"].encode()
                self.assertTrue(raw.endswith(old_suffix))
                self.assertEqual(effective, raw[:-len(old_suffix)] + new_suffix)
                self.assertEqual(projected["source_content_sha256"], source["content_sha256"])
                self.assertEqual(projected["content_sha256"], digest_bytes(effective))
                self.assertNotEqual(projected["content_sha256"], source["content_sha256"])
                self.assertEqual(projected["projection_version"], FOLLOWUP_PROMPT_PROJECTION)
                self.assertEqual({k: v for k, v in projected.items() if k not in {
                    "content", "content_sha256", "source_content_sha256", "projection_version"}},
                    {k: v for k, v in source.items() if k not in {"content", "content_sha256"}})
        self.assertEqual(rows, original)
        self.assertEqual(_validate_schedule(self.base_plan), {r["message_id"]: r for r in rows})

    def test_prior_unversioned_local_context_and_unrecognized_prompt_sources_fail_closed(self):
        runtime = dict(RUNTIME, execution_track=LOCAL_TOOLS_TRACK)
        local = execution_context(runtime)
        old_local = dict(local)
        old_local.pop("followup_prompt_projection")
        self.assertEqual(len(old_local), 8)
        with self.assertRaisesRegex(ValueError, "context policy"):
            validate_context_policy(old_local)
        plan = build_plan(self.profile, self.suite, runtime=runtime)
        plan["context_policy"] = old_local
        plan["plan_sha256"] = identity({k: v for k, v in plan.items() if k != "plan_sha256"})
        with self.assertRaisesRegex(ValueError, "context policy"):
            validate_plan(plan)
        source = self.base_plan["reliability"]["prompts"]["messages"][0]
        for text in (source["content"] + "extra", source["content"].replace("本轮不能调用工具或查询外部资料。", ""),
                     source["content"] + "本轮不能调用工具或查询外部资料。\n"):
            changed = dict(source, content=text, content_sha256=digest_bytes(text.encode()))
            with self.subTest(text_length=len(text)), self.assertRaisesRegex(ValueError, "permission suffix"):
                project_followup_prompt(changed, local)
        with self.assertRaisesRegex(ValueError, "source hash"):
            project_followup_prompt(dict(source, content_sha256="0" * 64), local)
        with self.assertRaisesRegex(ValueError, "already projected"):
            project_followup_prompt(project_followup_prompt(source, local), local)

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

    def test_shared_and_relocated_followups_match_and_real_collection_import_binds_both_hashes(self):
        runtime = dict(RUNTIME, execution_track=LOCAL_TOOLS_TRACK)
        plan = build_plan(self.profile, self.suite, ["all"], runtime=runtime)
        selected = select_slots(plan, ["neutral", "stance"])
        prompts = {p["message_id"]: p for p in self.base_plan["reliability"]["prompts"]["messages"]}
        source_snapshot = copy.deepcopy(prompts)
        answers, seen = {}, {}

        def adapter(request):
            slot = selected[len(seen)]
            sid = slot["slot_id"]
            seen[sid] = copy.deepcopy(request)
            raw = ("Synthetic original 初答\r\n" if slot["kind"] == "independent" else
                   "KEEP\r\nSynthetic original rationale\r\n" if slot["round"] == 1 else
                   "FULL\r\nSynthetic full replacement\r\n").encode()
            answers[sid] = raw
            return {"stdout": raw, "status": "ok", "usage": {"total_tokens": 1}}

        native = self.root / "shared-run"
        execute_reliability_run(plan, self.suite, native, adapter=adapter, targets=["neutral", "stance"])
        _, shared_records = inspect_reliability_run(native)
        self.assertEqual(len(seen), 56)
        before = {p.relative_to(self.download).as_posix(): (p.read_bytes(), p.stat().st_mtime_ns)
                  for p in self.download.rglob("*") if p.is_file()}
        runtime_path = self.root / "followup-runtime.json"
        write_json(runtime_path, runtime)
        run, responses = self.root / "portable-run", self.root / "portable-responses"
        helper = self.download / "tools/benchmark.py"
        self.portable(helper, "prepare", "--runtime", runtime_path, "--target", "neutral", "--target", "stance", "--out", run)
        manifest = inspect_release_run(run)
        target = selected[0]["case_id"]
        target_sids = []
        for slot in selected:
            sid = slot["slot_id"]
            if slot["case_id"] != target:
                if slot["kind"] == "independent":
                    skip_answer_slot(run, responses, sid, "Explicit synthetic fixture omission")
                continue
            target_sids.append(sid)
            stem = sid.replace(":", "-")
            request, response = self.root / (stem + ".json"), self.root / (stem + ".md")
            self.portable(helper, "request", "--run", run, "--responses", responses, "--slot", sid, "--out", request)
            actual = read_json(request)
            self.assertEqual(actual, seen[sid])
            response.write_bytes(answers[sid])
            self.portable(helper, "record", "--run", run, "--responses", responses, "--slot", sid,
                          "--request", request, "--response", response, "--status", "ok")
        self.assertEqual(len(target_sids), 7)
        for slot in selected:
            if slot["kind"] == "independent":
                self.assertEqual(seen[slot["slot_id"]]["messages"], [{"role": "user", "content": candidate_message(
                    self.suite.request(self.suite.cases[slot["case_id"]]))}])
                continue
            sid = slot["slot_id"]
            effective = project_followup_prompt(prompts[sid], plan["context_policy"])
            self.assertEqual(seen[sid]["messages"][-1]["content"], effective["content"])
            self.assertEqual(shared_records[sid]["prompt_sha256"], effective["content_sha256"])
            self.assertEqual(shared_records[sid]["source_prompt_sha256"], prompts[sid]["content_sha256"])
            self.assertEqual(shared_records[sid]["prompt_projection_version"], FOLLOWUP_PROMPT_PROJECTION)
            if slot["round"] == 2:
                prior = slot["parent_slot"]
                self.assertEqual(seen[sid]["messages"][2]["content"],
                                 project_followup_prompt(prompts[prior], plan["context_policy"])["content"])
                self.assertEqual(seen[sid]["messages"][3]["content"].encode(), answers[prior])
        archive, imported = self.root / "followup-answers.zip", self.root / "followup-imported"
        self.portable(helper, "pack", "--run", run, "--responses", responses, "--out", archive)
        import_answer_archive(archive, self.anchor, self.suite, imported)
        meta, imported_records = inspect_reliability_run(imported)
        for sid in target_sids:
            self.assertEqual((imported / imported_records[sid]["response_path"]).read_bytes(), answers[sid])
            if ":A1" not in sid:
                for key in ("prompt_sha256", "source_prompt_sha256", "prompt_projection_version"):
                    self.assertEqual(imported_records[sid][key], shared_records[sid][key])
                self.assertEqual(imported_records[sid]["material"]["status"], "resolved")
        self.assertEqual(meta["candidate_calls"], 0)
        self.assertEqual(meta["plan"]["planned"]["all_slots"], 177)
        self.assertEqual(self.base_plan["reliability"]["prompts"]["messages"], list(source_snapshot.values()))
        self.assertEqual(before, {p.relative_to(self.download).as_posix(): (p.read_bytes(), p.stat().st_mtime_ns)
                                  for p in self.download.rglob("*") if p.is_file()})
        self.assertEqual(read_json(run / "dataset/manifest.json")["prompts"], self.dataset["prompts"])
        sid = next(s for s in target_sids if s.endswith(":neutral:1"))
        record_path = imported / _slot_path(sid) / "record.json"
        original_record = record_path.read_bytes()
        run_path = imported / "run.json"
        original_meta = read_json(run_path)
        for key, value in (("prompt_sha256", "0" * 64), ("source_prompt_sha256", "1" * 64),
                           ("prompt_projection_version", "unknown/v2")):
            with self.subTest(tampered=key):
                record = json.loads(original_record)
                record[key] = value
                write_json(record_path, record)
                changed_meta = copy.deepcopy(original_meta)
                changed_hash = digest_bytes(record_path.read_bytes())
                changed_meta["slot_record_sha256"][sid] = changed_hash
                # Rebind outer record hashes so rejection proves the semantic
                # source/effective check rather than only the integrity layer.
                for evidence in changed_meta["budget_evidence"].values():
                    if evidence["slot_id"] == sid:
                        evidence["slot_record_sha256"] = changed_hash
                write_json(run_path, changed_meta)
                with self.assertRaisesRegex(ValueError, "source/effective followup prompt binding"):
                    inspect_reliability_run(imported)
        record_path.write_bytes(original_record)
        write_json(run_path, original_meta)
        inspect_reliability_run(imported)


if __name__ == "__main__":
    unittest.main()
