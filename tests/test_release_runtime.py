"""Relocated generic release -> caller runtime -> shared provisional review.

Every response and review here is an explicit synthetic fixture. No model or
Lean process is invoked, and no fixture establishes mathematical correctness.
"""

import contextlib
import copy
import io
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from math_gauge.benchmarks import BenchmarkProfile, build_plan, identity
from math_gauge.catalog import Suite, candidate_message, digest_bytes, read_json, write_json
from math_gauge.cli import main
from math_gauge.harness import (
    candidate_request_from_bundle, export_release_dataset, freeze_release_runtime,
    inspect_harness_bundle, inspect_release_dataset, inspect_release_run,
    reconstruct_release_plan, release_candidate_request, release_submission_template,
)
from math_gauge.harness_import import import_harness_submission
from math_gauge.reliability import (
    _slot_path, apply_reliability_reviews, inspect_reliability_run,
    reliability_review_templates, reliability_score_inputs,
)
from math_gauge.scoring import render_score, score_runs

ROOT = Path(__file__).resolve().parents[1]
CID = "MG-GR002"
RUNTIME = {"model_label": "offline-release-fixture", "adapter_identity": {"kind": "fixture"},
           "candidate_parameters": {"model": "caller-selected-fixture", "reasoning_effort": "high"},
           "budget": {"timeout_seconds": 2, "output_tokens": 1234, "max_transport_attempts": 354},
           "fresh_context": True}


class ReleaseRuntimeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.suite = Suite.load(ROOT / "cases")
        cls.profile = BenchmarkProfile.load(ROOT / "protocol/benchmark-profile.json", cls.suite)
        cls.base_plan = build_plan(cls.profile, cls.suite, ["all"])
        cls.shared_temp = tempfile.TemporaryDirectory()
        cls.addClassCleanup(cls.shared_temp.cleanup)
        cls.shared = Path(cls.shared_temp.name).resolve() / "dataset"
        cls.dataset_manifest = export_release_dataset(cls.base_plan, cls.suite, cls.shared)

    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name).resolve()
        self.dataset = self.root / "dataset"
        shutil.copytree(self.shared, self.dataset)
        self.run = self.root / "frozen-run"
        self.source = self.root / "submission"
        self.source.mkdir()
        self.input = self.source / "submission.json"
        self.output = self.root / "imported"

    def freeze(self, *, targets=None, runtime=None, output=None):
        return freeze_release_runtime(self.dataset, RUNTIME if runtime is None else runtime,
                                      output or self.run, targets=targets)

    def controller(self, root, *arguments):
        return subprocess.run([sys.executable, "-I", str(root / "controller.py"), *arguments],
                              cwd=self.root, capture_output=True, check=False)

    def descriptor(self, name, raw):
        raw = raw.encode("utf-8") if isinstance(raw, str) else raw
        path = self.source / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)
        return {"path": name, "bytes": len(raw), "sha256": digest_bytes(raw)}

    def submission(self, replies):
        manifest = inspect_release_run(self.run)
        dataset = inspect_release_dataset(self.run / "dataset")
        slots = {s["slot_id"]: s for s in dataset["slots"]}
        result = release_submission_template(self.run)
        for sid in manifest["selected_slot_ids"]:
            if sid not in replies:
                continue
            ancestors, parent = {}, slots[sid]["parent_slot"]
            while parent is not None:
                ancestors[parent] = replies[parent]
                parent = slots[parent]["parent_slot"]
            request = release_candidate_request(self.run, sid, ancestors)
            prefix = sid.replace(":", "-")
            result["slots"].append({"slot_id": sid, "projected_request": request, "attempts": [{
                "number": 1, "status": "ok", "projected_request_sha256": identity(request),
                "response": self.descriptor(prefix + "/response.md", replies[sid]),
                "stderr": self.descriptor(prefix + "/stderr.txt", b""), "usage": {"total_tokens": 3}}]})
        write_json(self.input, result)
        return result

    def import_run(self, value=None):
        if value is not None:
            write_json(self.input, value)
        return import_harness_submission(self.run, self.input, self.base_plan, self.suite, self.output)

    def rehash(self, root, value, key, *, files=False):
        if files:
            value["files_sha256"] = {name: digest_bytes((root / name).read_bytes())
                                     for name in value["files_sha256"]}
        value[key] = identity({k: v for k, v in value.items() if k != key})
        write_json(root / "manifest.json", value)

    def test_generic_export_is_deterministic_complete_and_contains_only_candidate_projection(self):
        other = self.root / "second-dataset"
        manifest = export_release_dataset(self.base_plan, self.suite, other)
        self.assertEqual(manifest, self.dataset_manifest)
        self.assertEqual(manifest["planned"]["all_slots"], 177)
        self.assertEqual(len(manifest["cases"]), 43)
        self.assertEqual(manifest["exported_slots"], 177)
        self.assertEqual(manifest["base_plan_sha256"], self.base_plan["plan_sha256"])
        self.assertNotIn("runtime", manifest)
        self.assertNotIn("profile", manifest)
        self.assertNotIn("plan_sha256", manifest)
        forbidden = {"expected_truth", "case_approved", "case_approval_source", "profile", "reference", "rubric"}

        def check_keys(value):
            if isinstance(value, dict):
                self.assertFalse(forbidden & set(value))
                for item in value.values():
                    check_keys(item)
            elif isinstance(value, list):
                for item in value:
                    check_keys(item)

        for path in self.dataset.rglob("*.json"):
            check_keys(read_json(path))
        self.assertFalse(any(p.name in {"plan.json", "reference.md", "rubric.json", "case.json"}
                             for p in self.dataset.rglob("*")))
        code = (self.dataset / "controller.py").read_text()
        self.assertNotIn("from .", code)
        self.assertNotIn("import math_gauge", code)
        self.assertNotIn("expected_truth", code)
        chapter = next(c for c in manifest["cases"] if c["case_id"] == "MG-C002")
        original = self.suite.request(self.suite.cases["MG-C002"])
        self.assertEqual((self.dataset / chapter["candidate_message_path"]).read_bytes(),
                         candidate_message(original).encode("utf-8"))
        self.assertTrue(any("**证明**" in f["content"] for f in original["files"]))

    def test_relocated_stdlib_helper_freezes_arbitrary_runtime_and_constructs_complete_requests(self):
        moved = self.root / "download"
        self.dataset.rename(moved)
        runtime_path = self.root / "runtime.json"
        runtime = copy.deepcopy(RUNTIME)
        runtime["model_label"] = "a different caller-selected runtime"
        runtime["candidate_parameters"].update(model="another-model", reasoning_effort="max")
        runtime["budget"].update(output_tokens=9001, max_total_tokens=20000)
        write_json(runtime_path, runtime)
        checked = self.controller(moved, "check")
        self.assertEqual(checked.returncode, 0, checked.stderr)
        self.assertTrue(json.loads(checked.stdout)["preparation_only"])
        failed = self.controller(moved, "request", "--slot", CID + ":A1")
        self.assertNotEqual(failed.returncode, 0)
        frozen = self.controller(moved, "freeze", "--runtime", str(runtime_path), "--target", "neutral",
                                 "--target", "stance", "--out", str(self.run))
        self.assertEqual(frozen.returncode, 0, frozen.stderr)
        self.assertEqual(inspect_release_run(self.run)["runtime"], runtime)
        shutil.rmtree(moved)
        requested = self.controller(self.run, "request", "--slot", CID + ":A1")
        self.assertEqual(requested.returncode, 0, requested.stderr)
        request = json.loads(requested.stdout)
        self.assertEqual(request["parameters"], {"model": "another-model", "reasoning_effort": "max",
                                                  "max_output_tokens": 9001})
        self.assertEqual(request["messages"], [{"role": "user", "content": candidate_message(
            self.suite.request(self.suite.cases[CID]))}])
        template_path = self.root / "new-template.json"
        templated = self.controller(self.run, "template", "--out", str(template_path))
        self.assertEqual(templated.returncode, 0, templated.stderr)
        self.assertEqual(read_json(template_path), release_submission_template(self.run))
        self.assertEqual(inspect_release_run(self.run)["planned"]["all_slots"], 177)

    def test_freeze_creates_independent_immutable_runs_and_keeps_dependency_closure(self):
        before = {p.relative_to(self.dataset).as_posix(): (p.read_bytes(), p.stat().st_mtime_ns)
                  for p in self.dataset.rglob("*") if p.is_file()}
        one = self.freeze(targets=["neutral"])
        two = self.freeze(targets=["lean-construction"], output=self.root / "second-run")
        self.assertNotEqual(one["run_id"], two["run_id"])
        self.assertNotEqual(one["run_sha256"], two["run_sha256"])
        self.assertEqual(one["planned"]["selected_slots"], 24)
        self.assertEqual(two["planned"]["selected_slots"], 18)
        self.assertEqual(one["planned"]["all_slots"], two["planned"]["all_slots"])
        self.assertIn(CID + ":A1", one["selected_slot_ids"])
        self.assertNotIn(CID + ":A2", one["selected_slot_ids"])
        self.assertEqual(before, {p.relative_to(self.dataset).as_posix(): (p.read_bytes(), p.stat().st_mtime_ns)
                                  for p in self.dataset.rglob("*") if p.is_file()})
        with self.assertRaisesRegex(ValueError, "new directory"):
            self.freeze()
        with self.assertRaisesRegex(ValueError, "separate"):
            self.freeze(output=self.dataset / "nested")

    def test_fresh_repeats_and_two_round_branch_history_are_exact_and_isolated(self):
        self.freeze()
        initial = release_candidate_request(self.run, CID + ":A1")
        for label in ("A2", "A3"):
            self.assertEqual(release_candidate_request(self.run, CID + ":" + label), initial)
            with self.assertRaisesRegex(ValueError, "ancestor"):
                release_candidate_request(self.run, CID + ":" + label, {CID + ":A1": "other answer"})
        a1, first = "initial α\r\n", "KEEP\r\nneutral round one\r\n"
        ancestors = {CID + ":A1": a1, CID + ":neutral:1": first}
        request = release_candidate_request(self.run, CID + ":neutral:2", ancestors)
        self.assertEqual([m["role"] for m in request["messages"]], ["user", "assistant", "user", "assistant", "user"])
        self.assertEqual([m["content"] for m in request["messages"] if m["role"] == "assistant"], [a1, first])
        for bad in ({CID + ":A1": a1}, dict(ancestors, **{CID + ":affirm:1": "peer"}),
                    {CID + ":A1": a1, CID + ":deny:1": "peer"}):
            with self.assertRaisesRegex(ValueError, "ancestor"):
                release_candidate_request(self.run, CID + ":neutral:2", bad)
        self.assertEqual(candidate_request_from_bundle(self.run, CID + ":neutral:2", ancestors), request)

    def test_unknown_tools_missing_budget_and_contradictory_parameters_are_rejected(self):
        mutations = [dict(RUNTIME, tools_allowed=["lean"]), dict(RUNTIME, tool_policy={"network": True}),
                     dict(RUNTIME, fresh_context=False), dict(RUNTIME, budget={"timeout_seconds": 2}),
                     dict(RUNTIME, budget={**RUNTIME["budget"], "tools": []}),
                     dict(RUNTIME, candidate_parameters={"max_output_tokens": 999}),
                     dict(RUNTIME, candidate_parameters={"model": ""}),
                     dict(RUNTIME, candidate_parameters={**RUNTIME["candidate_parameters"], "max_output_tokens": 999})]
        for runtime in mutations:
            with self.subTest(runtime=runtime), self.assertRaises(ValueError):
                self.freeze(runtime=runtime)
            self.assertFalse(self.run.exists())

    def test_case_output_overrides_remain_frozen_for_repeats_and_branch_rounds(self):
        runtime = copy.deepcopy(RUNTIME)
        runtime["budget"]["case_parameters"] = {"MG-C002": {"max_output_tokens": 40000},
                                                   CID: {"max_output_tokens": 2000}}
        self.freeze(runtime=runtime)
        for label in ("A1", "A2", "A3"):
            chapter = release_candidate_request(self.run, "MG-C002:" + label)
            self.assertEqual(chapter["parameters"]["max_output_tokens"], 40000)
            selected = release_candidate_request(self.run, CID + ":" + label)
            self.assertEqual(selected["parameters"]["max_output_tokens"], 2000)
        followup = release_candidate_request(self.run, CID + ":neutral:2",
                                              {CID + ":A1": "fixture", CID + ":neutral:1": "KEEP\nfixture"})
        self.assertEqual(followup["parameters"]["max_output_tokens"], 2000)
        value = self.submission({CID + ":A1": "fixture", CID + ":neutral:1": "KEEP\nfixture"})
        self.import_run(value)
        _, records = inspect_reliability_run(self.output)
        self.assertEqual(records[CID + ":neutral:1"]["status"], "responded")

    def test_partial_v2_import_preserves_originals_and_uses_shared_review_and_report(self):
        self.freeze(targets=["neutral", "stance"])
        replies = {CID + ":A1": "synthetic initial\r\n", CID + ":neutral:1": "KEEP\r\nfixture\r\n",
                   CID + ":neutral:2": "FULL\nsynthetic replacement\n"}
        value = self.submission(replies)
        original_submission = self.input.read_bytes()
        original_manifest = (self.run / "manifest.json").read_bytes()
        with patch("subprocess.Popen", side_effect=AssertionError("Import executed untrusted code")), \
                patch("math_gauge.execution.invoke_conversation", side_effect=AssertionError("Candidate called")):
            meta = self.import_run()
        self.assertEqual(meta["candidate_calls"], 0)
        self.assertEqual(meta["external_candidate_calls_declared"], 0)
        self.assertEqual((self.output / "external-import/submission.json").read_bytes(), original_submission)
        self.assertEqual((self.output / "external-import/bundle/manifest.json").read_bytes(), original_manifest)
        reconstructed = reconstruct_release_plan(self.run, self.base_plan, suite=self.suite)
        self.assertNotEqual(reconstructed["plan_sha256"], self.base_plan["plan_sha256"])
        self.assertEqual(meta["plan_sha256"], reconstructed["plan_sha256"])
        self.assertNotIn("plan_sha256", value)
        shutil.rmtree(self.source)
        shutil.rmtree(self.run)
        checked, records = inspect_reliability_run(self.output)
        self.assertEqual(checked["origin"], "external_import")
        self.assertEqual((self.output / _slot_path(CID + ":neutral:1") / "material-body.md").read_bytes(),
                         replies[CID + ":A1"].encode("utf-8"))
        self.assertEqual((self.output / _slot_path(CID + ":neutral:2") / "material-body.md").read_bytes(),
                         b"synthetic replacement\n")
        self.assertEqual(records[CID + ":affirm:1"]["reason"], "submission_missing")
        entry = next(e for e in reliability_review_templates(self.output) if e["slot_id"] == CID + ":A1")
        entry.update(reviewer="Offline release fixture", reviewer_kind="fixture", decision="partial",
                     notes="Synthetic incomplete answer; no model mathematics was assessed.")
        entry["format_review"].update(decision="valid", notes="Fixture format.")
        for stage in entry["stages"]:
            stage.update(decision="partial", failure_category="mathematical", notes="Fixture incomplete stage.")
            stage["math_review"].update(decision="partial", reasons=["candidate_incomplete"], notes="Fixture.")
        entry["focus_review"].update(decision="partial", reasons=["candidate_incomplete"], notes="Fixture.")
        apply_reliability_reviews(self.output, [entry])
        report = score_runs([self.output])
        self.assertEqual(report["result_kind"], "fixture")
        self.assertFalse(report["model_result"])
        self.assertEqual(report["execution_coverage"]["full_plan_slots"], 177)
        self.assertEqual(report["execution_coverage"]["unique_started_slots"], 3)
        self.assertIsNone(report["metrics"]["overall"]["exact"])
        self.assertIsNone(report["metrics"]["overall"]["formal_score"])
        self.assertIn("177", render_score(report))
        row = next(r for r in reliability_score_inputs(self.output)["slots"] if r["started"])
        self.assertIn("external_origin_unverified", row["execution_eligibility"]["reasons"])

    def test_changed_runtime_targets_base_anchor_and_preparation_only_import_fail_closed(self):
        manifest = self.freeze(targets=["neutral"])
        original = (self.run / "manifest.json").read_bytes()
        self.submission({CID + ":A1": "fixture"})
        mutations = [dict(manifest, runtime={**RUNTIME, "model_label": "changed"}),
                     dict(manifest, targets=["stance"]), dict(manifest, base_plan_sha256="0" * 64),
                     dict(manifest, runtime_frozen=False, preparation_only=True)]
        for changed in mutations:
            self.rehash(self.run, changed, "run_sha256")
            with self.subTest(changed=changed), self.assertRaises(ValueError):
                self.import_run()
            self.assertFalse(self.output.exists())
        (self.run / "manifest.json").write_bytes(original)
        other_plan = copy.deepcopy(self.base_plan)
        other_plan["plan_id"] = "different-trusted-anchor"
        other_plan["plan_sha256"] = identity({k: v for k, v in other_plan.items() if k != "plan_sha256"})
        with self.assertRaisesRegex(ValueError, "different trusted base"):
            import_harness_submission(self.run, self.input, other_plan, self.suite, self.output)
        with self.assertRaises(ValueError):
            import_harness_submission(self.dataset, self.input, self.base_plan, self.suite, self.output)
        self.assertFalse(self.output.exists())

    def test_gold_leaks_and_self_consistent_candidate_rewrites_are_rejected(self):
        manifest = read_json(self.dataset / "manifest.json")
        gold = self.dataset / "reference.md"
        gold.write_text("Forbidden evaluator answer", encoding="utf-8")
        manifest["files_sha256"]["reference.md"] = digest_bytes(gold.read_bytes())
        self.rehash(self.dataset, manifest, "dataset_sha256")
        with self.assertRaisesRegex(ValueError, "allowlist"):
            inspect_release_dataset(self.dataset)
        gold.unlink()
        manifest = copy.deepcopy(self.dataset_manifest)
        row = next(c for c in manifest["cases"] if c["case_id"] == CID)
        request = read_json(self.dataset / row["request_path"])
        request["task"] += "\nA self-consistent but unauthorized extra hint.\n"
        write_json(self.dataset / row["request_path"], request)
        (self.dataset / row["task_path"]).write_text(request["task"], encoding="utf-8")
        message = candidate_message(request).encode("utf-8")
        (self.dataset / row["candidate_message_path"]).write_bytes(message)
        row["request_sha256"] = digest_bytes(json.dumps(request, ensure_ascii=False, sort_keys=True).encode("utf-8"))
        row["candidate_message_sha256"] = digest_bytes(message)
        self.rehash(self.dataset, manifest, "dataset_sha256", files=True)
        inspect_release_dataset(self.dataset)  # Self-consistency is not trusted source identity.
        with self.assertRaisesRegex(ValueError, "trusted base plan"):
            inspect_release_dataset(self.dataset, plan=self.base_plan, suite=self.suite)

    def test_cross_branch_history_v1_binding_and_duplicate_submission_json_are_rejected(self):
        self.freeze(targets=["neutral", "stance"])
        original = self.submission({CID + ":A1": "fixture", CID + ":neutral:1": "KEEP\nfixture"})
        for kind in ("history", "invented-plan", "run-binding", "order"):
            value = copy.deepcopy(original)
            if kind == "history":
                value["slots"][-1]["projected_request"]["messages"][1]["content"] = "unrelated branch"
            elif kind == "invented-plan":
                value["plan_sha256"] = self.base_plan["plan_sha256"]
            elif kind == "run-binding":
                value["run_sha256"] = "0" * 64
            else:
                value["slots"].reverse()
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                self.import_run(value)
            self.assertFalse(self.output.exists())
        self.input.write_text('{"schema":"x","schema":"y"}', encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "Duplicate JSON"):
            self.import_run()

    def test_native_check_cli_supports_generic_and_frozen_release_bindings(self):
        self.freeze(targets=["lean-audit"])
        for bundle in (self.dataset, self.run):
            output, errors = io.StringIO(), io.StringIO()
            with contextlib.redirect_stdout(output), contextlib.redirect_stderr(errors):
                status = main(["benchmark-export-check", "--bundle", str(bundle), "--suite", str(ROOT / "cases"),
                               "--plan", str(Path(str(self.shared) + ".evaluator") / "plan.json")])
            self.assertEqual(status, 0, errors.getvalue())
            result = json.loads(output.getvalue())
            self.assertEqual(result["dataset_sha256"], self.dataset_manifest["dataset_sha256"])
            self.assertEqual(result["planned"]["all_slots"], 177)

