"""Offline evaluator profile and full-denominator plan contract tests."""

import contextlib
import copy
import io
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from math_gauge.benchmarks import (BenchmarkProfile, build_plan, identity,
                                    read_plan, select_slots, validate_plan, write_plan)
from math_gauge.catalog import Suite, candidate_message, read_json, write_json
from math_gauge.cli import main

ROOT = Path(__file__).resolve().parents[1]
RUNTIME = {"model_label": "offline-fixture", "budget": {"timeout_seconds": 120},
           "adapter_identity": {"kind": "fixture"}}


class BenchmarkPlanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.suite = Suite.load(ROOT / "cases")
        cls.profile = BenchmarkProfile.load(ROOT / "protocol/benchmark-profile.json", cls.suite)
        cls.plan = build_plan(cls.profile, cls.suite, runtime=RUNTIME)

    def changed_profile(self, change):
        data = copy.deepcopy(self.profile.data)
        change(data)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "profile.json"
            write_json(path, data)
            return BenchmarkProfile.load(path, self.suite, repository_root=ROOT)

    def test_default_partition_and_full_frozen_plan(self):
        self.assertEqual([len(x["case_ids"]) for x in self.profile.data["components"]], [29, 6, 6, 2])
        self.assertEqual(self.plan["planned"], {
            "papers": 43, "independent_slots": 129, "neutral_slots": 16,
            "stance_slots": 32, "all_slots": 177, "selected_slots": 177})
        self.assertEqual({tag for c in self.plan["case_index"] for tag in c["focus_tags"]},
                         {f"F{i:02}" for i in range(1, 10)})
        self.assertEqual(self.plan["candidate_calls"], 0)
        self.assertTrue(all(x["case_approved"] is False for x in self.plan["case_index"]))
        for case in self.plan["case_index"]:
            approval = case["case_approval_source"]
            self.assertEqual(approval["status"], "draft")
            self.assertEqual(approval["human_review"], "pending")
            self.assertTrue((self.suite.root / approval["manifest"]).is_file())

    def test_self_rehashed_approval_claim_is_rejected_against_actual_suite_before_execution(self):
        from math_gauge.reliability import execute_reliability_run

        plan = copy.deepcopy(self.plan)
        row = plan["case_index"][0]
        row["case_approved"] = True
        with self.assertRaisesRegex(ValueError, "approval contradicts"):
            changed = dict(plan, plan_sha256=identity({k: v for k, v in plan.items() if k != "plan_sha256"}))
            validate_plan(changed)
        row["case_approval_source"].update(status="approved", human_review="approved")
        plan["plan_sha256"] = identity({k: v for k, v in plan.items() if k != "plan_sha256"})
        validate_plan(plan)
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "run"
            with patch("subprocess.Popen", side_effect=AssertionError("approval failure must precede execution")):
                with self.assertRaisesRegex(ValueError, "approval differs from its actual suite source"):
                    execute_reliability_run(plan, self.suite, output, replay={})
            self.assertFalse(output.exists())

    def test_in_memory_status_change_is_not_an_approval_source(self):
        suite = copy.copy(self.suite)
        suite.cases = copy.deepcopy(self.suite.cases)
        case = next(iter(suite.cases.values()))
        case["status"] = "approved"
        case["review"]["human"] = "approved"
        with self.assertRaisesRegex(ValueError, "approval source changed"):
            build_plan(self.profile, suite, runtime=RUNTIME)

    def test_targets_select_dependency_closures_without_changing_denominators(self):
        expected = {"proofs": 87, "lean-audit": 18, "lean-construction": 18,
                    "chapters": 6, "repeat": 129, "core": 129,
                    "neutral": 24, "stance": 40, "all": 177}
        for target, count in expected.items():
            with self.subTest(target=target):
                slots = select_slots(self.plan, [target])
                self.assertEqual(len(slots), count)
                selected = {x["slot_id"] for x in slots}
                self.assertTrue(all(x["parent_slot"] in selected
                                    for x in slots if x["parent_slot"]))
        self.assertEqual(len(select_slots(self.plan, ["neutral", "stance"])), 56)
        partial = build_plan(self.profile, self.suite, ["neutral"])
        self.assertEqual(len(partial["slots"]), 177)
        self.assertEqual(partial["planned"]["selected_slots"], 24)
        with self.assertRaises(ValueError):
            select_slots(partial, ["all"])

    def test_empty_unknown_and_duplicate_targets_rejected(self):
        for targets in ([], ["unknown"], ["core", "core"]):
            with self.subTest(targets=targets), self.assertRaises(ValueError):
                build_plan(self.profile, self.suite, targets)
            with self.assertRaises(ValueError):
                select_slots(self.plan, targets)

    def test_invalid_weights_rejected_instead_of_normalized(self):
        for weight in (-1, 0, True, 25.0, float("inf"), float("nan")):
            with self.subTest(weight=weight), self.assertRaises(ValueError):
                self.changed_profile(lambda d: d["components"][0].update(weight=weight))
        with self.assertRaises(ValueError):
            self.changed_profile(lambda d: d["overall_weights"].update(core=69))
        with self.assertRaises(ValueError):
            self.changed_profile(lambda d: d["overall_weights"].update(core=True))

    def test_profile_identity_and_partition_drift_rejected(self):
        mutations = [
            lambda d: d["suite"].update(id="another-suite"),
            lambda d: d["suite"].update(version="another-version"),
            lambda d: d["suite"].update(sha256="0" * 64),
            lambda d: d["components"][1]["case_ids"].append(d["components"][0]["case_ids"][0]),
            lambda d: d["components"][0]["case_ids"].pop(),
            lambda d: d.update(operator_only=False),
            lambda d: d.update(attempts=["A1"]),
        ]
        for mutate in mutations:
            with self.subTest(mutate=mutate), self.assertRaises(ValueError):
                self.changed_profile(mutate)

    def test_reclassification_and_selection_truth_or_suite_drift_rejected(self):
        def swap_categories(data):
            a, b = data["components"][0]["case_ids"], data["components"][3]["case_ids"]
            a[0], b[0] = b[0], a[0]
        with self.assertRaises(ValueError):
            self.changed_profile(swap_categories)
        for change in (
            lambda p: p["reliability"]["selection"].update(source_suite_sha256="0" * 64),
            lambda p: p["reliability"]["selection"]["cases"][0].update(expected_truth="unknown"),
        ):
            plan = copy.deepcopy(self.plan)
            change(plan)
            plan["plan_sha256"] = identity({k: v for k, v in plan.items() if k != "plan_sha256"})
            with self.assertRaises(ValueError):
                validate_plan(plan)

    def test_tampered_plan_and_self_rehashed_semantic_drift_rejected(self):
        plan = copy.deepcopy(self.plan)
        plan["slots"][0]["selected"] = False
        with self.assertRaises(ValueError):
            validate_plan(plan)
        for change in (
                lambda p: next(x for x in p["slots"] if x["slot_id"].endswith(":neutral:2")).update(
                    parent_slot="MG-GR002:affirm:1"),
                lambda p: p["slots"][0].update(context="shared-history"),
                lambda p: p["planned"].update(papers=1),
                lambda p: p.update(runtime_frozen=False)):
            plan = copy.deepcopy(self.plan)
            change(plan)
            plan["plan_sha256"] = identity({k: v for k, v in plan.items() if k != "plan_sha256"})
            with self.assertRaises(ValueError):
                validate_plan(plan)

    def test_profile_does_not_change_any_candidate_projection(self):
        for case in self.suite.cases.values():
            request = self.suite.request(case)
            before = candidate_message(request)
            self.assertNotIn("overall_weights", before)
            self.assertNotIn("benchmark-profile", before)
            self.assertEqual(before, candidate_message(request))

    def test_plan_and_cli_checks_are_offline_and_refuse_overwrite(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "plan.json"
            with patch("subprocess.Popen", side_effect=AssertionError("planning must not call a model")):
                write_plan(path, self.plan)
                self.assertEqual(read_plan(path)["plan_sha256"], self.plan["plan_sha256"])
                with contextlib.redirect_stdout(io.StringIO()) as output:
                    self.assertEqual(main(["benchmark-check", "--plan", str(path)]), 0)
                self.assertEqual(json.loads(output.getvalue())["candidate_calls"], 0)
            with self.assertRaises(ValueError):
                write_plan(path, self.plan)
            self.assertEqual(read_json(path)["candidate_calls"], 0)

    def test_runtime_identity_is_part_of_plan(self):
        other = build_plan(self.profile, self.suite, runtime={
            **RUNTIME, "budget": {"timeout_seconds": 121}})
        self.assertNotEqual(other["runtime_sha256"], self.plan["runtime_sha256"])
        for runtime in ({}, {"model_label": "x", "budget": {}, "adapter_identity": "x"},
                        {**RUNTIME, "budget": {"timeout_seconds": float("nan")}}):
            with self.assertRaises(ValueError):
                build_plan(self.profile, self.suite, runtime=runtime)

    def test_cli_replay_review_collect_and_same_plan_dependency_reuse(self):
        """Exercise the real CLI without models, Lean or invented model results."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            plan_path = root / "plan.json"
            write_plan(plan_path, self.plan)
            previous = []
            for target in ("neutral", "stance"):
                replay = root / (target + "-replay.json")
                slots = select_slots(self.plan, [target])
                write_json(replay, {s["slot_id"]: (
                    "Synthetic offline transport fixture; no mathematical model result."
                    if s["kind"] == "independent" else "KEEP\nSynthetic incomplete audit rationale.")
                    for s in slots})
                run_path = root / target
                arguments = ["benchmark-run", "--plan", str(plan_path), "--suite", str(ROOT / "cases"),
                             "--target", target, "--out", str(run_path), "--replay", str(replay)]
                if previous:
                    arguments += ["--reuse-run", str(previous[0])]
                with patch("subprocess.Popen", side_effect=AssertionError("offline fixture may not invoke a process")):
                    with contextlib.redirect_stdout(io.StringIO()):
                        self.assertEqual(main(arguments), 0)
                        template = root / (target + "-template.json")
                        self.assertEqual(main(["benchmark-review-template", "--run", str(run_path),
                                               "--out", str(template)]), 0)
                        reviews = read_json(template)
                        if previous:
                            reviews = [r for r in reviews if not r["slot_id"].endswith(":A1")]
                        for entry in reviews:
                            entry.update(reviewer="Offline transport fixture", reviewer_kind="fixture",
                                         decision="partial", notes="Synthetic fixture, not an actual mathematical judgment.")
                            entry["format_review"].update(decision="valid", notes="Fixture mode and material were reconstructed.")
                            for stage in entry["stages"]:
                                stage.update(decision="partial", failure_category="mathematical",
                                             notes="Synthetic incomplete stage; no model mathematics was assessed.")
                                stage["math_review"].update(decision="partial", reasons=["candidate_incomplete"],
                                                            notes="Synthetic incomplete mathematical obligation.")
                            for key in ("focus_review", "keep_rationale_review"):
                                if key in entry:
                                    entry[key].update(decision="partial", reasons=["candidate_incomplete"],
                                                      notes="Synthetic incomplete focus or rationale.")
                        reviewed = root / (target + "-reviewed.json")
                        write_json(reviewed, reviews)
                        self.assertEqual(main(["benchmark-review", "--run", str(run_path), "--input", str(reviewed)]), 0)
                        self.assertEqual(main(["benchmark-check", "--run", str(run_path)]), 0)
                        self.assertEqual(main(["benchmark-collect", "--run", str(run_path),
                                               "--out", str(root / (target + "-collected.json"))]), 0)
                        if target == "neutral":
                            collected = read_json(root / "neutral-collected.json")
                            expected = collected["review_snapshot"]["sha256"]
                            snapshot_path = run_path / "review-snapshots/000001.json"
                            snapshot_bytes = snapshot_path.read_bytes()
                            revision = copy.deepcopy(reviews[:1])
                            revision[0]["notes"] += " Retained fixture review revision."
                            revision_path = root / "fixture-revision.json"
                            write_json(revision_path, revision)
                            with contextlib.redirect_stderr(io.StringIO()):
                                self.assertEqual(main(["benchmark-review", "--run", str(run_path),
                                    "--input", str(revision_path), "--revise",
                                    "--expected-review-snapshot", "0" * 64]), 2)
                            self.assertEqual(main(["benchmark-review", "--run", str(run_path),
                                "--input", str(revision_path), "--revise",
                                "--expected-review-snapshot", expected]), 0)
                            self.assertEqual(snapshot_path.read_bytes(), snapshot_bytes)
                            self.assertEqual(main(["benchmark-collect", "--run", str(run_path),
                                "--review-snapshot", "1", "--out", str(root / "retained-review.json")]), 0)
                            self.assertEqual(read_json(root / "retained-review.json")["review_snapshot"]["version"], 1)
                previous.append(run_path)
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(main(["benchmark-report", "--run", str(previous[0]),
                                       "--run", str(previous[1]), "--out", str(root / "report")]), 0)
            result = read_json(root / "report/report.json")
            self.assertEqual(result["result_kind"], "fixture")
            self.assertFalse(result["model_result"])
            self.assertEqual(result["metrics"]["neutral"]["exact"], 0)
            self.assertEqual(result["metrics"]["stance"]["exact"], 0)
            self.assertIsNone(result["metrics"]["overall"]["exact"])
            self.assertIsNone(result["metrics"]["overall"]["formal_score"])
            self.assertEqual([x["review_snapshot"]["version"] for x in result["review_snapshots"]], [2, 1])
            reused = read_json(previous[1] / "run.json")
            self.assertEqual(len(reused["reused_from"]), 8)
            self.assertEqual(reused["candidate_calls"], 0)
            self.assertEqual(Suite.load(ROOT / "cases").sha256, self.suite.sha256)


if __name__ == "__main__":
    unittest.main()
