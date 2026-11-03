"""Two-attempt, one-follow-up contracts using synthetic evidence only."""

import copy
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from math_gauge.benchmarks import (BenchmarkProfile, build_plan, identity,
                                   reliability_schedule, select_slots, validate_plan)
from math_gauge.catalog import digest_bytes, read_json, write_json
from math_gauge.harness import (candidate_request_from_bundle, export_harness_bundle,
    export_release_dataset, export_simple_release_dataset, freeze_release_runtime,
    inspect_harness_bundle, inspect_release_dataset, make_release_anchor)
from math_gauge.harness_answers import (issue_answer_request, pack_answer_archive,
                                        record_answer_attempt)
from math_gauge.harness_import import import_answer_archive
from math_gauge.reliability import (apply_reliability_reviews, execute_reliability_run,
    inspect_reliability_run, reliability_review_templates, reliability_score_inputs)
from math_gauge.scoring import (public_score_projection, render_score,
                                score_composed_runs, score_inputs, score_runs)
from test_composite_suites import synthetic_profile, synthetic_suite

CID = "SYN-COMPACT"
RUNTIME = {"model_label": "compact-offline-fixture", "adapter_identity": {"kind": "fixture"},
           "candidate_parameters": {"model": "synthetic-no-model-calls"},
           "budget": {"timeout_seconds": 2}, "fresh_context": True}


def compact_profile(root, suite, legacy):
    root.mkdir(parents=True)
    data = copy.deepcopy(legacy.data)
    data["version"] = "compact-fixture"
    data["reliability"]["protocol_version"] = "0.3.0"
    data["attempt_schedule"] = {cid: ["A1", "A2"] for cid in suite.cases}
    data["score_policy"]["repeat_attempt_labels"] = ["A1", "A2"]
    data["overall_weights"] = {"core": 75, "repeat": 5, "neutral": 10, "stance": 10}
    for key in ("selection", "prompts", "schedule"):
        value = read_json(legacy.root / legacy.data["reliability"][key])
        value["protocol_version"] = "0.3.0"
        if key == "prompts":
            value["messages"] = [row for row in value["messages"] if row["round"] == 1]
        if key == "schedule":
            value["slots"] = [row for row in value["slots"]
                              if row.get("attempt_label") != "A3" and row.get("round", 1) == 1]
            for ordinal, row in enumerate(value["slots"], 1):
                row["ordinal_per_model"] = ordinal
        write_json(root / data["reliability"][key], value)
    write_json(root / "profile.json", data)
    return BenchmarkProfile.load(root / "profile.json", suite, repository_root=root)


def fixture_rows(plan):
    return [{"slot_id": slot["slot_id"], "case_id": slot["case_id"], "started": True,
             "fixture_only": True, "origin": "fixture", "reviewer_kind": "fixture",
             "strict_pass": True, "completion": {"lower": 1, "upper": 1, "exact": 1},
             **{axis: {"state": "C", "reasons": [], "adjudicated": True}
                for axis in ("whole_strict", "whole_math", "focus_math")}}
            for slot in plan["slots"]]


def complete_reviews(root):
    rows = reliability_review_templates(root)
    def math_pass(value):
        value.update(decision="pass", assumption_fidelity="clean", proof_validity="valid",
                     scope_accuracy="correct", unnecessary_restriction=False, reasons=[],
                     notes="Synthetic complete evidence only.")
    for row in rows:
        math_pass(row)
        row.update(reviewer="compact protocol synthetic fixture reviewer", reviewer_kind="fixture",
                   format_review={"decision": "valid", "notes": "Synthetic complete raw bytes."})
        for stage in row["stages"]:
            math_pass(stage)
            stage.update(failure_category="none")
            math_pass(stage["math_review"])
        if "focus_review" in row:
            math_pass(row["focus_review"])
            row["focus_review"]["verdict"] = "true"
        if "keep_rationale_review" in row:
            math_pass(row["keep_rationale_review"])
    apply_reliability_reviews(root, rows)


class CompactProtocolTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="math-gauge-compact-protocol-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.suite = synthetic_suite(self.root / "cases", CID, visibility="public", research=False)
        self.legacy = synthetic_profile(self.root / "legacy", self.suite, repeated=[CID])
        self.profile = compact_profile(self.root / "compact", self.suite, self.legacy)
        self.plan = build_plan(self.profile, self.suite, runtime=RUNTIME)

    def score(self, rows):
        return score_inputs({"plan": self.plan, "model_label": RUNTIME["model_label"], "slots": rows})

    def test_versioned_plans_retain_legacy_and_compact_denominators(self):
        old = build_plan(self.legacy, self.suite, runtime=RUNTIME)
        self.assertEqual(old["planned"], {"papers": 1, "independent_slots": 3,
            "neutral_slots": 2, "stance_slots": 4, "all_slots": 9, "selected_slots": 9})
        self.assertEqual(self.plan["planned"], {"papers": 1, "independent_slots": 2,
            "neutral_slots": 1, "stance_slots": 2, "all_slots": 5, "selected_slots": 5})
        self.assertEqual({s["slot_id"] for s in select_slots(self.plan, ["repeat"])},
                         {CID + ":A1", CID + ":A2"})
        self.assertEqual(len(select_slots(self.plan, ["neutral"])), 2)
        for version in ("0.1.0", "0.2.0"):
            self.assertEqual(reliability_schedule(version), (("A1", "A2", "A3"), (1, 2)))
        for profile, labels in ((self.profile, ["A1", "A2", "A3"]), (self.legacy, ["A1", "A2"])):
            changed = copy.deepcopy(profile.data)
            changed["attempt_schedule"][CID] = labels
            path = profile.root / "invalid.json"
            write_json(path, changed)
            with self.assertRaisesRegex(ValueError, "independent arrangement"):
                BenchmarkProfile.load(path, self.suite, repository_root=profile.root)
        changed = copy.deepcopy(self.plan)
        changed["reliability"]["protocol_version"] = "0.2.0"
        changed["plan_sha256"] = identity({k: v for k, v in changed.items() if k != "plan_sha256"})
        with self.assertRaisesRegex(ValueError, "protocol versions differ"):
            validate_plan(changed)

    def test_repeat_requires_both_strict_and_missing_credit_remains_unresolved(self):
        for first, second, expected in ((False, False, 0), (True, False, 0), (True, True, 100),
                                        (True, None, None)):
            with self.subTest(first=first, second=second):
                rows = fixture_rows(self.plan)
                for row, value in zip(rows[:2], (first, second)):
                    row["strict_pass"] = value
                    if value is False:
                        row["completion"] = {"lower": 0, "upper": 0, "exact": 0}
                        for axis in ("whole_strict", "whole_math", "focus_math"):
                            row[axis] = {"state": "I", "reasons": ["mathematical"], "adjudicated": True}
                report = self.score(rows)
                self.assertEqual(report["metrics"]["repeat"]["exact"], expected)
                self.assertEqual(report["papers"][CID]["repeat_all_strict"], expected)
                self.assertEqual(report["papers"][CID]["two_of_two"], expected)
                self.assertIsNone(report["papers"][CID]["three_of_three"])
        report = self.score([r for r in fixture_rows(self.plan) if r["slot_id"] != CID + ":A2"])
        self.assertIsNone(report["metrics"]["overall"]["exact"])
        self.assertEqual((report["metrics"]["overall"]["lower"], report["metrics"]["overall"]["upper"]), (95, 100))
        self.assertEqual(report["metrics"]["strict_pass_rate"]["coverage"]["planned"], 2)

    def test_retired_attempts_rounds_and_cross_branch_parents_are_rejected(self):
        old = build_plan(self.legacy, self.suite, runtime=RUNTIME)
        for sid in (CID + ":A3", CID + ":neutral:2"):
            with self.subTest(slot_id=sid):
                changed = copy.deepcopy(self.plan)
                changed["slots"].append(next(s for s in old["slots"] if s["slot_id"] == sid))
                changed["plan_sha256"] = identity({k: v for k, v in changed.items() if k != "plan_sha256"})
                with self.assertRaisesRegex(ValueError, "independent and followup slots"):
                    validate_plan(changed)
        changed = copy.deepcopy(self.plan)
        next(s for s in changed["slots"] if s["slot_id"] == CID + ":neutral:1")["parent_slot"] = CID + ":A2"
        changed["plan_sha256"] = identity({k: v for k, v in changed.items() if k != "plan_sha256"})
        with self.assertRaisesRegex(ValueError, "fixed A1 branch"):
            validate_plan(changed)

    def test_one_round_metrics_public_projection_and_transition_display(self):
        report = self.score(fixture_rows(self.plan))
        self.assertEqual(report["metrics"]["overall"]["exact"], 100)
        self.assertEqual(report["metrics"]["neutral"]["coverage"]["planned"], 1)
        self.assertEqual(report["metrics"]["stance"]["coverage"]["planned"], 2)
        self.assertEqual(set(report["paired_stance"]["rounds"]), {"1"})
        for arm in report["trajectories"]["focus_math"].values():
            self.assertEqual(arm["trajectories"], {"C->C": 1})
            self.assertNotIn("round2", arm)
            self.assertNotIn("A1_to_round2", arm)
        self.assertNotIn("Round 2", render_score(report))
        projection = public_score_projection(report, self.plan, private_aliases={})
        self.assertEqual(projection["profile"]["repeat_attempt_labels"], ["A1", "A2"])
        self.assertEqual(projection["profile"]["self_check_rounds_per_arm"], 1)
        self.assertNotIn("repeat_case_ids", projection["profile"])

    def legacy_run(self):
        old = build_plan(self.legacy, self.suite, runtime=RUNTIME)
        run = self.root / "legacy-run"
        execute_reliability_run(old, self.suite, run, replay={
            s["slot_id"]: "Synthetic raw initial.\r\n" if s["kind"] == "independent"
            else "KEEP\r\nSynthetic rationale.\r\n" for s in old["slots"]})
        complete_reviews(run)
        return run

    def test_cross_schedule_composition_reuses_only_identical_a1_a2_and_r1(self):
        run = self.legacy_run()
        before = {str(p.relative_to(run)): p.read_bytes() for p in run.rglob("*") if p.is_file()}
        report = score_composed_runs(self.plan, [run])
        self.assertEqual(report["metrics"]["overall"]["exact"], 100)
        self.assertEqual(report["composition"]["new_candidate_calls"], 0)
        self.assertEqual(set(report["composition"]["source_runs"][0]["selected_slot_ids"]),
                         {s["slot_id"] for s in self.plan["slots"]})
        self.assertFalse(report["formal_eligibility"]["eligible"])
        self.assertEqual(before, {str(p.relative_to(run)): p.read_bytes() for p in run.rglob("*") if p.is_file()})
        changed = copy.deepcopy(self.plan)
        prompt = changed["reliability"]["prompts"]["messages"][0]
        prompt["content"] += " A changed request."
        prompt["content_sha256"] = digest_bytes(prompt["content"].encode())
        changed["plan_sha256"] = identity({k: v for k, v in changed.items() if k != "plan_sha256"})
        with self.assertRaisesRegex(ValueError, "original followup prompt"):
            score_composed_runs(changed, [run])
        changed = copy.deepcopy(self.plan)
        changed["case_index"][0]["candidate_message_sha256"] = "0" * 64
        changed["plan_sha256"] = identity({k: v for k, v in changed.items() if k != "plan_sha256"})
        with self.assertRaisesRegex(ValueError, "candidate input or review contract"):
            score_composed_runs(changed, [run])

    def test_frozen_report_reuse_still_checks_original_response_and_review_hashes(self):
        run = self.legacy_run()
        report_path = self.root / "original-report.json"
        write_json(report_path, score_runs([run]))
        snapshot = read_json(run / "reliability-reviews.json")["snapshots"][0]
        reference = {"path": str(report_path), "sha256": digest_bytes(report_path.read_bytes()),
                     "review_snapshot_sha256": snapshot["snapshot_sha256"]}
        report = score_composed_runs(self.plan, [run], frozen_reports={str(run): reference})
        self.assertEqual(report["metrics"]["overall"]["exact"], 100)
        reuse = report["composition"]["source_runs"][0]["frozen_report_reuse"]
        self.assertFalse(reuse["current_engine_reverification_claimed"])
        _, records = inspect_reliability_run(run)
        raw = run / records[CID + ":neutral:1"]["response_path"]
        original = raw.read_bytes()
        raw.write_bytes(original + b"changed")
        with self.assertRaisesRegex(ValueError, "response changed|transport budget evidence changed"):
            score_composed_runs(self.plan, [run], frozen_reports={str(run): reference})
        raw.write_bytes(original)
        review = run / snapshot["path"]
        review.write_bytes(review.read_bytes() + b"\n")
        with self.assertRaisesRegex(ValueError, "review snapshot"):
            score_composed_runs(self.plan, [run], frozen_reports={str(run): reference})

    def test_portable_controller_and_release_answer_archive_share_the_new_schedule(self):
        bundle = self.root / "bundle"
        export_harness_bundle(self.plan, self.suite, bundle)
        self.assertEqual(inspect_harness_bundle(bundle)["exported_slots"], 5)
        raw_a1 = "Synthetic raw A1.\r\n"
        expected = candidate_request_from_bundle(bundle, CID + ":neutral:1", {CID + ":A1": raw_a1})
        self.assertEqual(expected["messages"][-2]["content"], raw_a1)
        self.assertEqual(len(expected["messages"]), 3)
        checked = subprocess.run([sys.executable, str(bundle / "controller.py"), "check", "--bundle", str(bundle)],
                                 capture_output=True, text=True)
        self.assertEqual(checked.returncode, 0, checked.stderr)
        base = build_plan(self.profile, self.suite)
        generic = self.root / "generic-release"
        self.assertEqual(export_release_dataset(base, self.suite, generic)["exported_slots"], 5)
        dataset = self.root / "dataset"
        manifest = export_simple_release_dataset(base, self.suite, dataset,
            release_version=self.suite.metadata["version"], readme=b"Synthetic controller fixture.\n",
            extra_files={"LICENSE": b"Synthetic license\n", "THIRD_PARTY_NOTICES.md": b"Synthetic notice\n"})
        self.assertEqual(inspect_release_dataset(dataset)["exported_slots"], 5)
        checked = subprocess.run([sys.executable, str(dataset / "tools/benchmark.py"), "check", "--bundle", str(dataset)],
                                 capture_output=True, text=True)
        self.assertEqual(checked.returncode, 0, checked.stderr)
        frozen, responses = self.root / "release-run", self.root / "responses"
        freeze_release_runtime(dataset, RUNTIME, frozen)
        for index, slot in enumerate(base["slots"]):
            sid = slot["slot_id"]
            request, raw = self.root / f"request-{index}.json", self.root / "response.bin"
            wire = issue_answer_request(frozen, responses, sid, request)
            if slot["kind"] == "followup":
                self.assertEqual(wire["messages"][-2]["content"], raw_a1)
            raw.write_bytes(raw_a1.encode() if slot["kind"] == "independent" else b"KEEP\r\nSynthetic reason.\r\n")
            record_answer_attempt(frozen, responses, sid, request, raw, status="ok")
        archive, imported = self.root / "answers.zip", self.root / "imported"
        pack_answer_archive(frozen, responses, archive)
        import_answer_archive(archive, make_release_anchor(base, manifest), self.suite, imported)
        _, records = inspect_reliability_run(imported)
        self.assertEqual(set(records), {s["slot_id"] for s in base["slots"]})
        complete_reviews(imported)
        self.assertEqual(score_runs([imported])["metrics"]["overall"]["exact"], 100)
        self.assertEqual(len(reliability_score_inputs(imported)["slots"]), 5)


if __name__ == "__main__":
    unittest.main()
