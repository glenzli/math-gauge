"""Synthetic independently rooted data exercise the existing runner/review chain."""

import contextlib
import copy
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from math_gauge.benchmarks import BenchmarkProfile, build_plan, identity, select_slots
from math_gauge.catalog import Suite, candidate_message, digest_bytes, read_json, write_json
from math_gauge.cli import main, parser
from math_gauge.harness import export_harness_bundle, inspect_harness_bundle
from math_gauge.reliability import execute_reliability_run
from math_gauge.reliability_review import apply_reliability_reviews, reliability_review_templates
from math_gauge.scoring import public_score_projection, score_composed_runs, score_runs

RUNTIME = {"model_label": "synthetic-composition-fixture", "adapter_identity": {"kind": "fixture"},
           "candidate_parameters": {"model": "fixture"}, "budget": {"timeout_seconds": 1},
           "fresh_context": True}


def synthetic_suite(root, cid, *, suite_id=None, visibility="private", research=True):
    root = Path(root)
    case = {"schema": "math-gauge.case/v1", "id": cid, "version": "fixture-1",
            "title": "Synthetic data only", "language": "en", "path_base": "case",
            "track": "exploration" if research else "determinate", "task_kind": "written",
            "visibility": visibility, "status": "draft", "review": {"human": "pending"},
            "sources": ["synthetic"], "task": "task.md", "reference": "reference.md",
            "rubric": "rubric.json", "group_contract": "contract.json",
            "candidate_instruction": "", "solver_files": [{"source": "input.txt", "target": "input.txt"}],
            "lean_checks": [], "evaluator_files": []}
    write_json(root / "suite.json", {"schema": "math-gauge.suite/v1", "id": suite_id or "suite-" + cid,
               "version": "1.2.3", "visibility": visibility, "cases": ["paper/case.json"]})
    write_json(root / "sources.json", {"synthetic": {"kind": "synthetic", "title": "No real mathematical data"}})
    write_json(root / "paper/case.json", case)
    (root / "paper/task.md").write_bytes(b"Synthetic task only.\r\n")
    (root / "paper/input.txt").write_bytes(b"Complete synthetic attachment.\r\n")
    (root / "paper/reference.md").write_text("EVALUATOR_PRIVATE_REFERENCE_SENTINEL\n")
    write_json(root / "paper/rubric.json", {"schema": "math-gauge.rubric/v1",
               "expected": "open" if research else "true", "required_evidence": ["Synthetic criterion"],
               "critical_errors": ["EVALUATOR_PRIVATE_RUBRIC_SENTINEL"]})
    if research:
        contract = {"schema": "math-gauge.group-contract/v2", "kind": "research_exploration",
                    "id": cid, "version": case["version"], "assessment_unit": "review_dimension",
                    "dimensions": [{"id": "D" + str(i), "title": "Synthetic dimension " + str(i),
                                    "points": 4, "required_evidence": ["Bounded synthetic credit"],
                                    "critical_errors": ["Do not invent a result"]} for i in range(1, 5)]}
    else:
        contract = {"schema": "math-gauge.group-contract/v1", "kind": "progressive", "id": cid,
                    "version": case["version"], "all_stages_mandatory": True,
                    "stages": [{"id": "S" + str(i), "kind": "prove", "expected": "true",
                                "depends_on": [], "points": 1, "lean_required": False,
                                "assumptions": ["Synthetic"], "required_evidence": ["Synthetic"],
                                "critical_errors": ["Synthetic"]} for i in range(1, 6)],
                    "turns": [{"stage_id": "S2", "earlier_stage_ids": ["S1"], "expected_truth": "true",
                               "mechanism": "Synthetic", "changed_assumptions": "Synthetic",
                               "tempting_invalid_transfer": "Synthetic", "correct_boundary": "Synthetic"}]}
    write_json(root / "paper/contract.json", contract)
    return Suite.load(root)


def synthetic_profile(root, suite, *, repeated=None):
    """The fixture uses original scheduling and no second runner implementation."""
    root = Path(root)
    repeated = list(repeated or [])
    components = []
    for component, kind in (("proofs", "progressive"), ("exploration", "research_exploration")):
        ids = [cid for cid, case in suite.cases.items()
               if read_json(suite.case_file(cid, case["group_contract"]))["kind"] == kind]
        if ids:
            components.append({"id": component, "weight": 100, "case_ids": ids})
    if len(components) == 2:
        for component in components:
            component["weight"] = 50
    attempts = {cid: ["A1", "A2", "A3"] if cid in repeated else ["A1"] for cid in suite.cases}
    slots, messages = [], []
    for cid, labels in attempts.items():
        for label in labels:
            slots.append({"slot_id": cid + ":" + label, "case_id": cid, "kind": "independent",
                          "attempt_label": label, "context": "fresh", "parent_slot": None,
                          "message_id": None, "ordinal_per_model": len(slots) + 1})
    for cid in repeated:
        for arm in ("neutral", "affirm", "deny"):
            for rnd in (1, 2):
                sid = f"{cid}:{arm}:{rnd}"
                slots.append({"slot_id": sid, "case_id": cid, "kind": "followup", "arm": arm,
                              "round": rnd, "context": "branch-history-only",
                              "parent_slot": f"{cid}:A1" if rnd == 1 else f"{cid}:{arm}:1",
                              "message_id": sid, "ordinal_per_model": len(slots) + 1})
                text = "Synthetic followup. Use KEEP or FULL."
                messages.append({"message_id": sid, "case_id": cid, "arm": arm, "round": rnd,
                                 "role": "user", "content": text, "content_sha256": digest_bytes(text.encode())})
    selection = {"protocol_version": "0.2.0", "source_suite_sha256": suite.sha256,
                 "case_count": len(repeated), "truth_counts": {"true": len(repeated)} if repeated else {},
                 "cases": [{"case_id": cid, "stage_id": "S1", "expected_truth": "true"} for cid in repeated]}
    for name, value in (("selection", selection), ("prompts", {"protocol_version": "0.2.0", "messages": messages}),
                        ("schedule", {"protocol_version": "0.2.0", "slots": slots})):
        write_json(root / (name + ".json"), value)
    profile = {"schema": "math-gauge.benchmark-profile/v3", "id": "synthetic-composition",
               "version": "fixture-1", "operator_only": True, "path_base": "repository",
               "suite": {"id": suite.metadata["id"], "version": suite.metadata["version"], "sha256": suite.sha256},
               "components": components, "attempt_schedule": attempts,
               "score_policy": {"core_attempt_labels": ["A1"], "repeat_case_ids": repeated,
                                "repeat_attempt_labels": ["A1", "A2", "A3"]},
               "overall_weights": {"core": 70, "repeat": 10, "neutral": 10, "stance": 10} if repeated else
                                  {"core": 100, "repeat": 0, "neutral": 0, "stance": 0},
               "reliability": {"protocol_version": "0.2.0", "selection": "selection.json",
                               "prompts": "prompts.json", "schedule": "schedule.json"}}
    path = root / "profile.json"
    write_json(path, profile)
    return BenchmarkProfile.load(path, suite, repository_root=root)


def research_review(root, scores):
    reviews = reliability_review_templates(root)
    for row in reviews:
        row.update(reviewer="synthetic reviewer", reviewer_kind="fixture", decision="partial",
                   assumption_fidelity="clean", proof_validity="valid", scope_accuracy="correct",
                   notes="Synthetic assessment; no mathematical or model claim", findings=[],
                   format_review={"decision": "valid", "notes": "Original complete fixture bytes"})
        for dimension, score in zip(row["dimensions"], scores):
            dimension.update(score=score, notes="Synthetic bounded credit")
        if all(score == 4 for score in scores):
            row["decision"] = "pass"
    apply_reliability_reviews(root, reviews)


class CompositeSuiteTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="math-gauge-composition-fixture-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.first = synthetic_suite(self.root / "first/cases", "SYN-X")
        self.second = synthetic_suite(self.root / "second/cases", "SYN-Y")
        self.suite = Suite.load([self.first.root, self.second.root])

    def test_independent_roots_preserve_input_bytes_and_frozen_member_identity(self):
        self.assertEqual(set(self.suite.cases), {"SYN-X", "SYN-Y"})
        for member in (self.first, self.second):
            cid = next(iter(member.cases))
            self.assertEqual(self.suite.request(self.suite.cases[cid]), member.request(member.cases[cid]))
            self.assertEqual(self.suite.source_binding(cid)["sha256"], member.sha256)
            self.assertNotIn("EVALUATOR_PRIVATE", candidate_message(self.suite.request(self.suite.cases[cid])))
        manifest = self.root / "combined.json"
        write_json(manifest, {"schema": "math-gauge.suite-composition/v1", "id": "synthetic-combined",
                   "version": "1.2.3", "suites": [{"path": str(m.root), **m.source_binding(next(iter(m.cases)))}
                                                for m in (self.first, self.second)]})
        frozen = Suite.load(manifest)
        self.assertEqual(frozen.reload().sha256, frozen.sha256)
        (self.second.root / "paper/reference.md").write_text("Changed evaluator material")
        with self.assertRaisesRegex(ValueError, "different suite identity"):
            frozen.reload()

    def test_duplicate_ids_and_output_inside_any_source_are_rejected(self):
        duplicate = synthetic_suite(self.root / "duplicate/cases", "SYN-X", suite_id="another-source")
        with self.assertRaisesRegex(ValueError, "Duplicate case across suites"):
            Suite.load([self.first.root, duplicate.root])
        with self.assertRaisesRegex(ValueError, "outside the question suite"):
            self.suite.prepare(self.suite.cases["SYN-X"], self.second.root / "bad")
        self.assertFalse((self.second.root / "bad").exists())

    def test_repeated_cli_suite_option_does_not_change_the_default(self):
        self.assertEqual(parser().parse_args(["validate"]).suite, "cases")
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            code = main(["validate", "--suite", str(self.first.root), "--suite", str(self.second.root)])
        self.assertEqual(code, 0)
        self.assertIn('"cases": 2', output.getvalue())

    def test_existing_runner_reviews_credit_dimensions_and_keeps_missing_denominators(self):
        target_profile = synthetic_profile(self.root / "target-profile", self.suite)
        target_plan = build_plan(target_profile, self.suite, runtime=RUNTIME)
        source_profile = synthetic_profile(self.root / "source-profile", self.first)
        source_plan = build_plan(source_profile, self.first, runtime=RUNTIME)
        run = self.root / "source-run"
        execute_reliability_run(source_plan, self.first, run, replay={"SYN-X:A1": "Synthetic original answer\r\n"})
        research_review(run, [3, 3, 3, 3])
        original = score_runs([run])
        self.assertEqual(original["metrics"]["core"]["exact"], 75)
        self.assertFalse(original["papers"]["SYN-X"]["three_of_three"])
        with patch("math_gauge.execution.invoke_conversation", side_effect=AssertionError("No new calls")):
            report = score_composed_runs(target_plan, [run])
        score = report["metrics"]["core"]
        self.assertEqual((score["exact"], score["lower"], score["upper"]), (None, 37.5, 87.5))
        self.assertEqual(report["composition"]["new_candidate_calls"], 0)
        safe = public_score_projection(report, target_plan,
            private_aliases={"SYN-X": "Private-01", "SYN-Y": "Private-02"},
            source_kinds={"SYN-X": "existing_private", "SYN-Y": "new_private"})
        self.assertEqual(safe["coverage"]["slots_planned"], 2)
        self.assertEqual(safe["coverage"]["slots_reviewed"], 1)
        self.assertEqual(safe["private_records"][0]["completion"]["exact"], 0.75)
        import json
        public = json.dumps(safe)
        for hidden in ("SYN-X", "SYN-Y", str(self.root), "paper/contract", "EVALUATOR_PRIVATE"):
            self.assertNotIn(hidden, public)
        with self.assertRaisesRegex(ValueError, "neutral public alias"):
            public_score_projection(report, target_plan, private_aliases={})

    def test_combined_public_and_private_bundle_keeps_only_candidate_projection(self):
        public = synthetic_suite(self.root / "public/cases", "SYN-P", visibility="public", research=False)
        suite = Suite.combine([public, self.first, self.second], suite_id="synthetic-combined", version="1.2.3")
        profile = synthetic_profile(self.root / "combined-profile", suite, repeated=["SYN-P"])
        plan = build_plan(profile, suite)
        self.assertEqual(plan["planned"]["all_slots"], 11)
        self.assertEqual(len(select_slots(plan, ["exploration"])), 2)
        bundle = self.root / "bundle"
        export_harness_bundle(plan, suite, bundle)
        inspect_harness_bundle(bundle, plan=plan, suite=suite)
        for file in bundle.rglob("*"):
            if file.is_file():
                self.assertNotIn(b"EVALUATOR_PRIVATE", file.read_bytes())
        with self.assertRaisesRegex(ValueError, "overlap the question suite"):
            export_harness_bundle(plan, suite, self.second.root / "bad")

    def test_composition_rejects_changed_execution_conditions_and_requires_explicit_budget_strata(self):
        profile = synthetic_profile(self.root / "source-profile", self.first)
        source_plan = build_plan(profile, self.first, runtime=RUNTIME)
        run = self.root / "source-run"
        execute_reliability_run(source_plan, self.first, run, replay={"SYN-X:A1": "Synthetic original answer"})
        research_review(run, [3, 3, 3, 3])
        changed = copy.deepcopy(RUNTIME)
        changed["execution_track"] = "math-gauge.local-tools-no-search/v1"
        target = build_plan(profile, self.first, runtime=changed)
        with self.assertRaisesRegex(ValueError, "execution condition"):
            score_composed_runs(target, [run])
        changed = copy.deepcopy(RUNTIME)
        changed["candidate_parameters"]["reasoning_effort"] = "max"
        with self.assertRaisesRegex(ValueError, "generation parameters"):
            score_composed_runs(build_plan(profile, self.first, runtime=changed), [run])
        changed = copy.deepcopy(RUNTIME)
        changed["budget"]["timeout_seconds"] = 2
        target = build_plan(profile, self.first, runtime=changed)
        with self.assertRaisesRegex(ValueError, "source time budget"):
            score_composed_runs(target, [run])
        report = score_composed_runs(target, [run], budget_policy="retain_source_budgets")
        self.assertEqual(report["metrics"]["overall"]["exact"], 75)
        self.assertEqual(report["composition"]["source_runs"][0]["budget"]["timeout_seconds"], 1)

    def test_explicit_frozen_report_reuse_checks_original_hashes_without_current_review_revalidation(self):
        profile = synthetic_profile(self.root / "source-profile", self.first)
        plan = build_plan(profile, self.first, runtime=RUNTIME)
        run = self.root / "source-run"
        execute_reliability_run(plan, self.first, run, replay={"SYN-X:A1": "Synthetic original answer"})
        research_review(run, [3, 3, 3, 3])
        saved = score_runs([run])
        path = self.root / "frozen-score.json"
        write_json(path, saved)
        index = read_json(run / "reliability-reviews.json")
        reference = {"path": str(path), "sha256": digest_bytes(path.read_bytes()),
                     "review_snapshot_sha256": index["snapshots"][0]["snapshot_sha256"]}
        with patch("math_gauge.reliability_review._validate_entry", side_effect=AssertionError("Retain old review identity")):
            reused = score_composed_runs(plan, [run], frozen_reports={str(run): reference})
        self.assertEqual(reused["metrics"]["core"]["exact"], 75)
        self.assertFalse(reused["metrics"]["core"]["formal_comparison_eligible"])
        receipt = reused["composition"]["source_runs"][0]["frozen_report_reuse"]
        self.assertFalse(receipt["current_engine_reverification_claimed"])
        path.write_bytes(path.read_bytes() + b" ")
        with self.assertRaisesRegex(ValueError, "Frozen score report changed"):
            score_composed_runs(plan, [run], frozen_reports={str(run): reference})


if __name__ == "__main__":
    unittest.main()
