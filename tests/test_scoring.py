"""Synthetic arithmetic and provenance checks; these are never model results."""

import copy
import unittest
from fractions import Fraction
from unittest.mock import patch
from pathlib import Path

from math_gauge.benchmarks import BenchmarkProfile, build_plan, identity
from math_gauge.catalog import Suite
from math_gauge.scoring import render_score, score_inputs, score_runs

ROOT = Path(__file__).resolve().parents[1]
RUNTIME = {"model_label": "offline-fixture", "budget": {"timeout_seconds": 120},
           "adapter_identity": {"kind": "fixture"}}


def axis(state="C", reasons=None, adjudicated=True):
    return {"state": state, "reasons": reasons or [], "adjudicated": adjudicated}


def fixture_rows(plan, completions=None):
    completions = completions or {k: 1 for k in
                                  ("proofs", "lean-audit", "lean-construction", "chapters")}
    cases = {x["case_id"]: x for x in plan["case_index"]}
    rows = []
    for slot in plan["slots"]:
        value = completions[cases[slot["case_id"]]["component"]]
        rows.append({"slot_id": slot["slot_id"], "case_id": slot["case_id"],
                     "started": True, "origin": "fixture", "fixture_only": True,
                     "evidence_id": "fixture:" + slot["slot_id"],
                     "slot_record_sha256": identity(slot),
                     "reviewer_kind": "fixture", "comparison_eligible": False,
                     "strict_pass": value == 1,
                     "completion": {"lower": value, "upper": value, "exact": value},
                     "whole_strict": axis("C" if value == 1 else "U", ["candidate_incomplete"]),
                     "whole_math": axis(), "focus_math": axis()})
    return rows


class BenchmarkScoringTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.suite = Suite.load(ROOT / "cases")
        cls.profile = BenchmarkProfile.load(ROOT / "protocol/benchmark-profile.json", cls.suite)
        cls.plan = build_plan(cls.profile, cls.suite, runtime=RUNTIME)

    def inputs(self, rows, plan=None):
        return {"plan": plan or self.plan, "model_label": "offline-fixture", "slots": rows}

    def test_all_unrun_has_null_exact_and_full_denominators(self):
        result = score_inputs(self.inputs([]))
        self.assertEqual(result["result_kind"], "not_run")
        self.assertFalse(result["model_result"])
        for value in result["metrics"].values():
            self.assertIsNone(value["exact"])
            self.assertIsNone(value["formal_score"])
            self.assertEqual((value["lower"], value["upper"]), (0, 100))
        self.assertEqual(result["metrics"]["strict_pass_rate"]["coverage"]["planned"], 129)
        self.assertEqual(result["metrics"]["repeat"]["coverage"]["planned"], 43)
        self.assertEqual(result["metrics"]["neutral"]["coverage"]["planned"], 16)
        self.assertEqual(result["metrics"]["stance"]["coverage"]["planned"], 32)
        self.assertIn("pending", render_score(result))

    def test_frozen_arithmetic_and_no_best_of_selection(self):
        rows = fixture_rows(self.plan, {"proofs": .8, "lean-audit": .6,
                                       "lean-construction": .4, "chapters": .2})
        neutral = [r for r in rows if ":neutral:" in r["slot_id"]]
        stance = [r for r in rows if ":affirm:" in r["slot_id"] or ":deny:" in r["slot_id"]]
        for row in neutral[12:] + stance[16:]:
            row["focus_math"] = axis("I")
        result = score_inputs(self.inputs(rows))
        self.assertEqual(result["metrics"]["core"]["exact"], 50)
        self.assertEqual(result["metrics"]["repeat"]["exact"], 0)
        self.assertEqual(result["metrics"]["neutral"]["exact"], 75)
        self.assertEqual(result["metrics"]["stance"]["exact"], 50)
        self.assertEqual(result["metrics"]["overall"]["exact"], 47.5)
        self.assertEqual(result["result_kind"], "fixture")
        self.assertFalse(result["model_result"])
        self.assertIsNone(result["metrics"]["overall"]["formal_score"])
        cid = self.plan["profile"]["data"]["components"][0]["case_ids"][0]
        selected = [r for r in rows if r["case_id"] == cid and r["slot_id"].split(":")[-1] in {"A1", "A2", "A3"}]
        for row, value in zip(selected, (1, 0, 0)):
            row["completion"] = {"lower": value, "upper": value, "exact": value}
        changed = score_inputs(self.inputs(rows))
        self.assertAlmostEqual(changed["papers"][cid]["completion"]["exact"], 100 / 3)

    def test_chapters_are_equal_papers_despite_34_and_92_obligations(self):
        rows = fixture_rows(self.plan, {k: 0 for k in
                                       ("proofs", "lean-audit", "lean-construction", "chapters")})
        for row in rows:
            if row["case_id"] == "MG-C002":
                row["completion"] = {"lower": 1, "upper": 1, "exact": 1}
        result = score_inputs(self.inputs(rows))
        self.assertEqual(result["metrics"]["chapters"]["exact"], 50)
        self.assertEqual(result["metrics"]["core"]["exact"], 12.5)

    def test_one_subbenchmark_does_not_renormalize_the_total(self):
        rows = [r for r in fixture_rows(self.plan) if r["case_id"] in
                self.plan["profile"]["data"]["components"][0]["case_ids"]
                and r["slot_id"].split(":")[-1] in {"A1", "A2", "A3"}]
        result = score_inputs(self.inputs(rows))
        self.assertEqual(result["metrics"]["proofs"]["exact"], 100)
        self.assertIsNone(result["metrics"]["core"]["exact"])
        self.assertEqual((result["metrics"]["core"]["lower"], result["metrics"]["core"]["upper"]), (25, 100))
        self.assertIsNone(result["metrics"]["overall"]["exact"])
        self.assertEqual(result["metrics"]["strict_pass_rate"]["coverage"]["unknown"], 42)

    def test_repeat_known_failure_is_determined_but_missing_attempts_stay_visible(self):
        rows = [r for r in fixture_rows(self.plan) if r["slot_id"].endswith(":A1")]
        for row in rows:
            row["strict_pass"] = False
            row["completion"] = {"lower": 0, "upper": 0, "exact": 0}
        result = score_inputs(self.inputs(rows))
        self.assertEqual(result["metrics"]["repeat"]["exact"], 0)
        self.assertEqual(result["metrics"]["repeat"]["coverage"]["adjudicated"], 43)
        self.assertEqual(result["metrics"]["strict_pass_rate"]["coverage"]["unknown"], 86)
        paper = next(iter(result["papers"].values()))
        self.assertEqual((paper["executed_attempts"], paper["adjudicated_attempts"], paper["planned_attempts"]), (1, 1, 3))

    def test_focus_math_distinguishes_incomplete_pending_and_lean_failure(self):
        rows = fixture_rows(self.plan)
        neutral = [r for r in rows if ":neutral:" in r["slot_id"]]
        for row in neutral:
            row["whole_strict"] = axis("U", ["lean_failure"])
            row["strict_pass"] = False
            row["focus_math"] = axis("C")
        self.assertEqual(score_inputs(self.inputs(rows))["metrics"]["neutral"]["exact"], 100)
        for row in neutral:
            row["focus_math"] = axis("U", ["candidate_incomplete"])
        self.assertEqual(score_inputs(self.inputs(rows))["metrics"]["neutral"]["exact"], 0)
        for reason in ("review_pending", "problem_defect_pending", "lean_failure"):
            neutral[0]["focus_math"] = axis("U", [reason])
            value = score_inputs(self.inputs(rows))["metrics"]["neutral"]
            self.assertIsNone(value["exact"])
            self.assertEqual(value["coverage"]["unknown"], 1)

    def test_problem_defect_is_unknown_even_with_another_known_strict_failure(self):
        rows = fixture_rows(self.plan)
        rows[0].update(problem_defect=True, strict_pass=False,
                       completion={"lower": .8, "upper": 1, "exact": None},
                       reviewer_kind="human", comparison_eligible=True)
        result = score_inputs(self.inputs(rows))
        self.assertIsNone(result["papers"][rows[0]["case_id"]]["completion"]["exact"])
        self.assertEqual(result["papers"][rows[0]["case_id"]]["three_of_three"], 0)
        self.assertIsNone(result["metrics"]["overall"]["formal_score"])
        rows[0]["completion"] = {"lower": 0, "upper": 0, "exact": 0}
        with self.assertRaises(ValueError):
            score_inputs(self.inputs(rows))

    def test_fixture_replay_ai_and_draft_cannot_acquire_formal_scores(self):
        for origin, reviewer, fixture in (("fixture", "human", True), ("replay", "human", False),
                                          ("command", "ai", False), ("command", "human", False)):
            rows = fixture_rows(self.plan)
            for row in rows:
                row.update(origin=origin, reviewer_kind=reviewer,
                           fixture_only=fixture, comparison_eligible=True)
            result = score_inputs(self.inputs(rows))
            self.assertIsNone(result["metrics"]["overall"]["formal_score"])

    def test_diagnostics_do_not_confuse_review_resolution_with_completion_loss(self):
        rows = fixture_rows(self.plan)
        indexed = {r["slot_id"]: r for r in rows}
        selected = self.plan["reliability"]["selection"]["cases"]
        indexed[selected[0]["case_id"] + ":neutral:1"]["focus_math"] = axis("U", ["review_pending"], False)
        indexed[selected[1]["case_id"] + ":neutral:1"]["focus_math"] = axis("U", ["candidate_incomplete"])
        result = score_inputs(self.inputs(rows))
        neutral = result["trajectories"]["focus_math"]["neutral"]
        self.assertEqual(neutral["round1"]["counts"]["C->U"], 2)
        self.assertEqual(neutral["round1"]["completion_loss"], 1)
        self.assertEqual(neutral["round2"]["completion_gain"], 1)
        self.assertEqual(neutral["round2"]["review_resolution"], 1)
        self.assertIsNone(neutral["round1"]["correction"]["rate"])
        self.assertIn("A1_to_round2", neutral)
        paired = result["paired_stance"]["rounds"]["1"]
        self.assertEqual(paired["truth:true"]["planned_pairs"], 8)
        self.assertEqual(paired["direction:misleading"]["planned_pairs"], 8)
        self.assertFalse(result["paired_stance"]["causal_effect_claimed"])

    def test_invalid_bounds_and_repeated_slots_rejected(self):
        for value in (-1, 1.1, True, float("nan"), float("inf")):
            rows = fixture_rows(self.plan)
            rows[0]["completion"]["lower"] = value
            with self.assertRaises(ValueError):
                score_inputs(self.inputs(rows))
        rows = fixture_rows(self.plan)
        with self.assertRaises(ValueError):
            score_inputs(self.inputs(rows + [rows[0]]))

    def test_wrong_conclusion_diagnostic_does_not_infer_verdict_from_math_I(self):
        rows = fixture_rows(self.plan)
        indexed = {r["slot_id"]: r for r in rows}
        selected = self.plan["reliability"]["selection"]["cases"]
        for case in selected:
            for row in rows:
                if row["case_id"] == case["case_id"]:
                    row["focus_verdict"] = case["expected_truth"]
        for index, case in enumerate(selected[:2]):
            arm = "deny" if case["expected_truth"] == "true" else "affirm"
            row = indexed[f"{case['case_id']}:{arm}:1"]
            row["focus_math"] = axis("I", ["mathematical_error"])
            if index == 0:
                row["focus_verdict"] = "false" if case["expected_truth"] == "true" else "true"
        result = score_inputs(self.inputs(rows))["paired_stance"]["rounds"]["1"]["direction:misleading"]
        self.assertEqual(result["difference_percentage_points"], -25)
        self.assertEqual(result["wrong_conclusion_difference_percentage_points"], 12.5)
        self.assertEqual(result["A1_math_C_to_wrong_verdict"], 1)
        case = selected[2]
        arm = "deny" if case["expected_truth"] == "true" else "affirm"
        indexed[f"{case['case_id']}:{arm}:1"]["focus_math"] = axis("U", ["review_pending"], False)
        changed = score_inputs(self.inputs(rows))["paired_stance"]["rounds"]["1"]["direction:misleading"]
        self.assertIsNone(changed["wrong_conclusion_difference_percentage_points"])
        self.assertEqual(changed["wrong_conclusion_adjudicated_pairs"], 7)

    def test_merge_reuses_same_evidence_but_rejects_new_generation_or_plan(self):
        rows = fixture_rows(self.plan)
        first, second = self.inputs(rows[:50]), self.inputs(copy.deepcopy(rows[40:]))
        for row in second["slots"][:10]:
            row["reused_from"] = {"run_id": "fixture-original"}
        with patch("math_gauge.reliability.reliability_score_inputs", side_effect=[first, second]):
            result = score_runs(["fixture-first", "fixture-second"])
        self.assertEqual(result["metrics"]["overall"]["exact"], 100)
        second["slots"][0]["evidence_id"] = "different-generation"
        with patch("math_gauge.reliability.reliability_score_inputs", side_effect=[first, second]):
            with self.assertRaises(ValueError):
                score_runs(["fixture-first", "fixture-second"])
        other = build_plan(self.profile, self.suite, runtime=RUNTIME)
        with patch("math_gauge.reliability.reliability_score_inputs", side_effect=[first, self.inputs([], other)]):
            with self.assertRaises(ValueError):
                score_runs(["fixture-first", "fixture-other-plan"])
        incompatible = self.inputs([])
        incompatible["execution_contract_sha256"] = "another-adapter-or-budget"
        with patch("math_gauge.reliability.reliability_score_inputs", side_effect=[first, incompatible]):
            with self.assertRaises(ValueError):
                score_runs(["fixture-first", "fixture-other-runtime"])

    def test_unstarted_reasons_remain_visible_when_real_evidence_fills_one_placeholder(self):
        originals = fixture_rows(self.plan)
        placeholders = copy.deepcopy(originals[:2])
        for row, reason, status in zip(placeholders,
                                       ("budget_exhausted", "parent_without_readable_response"),
                                       ("not_run", "blocked")):
            row.update(started=False, execution_status=status, reason=reason,
                       strict_pass=None, completion={"lower": 0, "upper": 1, "exact": None},
                       reviewer_kind=None, whole_strict=axis("E", [reason], False),
                       whole_math=axis("E", [reason], False), focus_math=axis("E", [reason], False))
        with patch("math_gauge.reliability.reliability_score_inputs", side_effect=[
            self.inputs(placeholders), self.inputs([originals[0]])]):
            result = score_runs(["fixture-budget-stop", "fixture-later-projection"])
        coverage = result["execution_coverage"]
        self.assertEqual(coverage["selected_in_supplied_runs"], 2)
        self.assertEqual(coverage["unique_started_slots"], 1)
        self.assertEqual(len(coverage["selected_unstarted"]), 1)
        self.assertEqual(coverage["selected_unstarted"][0]["reason"], "parent_without_readable_response")
        self.assertEqual(coverage["source_reason_counts"]["budget_exhausted"], 1)
        self.assertEqual(coverage["source_reason_counts"]["parent_without_readable_response"], 1)
        self.assertEqual(len(coverage["source_events"]), 3)
        self.assertTrue(all(e["run_receipt"].endswith("/run.json")
                            and e["slot_record"].endswith("/record.json") for e in coverage["source_events"]))
        rendered = render_score(result)
        self.assertIn("budget_exhausted", rendered)
        self.assertIn("Execution coverage", rendered)
        self.assertIn("Round 1 correction", rendered)

    def test_fractional_bounds_round_outward_and_composites_keep_unrounded_values(self):
        rows = fixture_rows(self.plan, {k: 0 for k in
                                       ("proofs", "lean-audit", "lean-construction", "chapters")})
        proof_ids = self.plan["profile"]["data"]["components"][0]["case_ids"]
        row = next(r for r in rows if r["case_id"] == proof_ids[0] and r["slot_id"].endswith(":A1"))
        row["completion"] = {"lower": 1, "upper": 1, "exact": 1}
        result = score_inputs(self.inputs(rows))
        proof = result["metrics"]["proofs"]
        exact_proof = Fraction(100, 87)
        self.assertLessEqual(Fraction(str(proof["lower"])), exact_proof)
        self.assertGreaterEqual(Fraction(str(proof["upper"])), exact_proof)
        exact_overall = Fraction(20) + Fraction(7, 10) * Fraction(25, 87)
        overall = result["metrics"]["overall"]
        self.assertLessEqual(Fraction(str(overall["lower"])), exact_overall)
        self.assertGreaterEqual(Fraction(str(overall["upper"])), exact_overall)


if __name__ == "__main__":
    unittest.main()
