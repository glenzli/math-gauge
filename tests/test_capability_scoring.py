"""Positive credit uses the same reviewed mathematics without explicit penalties."""
import copy
import json
from pathlib import Path
import unittest
from unittest.mock import patch

import test_theorem_extension as research_fixtures
from test_alignment_scoring import alignment_review
from math_gauge.records import evidence_bytes, load_assessment_results, project_assessment_score
from math_gauge.scoring import (_alignment_trajectory, score_assessment_inputs,
                                validate_capability_policy)

ROOT = Path(__file__).resolve().parents[1]
CAPABILITY = json.loads((ROOT / "protocol/capability-scoring-policy.json").read_text())


class PositiveTrajectoryTests(unittest.TestCase):
    def setUp(self):
        self.policy = json.loads((ROOT / "results/v0.6.0/gemini-3.8-flash-high/20261105/scoring-policy.json").read_text())
        self.ids = self.policy["obligation_ids"]

    def review(self, before, after, diagnoses):
        value = alignment_review(self.policy, before, round_passes=after, diagnoses=diagnoses)
        value["scoring_version"] = self.policy["version"]
        return value

    def test_false_claim_keeps_only_review_awarded_credit_without_blanket_zero_or_penalty(self):
        review = self.review(self.ids[:74], [self.ids[:83]] * 3, [(0, 12, True, False)] * 3)
        old = copy.deepcopy(review)
        positive, _ = _alignment_trajectory(review, self.policy, positive_only=True)
        reliable, _ = _alignment_trajectory(review, self.policy)
        self.assertEqual(positive["rounds"][0]["score"]["exact"], 47)
        self.assertEqual(reliable["rounds"][0]["score"]["exact"], 15)
        self.assertEqual(positive["rounds"][1]["score"]["exact"], 12)
        self.assertEqual(positive["major_false_complete_events"], reliable["major_false_complete_events"])
        self.assertFalse(positive["rounds"][0]["strict_pass"])
        self.assertEqual(review, old)

    def test_regression_is_still_reported_but_does_not_cancel_valid_new_repairs(self):
        after = self.ids[18:23]
        review = self.review(self.ids[:18], [after] * 3, [(10, 8, False, False)] * 3)
        positive, _ = _alignment_trajectory(review, self.policy, positive_only=True)
        reliable, _ = _alignment_trajectory(review, self.policy)
        first = positive["rounds"][0]
        self.assertEqual((first["repaired"], first["regressed"]), (5, 18))
        self.assertGreater(first["repair_or_preservation_points"], 0)
        self.assertLess(reliable["rounds"][0]["repair_or_preservation_points"], 0)
        self.assertGreater(first["score"]["exact"], reliable["rounds"][0]["score"]["exact"])

    def test_preservation_counts_currently_verified_work_and_missing_rounds_stay_unknown(self):
        review = self.review(self.ids, [self.ids[:91]] * 3, [(0, 0, False, False)] * 3)
        positive, _ = _alignment_trajectory(review, self.policy, positive_only=True)
        self.assertAlmostEqual(positive["rounds"][0]["repair_or_preservation_points"], 70 * 91 / 92)
        review = self.review(self.ids, [self.ids] * 3, [(10, 20, True, True)] * 3)
        review["rounds"].pop(1)
        positive, _ = _alignment_trajectory(review, self.policy, positive_only=True)
        self.assertIsNone(positive["metric"]["exact"])
        self.assertAlmostEqual(positive["metric"]["lower"], 100 / 3)
        self.assertEqual(positive["metric"]["coverage"]["planned"], 3)


class CapabilityResearchTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        fixtures = research_fixtures.TheoremExtensionScoringTests
        fixtures.setUpClass()
        cls.fixture = fixtures("test_six_families_are_equal_and_invited_results_do_not_backfill")

    def score(self, data, **extra):
        f = self.fixture
        return score_assessment_inputs({"plan": f.plan, "model_label": f.plan["model_label"], "slots": []},
            f.policy, f.strict, mode="capability", capability_policy=CAPABILITY,
            theorem_extension_inputs=data, **extra)

    def test_valid_independent_extension_is_credited_without_the_baseline_deduction(self):
        data = self.fixture.research((1,) * 6, (0,) * 6)
        original = copy.deepcopy(data)
        result = self.score(data)
        self.assertAlmostEqual(result["contributions"]["theorem-extension"]["exact"], 10 / 3)
        self.assertAlmostEqual(self.fixture.score(data)["contributions"]["theorem-extension"]["exact"], -10 / 3)
        self.assertTrue(all(not x["strict_pass"] for x in result["tasks"] if "research" in x))
        self.assertEqual(data, original)

    def test_absent_or_failed_research_is_never_positive_and_unrun_stays_unknown(self):
        data = self.fixture.research((0,) * 6, (0,) * 6)
        self.assertEqual(self.score(data)["contributions"]["theorem-extension"]["exact"], 0)
        for row in data["slots"]:
            row.update(status="not_run", baseline_B=None, research_R=None, response=None, review=None)
        result = self.score(data)
        self.assertEqual(result["contributions"]["theorem-extension"]["lower"], 0)
        self.assertEqual(result["contributions"]["theorem-extension"]["upper"], 10)
        self.assertIsNone(result["contributions"]["theorem-extension"]["exact"])
        self.assertEqual(result["metrics"]["theorem-extension"]["coverage"]["planned"], 6)
        self.assertNotIn("Fixture-Private", json.dumps(project_assessment_score(result)))

    def test_mode_requires_its_policy_and_cannot_reuse_a_penalized_trajectory(self):
        with self.assertRaises(ValueError):
            validate_capability_policy(dict(CAPABILITY, regression_deduction=True))
        with self.assertRaisesRegex(ValueError, "positive-contribution trajectory"):
            self.score(self.fixture.research(), alignment_summary={"metric": {"exact": -20}})


class CapabilityRecordTests(unittest.TestCase):
    def test_capability_policy_binding_is_verified_in_public_archives(self):
        root = ROOT / "results/v0.6.0/deepseek-v4.1-flash-1017/20261105"
        record = json.loads((root / "record.json").read_text())
        data = load_assessment_results(root, record, mode="capability")
        self.assertEqual(set(data), {"single_attempt", "nonlogical_retry_3"})
        def poisoned(base, item):
            raw = evidence_bytes(base, item)
            if item["path"] == record["capability_results"]["single_attempt"]["path"]:
                value = json.loads(raw)
                value["source_bindings"]["capability_policy_sha256"] = "0" * 64
                return json.dumps(value).encode()
            return raw
        with patch("math_gauge.records.evidence_bytes", side_effect=poisoned), self.assertRaisesRegex(ValueError, "Capability score binds"):
            load_assessment_results(root, record, mode="capability")
