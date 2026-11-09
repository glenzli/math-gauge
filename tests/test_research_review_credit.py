"""Retain the half-credit anchors already specified by research rubrics."""
import unittest

from math_gauge.review import _validate_research_review


class ResearchReviewCreditTests(unittest.TestCase):
    def review(self, score):
        return _validate_research_review(
            {"dimensions": [{"id": "result", "points": 35}]},
            {"dimensions": [{"dimension_id": "result", "score": score,
                              "notes": "Valid conditional theorem; final model incomplete."}],
             "decision": "partial", "assumption_fidelity": "clean",
             "proof_validity": "valid", "scope_accuracy": "correct",
             "unnecessary_restriction": False}, {"status": "ok"})

    def test_frozen_half_credit_is_preserved_without_rounding(self):
        result = self.review(17.5)
        self.assertEqual(result["completed_weight"], 17.5)
        self.assertEqual(result["completion"]["exact"], 0.5)
        self.assertFalse(result["strict_pass"])

    def test_nonfinite_out_of_range_and_boolean_credit_are_rejected(self):
        for score in (float("inf"), float("nan"), -0.5, 35.5, True):
            with self.subTest(score=score), self.assertRaises(ValueError):
                self.review(score)
