"""Synthetic quotations and strictly separated whole-trajectory review evidence."""

from copy import deepcopy
import hashlib
import unittest

from math_gauge import independent_research_review as review
from math_gauge import taste_v130 as flow
import test_taste_v130 as fixture_support


def write_policy(fixture):
    evaluator = fixture.case / "evaluator"
    rubric = evaluator / "rubric-trajectory.md"
    rubric.write_bytes(b"TRAJECTORY-PRIVATE-RUBRIC-SENTINEL\n")
    provenance = evaluator / "review-correction-provenance.json"
    fixture_support.write_json(provenance, {"synthetic": True})
    path = evaluator / review.POLICY_NAME
    fixture_support.write_json(path, {
        "schema": review.POLICY, "edition": flow.EDITION,
        "registration_sha256": hashlib.sha256(fixture.registration.read_bytes()).hexdigest(),
        "base_review_contract_sha256": fixture.reg["review_contract"]["sha256"],
        "capacity_aggregation": "whole-three-round-trajectory",
        "rubric": fixture_support.descriptor(rubric, evaluator),
        "provenance": fixture_support.descriptor(provenance, evaluator),
    })
    return path


def reviewed_trajectory(fixture, old, policy):
    value = deepcopy(old)
    value.update(schema=review.REVIEW, review_policy_sha256=review.policy_sha256(fixture.registration, policy))
    value["axes"]["capacity"]["evidence"] = [fixture.citation(rid) for rid in flow.ROUNDS]
    value["round_reviews"]["capacity"] = {rid: {
        "score": 80, "strict": rid != "R1", "reason": "Synthetic manuscript-specific judgment.",
        "evidence": [fixture.citation(rid)],
    } for rid in flow.ROUNDS}
    value["gates"]["capacity"]["C0"].update(
        reason="Established in R1. R2 left its scope intact. R3 omitted the result.",
        evidence=[fixture.citation("R1")],
    )
    value["gates"]["capacity"]["C1"].update(
        reason="First established in R2 within its stated scope. R3 did not change it.",
        evidence=[fixture.citation("R2")],
    )
    return value


class TrajectoryReviewTests(unittest.TestCase):
    def setUp(self):
        self.fixture = fixture_support.ProtocolFixture("runTest")
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        fixture = self.fixture
        fixture.contract["round_coverage"]["capacity"] = ["R3"]
        original_contract = fixture.case / "evaluator/review-contract.json"
        fixture_support.write_json(original_contract, fixture.contract)
        fixture.reg["review_contract"] = fixture_support.descriptor(original_contract, fixture.case)
        fixture_support.write_json(fixture.registration, fixture.reg)
        self.policy = write_policy(fixture)
        self.original = fixture.review()
        self.corrected = reviewed_trajectory(fixture, self.original, self.policy)
        self.output = fixture.root / "new-review.json"

    def check(self, value):
        fixture_support.write_json(self.output, value)
        return review.validate_review(self.fixture.registration, self.fixture.state, self.output, self.policy)

    def test_earlier_valid_gates_need_no_third_round_restatement(self):
        axes = self.check(self.corrected)
        self.assertTrue(axes["capacity"]["strict"])
        self.assertFalse(self.corrected["round_reviews"]["capacity"]["R1"]["strict"])
        self.assertEqual(axes["capacity"]["score"], 80)
        with self.assertRaisesRegex(ValueError, "whole-trajectory review"):
            self.check(self.original)

    def test_c_overall_cites_every_round_but_each_direction_can_cite_one(self):
        value = deepcopy(self.corrected)
        value["axes"]["capacity"]["evidence"].pop(1)
        with self.assertRaisesRegex(ValueError, "all three manuscripts"):
            self.check(value)
        value = deepcopy(self.corrected)
        del value["round_reviews"]["capacity"]["R2"]
        with self.assertRaisesRegex(ValueError, "Missing per-manuscript"):
            self.check(value)
        value = deepcopy(self.corrected)
        value["gates"]["capacity"]["C0"]["reason"] = review.CAPACITY_PENDING
        with self.assertRaisesRegex(ValueError, "cross-round state"):
            self.check(value)

    def test_a_and_t_keep_the_original_round_constraints(self):
        for axis, gate, refs in (("autonomy", "A1", [self.fixture.citation("R3")]),
                                 ("taste", "T1", [self.fixture.citation("R1")])):
            value = deepcopy(self.corrected)
            value["gates"][axis][gate]["evidence"] = refs
            with self.assertRaisesRegex(ValueError, "Invalid evidence citation|all specified manuscripts"):
                self.check(value)

    def test_failed_capacity_gate_preserves_the_reviewer_judgment(self):
        value = deepcopy(self.corrected)
        value["gates"]["capacity"]["C0"].update(verdict=False,
            reason="R1 asserted an overbroad claim. R2 presents a counterexample. R3 keeps only the restricted claim.",
            evidence=[self.fixture.citation("R1"), self.fixture.citation("R2"), self.fixture.citation("R3")])
        with self.assertRaisesRegex(ValueError, "Strict must equal all required gates"):
            self.check(value)
        value["axes"]["capacity"]["strict"] = False
        self.assertFalse(self.check(value)["capacity"]["strict"])

    def test_binds_the_policy_and_original_verbatim_evidence(self):
        value = deepcopy(self.corrected)
        value["review_policy_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "Unbound"):
            self.check(value)
        value = deepcopy(self.corrected)
        value["gates"]["capacity"]["C0"]["evidence"][0]["quote"] += "invented"
        with self.assertRaisesRegex(ValueError, "quotation"):
            self.check(value)
        self.policy.with_name("rubric-trajectory.md").write_bytes(b"Changed private rubric\n")
        with self.assertRaisesRegex(ValueError, "Source hash mismatch"):
            self.check(self.corrected)

    def test_template_and_check_leave_all_frozen_bytes_intact(self):
        fixture = self.fixture
        original = fixture.registration.read_bytes()
        draft_path = fixture.root / "draft.json"
        self.assertEqual(review.main(["template", str(fixture.registration), str(fixture.state), str(self.policy),
                                      "fixture-reviewer", "independent-draft", str(draft_path)]), 0)
        draft = flow._load(draft_path)
        self.assertEqual(tuple(draft["round_reviews"]["capacity"]), flow.ROUNDS)
        self.assertEqual(tuple(draft["round_reviews"]["autonomy"]), ("R1", "R2"))
        self.assertIsNone(self.check(draft)["capacity"]["score"])
        self.assertEqual(fixture.registration.read_bytes(), original)


if __name__ == "__main__":
    unittest.main()
