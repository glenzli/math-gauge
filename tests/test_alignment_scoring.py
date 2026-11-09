"""Synthetic alignment judgments test scoring; none are model or human evidence."""

import copy
import json
import tempfile
import unittest
from fractions import Fraction
from pathlib import Path

from math_gauge.benchmarks import BenchmarkProfile, build_plan
from math_gauge.catalog import Suite, digest_bytes
from math_gauge.scoring import (_score_inputs, alignment_augmented_score,
                                public_score_projection, score_alignment_trajectory, score_inputs,
                                source_qualified_engineering_score)
from test_scoring import fixture_rows
from benchmark_fixtures import arithmetic_source_plan

ROOT = Path(__file__).resolve().parents[1]
RUNTIME = {"model_label": "offline-alignment-fixture", "budget": {"timeout_seconds": 5400},
           "adapter_identity": {"kind": "fixture"},
           "execution_track": "math-gauge.local-tools-no-search/v1"}


def alignment_policy(ids=None):
    return {"schema": "math-gauge.alignment-selfcheck-policy/v1", "version": "0.1.0",
            "case_id": "MG-C003", "case_version": "0.1.1", "rounds": 3,
            "obligation_ids": ids or [f"O-{i:02d}" for i in range(92)], "obligation_weight": 1,
            "repair_points": 70, "diagnosis_points": {"global": 10, "localization": 20},
            "neutral_group_weights": {"written": 1, "lean_alignment": 1},
            "overall_weights": {"core": 75, "repeat": 5, "neutral": 10, "stance": 10}}


def alignment_snapshot(policy, passed, *, index=0, unknown=(), delivery=True):
    passed, unknown = set(passed), set(unknown)
    return {"source_id": f"synthetic-source-{index}", "source_sha256": f"{index + 1:064x}",
            "source_kind": "sealed_workspace", "delivery_verified": delivery,
            "review_evidence_sha256": ["b" * 64],
            "obligations": [{"id": sid, "complete": None if sid in unknown else sid in passed}
                            for sid in policy["obligation_ids"]]}


def alignment_review(policy, baseline_passes, *, round_passes=None, diagnoses=None):
    round_passes = [baseline_passes] * 3 if round_passes is None else round_passes
    diagnoses = [(10, 20, False, True)] * 3 if diagnoses is None else diagnoses
    rounds = []
    for index, (passed, diagnosis) in enumerate(zip(round_passes, diagnoses), 1):
        snapshot = alignment_snapshot(policy, passed, index=index)
        global_points, localization, claims, accurate = diagnosis
        rounds.append({"round": index, "snapshot": snapshot,
            "diagnosis": {"source_sha256": snapshot["source_sha256"], "global_points": global_points,
                "localization_points": localization, "claims_complete": claims, "accurate": accurate,
                "review_evidence_sha256": ["c" * 64]}})
    return {"schema": "math-gauge.alignment-selfcheck-review/v1", "scoring_version": "0.1.0",
            "case_id": "MG-C003", "case_version": "0.1.1", "model_label": RUNTIME["model_label"],
            "reviewer_kind": "ai", "human_review": "pending", "formal_comparison_eligible": False,
            "policy_sha256": "a" * 64, "primary_source_kind": "sealed_workspace",
            "baseline": alignment_snapshot(policy, baseline_passes), "rounds": rounds}


class AlignmentTrajectoryTests(unittest.TestCase):
    def setUp(self):
        self.policy = alignment_policy()
        self.ids = self.policy["obligation_ids"]

    def score(self, review):
        return score_alignment_trajectory(review, self.policy)

    def test_partial_repair_and_three_fixed_rounds(self):
        review = alignment_review(self.policy, self.ids[:74], round_passes=[self.ids[:83]] * 3)
        result = self.score(review)
        first = result["rounds"][0]
        self.assertEqual((first["repaired"], first["regressed"], first["remaining_previous"]), (9, 0, 18))
        self.assertEqual(first["score"]["exact"], 65)
        self.assertFalse(first["strict_pass"])
        self.assertEqual(result["metric"]["exact"], round(125 / 3, 10))
        self.assertEqual(result["metric"]["coverage"]["planned"], 3)

    def test_regression_is_added_to_diagnosis_before_the_single_clamp(self):
        review = alignment_review(self.policy, self.ids[:18],
            round_passes=[[], self.ids[18:23], self.ids[:13] + self.ids[18:43]],
            diagnoses=[(10, 8, False, True), (10, 12, False, True), (10, 20, False, True)])
        result = self.score(review)
        self.assertEqual(result["rounds"][0]["score"]["exact"], round(float(Fraction(36, 37)), 10))
        third = result["rounds"][2]
        self.assertEqual((third["repaired"], third["restored"], third["first_new"]), (33, 13, 20))
        self.assertEqual(result["last_completion"]["complete"], 38)
        self.assertEqual(result["rounds"][0]["regressed"], 18)

    def test_correct_keep_and_verified_delivery_are_distinct(self):
        review = alignment_review(self.policy, self.ids, diagnoses=[(10, 20, True, True)] * 3)
        result = self.score(review)
        self.assertEqual(result["metric"]["exact"], 100)
        self.assertEqual(result["strict_pass_rate"]["exact"], 100)
        self.assertEqual(result["rounds"][0]["repair_or_preservation_points"], 70)
        review["rounds"][0]["snapshot"]["delivery_verified"] = False
        result = self.score(review)
        self.assertEqual(result["rounds"][0]["score"]["exact"], 100)
        self.assertFalse(result["rounds"][0]["strict_pass"])
        review["rounds"][0]["snapshot"]["obligations"][0]["complete"] = False
        review["rounds"][0]["diagnosis"]["claims_complete"] = False
        self.assertAlmostEqual(self.score(review)["rounds"][0]["repair_or_preservation_points"], 70 * 91 / 92)

    def test_false_complete_forces_diagnosis_zero_and_keeps_verified_repairs(self):
        review = alignment_review(self.policy, self.ids[:74], diagnoses=[(10, 20, True, True)] * 3)
        result = self.score(review)
        self.assertEqual(result["metric"]["exact"], 0)
        self.assertEqual(result["major_false_complete_events"], {"count": 3, "applicable_rounds": 3, "unknown_rounds": 0})
        review["rounds"][0]["snapshot"] = alignment_snapshot(self.policy, self.ids[:83], index=1)
        result = self.score(review)
        self.assertEqual(result["rounds"][0]["score"]["exact"], 35)
        self.assertEqual(result["rounds"][0]["diagnosis_points"], 0)
        self.assertFalse(result["rounds"][0]["strict_pass"])

    def test_missing_round_cannot_be_renormalized_or_skipped_in_adjacency(self):
        review = alignment_review(self.policy, self.ids, diagnoses=[(10, 20, True, True)] * 3)
        del review["rounds"][1]
        result = self.score(review)
        self.assertIsNone(result["metric"]["exact"])
        self.assertEqual(result["metric"]["coverage"]["unknown"], 2)
        self.assertAlmostEqual(result["metric"]["lower"], 100 / 3)
        self.assertEqual(result["metric"]["upper"], 100)
        self.assertIsNone(result["rounds"][2]["repaired"])
        self.assertEqual(result["last_completion"]["complete"], 92)

    def test_environment_unknown_is_not_ninety_two_mathematical_failures(self):
        review = alignment_review(self.policy, self.ids)
        review["rounds"][0]["snapshot"] = alignment_snapshot(self.policy, [], index=1,
                                                              unknown=self.ids, delivery=None)
        review["rounds"][0]["diagnosis"].update(global_points=None, localization_points=None,
                                                   claims_complete=None, accurate=None)
        first = self.score(review)["rounds"][0]
        self.assertIsNone(first["score"]["exact"])
        self.assertEqual((first["not_complete"], first["unknown_obligations"]), (0, 92))
        self.assertIsNone(first["strict_pass"])
        self.assertIsNone(first["major_false_complete"])

    def test_proved_missing_final_is_zero_but_missing_mathematics_stays_unknown(self):
        review = alignment_review(self.policy, self.ids)
        snapshot = review["rounds"][2]["snapshot"]
        snapshot.update(source_kind="not_available", source_sha256=None,
                        delivery_status="delivery_failed", delivery_verified=False)
        for obligation in snapshot["obligations"]:
            obligation["complete"] = None
        review["rounds"][2]["diagnosis"] = None
        last = self.score(review)["rounds"][2]
        self.assertEqual(last["score"]["exact"], 0)
        self.assertFalse(last["strict_pass"])
        self.assertEqual((last["not_complete"], last["unknown_obligations"]), (0, 92))
        self.assertIsNone(last["regressed"])
        self.assertIsNone(last["major_false_complete"])
        snapshot.update(delivery_status="not_run", delivery_verified=None)
        self.assertIsNone(self.score(review)["rounds"][2]["score"]["exact"])

    def test_versions_id_inventories_booleans_and_source_binding_are_validated(self):
        mutations = [lambda r: r.update(scoring_version="0.2.0"),
            lambda r: r["rounds"].append(copy.deepcopy(r["rounds"][0])),
            lambda r: r["baseline"]["obligations"][0].update(id=self.ids[1]),
            lambda r: r["baseline"]["obligations"][0].update(complete=1),
            lambda r: r["rounds"][0]["snapshot"].update(delivery_verified=0),
            lambda r: r["rounds"][0]["snapshot"].update(source_kind="response_inline"),
            lambda r: r["rounds"][0]["diagnosis"].update(source_sha256="d" * 64),
            lambda r: r["rounds"][0]["diagnosis"].update(global_points=float("nan")),
            lambda r: r["rounds"][0]["diagnosis"].update(localization_points=float("inf")),
            lambda r: r["rounds"][0]["diagnosis"].update(accurate=1)]
        for mutate in mutations:
            with self.subTest(mutation=mutate):
                review = alignment_review(self.policy, self.ids[:74])
                mutate(review)
                with self.assertRaises(ValueError):
                    self.score(review)

    def test_policy_weights_versions_and_unique_ids_are_validated(self):
        mutations = [lambda p: p.update(version="0.0.0"), lambda p: p.update(rounds=True),
            lambda p: p["obligation_ids"].__setitem__(0, self.ids[1]),
            lambda p: p.update(repair_points=80), lambda p: p["overall_weights"].update(neutral=20),
            lambda p: p["neutral_group_weights"].update(lean_alignment=0),
            lambda p: p["neutral_group_weights"].update(written=True),
            lambda p: p["neutral_group_weights"].update(written=float("inf"))]
        for mutate in mutations:
            with self.subTest(mutation=mutate):
                policy = copy.deepcopy(self.policy)
                mutate(policy)
                with self.assertRaises(ValueError):
                    score_alignment_trajectory(alignment_review(policy, self.ids[:74]), policy)

    def engineering_policy(self):
        self.policy.update(version="0.2.0", false_complete_penalty_points=20, allow_negative_selfcheck=True)

    def test_v02_false_complete_penalty_survives_the_base_score_floor(self):
        self.engineering_policy()
        review = alignment_review(self.policy, self.ids[:74], diagnoses=[(10, 20, True, True)] * 3)
        review["scoring_version"] = "0.2.0"
        result = self.score(review)
        self.assertEqual(result["metric"]["exact"], -20)
        for row in result["rounds"]:
            self.assertEqual((row["base_score"], row["penalty_points"], row["net_score"]), (0, 20, -20))
        review["rounds"][0]["snapshot"] = alignment_snapshot(self.policy, self.ids[:83], index=1)
        first = self.score(review)["rounds"][0]
        self.assertEqual((first["base_score"], first["penalty_points"], first["net_score"]), (35, 20, 15))

    def test_v02_honest_global_judgment_is_ten_points_and_missing_rounds_stay_unknown(self):
        self.engineering_policy()
        review = alignment_review(self.policy, self.ids[:74], diagnoses=[(10, 0, False, True)] * 3)
        review["scoring_version"] = "0.2.0"
        self.assertEqual(self.score(review)["metric"]["exact"], 10)
        review["rounds"] = []
        result = self.score(review)
        self.assertIsNone(result["metric"]["exact"])
        self.assertEqual((result["metric"]["lower"], result["metric"]["upper"]), (-20, 100))
        self.assertEqual(result["metric"]["coverage"]["planned"], 3)
        self.assertTrue(all(row["penalty_points"] == 0 for row in result["rounds"]))

    def test_v02_unknown_math_does_not_confirm_a_false_complete_penalty(self):
        self.engineering_policy()
        review = alignment_review(self.policy, self.ids[:74], diagnoses=[(10, 20, True, True)] * 3)
        review["scoring_version"] = "0.2.0"
        review["rounds"][0]["snapshot"] = alignment_snapshot(self.policy, [], index=1,
                                                               unknown=self.ids, delivery=None)
        first = self.score(review)["rounds"][0]
        self.assertIsNone(first["major_false_complete"])
        self.assertEqual(first["penalty_points"], 0)
        self.assertIsNone(first["net_score"])
        review["baseline"] = alignment_snapshot(self.policy, [], unknown=self.ids)
        review["rounds"][0]["snapshot"] = alignment_snapshot(self.policy, self.ids[:74], index=1)
        first = self.score(review)["rounds"][0]
        self.assertEqual(first["penalty_points"], 20)
        self.assertEqual((first["score"]["lower"], first["score"]["upper"]), (-20, 80))
        for field, value in (("false_complete_penalty_points", 19), ("allow_negative_selfcheck", False)):
            policy = dict(self.policy, **{field: value})
            with self.assertRaises(ValueError):
                score_alignment_trajectory(review, policy)


class BoundAlignmentFixture(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.plan = arithmetic_source_plan(RUNTIME)

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.rows = fixture_rows(self.plan)
        for row in self.rows:
            row["review_sha256"] = "1" * 64
        self.inputs = {"plan": self.plan, "model_label": RUNTIME["model_label"], "slots": self.rows}
        report = score_inputs(self.inputs)
        summary = public_score_projection(report, self.plan, private_aliases={})
        ids = [stage["stage_id"] for case in self.plan["case_index"] if case["case_id"] == "MG-C003"
               for stage in case["stages"]]
        policy = alignment_policy(ids)
        review = alignment_review(policy, ids[:74], diagnoses=[(10, 20, True, True)] * 3)
        self.documents = {"original_summary": summary, "original_report": report,
                          "original_plan": self.plan, "policy": policy, "alignment_review": review}
        self.sources, self.hashes = {}, {}
        for name in self.documents:
            self.save(name)
        review["policy_sha256"] = self.hashes["policy"]
        self.save("alignment_review")

    def save(self, name):
        path = self.root / (name + ".json")
        path.write_text(json.dumps(self.documents[name], ensure_ascii=False, indent=2) + "\n")
        self.sources[name] = path
        self.hashes[name] = digest_bytes(path.read_bytes())

    def score(self):
        return alignment_augmented_score(self.sources, expected_sha256=self.hashes)


class AlignmentAugmentedTests(BoundAlignmentFixture):
    def test_equal_group_weights_shared_exact_aggregation_and_legacy_compatibility(self):
        before = {name: path.read_bytes() for name, path in self.sources.items()}
        result = self.score()
        self.assertEqual(result["schema"], "math-gauge.alignment-augmented-score/v1")
        self.assertEqual(result["metrics"]["neutral_written"]["exact"], 100)
        self.assertEqual(result["metrics"]["lean_alignment_selfcheck"]["exact"], 0)
        self.assertEqual(result["metrics"]["neutral"]["exact"], 50)
        self.assertEqual(result["metrics"]["overall"]["exact"], 95)
        for name in set(self.documents["original_summary"]["metrics"]) - {"neutral", "overall"}:
            self.assertEqual(result["metrics"][name], self.documents["original_summary"]["metrics"][name])
        self.assertEqual(result["coverage"]["slots_planned"], 42)
        self.assertEqual(result["alignment_study_coverage"]["mathematical_families"], 1)
        self.assertEqual(result["alignment_study_coverage"]["standard_slots_added"], 0)
        self.assertEqual(self.documents["original_report"]["metrics"], score_inputs(self.inputs)["metrics"])
        self.assertEqual(before, {name: path.read_bytes() for name, path in self.sources.items()})
        self.assertFalse(result["formal_comparison_eligible"])
        serialized = json.dumps(result)
        for private_field in (str(self.root), '"obligations":', "case_index", "review_evidence_sha256", "slot_evidence"):
            self.assertNotIn(private_field, serialized)

    def test_four_to_one_policy_preserves_the_family_weight_alternative(self):
        self.documents["policy"]["neutral_group_weights"]["written"] = 4
        self.save("policy")
        self.documents["alignment_review"]["policy_sha256"] = self.hashes["policy"]
        self.save("alignment_review")
        result = self.score()
        self.assertEqual(result["metrics"]["neutral"]["exact"], 80)
        self.assertEqual(result["metrics"]["overall"]["exact"], 98)

    def test_missing_lean_rounds_keep_their_full_share_in_overall_bounds(self):
        del self.documents["alignment_review"]["rounds"][1]
        self.save("alignment_review")
        result = self.score()
        self.assertIsNone(result["metrics"]["overall"]["exact"])
        self.assertEqual(result["metrics"]["overall"]["lower"], 95)
        self.assertAlmostEqual(result["metrics"]["overall"]["upper"], 100 - 5 / 3)
        self.assertEqual(result["alignment_selfcheck"]["metric"]["coverage"]["planned"], 3)
        self.assertEqual(result["coverage"]["slots_planned"], 42)

    def test_changed_hash_and_self_consistent_original_score_drift_are_rejected(self):
        self.sources["alignment_review"].write_bytes(self.sources["alignment_review"].read_bytes() + b" ")
        with self.assertRaisesRegex(ValueError, "source hash changed"):
            self.score()
        self.save("alignment_review")
        self.documents["original_summary"]["metrics"]["overall"]["exact"] = 99
        self.save("original_summary")
        with self.assertRaisesRegex(ValueError, "frozen original metrics"):
            self.score()

    def test_selected_gemini_capability_is_bound_and_never_inferred_from_followups(self):
        target = next(row for row in self.rows if row["slot_id"] == "MG-C003:A1")
        target.update(completion={"lower": 0, "upper": 1, "exact": None}, strict_pass=None,
                      reviewer_kind=None, review_sha256=None)
        report = score_inputs(self.inputs)
        self.documents["original_report"] = report
        self.documents["original_summary"] = public_score_projection(report, self.plan, private_aliases={})
        self.save("original_report")
        self.save("original_summary")
        unselected = self.score()
        self.assertIsNone(unselected["metrics"]["overall"]["exact"])
        self.assertEqual(unselected["capability_source"], "original_A1")
        value = Fraction(74, 92)
        derived = _score_inputs(self.inputs, mathematical_substitutions={"MG-C003:A1": (value, value, value)})
        policy = self.documents["policy"]
        self.documents["source_qualified_score"] = {
            "schema": "math-gauge.source-qualified-score/v1", "scope": "public",
            "id": "gemini-v06-sealed-extension-math-public/v1", "scoring_view_version": "c003-sealed-extension/v1",
            "human_review": "pending", "formal_comparison_eligible": False,
            "profile": self.documents["original_summary"]["profile"],
            "coverage": self.documents["original_summary"]["coverage"],
            "metrics": public_score_projection(derived, self.plan, private_aliases={})["metrics"],
            "source_bindings": {name + "_sha256": self.hashes[name]
                for name in ("original_summary", "original_report", "original_plan")},
            "mathematical_substitution": {"case_id": "MG-C003", "case_version": "0.1.1",
                "original_weight_slot": "MG-C003:A1", "original_A1_replaced": False,
                "complete": 74, "not_complete": 18, "total": 92,
                "pass_ids": policy["obligation_ids"][:74], "not_complete_ids": policy["obligation_ids"][74:]}}
        self.save("source_qualified_score")
        result = self.score()
        expected = Fraction(1) - Fraction(75, 100) * Fraction(45, 100) * Fraction(1, 2) * Fraction(18, 92) - Fraction(5, 100)
        self.assertEqual(result["metrics"]["overall"]["exact"], round(float(100 * expected), 10))
        self.assertEqual(result["capability_source"], "selected_sealed_extension_74_of_92")
        self.assertEqual(result["coverage"]["slots_reviewed"], 41)
        self.assertIsNone(result["metrics"]["strict_pass_rate"]["exact"])
        self.documents["source_qualified_score"]["mathematical_substitution"]["complete"] = 92
        self.save("source_qualified_score")
        with self.assertRaisesRegex(ValueError, "admitted Gemini"):
            self.score()

    def test_v02_floor_applies_to_overall_after_weighting_and_keeps_negative_neutral(self):
        policy = self.documents["policy"]
        policy.update(version="0.2.0", false_complete_penalty_points=20, allow_negative_selfcheck=True)
        rows = fixture_rows(self.plan, {component["id"]: 0 for component in self.plan["profile"]["data"]["components"]})
        for row in rows:
            row["focus_math"]["state"] = "I"
        point = Fraction(-1, 5)
        report = _score_inputs(dict(self.inputs, slots=rows), neutral_alignment=((point, point, point), policy))
        self.assertEqual(report["metrics"]["neutral"]["exact"], -10)
        self.assertEqual(report["metrics"]["overall"]["exact"], 0)


class EngineeringCapabilityTests(BoundAlignmentFixture):
    def setUp(self):
        super().setUp()
        self.workspace = self.root / "first-workspace"
        self.workspace.mkdir()
        (self.workspace / "Main.lean").write_text("theorem synthetic : True := True.intro\n")
        ids = self.documents["policy"]["obligation_ids"]
        alignment = {"case_id": "MG-C003", "version": "0.1.1", "items": [
            {"id": sid, "status": "complete" if index < 74 else "incomplete",
             "declarations": [{"file": "Main.lean", "name": "synthetic"}] if index < 74 else []}
            for index, sid in enumerate(ids)]}
        (self.workspace / "alignment.json").write_text(json.dumps(alignment))
        files = {name: {"sha256": digest_bytes((self.workspace / name).read_bytes()),
                        "bytes": len((self.workspace / name).read_bytes())}
                 for name in ("Main.lean", "alignment.json")}
        tree_hash = "5" * 64
        self.documents["source_manifest"] = {"tree_sha256": tree_hash, "files": files}
        self.save("source_manifest")
        target = next(row for row in self.rows if row["slot_id"] == "MG-C003:A1")
        target.update(response_sha256="f" * 64, strict_pass=False,
                      completion={"lower": 18 / 92, "upper": 18 / 92, "exact": 18 / 92})
        report = score_inputs(self.inputs)
        self.documents["original_report"] = report
        self.documents["original_summary"] = public_score_projection(report, self.plan, private_aliases={})
        self.save("original_report")
        self.save("original_summary")
        case = next(case for case in self.plan["case_index"] if case["case_id"] == "MG-C003")
        self.documents["engineering_review"] = {
            "schema": "math-gauge.source-bound-forced-snapshot-formalization-peer/v1",
            "case_id": "MG-C003", "case_version": "0.1.1", "slot_id": "MG-C003:A1",
            "model_label": "terra", "reviewer_kind": "ai", "human_review": "pending",
            "old_inline_response_sha256": target["response_sha256"],
            "snapshot": {"manifest": {"sha256": self.hashes["source_manifest"]}, "tree_sha256": tree_hash,
                "entry": {"sha256": files["Main.lean"]["sha256"]},
                "workspace_alignment": {"sha256": files["alignment.json"]["sha256"]}},
            "frozen_case_files": [{"path": str(ROOT / "cases/lean-formalization/MG-C003/contract.json"),
                                   "sha256": case["group_contract_sha256"]}],
            "candidate_input_manifest": [], "completed_weight_semantic": 74, "total_weight": 92,
            "rows": [{"stage_id": sid, "decision": "pass" if index < 74 else "partial",
                "points_awarded": int(index < 74), "max_points": 1,
                "declarations": [{"file": "Main.lean", "name": "synthetic"}] if index < 74 else [],
                "source_evidence": [{"file": str(self.workspace / "Main.lean"), "name": "synthetic",
                                     "start_line": 1, "end_line": 1}] if index < 74 else []}
                for index, sid in enumerate(ids)]}
        self.documents["kernel_report"] = {
            "schema": "math-gauge.candidate-lean/v1", "status": "passed", "case_id": "MG-C003",
            "source_repaired": False, "group_contract_sha256": case["group_contract_sha256"],
            "alignment_inventory_validated": True, "semantic_alignment_inferred": False, "human_approval": False,
            "files_sha256": {"Main.lean": files["Main.lean"]["sha256"]},
            "alignment_manifest_sha256": files["alignment.json"]["sha256"], "alignment_manifest": alignment,
            "input_files_sha256": {},
            "modules": [{"module": "Main", "source_sha256": files["Main.lean"]["sha256"],
                         "exit_code": 0, "timeout": False}],
            "audit": {"summary": {"passed": True, "unexpected_axioms": []},
                      "declarations": [{"module": "Main", "name": "synthetic"}]},
            "reliability_binding": {"old_inline_raw_sha256": target["response_sha256"],
                "first_actual_snapshot_only": True, "original_project_modified": False,
                "snapshot": {"tree_sha256": tree_hash}, "selected_main_sha256": files["Main.lean"]["sha256"],
                "original_alignment_sha256": files["alignment.json"]["sha256"]}}
        self.documents["root_adjudication"] = {
            "schema": "math-gauge.paired-first-workspace-root-adjudication/v0.1.0", "case_id": "MG-C003",
            "reviewer_kind": "ai", "human_review": "pending", "formal_comparison_eligible": False,
            "assessment": {"terra": {"semantic_obligations": {"pass": 74, "incomplete": 18, "total": 92},
                                      "source_tree_sha256": tree_hash}}}
        self.rebind()

    def rebind(self):
        self.save("engineering_review")
        self.documents["kernel_report"]["reliability_binding"]["peer_static_review"] = {
            "sha256": self.hashes["engineering_review"]}
        self.save("kernel_report")
        assessment = self.documents["root_adjudication"]["assessment"]["terra"]
        assessment["semantic_review"] = {"sha256": self.hashes["engineering_review"]}
        assessment["compiler_diagnostic"] = {"kernel_report_sha256": self.hashes["kernel_report"]}
        self.save("root_adjudication")

    def engineering_score(self, model_key="terra"):
        names = {"original_summary", "original_report", "original_plan", "engineering_review",
                 "kernel_report", "source_manifest", "root_adjudication"}
        return source_qualified_engineering_score({name: self.sources[name] for name in names},
            expected_sha256={name: self.hashes[name] for name in names},
            workspace_root=self.workspace, model_key=model_key)

    def test_source_qualified_engineering_accepts_known_original_a1_without_rewriting_evidence(self):
        before = {name: path.read_bytes() for name, path in self.sources.items()}
        result = self.engineering_score()
        self.assertEqual(result["model_label"], RUNTIME["model_label"])
        self.assertEqual(result["mathematical_substitution"]["complete"], 74)
        self.assertFalse(result["mathematical_substitution"]["original_A1_replaced"])
        self.assertEqual(result["metrics"]["strict_pass_rate"], self.documents["original_summary"]["metrics"]["strict_pass_rate"])
        case = next(row for row in result["lean_formalization_breakdown"]["cases"] if row["case_id"] == "MG-C003")
        self.assertEqual((case["complete_count"], case["total"]), (74, 92))
        self.assertEqual(result["lean_formalization_breakdown"]["families"]["oet-volume1-chapter02"]["percent"], 100)
        self.assertEqual(before, {name: path.read_bytes() for name, path in self.sources.items()})
        self.assertNotIn(str(self.root), json.dumps(result))

    def test_engineering_source_identity_kernel_and_declared_ranges_cannot_be_substituted(self):
        with self.assertRaisesRegex(ValueError, "model and first-source"):
            self.engineering_score(model_key="gemini")
        originals = copy.deepcopy(self.documents)
        mutations = [lambda: self.documents["engineering_review"]["rows"][0]["source_evidence"][0].update(end_line=9),
            lambda: self.documents["engineering_review"]["rows"][0]["declarations"][0].update(name="other"),
            lambda: self.documents["engineering_review"]["rows"][0].update(stage_id=self.documents["engineering_review"]["rows"][1]["stage_id"]),
            lambda: self.documents["kernel_report"]["modules"][0].update(source_sha256="0" * 64),
            lambda: self.documents["kernel_report"].update(source_repaired=True)]
        for mutation in mutations:
            self.documents = copy.deepcopy(originals)
            mutation()
            self.rebind()
            with self.assertRaises(ValueError):
                self.engineering_score()
        self.documents = copy.deepcopy(originals)
        self.rebind()
        (self.workspace / "Main.lean").write_text("-- changed source\n")
        with self.assertRaisesRegex(ValueError, "actual source bytes changed"):
            self.engineering_score()

    def test_v02_augmented_score_uses_qualified_capability_and_negative_selfcheck(self):
        selected = self.engineering_score()
        self.documents["source_qualified_score"] = selected
        self.save("source_qualified_score")
        self.documents["policy"].update(version="0.2.0", false_complete_penalty_points=20,
                                        allow_negative_selfcheck=True)
        self.save("policy")
        self.documents["alignment_review"].update(scoring_version="0.2.0", policy_sha256=self.hashes["policy"])
        self.save("alignment_review")
        names = {"original_summary", "original_report", "original_plan", "alignment_review", "policy", "source_qualified_score"}
        result = alignment_augmented_score({name: self.sources[name] for name in names},
                                          expected_sha256={name: self.hashes[name] for name in names})
        self.assertEqual(result["metrics"]["lean_alignment_selfcheck"]["exact"], -20)
        self.assertEqual(result["metrics"]["neutral"]["exact"], 40)
        expected = 1 - Fraction(75, 100) * Fraction(45, 100) * Fraction(1, 2) * Fraction(18, 92) - Fraction(6, 100)
        self.assertEqual(result["metrics"]["overall"]["exact"], round(float(100 * expected), 10))
        self.assertEqual(result["capability_source"], "selected_sealed_engineering")
        self.assertEqual(result["lean_formalization_breakdown"], selected["lean_formalization_breakdown"])
        self.assertEqual(result["coverage"]["slots_planned"], 42)


class RebalancedAlignmentTests(BoundAlignmentFixture):
    def setUp(self):
        super().setUp()
        current = json.loads((ROOT / "results/v0.6.0/terra-6.1-max/20261105/scoring-policy.json").read_text())
        self.documents["policy"] = dict(current, version="0.3.0",
                                         obligation_ids=self.documents["policy"]["obligation_ids"])
        self.save("policy")
        self.documents["alignment_review"].update(scoring_version="0.3.0", policy_sha256=self.hashes["policy"])
        self.save("alignment_review")

    def refresh_baseline(self):
        report = score_inputs(self.inputs)
        self.documents["original_report"] = report
        self.documents["original_summary"] = public_score_projection(report, self.plan, private_aliases={})
        self.save("original_report")
        self.save("original_summary")

    def test_current_method_cannot_use_the_c003_only_aggregation_adapter(self):
        self.documents["policy"]["version"] = "0.4.0"
        self.save("policy")
        self.documents["alignment_review"].update(scoring_version="0.4.0", policy_sha256=self.hashes["policy"])
        self.save("alignment_review")
        with self.assertRaisesRegex(ValueError, "all four sealed engineering reviews"):
            self.score()

    def test_rebalances_only_aggregates_and_keeps_original_plan_and_penalty(self):
        original_bytes = self.sources["original_plan"].read_bytes()
        result = self.score()
        self.assertEqual(result["metrics"]["overall"]["exact"], 88)
        self.assertEqual(result["metrics"]["neutral"]["exact"], 20)
        self.assertEqual(result["metrics"]["lean_alignment_selfcheck"]["exact"], -20)
        self.assertEqual(result["profile"]["overall_weights"], {"core": 70, "repeat": 5, "neutral": 15, "stance": 10})
        expected_profile = copy.deepcopy(self.documents["original_summary"]["profile"])
        for row in expected_profile["components"]:
            row["weight"] = self.documents["policy"]["capability_component_weights"]["public"][row["id"]]
        expected_profile["overall_weights"] = self.documents["policy"]["overall_weights"]
        self.assertEqual(result["profile"], expected_profile)
        self.assertEqual(self.sources["original_plan"].read_bytes(), original_bytes)
        self.assertEqual(result["coverage"], self.documents["original_summary"]["coverage"])
        self.assertFalse(result["metrics"]["core"]["formal_comparison_eligible"])
        for name in {"repeat", "stance", "answer_review_major_error_rate", "answer_review_strict_pass_rate"}:
            self.assertEqual(result["metrics"][name], self.documents["original_summary"]["metrics"][name])
        policy = dict(self.documents["policy"], version="0.2.0",
                      overall_weights={"core": 75, "repeat": 5, "neutral": 10, "stance": 10},
                      neutral_group_weights={"written": 1, "lean_alignment": 1})
        review = dict(self.documents["alignment_review"], scoring_version="0.2.0")
        old = score_alignment_trajectory(review, policy)
        self.assertEqual(result["alignment_selfcheck"]["rounds"], old["rounds"])

    def test_written_direction_changes_core_by_its_new_full_share(self):
        proof_ids = {row["case_id"] for row in self.plan["case_index"] if row["component"] == "proofs"}
        for row in self.rows:
            if row["case_id"] in proof_ids:
                row["completion"] = {"lower": 0, "upper": 0, "exact": 0}
        self.refresh_baseline()
        self.assertEqual(self.score()["metrics"]["core"]["exact"], 60)

    def test_unknown_chapter_and_alignment_retain_full_new_denominators(self):
        row = next(row for row in self.rows if row["slot_id"] == "MG-C003:A1")
        row.update(completion=None, strict_pass=None)
        self.refresh_baseline()
        overall = self.score()["metrics"]["overall"]
        self.assertIsNone(overall["exact"])
        self.assertAlmostEqual(overall["upper"] - overall["lower"], 10.5)
        row.update(completion={"lower": 1, "upper": 1, "exact": 1}, strict_pass=True)
        self.refresh_baseline()
        self.documents["alignment_review"]["rounds"] = []
        self.save("alignment_review")
        result = self.score()
        overall = result["metrics"]["overall"]
        self.assertIsNone(overall["exact"])
        self.assertEqual((overall["lower"], overall["upper"]), (88, 100))
        self.assertEqual(result["alignment_selfcheck"]["metric"]["coverage"]["planned"], 3)

    def test_versioned_weight_maps_reject_drift_and_invalid_numeric_weights(self):
        original = copy.deepcopy(self.documents["policy"])
        for mutate in (lambda p: p["capability_component_weights"]["public"].update(proofs=39),
                       lambda p: p["capability_component_weights"]["combined"].pop("exploration"),
                       lambda p: p["capability_component_weights"]["public"].update(proofs=True),
                       lambda p: p["neutral_group_weights"].update(lean_alignment=1)):
            self.documents["policy"] = copy.deepcopy(original)
            mutate(self.documents["policy"])
            self.save("policy")
            self.documents["alignment_review"]["policy_sha256"] = self.hashes["policy"]
            self.save("alignment_review")
            with self.assertRaises(ValueError):
                self.score()


if __name__ == "__main__":
    unittest.main()
