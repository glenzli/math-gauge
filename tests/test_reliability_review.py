"""Offline review binding and provisional score gates; no mathematical claims."""

import copy
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from math_gauge.benchmarks import BenchmarkProfile, build_plan, identity, select_slots
from math_gauge.catalog import Suite, digest_bytes, read_json, write_json
from math_gauge.reliability import (apply_reliability_reviews, execute_reliability_run,
                                    inspect_reliability_run, reliability_review_templates,
                                    reliability_score_inputs, _slot_path)
from math_gauge.reliability_review import (_lean_evidence, _source_bundle, _verify_lean_artifact,
                                           review_binding, verify_reliability_candidate_lean)

ROOT = Path(__file__).resolve().parents[1]


class ReliabilityReviewTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.suite = Suite.load(ROOT / "cases")
        cls.profile = BenchmarkProfile.load(ROOT / "protocol/benchmark-profile.json", cls.suite)

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.plan = build_plan(self.profile, self.suite, ["neutral"], runtime={
            "model_label": "offline-review-fixture", "adapter_identity": "review-fixture-v1",
            "budget": {"timeout_seconds": 2}})
        replies = {s["slot_id"]: "synthetic bookkeeping only\r\n" if s["kind"] == "independent" else "KEEP\r\ncurrent rationale\r\n"
                   for s in select_slots(self.plan)}
        self.run = self.root / "run"
        execute_reliability_run(self.plan, self.suite, self.run, replay=replies)
        self.templates = {e["slot_id"]: e for e in reliability_review_templates(self.run)}
        self.cid = "MG-GR002"

    def math_pass(self, value):
        value.update(decision="pass", assumption_fidelity="clean", proof_validity="valid",
                     scope_accuracy="correct", unnecessary_restriction=False, reasons=[],
                     notes="Synthetic contract bookkeeping; no real candidate judgment.")

    def passing(self, sid):
        entry = copy.deepcopy(self.templates[sid])
        entry.update(reviewer="synthetic reviewer", reviewer_kind="fixture", decision="pass",
                     assumption_fidelity="clean", proof_validity="valid", scope_accuracy="correct",
                     unnecessary_restriction=False, notes="Synthetic fixture evidence, not a model result.")
        entry["format_review"] = {"decision": "valid", "notes": "Frozen valid format for this fixture."}
        for row in entry["stages"]:
            row.update(decision="pass", assumption_fidelity="clean", proof_validity="valid",
                       scope_accuracy="correct", failure_category="none", notes="Synthetic complete stage.")
            self.math_pass(row["math_review"])
        if "focus_review" in entry:
            self.math_pass(entry["focus_review"])
            focus = next(x for x in self.plan["reliability"]["selection"]["cases"] if x["case_id"] == entry["case_id"])
            entry["focus_review"]["verdict"] = focus["expected_truth"]
        if "keep_rationale_review" in entry:
            self.math_pass(entry["keep_rationale_review"])
        return entry

    def row(self, sid):
        return next(r for r in reliability_score_inputs(self.run)["slots"] if r["slot_id"] == sid)

    def test_stage_weights_derive_completion_and_fixture_never_becomes_formal(self):
        sid = self.cid + ":A1"
        entry = self.passing(sid)
        entry.update(reviewer_kind="human", completion=999, strict_pass=False)
        apply_reliability_reviews(self.run, [entry])
        row = self.row(sid)
        self.assertTrue(row["strict_pass"])
        self.assertEqual(row["completion"], {"lower": 1, "upper": 1, "exact": 1})
        self.assertEqual(row["whole_math"]["state"], "C")
        self.assertFalse(row["comparison_eligible"])
        self.assertTrue(row["fixture_only"])

    def test_legacy_runtime_labels_cannot_supply_missing_original_execution_audit(self):
        before = read_json(self.run / "run.json")
        labeled = dict(before, model_identity_verified=True, fresh_context_verified=True,
                       candidate_tools_verified_disabled=True)
        write_json(self.run / "run.json", labeled)
        sid = self.cid + ":A1"
        row = self.row(sid)
        self.assertFalse(row["comparison_eligible"])
        self.assertIsNone(row["execution_receipt_sha256"])
        self.assertIn("execution_evidence_missing", row["execution_eligibility"]["reasons"])
        self.assertEqual(row["slot_record_sha256"], before["slot_record_sha256"][sid])

    def test_candidate_incomplete_is_zero_without_becoming_mathematical_error(self):
        sid = self.cid + ":A1"
        entry = self.passing(sid)
        entry["decision"] = "partial"
        stage = entry["stages"][0]
        stage.update(decision="partial", failure_category="mathematical", proof_validity="unknown")
        stage["math_review"].update(decision="partial", proof_validity="unknown", reasons=["candidate_incomplete"])
        apply_reliability_reviews(self.run, [entry])
        row = self.row(sid)
        points = self.plan["case_index"][[c["case_id"] for c in self.plan["case_index"]].index(self.cid)]["stages"][0]["points"]
        self.assertEqual(row["completion"]["exact"], (100 - points) / 100)
        self.assertFalse(row["strict_pass"])
        self.assertEqual(row["whole_math"]["state"], "U")
        self.assertTrue(row["whole_math"]["adjudicated"])

    def test_pending_problem_defect_overrides_fail_weight(self):
        sid = self.cid + ":A1"
        entry = self.passing(sid)
        entry["decision"] = "partial"
        stage = entry["stages"][0]
        stage.update(decision="fail", failure_category="problem_defect")
        stage["math_review"].update(decision="unresolved", reasons=["problem_defect_pending"])
        apply_reliability_reviews(self.run, [entry])
        row = self.row(sid)
        self.assertIsNone(row["completion"]["exact"])
        self.assertIsNone(row["strict_pass"])
        self.assertTrue(row["problem_defect"])
        self.assertIn("problem_defect_pending", row["whole_math"]["reasons"])

    def test_keep_current_wrong_rationale_cannot_inherit_a_correct_pass(self):
        sid = self.cid + ":neutral:1"
        entry = self.passing(sid)
        entry["decision"] = "fail"
        rationale = entry["keep_rationale_review"]
        rationale.update(decision="fail", proof_validity="invalid", reasons=["mathematical_error"],
                         notes="Synthetic invalid current rationale, independent from inherited body.")
        apply_reliability_reviews(self.run, [entry])
        row = self.row(sid)
        self.assertFalse(row["strict_pass"])
        self.assertEqual(row["whole_math"]["state"], "I")
        self.assertEqual(row["focus_math"]["state"], "I")
        self.assertEqual(row["completion"]["exact"], 0)

    def test_old_rationale_is_not_a_current_claim_in_next_keep(self):
        first = self.passing(self.cid + ":neutral:1")
        first["decision"] = "fail"
        first["keep_rationale_review"].update(decision="fail", proof_validity="invalid", reasons=["mathematical_error"])
        second = self.passing(self.cid + ":neutral:2")
        apply_reliability_reviews(self.run, [first, second])
        self.assertEqual(self.row(second["slot_id"])["whole_math"]["state"], "C")
        self.assertTrue(self.row(second["slot_id"])["strict_pass"])

    def test_whole_lean_failure_preserves_focus_mathematics(self):
        sid = "MG-GF106:A1"
        entry = self.passing(sid)
        entry["decision"] = "partial"
        for row in entry["stages"]:
            if row["lean_status"] != "not_required":
                row.update(decision="partial", failure_category="lean_compilation", lean_status="compile_error")
        apply_reliability_reviews(self.run, [entry])
        row = self.row(sid)
        self.assertFalse(row["strict_pass"])
        self.assertEqual(row["whole_math"]["state"], "C")
        self.assertEqual(row["focus_math"]["state"], "C")
        self.assertEqual(row["whole_strict"]["state"], "U")
        self.assertIn("lean_failure", row["whole_strict"]["reasons"])

    def test_no_source_receipt_cannot_claim_lean_pass(self):
        entry = self.passing("MG-GF106:A1")
        for row in entry["stages"]:
            row.update(lean_status="passed", declarations=[{"file": "Solution.lean", "name": "proof"}])
        with self.assertRaisesRegex(ValueError, "actual original-source"):
            apply_reliability_reviews(self.run, [entry])

    def test_minimal_self_hashed_lean_receipt_is_not_compilation_evidence(self):
        entry = self.passing("MG-GF106:A1")
        meta, records = inspect_reliability_run(self.run)
        record = records[entry["slot_id"]]
        case = next(c for c in self.plan["case_index"] if c["case_id"] == record["case_id"])
        receipt = {"schema": "math-gauge.candidate-lean/v1", "status": "passed", "source_repaired": False,
                   "case_id": record["case_id"], "response_sha256": record["response_sha256"],
                   "request_sha256": case["request_sha256"], "group_contract_sha256": case["group_contract_sha256"],
                   "reliability_binding": review_binding(meta, record)}
        path = self.run / "fake-receipt/report.json"
        write_json(path, receipt)
        entry.update(candidate_lean_report="fake-receipt/report.json", candidate_lean_report_sha256=digest_bytes(path.read_bytes()))
        for row in entry["stages"]:
            row.update(lean_status="passed", declarations=[{"file": "Solution.lean", "name": "proof"}])
        with self.assertRaisesRegex(ValueError, "Missing or escaping file"):
            apply_reliability_reviews(self.run, [entry])

    def test_review_binding_tampering_is_rejected(self):
        sid = self.cid + ":neutral:1"
        for key in ("response_sha256", "history_sha256", "parent_material_sha256", "parser_version", "body_origin"):
            with self.subTest(key=key):
                entry = self.passing(sid)
                entry["binding"][key] = "forged"
                with self.assertRaisesRegex(ValueError, "binding changed"):
                    apply_reliability_reviews(self.run, [entry])

    def test_focus_pass_requires_correct_frozen_truth_and_valid_argument(self):
        entry = self.passing(self.cid + ":A1")
        entry["focus_review"]["verdict"] = "true"
        with self.assertRaisesRegex(ValueError, "frozen target truth"):
            apply_reliability_reviews(self.run, [entry])
        entry = self.passing(self.cid + ":A1")
        entry["focus_review"]["proof_validity"] = "unknown"
        with self.assertRaisesRegex(ValueError, "Pass contradicts"):
            apply_reliability_reviews(self.run, [entry])

    def test_saved_review_revalidated_not_trusted_as_numeric_result(self):
        sid = self.cid + ":A1"
        apply_reliability_reviews(self.run, [self.passing(sid)])
        path = self.run / "review-snapshots/000001.json"
        snapshot = read_json(path)
        review = snapshot["reviews"][sid]
        review["stages"][0]["proof_validity"] = "invalid"
        review["review_sha256"] = identity({k: v for k, v in review.items() if k != "review_sha256"})
        snapshot["snapshot_sha256"] = identity({k: v for k, v in snapshot.items() if k != "snapshot_sha256"})
        write_json(path, snapshot)
        index_path = self.run / "reliability-reviews.json"
        index = read_json(index_path)
        index["snapshots"][0].update(file_sha256=digest_bytes(path.read_bytes()), snapshot_sha256=snapshot["snapshot_sha256"])
        write_json(index_path, index)
        with self.assertRaisesRegex(ValueError, "stage pass contradicts"):
            reliability_score_inputs(self.run)

    def test_unreviewed_and_technical_slots_remain_unknown(self):
        row = self.row(self.cid + ":A1")
        self.assertIsNone(row["strict_pass"])
        self.assertIsNone(row["completion"]["exact"])
        self.assertFalse(row["focus_math"]["adjudicated"])
        self.assertEqual(row["focus_math"]["reasons"], ["review_pending"])

    def test_verifier_uses_original_response_not_reconstructed_single_run(self):
        sid = "MG-GF106:neutral:1"
        before = {p: p.read_bytes() for p in self.run.rglob("response.md")}
        result = verify_reliability_candidate_lean(self.run, sid, self.root / "compile-fixture",
                                                    dependency_root=self.root / "absent")
        self.assertEqual(result["status"], "format_error")
        self.assertEqual(result["reliability_binding"]["slot_id"], sid)
        self.assertEqual(result["reliability_binding"]["body_origin"]["slot_id"], "MG-GF106:A1")
        self.assertEqual(before, {p: p.read_bytes() for p in self.run.rglob("response.md")})

    def test_focus_in_pending_defective_stage_stays_unknown(self):
        sid = self.cid + ":neutral:1"
        entry = self.passing(sid)
        entry["decision"] = "partial"
        target = entry["focus_review"]["stage_id"]
        stage = next(s for s in entry["stages"] if s["stage_id"] == target)
        stage.update(decision="partial", failure_category="problem_defect")
        stage["math_review"].update(decision="unresolved", reasons=["problem_defect_pending"])
        apply_reliability_reviews(self.run, [entry])
        axis = self.row(sid)["focus_math"]
        self.assertEqual(axis["state"], "U")
        self.assertFalse(axis["adjudicated"])
        self.assertEqual(axis["reasons"], ["problem_defect_pending"])

    def test_math_failure_cannot_be_relabelled_math_c(self):
        entry = self.passing(self.cid + ":A1")
        entry["decision"] = "partial"
        entry["stages"][0].update(decision="partial", failure_category="mathematical")
        with self.assertRaisesRegex(ValueError, "Mathematical stage failure"):
            apply_reliability_reviews(self.run, [entry])

    def test_pending_review_revision_preserves_append_only_snapshots(self):
        sid = self.cid + ":A1"
        pending = self.passing(sid)
        pending["decision"] = "unresolved"
        for row in pending["stages"]:
            row.update(decision="unresolved", failure_category="unresolved")
            row["math_review"].update(decision="unresolved", reasons=["review_pending"])
        pending["focus_review"].update(decision="unresolved", reasons=["review_pending"])
        apply_reliability_reviews(self.run, [pending])
        original_path = self.run / "review-snapshots/000001.json"
        original = original_path.read_bytes()
        one = reliability_score_inputs(self.run)
        with self.assertRaisesRegex(ValueError, "explicit revise"):
            apply_reliability_reviews(self.run, [self.passing(sid)])
        with self.assertRaisesRegex(ValueError, "expected snapshot"):
            apply_reliability_reviews(self.run, [self.passing(sid)], revise=True, expected_snapshot="wrong")
        apply_reliability_reviews(self.run, [self.passing(sid)], revise=True,
                                  expected_snapshot=one["review_snapshot"]["sha256"])
        self.assertEqual(original_path.read_bytes(), original)
        current = reliability_score_inputs(self.run)
        prior = reliability_score_inputs(self.run, snapshot=1)
        self.assertEqual(current["review_snapshot"]["version"], 2)
        self.assertEqual(prior["review_snapshot"]["version"], 1)
        c = next(r for r in current["slots"] if r["slot_id"] == sid)
        p = next(r for r in prior["slots"] if r["slot_id"] == sid)
        self.assertEqual(c["evidence_id"], p["evidence_id"])
        self.assertEqual(c["binding"], p["binding"])
        self.assertIsNone(p["strict_pass"])
        self.assertTrue(c["strict_pass"])

    def test_overall_failure_cannot_promote_initial_full_or_keep_to_pass(self):
        for suffix in (":A1", ":neutral:1"):
            with self.subTest(mode=suffix):
                entry = self.passing(self.cid + suffix)
                entry.update(decision="fail", proof_validity="invalid")
                with self.assertRaisesRegex(ValueError, "All-stage pass|attributed stage|whole-answer decision"):
                    apply_reliability_reviews(self.run, [entry])
        # A separate FULL node must have the same reverse-consistency gate.
        replies = {s["slot_id"]: "fixture initial" if s["kind"] == "independent" else "FULL\nfixture complete replacement"
                   for s in select_slots(self.plan)}
        other = self.root / "full"
        execute_reliability_run(self.plan, self.suite, other, replay=replies)
        entry = next(e for e in reliability_review_templates(other) if e["slot_id"] == self.cid + ":neutral:1")
        current = self.templates
        try:
            self.templates = {entry["slot_id"]: entry}
            failed = self.passing(entry["slot_id"])
        finally:
            self.templates = current
        failed.update(decision="fail", proof_validity="invalid")
        with self.assertRaisesRegex(ValueError, "All-stage pass|attributed stage"):
            apply_reliability_reviews(other, [failed])

    def test_stage_scope_focus_cannot_claim_an_incomplete_whole_stage(self):
        sid = "MG-GR007:neutral:1"
        entry = self.passing(sid)
        entry["decision"] = "partial"
        target = entry["focus_review"]["stage_id"]
        stage = next(s for s in entry["stages"] if s["stage_id"] == target)
        stage.update(decision="partial", failure_category="mathematical", proof_validity="unknown")
        stage["math_review"].update(decision="partial", proof_validity="unknown", reasons=["candidate_incomplete"])
        with self.assertRaisesRegex(ValueError, "Whole-stage focus review contradicts"):
            apply_reliability_reviews(self.run, [entry])

    def test_unrelated_bad_keep_rationale_blocks_strict_without_erasing_stage_credit(self):
        sid = self.cid + ":neutral:1"
        entry = self.passing(sid)
        entry.update(decision="fail", proof_validity="invalid")
        entry["keep_rationale_review"].update(decision="fail", proof_validity="invalid",
                                               reasons=["mathematical_error"],
                                               affects_focus=False, affected_stages=[])
        apply_reliability_reviews(self.run, [entry])
        row = self.row(sid)
        self.assertFalse(row["strict_pass"])
        self.assertEqual(row["whole_math"]["state"], "I")
        self.assertEqual(row["focus_math"]["state"], "C")
        self.assertEqual(row["completion"]["exact"], 1)

    def test_unchanged_keep_reuses_only_the_bound_original_source_identity(self):
        meta, records = inspect_reliability_run(self.run)
        sid = "MG-GF106:neutral:1"
        source = records["MG-GF106:A1"]
        record = records[sid]
        path = self.run / "binding-fixture.json"
        write_json(path, {"reliability_binding": review_binding(meta, source)})
        entry = {"candidate_lean_report": path.name,
                 "candidate_lean_report_sha256": digest_bytes(path.read_bytes())}
        contract = read_json(self.run / meta["inputs"]["MG-GF106"]["contract"])
        # Isolate source reuse from the artifact verifier. This stub is never
        # applied as a review or reported as a compilation/model result.
        with patch("math_gauge.reliability_review._verify_lean_artifact", return_value={"binding-fixture": True}) as gate:
            self.assertEqual(_lean_evidence(self.run, meta, records, record, entry, contract), {"binding-fixture": True})
            gate.assert_called_once()
        value = read_json(path)
        value["reliability_binding"]["body_origin"]["response_sha256"] = "forged"
        write_json(path, value)
        entry["candidate_lean_report_sha256"] = digest_bytes(path.read_bytes())
        with self.assertRaisesRegex(ValueError, "original source"):
            _lean_evidence(self.run, meta, records, record, entry, contract)

    def test_real_extraction_artifact_rejects_saved_source_and_engine_tampering(self):
        source = "```lean filename=Answer.lean\r\ntheorem syntheticProof : True := True.intro\r\n```\r\n"
        replies = {s["slot_id"]: source if s["kind"] == "independent" else "KEEP\r\ncurrent rationale\r\n"
                   for s in select_slots(self.plan)}
        root = self.root / "source-run"
        execute_reliability_run(self.plan, self.suite, root, replay=replies)
        output = self.root / "source-artifact"
        report = verify_reliability_candidate_lean(root, "MG-GF106:neutral:1", output,
                                                    dependency_root=self.root / "absent")
        self.assertEqual(report["status"], "infrastructure_error")
        meta, records = inspect_reliability_run(root)
        bundle = _source_bundle(root, meta, records, records["MG-GF106:neutral:1"])
        raw = bundle["response_path"].read_bytes()
        request = read_json(bundle["request_path"])
        contract = read_json(bundle["contract_path"])
        # Negative fixture: altering a status/hash label never suffices to
        # promote the failed real extraction/manifest into a valid artifact.
        forged = dict(report, status="passed")
        saved = output / "submitted/Answer.lean"
        saved.write_bytes(saved.read_bytes() + b"-- repaired\n")
        with self.assertRaisesRegex(ValueError, "source bytes changed"):
            _verify_lean_artifact(output / "report.json", forged, bundle["record"], raw, request, contract)
        saved.write_bytes(b"theorem syntheticProof : True := True.intro\r\n")
        forged["engine_identity"] = {"execution": "forged"}
        with self.assertRaisesRegex(ValueError, "engine or audit identity changed"):
            _verify_lean_artifact(output / "report.json", forged, bundle["record"], raw, request, contract)


if __name__ == "__main__":
    unittest.main()
