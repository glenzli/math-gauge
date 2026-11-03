"""Offline author-evidence boundaries; new written papers inherit no Lean proof."""

import copy
import importlib.util
from pathlib import Path
import unittest
from unittest.mock import patch

import test_formal_verifier as formal

ROOT = Path(__file__).resolve().parents[1]


class AuthorEvidenceScopeTests(unittest.TestCase):
    def setUp(self):
        self.fixture = formal.RetainedEvidenceTests(methodName="runTest")
        self.fixture.setUp()
        self.addCleanup(self.fixture.tearDown)
        self.repo = self.fixture.repo
        self.original_id = self.fixture.mapping["id"]
        self.original_manifest = f"proofs/{self.original_id}/case.json"

    def add_assessment(self, cid="SYN-WRITTEN", *, kind="written_proof"):
        base = self.repo / "cases/proofs" / cid
        base.mkdir(parents=True)
        for name in ("task.md", "reference.md"):
            (base / name).write_text("Synthetic mathematical material only\n")
        formal.V.save(base / "rubric.json", {"required_evidence": ["Synthetic"], "critical_errors": ["Synthetic"]})
        written = kind == "written_proof"
        formal.V.save(base / "contract.json", {
            "schema": "math-gauge.group-contract/v2", "id": cid, "version": "fixture-1", "kind": kind,
            "assessment_unit": "proof_criterion" if written else "review_dimension",
            ("criteria" if written else "dimensions"): [{"id": "C1", "points": 100,
                "title": "Synthetic criterion", "required_evidence": ["Synthetic"], "critical_errors": ["Synthetic"]}]})
        case = {"schema": "math-gauge.case/v1", "id": cid, "version": "fixture-1", "path_base": "case",
                "task_kind": "written" if written else "answer_review", "track": "determinate",
                "family_id": "synthetic-parent-family", "lean_checks": [], "sources": ["synthetic-source"],
                "task": "task.md", "reference": "reference.md", "rubric": "rubric.json",
                "group_contract": "contract.json", "evaluator_files": ["provenance.json", "review.json"],
                "review": {"mathematical": "author-ai-fixture", "human": "pending",
                    "formalization": {"status": "not-performed" if written else "not-required-for-written-review",
                                      "inherited_parent_evidence": False}}}
        formal.V.save(base / "case.json", case)
        formal.V.save(base / "provenance.json", {"kind": "synthetic", "author_lean_coverage_inherited": False})
        formal.V.save(base / "review.json", {"mathematical": "author-ai-fixture", "human": "pending",
                                             "parent_lean_evidence_inherited": False})
        formal.V.save(self.repo / "cases/sources.json", {"synthetic-source": {"title": "Synthetic provenance"}})
        path = self.repo / "cases/suite.json"
        suite = formal.V.load(path)
        suite["cases"].append(f"proofs/{cid}/case.json")
        formal.V.save(path, suite)
        return base

    def checked(self):
        with patch.object(formal.V, "command", side_effect=AssertionError("No compilation or model calls")):
            return formal.E.check_all(self.repo)

    def test_original_bank_stays_complete_and_additional_units_stay_separate(self):
        before = self.checked()
        frozen = (self.repo / "verification/author/checked-ledger.json").read_bytes()
        base = self.add_assessment()
        self.add_assessment("SYN-REVIEW", kind="answer_review")
        result = self.checked()
        self.assertEqual(result["counts"], before["counts"])
        self.assertEqual(result["cases"], before["cases"])
        self.assertEqual(result["counts"]["fully_formalized_papers"], 1)
        self.assertEqual(result["written_proofs"]["papers"], 1)
        self.assertEqual(result["written_proofs"]["proof_criteria"], 1)
        self.assertEqual(result["written_proofs"]["formalized_papers"], 0)
        row = result["written_proofs"]["cases"][0]
        self.assertEqual(row["formal_status"], "not-performed")
        self.assertFalse(row["inherited_author_coverage"])
        self.assertEqual(row["sha256"]["reference"], formal.V.digest(base / "reference.md"))
        self.assertEqual(result["answer_reviews"]["tasks"], 1)
        self.assertEqual(result["answer_reviews"]["review_dimensions"], 1)
        self.assertEqual(result["answer_reviews"]["formal_status"], "not-applicable")
        self.assertEqual(frozen, (self.repo / "verification/author/checked-ledger.json").read_bytes())

    def test_manifest_only_reserve_selection_preserves_all_original_paths_and_bytes(self):
        before = {str(path): path.read_bytes() for path in self.fixture.case.rglob("*") if path.is_file()}
        self.add_assessment()
        suite_path = self.repo / "cases/suite.json"
        suite = formal.V.load(suite_path)
        suite["cases"].remove(self.original_manifest)
        formal.V.save(suite_path, suite)
        formal.V.save(self.repo / "cases/reserve-suite.json", {"schema": "math-gauge.suite/v1",
                                                              "cases": [self.original_manifest]})
        result = self.checked()
        self.assertEqual(result["counts"]["papers"], 1)
        self.assertEqual(result["written_proofs"]["papers"], 1)
        self.assertEqual(before, {str(path): path.read_bytes() for path in self.fixture.case.rglob("*") if path.is_file()})

    def test_additional_assessments_cannot_hide_a_missing_original_or_duplicate_its_id(self):
        base = self.add_assessment()
        suite_path = self.repo / "cases/suite.json"
        original = formal.V.load(suite_path)
        changed = copy.deepcopy(original)
        changed["cases"].remove(self.original_manifest)
        formal.V.save(suite_path, changed)
        with self.assertRaisesRegex(formal.V.VerificationError, "original evidence layout disagree"):
            self.checked()
        formal.V.save(suite_path, original)
        case = formal.V.load(base / "case.json")
        case["id"] = self.original_id
        formal.V.save(base / "case.json", case)
        with self.assertRaisesRegex(formal.V.VerificationError, "IDs must be distinct"):
            self.checked()

    def test_missing_reference_provenance_or_review_status_cannot_receive_an_inventory(self):
        base = self.add_assessment()
        for name, replacement in (("reference.md", b""), ("review.json", b'{}\n'),
                                  ("provenance.json", b'{}\n')):
            path = base / name
            original = path.read_bytes()
            path.write_bytes(replacement)
            with self.subTest(name=name), self.assertRaises(formal.V.VerificationError):
                self.checked()
            path.write_bytes(original)
        (base / "provenance.json").unlink()
        with self.assertRaisesRegex(formal.V.VerificationError, "Missing or escaping"):
            self.checked()

    def test_formal_completion_or_inherited_parent_evidence_is_rejected(self):
        base = self.add_assessment()
        case_path = base / "case.json"
        original = formal.V.load(case_path)
        for field, value in (("status", "complete"), ("inherited_parent_evidence", True)):
            case = copy.deepcopy(original)
            case["review"]["formalization"][field] = value
            formal.V.save(case_path, case)
            with self.subTest(field=field), self.assertRaises(formal.V.VerificationError):
                self.checked()
        formal.V.save(case_path, original)
        provenance = formal.V.load(base / "provenance.json")
        provenance["author_lean_coverage_inherited"] = True
        formal.V.save(base / "provenance.json", provenance)
        with self.assertRaisesRegex(formal.V.VerificationError, "cannot inherit"):
            self.checked()

    def test_unknown_mathematical_case_requires_its_own_author_evidence(self):
        base = self.add_assessment()
        contract = formal.V.load(base / "contract.json")
        contract["kind"] = "progressive"
        formal.V.save(base / "contract.json", contract)
        with self.assertRaisesRegex(formal.V.VerificationError, "need their own author evidence"):
            self.checked()

    def test_protocol_summary_reports_current_unformalized_criteria_without_adding_lean_credit(self):
        formal.V.save(self.repo / "verification/author/ledger.json", self.checked())
        self.add_assessment()
        self.add_assessment("SYN-REVIEW", kind="answer_review")
        spec = importlib.util.spec_from_file_location("author_scope_protocol", ROOT / "scripts/validate_protocol.py")
        protocol = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(protocol)
        before = (self.repo / "verification/author/ledger.json").read_bytes()
        summary = protocol.author_summary(self.repo)
        self.assertEqual(summary["retained_author_papers"], 1)
        self.assertEqual(summary["full_papers"], 1)
        self.assertEqual(summary["mandatory_units_complete"], 1)
        self.assertEqual(summary["unformalized_written_proofs"], 1)
        self.assertEqual(summary["proof_criteria"], 1)
        self.assertEqual(summary["answer_review_tasks"], 1)
        self.assertFalse(summary["written_proof_cases"][0]["inherited_author_coverage"])
        self.assertEqual(before, (self.repo / "verification/author/ledger.json").read_bytes())


if __name__ == "__main__":
    unittest.main()
