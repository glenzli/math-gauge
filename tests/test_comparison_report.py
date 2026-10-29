"""Synthetic comparison contracts, never real model results."""

import json
from pathlib import Path
import tempfile
import unittest

from math_gauge.catalog import digest_bytes, write_json
from math_gauge.review import compare_models


class ComparisonContracts(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.cid = "TEST-ONLY"
        self.request = {
            "schema": "math-gauge.request/v1",
            "case_id": self.cid,
            "case_version": "1",
            "track": "exploration",
            "instruction": "",
            "task": "Synthetic transport fixture.",
            "files": [],
        }
        self.request_hash = digest_bytes(
            json.dumps(self.request, ensure_ascii=False, sort_keys=True).encode()
        )
        self.message_hash = digest_bytes(self.request["task"].encode())
        self.response = b"Synthetic answer, not mathematical evidence."
        self.response_hash = digest_bytes(self.response)
        self.index = [
            {
                "case_id": self.cid,
                "version": "1",
                "task_kind": "written",
                "family_id": "fixture",
                "section": "fixture",
                "suite_sha256": "fixture-suite",
                "author_lean_coverage": "synthetic-not-mathematical-evidence",
                "request_sha256": self.request_hash,
                "candidate_message_sha256": self.message_hash,
            }
        ]
        self.runs = {}
        self.receipts = {}
        for label in ("synthetic-a", "synthetic-b"):
            root = self.root / label
            write_json(
                root / "run.json",
                {
                    "schema": "math-gauge.run/v1",
                    "origin": "command",
                    "run_id": label + "-fixture-run",
                    "model_label": label,
                    "suite_sha256": "fixture-suite",
                    "cases": [{"id": self.cid, "version": "1", "case_approved": False}],
                },
            )
            write_json(root / self.cid / "solver/request.json", self.request)
            (root / self.cid / "response.md").write_bytes(self.response)
            write_json(
                root / self.cid / "record.json",
                {
                    "case_id": self.cid,
                    "status": "ok",
                    "request_sha256": self.request_hash,
                    "response_sha256": self.response_hash,
                },
            )
            write_json(
                root / "reviews.json",
                {
                    self.cid: {
                        "response_sha256": self.response_hash,
                        "reviewer": "Synthetic test fixture",
                        "reviewer_kind": "ai",
                        "decision": "pass",
                        "assumption_fidelity": "clean",
                        "proof_validity": "valid",
                        "scope_accuracy": "correct",
                        "unnecessary_restriction": False,
                    }
                },
            )
            receipt = root / "execution-assessment.json"
            write_json(
                receipt,
                {
                    "case_id": self.cid,
                    "run_id": label + "-fixture-run",
                    "model_label": label,
                    "response_sha256": self.response_hash,
                    "request_sha256": self.request_hash,
                    "candidate_message_sha256": self.message_hash,
                    "mathematical_request_count": 1,
                    "valid_for_comparison": True,
                    "outcome": "synthetic-test-only",
                },
            )
            self.runs[label] = [root]
            self.receipts[label] = {self.cid: receipt}

    def result(self, **kwargs):
        return compare_models(
            self.index, self.runs, execution_receipts=self.receipts, **kwargs
        )

    def test_same_frozen_inputs_produce_provisional_paired_counts(self):
        result = self.result()
        self.assertTrue(result["complete"])
        self.assertEqual(result["paired"]["counts"]["both_pass"], 1)
        self.assertEqual(
            result["models"]["synthetic-a"]["human_comparison_eligible"], 0
        )

    def test_missing_run_does_not_publish_complete_suite_rate(self):
        self.runs["synthetic-b"] = []
        result = self.result()
        self.assertFalse(result["complete"])
        self.assertIsNone(
            result["models"]["synthetic-b"]["summary"]["strict_pass_rate"]
        )
        self.assertEqual(result["paired"]["comparable"], 0)

    def test_missing_receipt_keeps_request_count_unknown(self):
        self.receipts["synthetic-a"] = {}
        summary = self.result()["models"]["synthetic-a"]["summary"]
        self.assertIsNone(summary["mathematical_requests"])
        self.assertEqual(summary["unknown_request_counts"], 1)
        self.assertEqual(summary["known_mathematical_requests"], 0)

    def test_identical_answer_cannot_reuse_other_models_receipt(self):
        self.receipts["synthetic-a"] = self.receipts["synthetic-b"]
        with self.assertRaisesRegex(ValueError, "different model or run"):
            self.result()

    def test_unresolved_human_review_is_not_eligible(self):
        for paths in self.runs.values():
            p = paths[0] / "run.json"
            meta = json.loads(p.read_text())
            meta["cases"][0]["case_approved"] = True
            write_json(p, meta)
            p = paths[0] / "reviews.json"
            reviews = json.loads(p.read_text())
            reviews[self.cid].update(reviewer_kind="human", decision="unresolved")
            write_json(p, reviews)
        result = self.result()
        self.assertFalse(result["complete"])
        self.assertEqual(
            result["models"]["synthetic-a"]["human_comparison_eligible"], 0
        )

    def test_lean_failure_does_not_resolve_human_review_eligibility(self):
        for task_kind in ("generate", "repair"):
            for lean_status in ("compile_error", "axiom_rejected"):
                for decision in ("unresolved", "fail", "partial"):
                    with self.subTest(
                        task_kind=task_kind,
                        lean_status=lean_status,
                        decision=decision,
                    ):
                        self.index[0]["task_kind"] = task_kind
                        reports = {}
                        for label, paths in self.runs.items():
                            root = paths[0]
                            p = root / "run.json"
                            meta = json.loads(p.read_text())
                            meta["cases"][0]["case_approved"] = True
                            write_json(p, meta)
                            lean_path = root / "candidate-lean.json"
                            write_json(
                                lean_path,
                                {
                                    "case_id": self.cid,
                                    "response_sha256": self.response_hash,
                                    "request_sha256": self.request_hash,
                                    "status": lean_status,
                                },
                            )
                            reports[label] = {self.cid: lean_path}
                            p = root / "reviews.json"
                            reviews = json.loads(p.read_text())
                            reviews[self.cid].update(
                                reviewer_kind="human",
                                decision=decision,
                                assumption_fidelity="unknown",
                                proof_validity="unknown",
                                scope_accuracy="unknown",
                                candidate_lean_report_sha256=digest_bytes(
                                    lean_path.read_bytes()
                                ),
                            )
                            write_json(p, reviews)
                        result = self.result(lean_reports=reports)
                        # A Lean rejection settles strict failure, not the human opinion.
                        self.assertTrue(result["complete"])
                        self.assertEqual(
                            result["paired"]["counts"]["neither_pass"], 1
                        )
                        for model in result["models"].values():
                            row = model["cases"][0]
                            self.assertTrue(row["resolved"])
                            self.assertFalse(row["strict_pass"])
                            self.assertEqual(row["decision"], decision)
                            self.assertEqual(
                                row["outcome"], "candidate_lean_" + lean_status
                            )
                            self.assertEqual(
                                row["human_comparison_eligible"],
                                decision != "unresolved",
                            )
                            self.assertEqual(
                                model["human_comparison_eligible"],
                                int(decision != "unresolved"),
                            )

    def test_audit_polarity_is_paired_and_stratified(self):
        self.index[0].update(task_kind="audit", audit_expected="misaligned")
        result = self.result()
        self.assertEqual(
            result["paired"]["groups"]["audit_expected"]["misaligned"]["counts"][
                "both_pass"
            ],
            1,
        )

    def test_changed_prompt_and_replay_are_rejected(self):
        root = self.runs["synthetic-a"][0]
        p = root / self.cid / "solver/request.json"
        write_json(p, dict(self.request, task="Changed fixture."))
        with self.assertRaisesRegex(ValueError, "candidate input changed"):
            self.result()
        write_json(p, self.request)
        p = root / "run.json"
        meta = json.loads(p.read_text())
        meta["origin"] = "replay"
        write_json(p, meta)
        with self.assertRaisesRegex(ValueError, "Replay"):
            self.result()

    def test_lean_compile_failure_cannot_become_a_strict_pass(self):
        self.index[0]["task_kind"] = "generate"
        reports = {}
        for label in self.runs:
            p = self.runs[label][0] / "candidate-lean.json"
            write_json(
                p,
                {
                    "case_id": self.cid,
                    "response_sha256": self.response_hash,
                    "request_sha256": self.request_hash,
                    "status": "compile_error",
                },
            )
            reports[label] = {self.cid: p}
        result = self.result(lean_reports=reports)
        self.assertTrue(result["complete"])
        self.assertEqual(result["paired"]["counts"]["neither_pass"], 1)
        self.assertEqual(result["models"]["synthetic-a"]["summary"]["strict_passes"], 0)

    def test_successful_lean_semantic_review_must_bind_its_report(self):
        self.index[0]["task_kind"] = "repair"
        reports = {}
        for label in self.runs:
            p = self.runs[label][0] / "candidate-lean.json"
            write_json(
                p,
                {
                    "case_id": self.cid,
                    "response_sha256": self.response_hash,
                    "request_sha256": self.request_hash,
                    "status": "passed",
                },
            )
            reports[label] = {self.cid: p}
        with self.assertRaisesRegex(ValueError, "must bind candidate Lean evidence"):
            self.result(lean_reports=reports)


if __name__ == "__main__":
    unittest.main()
