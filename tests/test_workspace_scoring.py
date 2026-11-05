"""Synthetic source-selection checks; no fixture is real model or human evidence."""

import copy
import json
import tempfile
import unittest
from fractions import Fraction
from pathlib import Path

from math_gauge.benchmarks import BenchmarkProfile, build_plan
from math_gauge.catalog import Suite, digest_bytes
from math_gauge.scoring import (public_score_projection, score_inputs,
                                source_qualified_workspace_score)
from test_scoring import fixture_rows
from benchmark_fixtures import arithmetic_source_plan

ROOT = Path(__file__).resolve().parents[1]
RUNTIME = {"model_label": "offline-workspace-fixture", "budget": {"timeout_seconds": 5400},
           "adapter_identity": {"kind": "fixture"},
           "execution_track": "math-gauge.local-tools-no-search/v1"}


class WorkspaceScoringTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.plan = arithmetic_source_plan(RUNTIME)

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.workspace = self.root / "workspace"
        self.workspace.mkdir()
        main = self.workspace / "Main.lean"
        main.write_text("-- Synthetic source binding only; never compiled.\n")
        self.source_sha = digest_bytes(main.read_bytes())
        self.stage_ids = [stage["stage_id"] for case in self.plan["case_index"]
                          if case["case_id"] == "MG-C003" for stage in case["stages"]]
        rows = fixture_rows(self.plan)
        target = next(row for row in rows if row["slot_id"] == "MG-C003:A1")
        target.update(completion={"lower": 0, "upper": 1, "exact": None}, strict_pass=None,
                      reviewer_kind=None, review_sha256=None)
        # The projection's reviewed coverage is bound to actual review hashes.
        for row in rows:
            if row is not target:
                row["review_sha256"] = "1" * 64
        report = score_inputs({"plan": self.plan, "model_label": RUNTIME["model_label"], "slots": rows})
        summary = public_score_projection(report, self.plan, private_aliases={})
        partial_ids = self.stage_ids[74:]
        root = {"schema": "math-gauge.root-G92-closed-semantic-adjudication/v1",
            "case_id": "MG-C003", "reviewer_kind": "ai", "human_review": "pending",
            "formal_comparison_eligible": False, "not_standard_A1": True,
            "not_standard_42_45": True, "semantic_counts": {"pass": 74, "partial": 18}, "total": 92,
            "strict_peer_sha256": "2" * 64, "root_accepted_changed_items": partial_ids[:8],
            "native_result_status": "ERROR", "original_owner_status": "ok",
            "strict_delivery_format_status": "format_error", "source_kernel_only_status": "passed",
            "kernel_report_sha256": "3" * 64, "forced_manifest_sha256": "4" * 64}
        self.documents = {"original_plan": self.plan, "original_report": report,
                          "original_summary": summary, "root_adjudication": root}
        self.sources = {name: self.root / (name + ".json") for name in self.documents}
        self.hashes = {}
        for name in self.documents:
            self.save(name)
        diagnostic = {"schema": "math-gauge.closed-chapter-diagnostic-summary/v1",
            "case_id": "MG-C003", "case_version": "0.1.1",
            "root_adjudication_sha256": self.hashes["root_adjudication"],
            "gemini_one_operational_extension": {
                "strict_semantic_completion": {"complete": 74, "not_complete": 18, "total": 92,
                                                "strict_reconciliation_sha256": "2" * 64},
                "actual_native_submissions": 1, "native_result_status": "ERROR",
                "native_error_class": "synthetic output/token limit fixture",
                "original_owner_status": "ok", "original_owner_gate_accepted": True,
                "delivery_format": {"status": "format_error", "original_version": "v0.1.1",
                                    "required_version": "0.1.1", "original_json_repaired": False},
                "source_kernel_only": {"status": "passed", "kernel_report_sha256": "3" * 64},
                "sealed_manifest_sha256": "4" * 64, "sealed_tree_sha256": "5" * 64,
                "selected_source_sha256": {"Main.lean": self.source_sha}},
            "per_obligation": [{"id": sid, "decision": "pass" if index < 74 else "partial",
                "declarations": [{"file": "Main.lean", "file_sha256": self.source_sha}]}
                for index, sid in enumerate(self.stage_ids)]}
        self.documents["diagnostic"] = diagnostic
        self.sources["diagnostic"] = self.root / "diagnostic.json"
        self.save("diagnostic")

    def save(self, name):
        self.sources[name].write_text(json.dumps(self.documents[name], ensure_ascii=False, indent=2) + "\n")
        self.hashes[name] = digest_bytes(self.sources[name].read_bytes())

    def score(self):
        return source_qualified_workspace_score(self.sources, expected_sha256=self.hashes,
                                                workspace_root=self.workspace)

    def test_exact_shared_aggregation_and_original_evidence_are_separate(self):
        before = {name: path.read_bytes() for name, path in self.sources.items()}
        result = self.score()
        expected = Fraction(1) - Fraction(75, 100) * Fraction(45, 100) * Fraction(1, 2) * Fraction(18, 92)
        self.assertEqual(result["metrics"]["overall"]["exact"], round(float(100 * expected), 10))
        self.assertEqual(result["metrics"]["strict_pass_rate"],
                         self.documents["original_summary"]["metrics"]["strict_pass_rate"])
        self.assertIsNone(result["metrics"]["strict_pass_rate"]["exact"])
        for metric in set(result["metrics"]) - {"lean-formalization", "core", "overall"}:
            self.assertEqual(result["metrics"][metric], self.documents["original_summary"]["metrics"][metric])
        self.assertEqual(result["profile"], self.documents["original_summary"]["profile"])
        self.assertEqual(result["coverage"]["slots_planned"], 42)
        self.assertEqual(result["coverage"]["slots_reviewed"], 41)
        math_coverage = result["mathematical_source_coverage"]
        self.assertEqual(math_coverage["effective_mathematical_slots_adjudicated"], 42)
        for field in ("fresh_A1_slots_added", "successful_native_deliveries_added", "formal_eligible_slots_added"):
            self.assertEqual(math_coverage[field], 0)
        self.assertEqual(result["mathematical_substitution"]["native_result_status"], "ERROR")
        self.assertEqual(result["mathematical_substitution"]["delivery_format"]["status"], "format_error")
        self.assertEqual(result["new_candidate_calls"], 0)
        self.assertFalse(result["formal_comparison_eligible"])
        self.assertNotIn("slot_evidence", result)
        self.assertEqual(before, {name: path.read_bytes() for name, path in self.sources.items()})
        serialized = json.dumps(result)
        self.assertNotIn(str(self.root), serialized)
        self.assertNotIn("case_index", serialized)

    def test_hash_and_selected_actual_source_changes_are_rejected(self):
        self.sources["diagnostic"].write_bytes(self.sources["diagnostic"].read_bytes() + b" ")
        with self.assertRaisesRegex(ValueError, "source hash changed"):
            self.score()
        self.save("diagnostic")
        (self.workspace / "Main.lean").write_text("-- Changed fixture source.\n")
        with self.assertRaisesRegex(ValueError, "source bytes changed"):
            self.score()

    def test_wrong_case_version_total_and_pass_inventory_are_rejected(self):
        for mutation in (lambda d: d.update(case_version="0.1.0"),
                         lambda d: d["gemini_one_operational_extension"]["strict_semantic_completion"].update(total=91),
                         lambda d: d["per_obligation"][0].update(id=d["per_obligation"][1]["id"]),
                         lambda d: d["per_obligation"][0].update(decision="partial")):
            original = copy.deepcopy(self.documents["diagnostic"])
            mutation(self.documents["diagnostic"])
            self.save("diagnostic")
            with self.assertRaises(ValueError):
                self.score()
            self.documents["diagnostic"] = original
            self.save("diagnostic")

    def test_original_coverage_and_profile_or_score_cannot_drift(self):
        for mutation in (lambda d: d["coverage"].update(slots_reviewed=42),
                         lambda d: d["profile"]["components"][0].update(weight=23),
                         lambda d: d["metrics"]["proofs"].update(exact=99)):
            original = copy.deepcopy(self.documents["original_summary"])
            mutation(self.documents["original_summary"])
            self.save("original_summary")
            with self.assertRaises(ValueError):
                self.score()
            self.documents["original_summary"] = original
            self.save("original_summary")

    def test_native_success_or_format_repair_is_not_inferred(self):
        for mutation in (lambda d: d["gemini_one_operational_extension"].update(native_result_status="SUCCESS"),
                         lambda d: d["gemini_one_operational_extension"]["delivery_format"].update(status="passed"),
                         lambda d: d["gemini_one_operational_extension"].update(original_owner_gate_accepted=False)):
            original = copy.deepcopy(self.documents["diagnostic"])
            mutation(self.documents["diagnostic"])
            self.save("diagnostic")
            with self.assertRaisesRegex(ValueError, "statuses"):
                self.score()
            self.documents["diagnostic"] = original
            self.save("diagnostic")

    def test_root_and_declaration_bindings_cannot_be_substituted(self):
        self.documents["diagnostic"]["root_adjudication_sha256"] = "0" * 64
        self.save("diagnostic")
        with self.assertRaisesRegex(ValueError, "root AI adjudication"):
            self.score()
        self.documents["diagnostic"]["root_adjudication_sha256"] = self.hashes["root_adjudication"]
        self.documents["diagnostic"]["per_obligation"][0]["declarations"][0]["file_sha256"] = "0" * 64
        self.save("diagnostic")
        with self.assertRaisesRegex(ValueError, "declaration source binding"):
            self.score()


if __name__ == "__main__":
    unittest.main()
