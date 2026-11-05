"""Regression checks for source-bound, operator-only focus indexes."""
from __future__ import annotations

import copy
import hashlib
import importlib.util
import json
import tempfile
import unittest
from collections import Counter
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "focus_catalog", ROOT / "scripts/catalog.py"
)
focus_catalog = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(focus_catalog)


class FocusCatalogTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.taxonomy = json.loads((ROOT / focus_catalog.TAXONOMY).read_text())

    def changed_taxonomy(self):
        return copy.deepcopy(self.taxonomy)

    def test_exact_paper_units_and_independent_review_statuses(self):
        catalog, _ = focus_catalog.build()
        entries = catalog["entries"]
        self.assertEqual(catalog["counts"]["papers"], len(entries))
        for membership in ("default", "reserve"):
            selected = [row for row in entries if row["membership"] == membership]
            self.assertEqual(catalog["counts"][membership + "_papers"], len(selected))
            self.assertEqual(catalog["counts"][membership + "_obligations"], sum(row["stage_count"] for row in selected))
        progressive = [row for row in entries if row["kind"] == "progressive"]
        self.assertEqual(catalog["scope"]["progressive_papers"], len(progressive))
        self.assertEqual(catalog["counts"]["progressive_stages"], sum(row["stage_count"] for row in progressive))
        written = [row for row in entries if row["kind"] == "written_proof"]
        if written:
            self.assertEqual(catalog["counts"]["proof_criteria"], sum(row["proof_criterion_count"] for row in written))
            self.assertTrue(all(row["stage_count"] == 0 for row in written))
        self.assertEqual(
            catalog["scope"]["chapter_obligations"], {"LCH02": 34, "MG-C003": 92, "LCH01": 8, "LCH02": 20, "HCH02": 40}
        )
        self.assertEqual(catalog["counts"]["source_human_approved"], 0)
        self.assertEqual(catalog["counts"]["model_calls_by_indexer"], 0)
        self.assertTrue(all(
            entry["sample_unit"] == ("one-complete-answer-review; parent-correlated"
                                      if entry["kind"] == "answer_review" else "one-full-paper")
            and entry["classification_review"]["human"] == "pending"
            and entry["source_review"]["human"] == "pending"
            for entry in catalog["entries"]
        ))

    def test_rejects_missing_or_repeated_paper(self):
        for duplicate in (False, True):
            with self.subTest(duplicate=duplicate):
                taxonomy = self.changed_taxonomy()
                if duplicate:
                    taxonomy["paper_assignments"][-1] = copy.deepcopy(
                        taxonomy["paper_assignments"][0]
                    )
                else:
                    taxonomy["paper_assignments"].pop()
                with self.assertRaisesRegex(ValueError, "every selected mathematical paper and answer review exactly once"):
                    focus_catalog.build(taxonomy_data=taxonomy)

    def test_current_membership_retains_original_source_identity(self):
        catalog, _ = focus_catalog.build()
        self.assertEqual(catalog["counts"]["reserve_papers"], 0)
        entries = {row["case_id"]: row for row in catalog["entries"]}
        for cid in ["MG-GR002", "MG-GR021", "MG-C003"]:
            row = entries[cid]
            self.assertEqual(row["membership"], "default")
            self.assertEqual(row["original_sha256"][row["paths"]["task"]],
                hashlib.sha256((ROOT / row["paths"]["task"]).read_bytes()).hexdigest())

    def test_rejects_duplicate_primary_or_focus_tag(self):
        for field, value, message in (
            ("role", "primary", "exactly one leading primary"),
            ("focus_id", "F09", "duplicate focus tag"),
        ):
            with self.subTest(field=field):
                taxonomy = self.changed_taxonomy()
                if field == "focus_id":
                    value = taxonomy["paper_assignments"][0]["focus"][0]["focus_id"]
                taxonomy["paper_assignments"][0]["focus"][1][field] = value
                with self.assertRaisesRegex(ValueError, message):
                    focus_catalog.build(taxonomy_data=taxonomy)

    def test_rejects_tag_without_evidence(self):
        taxonomy = self.changed_taxonomy()
        taxonomy["paper_assignments"][0]["focus"][0]["evidence"] = []
        with self.assertRaisesRegex(ValueError, "tag lacks evidence"):
            focus_catalog.build(taxonomy_data=taxonomy)

    def test_rejects_nonexistent_stage_or_obligation(self):
        for cid, invalid in (("MG-GR002", "S99"), ("MG-C003", "CH03-P99-99")):
            with self.subTest(cid=cid):
                taxonomy = self.changed_taxonomy()
                assignment = next(item for item in taxonomy["paper_assignments"]
                                  if item["case_id"] == cid)
                assignment["focus"][0]["evidence"][0]["stage_id"] = invalid
                with self.assertRaisesRegex(ValueError, "invalid evidence ID"):
                    focus_catalog.build(taxonomy_data=taxonomy)

    def test_rejects_stale_source_bytes_and_suite_identity(self):
        for suite_change in (False, True):
            with self.subTest(suite_change=suite_change):
                taxonomy = self.changed_taxonomy()
                if suite_change:
                    taxonomy["source_suites"][0]["suite_sha256"] = "0" * 64
                else:
                    bindings = taxonomy["paper_assignments"][0]["source_bindings"]
                    bindings[next(iter(bindings))] = "0" * 64
                with self.assertRaisesRegex(ValueError, "drift"):
                    focus_catalog.build(taxonomy_data=taxonomy)

    def test_rejects_stale_task_locator(self):
        taxonomy = self.changed_taxonomy()
        assignment = next(item for item in taxonomy["paper_assignments"]
                          if item["case_id"] == "MG-GR002")
        assignment["focus"][0]["evidence"][0]["task_locator"]["line"] += 1
        with self.assertRaisesRegex(ValueError, "task heading locator drift"):
            focus_catalog.build(taxonomy_data=taxonomy)

    def test_rejects_invented_lean_delivery_or_human_approval(self):
        for human_change in (False, True):
            with self.subTest(human_change=human_change):
                taxonomy = self.changed_taxonomy()
                assignment = next(item for item in taxonomy["paper_assignments"]
                                  if item["case_id"] == "MG-GR005")
                if human_change:
                    assignment["classification_review"]["human"] = "approved"
                    message = "human review must stay pending"
                else:
                    assignment["focus"][0]["focus_id"] = "F09"
                    message = "does not require candidate Lean"
                with self.assertRaisesRegex(ValueError, message):
                    focus_catalog.build(taxonomy_data=taxonomy)

    def test_check_is_read_only_and_has_no_legacy_dependency(self):
        paths = [ROOT / name for name in (focus_catalog.TAXONOMY, *focus_catalog.OUTPUTS)]
        before = {path: (path.read_bytes(), path.stat().st_mtime_ns) for path in paths}
        with patch.object(Path, "write_text", side_effect=AssertionError("write in check")):
            with patch.object(Path, "write_bytes", side_effect=AssertionError("write in check")):
                summary = focus_catalog.refresh(check=True)
        self.assertEqual(summary["mode"], "check")
        self.assertEqual(before, {
            path: (path.read_bytes(), path.stat().st_mtime_ns) for path in paths
        })
        catalog, _ = focus_catalog.build()
        self.assertNotIn("protected_legacy_files", self.taxonomy)
        self.assertNotIn("protected_legacy_files", catalog)
        self.assertEqual([row["root"] for row in catalog["suites"]], ["cases"])
        self.assertEqual([row["membership"] for row in catalog["suites"]], ["default"])
        self.assertEqual([row["paper_count"] for row in catalog["suites"]],
                         [catalog["counts"][key + "_papers"] for key in ("default",)])

    def test_refresh_writes_only_current_derived_outputs(self):
        catalog, document = focus_catalog.build()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "cases").mkdir()
            with patch.object(focus_catalog, "build", return_value=(catalog, document)):
                focus_catalog.refresh(root)
            self.assertEqual(
                {str(path.relative_to(root)) for path in root.rglob("*") if path.is_file()},
                set(focus_catalog.OUTPUTS),
            )

    def test_exact_current_categories_and_run_catalog_interface(self):
        catalog, _ = focus_catalog.build()
        self.assertEqual(catalog["schema"], "math-gauge.case-catalog/v1")
        self.assertEqual(catalog["snapshot_status"], "final-catalog-snapshot")
        expected = Counter(Path(manifest).parent.parent.name
                           for _, name in focus_catalog.SUITES
                           for manifest in focus_catalog.Suite.load(ROOT / name).metadata["cases"])
        self.assertEqual([(item["id"], item["count"]) for item in catalog["categories"]],
                         [(category, expected[category]) for category, _ in focus_catalog.CATEGORIES])
        ids = [cid for item in catalog["categories"] for cid in item["case_ids"]]
        self.assertEqual(len(ids), len(set(ids)))
        self.assertEqual(set(ids), {item["case_id"] for item in catalog["entries"]})
        default = set(catalog["suites"][0]["cases"])
        self.assertEqual(default, set(ids))
        for item in catalog["entries"]:
            self.assertEqual(item["membership"], "default" if item["case_id"] in default else "reserve")
            canonical = f"{item['category']}/{item['case_id']}/case.json"
            allowed = {f"cases/{canonical}"}
            if item["membership"] == "reserve":
                allowed.add(f"cases/reserve/{canonical}")
            self.assertIn(item["paths"]["case"], allowed)
            self.assertIn(item["task_kind"], {"written", "audit", "repair", "generate", "answer_review"})

    def test_check_rejects_stale_derived_text(self):
        catalog, document = focus_catalog.build()
        with patch.object(focus_catalog, "build", return_value=(catalog, document + "stale\n")):
            with self.assertRaisesRegex(ValueError, "Stale focus output"):
                focus_catalog.refresh(check=True)

    def test_candidate_projection_has_no_focus_material(self):
        catalog, _ = focus_catalog.build()
        by_id = {entry["case_id"]: entry for entry in catalog["entries"]}
        for relative in focus_catalog.SUITE_ROOTS:
            suite = focus_catalog.Suite.load(ROOT / relative)
            for cid, case in suite.cases.items():
                request = suite.request(case)
                self.assertEqual(request["task"], (suite.root / case["task"]).read_text())
                self.assertEqual([item["name"] for item in request["files"]],
                                 [item["target"] for item in case["solver_files"]])
                self.assertFalse({item["name"] for item in request["files"]}
                                 & {Path(name).name for name in focus_catalog.FOCUS_FILES})
                encoded = json.dumps(request, sort_keys=True, ensure_ascii=False,
                                     separators=(",", ":")).encode()
                self.assertEqual(hashlib.sha256(encoded).hexdigest(),
                                 by_id[cid]["candidate_projection_sha256"])


if __name__ == "__main__":
    unittest.main()
