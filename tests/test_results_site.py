"""Own portable display contract tests: frozen scores, safe projection and links."""

import copy
from html.parser import HTMLParser
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parents[1]
SOURCE_ROOT = ROOT
SPEC = importlib.util.spec_from_file_location(
    "math_gauge_results_site", ROOT / "scripts" / "render_results_site.py"
)
site = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(site)


class Links(HTMLParser):
    def __init__(self):
        super().__init__()
        self.ids, self.links, self.tags = set(), [], []

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        self.tags.append(tag)
        if "id" in attrs:
            self.ids.add(attrs["id"])
        for key in ("href", "src", "action"):
            if key in attrs:
                self.links.append((tag, attrs[key]))


class ResultsSiteTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = site.load_data(SOURCE_ROOT, use_workspace_source=False)

    def test_frozen_scores_nulls_and_full_denominators(self):
        terra, gemini = self.data["models"]
        self.assertEqual(terra["public"]["metrics"]["overall"]["exact"], 86.3328804348)
        self.assertEqual(terra["combined"]["metrics"]["overall"]["exact"], 89.0475543478)
        expected = (("public", 63.3707589285, 80.2457589286, 41, 42, 26, 18),
                    ("combined", 62.0291964285, 75.5291964286, 44, 45, 29, 21))
        for scope, lower, upper, reviewed, planned, tasks, families in expected:
            result = gemini[scope]
            self.assertIsNone(result["metrics"]["overall"]["exact"])
            self.assertEqual((result["metrics"]["overall"]["lower"],
                              result["metrics"]["overall"]["upper"]), (lower, upper))
            self.assertEqual((result["coverage"]["slots_reviewed"],
                              result["coverage"]["slots_planned"]), (reviewed, planned))
            self.assertEqual((result["coverage"]["papers_planned"],
                              result["coverage"]["parent_families"]), (tasks, families))
            self.assertEqual(terra[scope]["coverage"]["slots_reviewed"], planned)
        self.assertFalse(self.data["formal_comparison_eligible"])
        self.assertFalse(self.data["backend_identity_independently_verified"])
        for model in self.data["models"]:
            for scope in ("public", "combined"):
                self.assertEqual(model[scope]["human_review"], "pending")
                self.assertIs(model[scope]["formal_comparison_eligible"], False)

    def test_weights_and_family_counts_are_copied_from_frozen_profiles(self):
        public = self.data["models"][0]["public"]["profile"]
        combined = self.data["models"][0]["combined"]["profile"]
        self.assertEqual({row["id"]: row["weight"] for row in public["components"]},
                         {"proofs": 22.5, "lean-audit": 22.5,
                          "lean-formalization": 45, "answer-review": 10})
        self.assertEqual({row["id"]: row["weight"] for row in combined["components"]},
                         {"proofs": 22.5, "lean-audit": 18, "lean-formalization": 36,
                          "exploration": 13.5, "answer-review": 10})
        self.assertEqual(public["overall_weights"],
                         {"core": 75, "repeat": 5, "neutral": 10, "stance": 10})
        self.assertEqual(site.component(public, "lean-formalization")["family_count"], 2)
        for model in self.data["models"]:
            for scope, filename in (("public", "result.json"),
                                    ("combined", "combined-aggregate.json")):
                original = json.loads((SOURCE_ROOT / "docs/results" /
                                       (model["id"] + "-v0.6.0") / filename).read_text())
                for key, metric in model[scope]["metrics"].items():
                    for field in ("exact", "lower", "upper", "complete"):
                        self.assertEqual(metric[field], original["metrics"][key][field])

    def test_public_panel_keeps_whole_answer_separate_from_focus(self):
        terra, gemini = self.data["models"]
        self.assertEqual([row["public_case_id"] for row in gemini["written_panel"]],
                         list(site.PUBLIC_PANEL))
        self.assertEqual(gemini["public"]["metrics"]["neutral"]["exact"], 100)
        self.assertEqual(gemini["written_panel"][3]["whole_answer_completion"],
                         [.75, 1, .75, .75, .75])
        self.assertTrue(all(row["whole_answer_completion"] == [1] * 5
                            for row in terra["written_panel"]))

    def test_projection_drops_private_details_and_raw_execution_extras(self):
        marker = "PRIVATE-SENTINEL-DO-NOT-EXPORT"
        with tempfile.TemporaryDirectory() as tmp:
            source_root = Path(tmp)
            for source in self.data["sources"]:
                relative = source["path"]
                original = json.loads((SOURCE_ROOT / relative).read_text())
                original.update(private_records=[{"private_id": marker, "answer": marker}],
                                raw_execution=marker, full_plan=marker,
                                task=marker, reference=marker, rubric=marker)
                original["coverage"]["private_name"] = marker
                original["profile"]["components"][0]["private_name"] = marker
                original["metrics"]["overall"]["raw_output"] = marker
                original["metrics"]["private_metric"] = marker
                path = source_root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(json.dumps(original))
            projected = site.load_data(source_root, use_workspace_source=False)
            self.assertNotIn(marker, json.dumps(projected))
            self.assertNotIn(marker, site.render_html(projected))
            for model in projected["models"]:
                for scope in ("public", "combined"):
                    self.assertNotIn("slot_evidence", model[scope])
                    self.assertNotIn("private_records", model[scope])
                    self.assertEqual(set(model[scope]["metrics"]["overall"]),
                                     {"exact", "lower", "upper", "complete", "coverage"})

    def test_requires_explicit_public_schema_and_finite_metrics(self):
        original = json.loads((SOURCE_ROOT /
                               "docs/results/terra-v0.6.0/result.json").read_text())
        unsafe = copy.deepcopy(original)
        unsafe["schema"] = "math-gauge.private-full-score/v1"
        with self.assertRaisesRegex(ValueError, "explicit public"):
            site.aggregate_projection(unsafe, "public")
        unsafe = copy.deepcopy(original)
        unsafe["metrics"]["overall"]["exact"] = float("nan")
        with self.assertRaisesRegex(ValueError, "finite"):
            site.aggregate_projection(unsafe, "public")
        unsafe = copy.deepcopy(original)
        unsafe["evidence_status"]["human_approval"] = "approved"
        with self.assertRaisesRegex(ValueError, "human-pending"):
            site.aggregate_projection(unsafe, "public")

    def test_display_copies_exact_score_without_rescoring(self):
        data = copy.deepcopy(self.data)
        metric = data["models"][0]["public"]["metrics"]["overall"]
        metric.update(exact=12.34567, lower=12.34567, upper=12.34567)
        rendered = site.render_html(data)
        self.assertIn('12.35</strong>', rendered)
        self.assertIn('class="unresolved">未决</strong>', rendered)
        self.assertIn("[63.37, 80.25]", rendered)
        self.assertIn("[62.03, 75.53]", rendered)
        self.assertIn("原标准答卷结果", rendered)
        self.assertIn("不是统计置信区间", rendered)
        self.assertIn("原 92 项首答为 ERROR", rendered)

    def test_deterministic_bundle_has_only_portable_resolvable_local_links(self):
        with tempfile.TemporaryDirectory() as tmp:
            first, second = Path(tmp) / "nested path" / "results", Path(tmp) / "elsewhere"
            site.build_site(SOURCE_ROOT, first, use_workspace_source=False)
            site.build_site(SOURCE_ROOT, second, use_workspace_source=False)
            self.assertEqual({path.name for path in first.iterdir()}, {"index.html", "data.json"})
            for filename in ("index.html", "data.json"):
                self.assertEqual((first / filename).read_bytes(), (second / filename).read_bytes())
            rendered = (first / "index.html").read_text()
            self.assertNotIn(str(SOURCE_ROOT), rendered)
            self.assertNotIn("@import", rendered)
            self.assertNotIn("url(", rendered)
            parser = Links()
            parser.feed(rendered)
            self.assertNotIn("script", parser.tags)
            self.assertNotIn("iframe", parser.tags)
            for tag, target in parser.links:
                url = urlsplit(target)
                if url.scheme:
                    self.assertEqual(tag, "a")
                    self.assertEqual(url.scheme, "https")
                    continue
                self.assertFalse(url.netloc)
                self.assertFalse(url.path.startswith("/"))
                if url.path:
                    self.assertEqual(url.path, "data.json")
                    self.assertTrue((first / unquote(url.path)).is_file())
                if url.fragment:
                    self.assertIn(unquote(url.fragment), parser.ids)

    def test_cli_supports_an_arbitrary_destination_and_working_directory(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "portable output"
            result = subprocess.run(
                [sys.executable, str(ROOT / "scripts/render_results_site.py"),
                 "--source-root", str(SOURCE_ROOT), "--out-dir", str(out), "--original-only"],
                cwd=tmp, check=False, capture_output=True, text=True,
                env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(json.loads((out / "data.json").read_text()), self.data)


class WorkspaceResultsSiteTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = site.load_data(SOURCE_ROOT)
        cls.original = site.load_data(SOURCE_ROOT, use_workspace_source=False)

    def copy_sources(self, root):
        for source in self.data["sources"]:
            target = root / source["path"]
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes((SOURCE_ROOT / source["path"]).read_bytes())

    def qualified_path(self, root, filename="result.json"):
        return root / "docs/results/gemini-v0.6.0-extension" / filename

    def test_current_points_preserve_original_null_and_execution_status(self):
        self.assertEqual(self.data["schema"], "math-gauge.portable-results/v2")
        self.assertEqual(self.data["view"], "workspace-mathematics")
        terra, gemini = self.data["models"]
        self.assertEqual(terra, self.original["models"][0])
        self.assertEqual(gemini["public"]["metrics"]["overall"]["exact"], 76.9441284938)
        self.assertEqual(gemini["combined"]["metrics"]["overall"]["exact"], 72.8878920807)
        for scope, reviewed, planned in (("public", 41, 42), ("combined", 44, 45)):
            result = gemini[scope]
            self.assertEqual(result["metrics"]["lean-formalization"]["exact"], 72.7173913043)
            self.assertEqual(result["coverage"]["slots_reviewed"], reviewed)
            self.assertEqual(result["coverage"]["slots_planned"], planned)
            prior = result["original_score"]
            baseline = self.original["models"][1][scope]
            self.assertEqual(prior["metrics"], baseline["metrics"])
            self.assertEqual(prior["coverage"], baseline["coverage"])
            self.assertIsNone(prior["metrics"]["overall"]["exact"])
            self.assertIs(prior["standard_evidence_rewritten"], False)
            self.assertEqual(result["mathematical_source_coverage"]["effective_mathematical_slots_adjudicated"], planned)
            for key in ("fresh_A1_slots_added", "successful_native_deliveries_added", "formal_eligible_slots_added"):
                self.assertEqual(result["mathematical_source_coverage"][key], 0)
            status = result["mathematical_substitution"]
            self.assertEqual(status["native_result_status"], "ERROR")
            self.assertEqual(status["source_kernel_only_status"], "passed")
            self.assertEqual(status["delivery_format"]["status"], "format_error")
            self.assertIs(status["original_owner_gate_accepted"], True)
            self.assertIs(status["fresh_A1"], False)
            self.assertIs(status["equal_time_comparison"], False)
            self.assertIs(result["formal_comparison_eligible"], False)
            self.assertEqual(result["human_review"], "pending")
            self.assertEqual(result["candidate_call_accounting"],
                             {"scoring_recompute": 0, "selected_extension_original_submissions": 1,
                              "further_submissions_by_this_view": 0})
            self.assertEqual(len(result["scoring_implementation_sha256"]), 64)
            for key in set(baseline["metrics"]) - set(site.WORKSPACE_METRICS):
                self.assertEqual(result["metrics"][key], baseline["metrics"][key])

    def test_missing_snapshot_fails_instead_of_silently_using_original_scores(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.copy_sources(root)
            self.qualified_path(root).unlink()
            with self.assertRaises(FileNotFoundError):
                site.load_data(root)
            self.assertEqual(site.load_data(root, use_workspace_source=False)["view"],
                             "original-standard")

    def test_mismatched_original_hash_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.copy_sources(root)
            path = self.qualified_path(root)
            snapshot = json.loads(path.read_text())
            snapshot["source_bindings"]["original_summary_sha256"] = "0" * 64
            path.write_text(json.dumps(snapshot))
            with self.assertRaisesRegex(ValueError, "original summary hash"):
                site.load_data(root)

    def test_unrelated_metric_profile_coverage_and_original_rewrites_are_rejected(self):
        for field in ("unrelated", "profile", "coverage", "original", "native"):
            with self.subTest(field=field), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self.copy_sources(root)
                path = self.qualified_path(root)
                snapshot = json.loads(path.read_text())
                if field == "unrelated":
                    snapshot["metrics"]["proofs"]["exact"] = 0
                elif field == "profile":
                    snapshot["profile"]["components"][0]["weight"] = 25
                elif field == "coverage":
                    snapshot["coverage"]["slots_reviewed"] = 42
                elif field == "original":
                    snapshot["original_score"]["standard_evidence_rewritten"] = True
                else:
                    snapshot["mathematical_substitution"]["native_result_status"] = "SUCCESS"
                path.write_text(json.dumps(snapshot))
                with self.assertRaises(ValueError):
                    site.load_data(root)

    def test_qualified_projection_discards_private_extras_local_paths_and_raw_output(self):
        marker = "PRIVATE-WORKSPACE-SENTINEL-DO-NOT-EXPORT"
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.copy_sources(root)
            for filename in ("result.json", "combined-aggregate.json"):
                path = self.qualified_path(root, filename)
                snapshot = json.loads(path.read_text())
                snapshot.update(private_records=[{"private_id": marker, "answer": marker}],
                                full_plan=marker, original_answer=marker,
                                reference=marker, rubric=marker, local_path="/private/" + marker)
                snapshot["mathematical_substitution"]["raw_execution"] = marker
                snapshot["mathematical_substitution"]["selected_source_sha256"] = {marker: marker}
                snapshot["source_bindings"]["private_id"] = marker
                snapshot["original_score"]["raw_answer"] = marker
                snapshot["metrics"]["core"]["raw_output"] = marker
                path.write_text(json.dumps(snapshot))
            projected = site.load_data(root)
            self.assertNotIn(marker, json.dumps(projected))
            self.assertNotIn(marker, site.render_html(projected))
            self.assertEqual(len(projected["sources"]), 6)

    def test_qualified_metrics_are_copied_without_any_scoring_calculation(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.copy_sources(root)
            expected = {"lean-formalization": 1.23, "core": 4.56, "overall": 7.89}
            for filename in ("result.json", "combined-aggregate.json"):
                path = self.qualified_path(root, filename)
                snapshot = json.loads(path.read_text())
                for key, value in expected.items():
                    snapshot["metrics"][key].update(exact=value, lower=value, upper=value)
                path.write_text(json.dumps(snapshot))
            projected = site.load_data(root)
            for scope in ("public", "combined"):
                for key, value in expected.items():
                    self.assertEqual(projected["models"][1][scope]["metrics"][key]["exact"], value)

    def test_current_bundle_is_deterministic_portable_and_names_both_sources(self):
        with tempfile.TemporaryDirectory() as tmp:
            first, second = Path(tmp) / "deep path" / "results", Path(tmp) / "elsewhere"
            site.build_site(SOURCE_ROOT, first)
            site.build_site(SOURCE_ROOT, second)
            for filename in ("index.html", "data.json"):
                self.assertEqual((first / filename).read_bytes(), (second / filename).read_bytes())
            rendered = (first / "index.html").read_text()
            self.assertIn("当前计分结果", rendered)
            self.assertIn("76.94</strong>", rendered)
            self.assertIn("72.89</strong>", rendered)
            self.assertIn("另接纳 1 份工程数学审核", rendered)
            self.assertIn("原答审核 41 / 42", rendered)
            self.assertIn("原答审核 44 / 45", rendered)
            self.assertIn("Gemini 原标准答卷分（保留）", rendered)
            self.assertIn("180 分钟", rendered)
            self.assertIn("原答汇总", rendered)
            self.assertIn("工程数学计分", rendered)
            self.assertNotIn("formal_comparison_eligible", rendered)
            self.assertNotIn(str(SOURCE_ROOT), rendered)
            parser = Links()
            parser.feed(rendered)
            self.assertNotIn("script", parser.tags)
            for tag, target in parser.links:
                url = urlsplit(target)
                if url.scheme:
                    self.assertEqual((tag, url.scheme), ("a", "https"))
                elif url.path:
                    self.assertEqual(url.path, "data.json")
                    self.assertTrue((first / url.path).is_file())
                if url.fragment and not url.scheme:
                    self.assertIn(unquote(url.fragment), parser.ids)

    def test_default_cli_uses_the_source_qualified_view(self):
        with tempfile.TemporaryDirectory() as tmp:
            result = subprocess.run(
                [sys.executable, str(ROOT / "scripts/render_results_site.py"),
                 "--source-root", str(SOURCE_ROOT), "--out-dir", str(Path(tmp) / "site")],
                cwd=tmp, check=False, capture_output=True, text=True,
                env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(json.loads((Path(tmp) / "site/data.json").read_text()), self.data)


if __name__ == "__main__":
    unittest.main()
