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
        cls.data = site.load_data(SOURCE_ROOT, use_alignment_source=False)
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
                site.load_data(root, use_alignment_source=False)
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
                site.load_data(root, use_alignment_source=False)

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
                    site.load_data(root, use_alignment_source=False)

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
            projected = site.load_data(root, use_alignment_source=False)
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
            projected = site.load_data(root, use_alignment_source=False)
            for scope in ("public", "combined"):
                for key, value in expected.items():
                    self.assertEqual(projected["models"][1][scope]["metrics"][key]["exact"], value)

    def test_current_bundle_is_deterministic_portable_and_names_both_sources(self):
        with tempfile.TemporaryDirectory() as tmp:
            first, second = Path(tmp) / "deep path" / "results", Path(tmp) / "elsewhere"
            site.build_site(SOURCE_ROOT, first, use_alignment_source=False)
            site.build_site(SOURCE_ROOT, second, use_alignment_source=False)
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

    def test_workspace_only_cli_uses_the_source_qualified_view(self):
        with tempfile.TemporaryDirectory() as tmp:
            result = subprocess.run(
                [sys.executable, str(ROOT / "scripts/render_results_site.py"),
                 "--source-root", str(SOURCE_ROOT), "--out-dir", str(Path(tmp) / "site"), "--workspace-only"],
                cwd=tmp, check=False, capture_output=True, text=True,
                env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(json.loads((Path(tmp) / "site/data.json").read_text()), self.data)


class AlignmentResultsSiteTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = site.load_data(SOURCE_ROOT, use_engineering_source=False)
        cls.baseline = site.load_data(SOURCE_ROOT, use_alignment_source=False)

    def copy_sources(self, root):
        paths = {row["path"] for row in self.data["sources"]}
        paths.add("protocol/lean-alignment/scoring-v0.1.0.json")
        paths.update(f"docs/results/alignment-v0.1.0/{model}-review.json"
                     for model, _ in site.MODELS)
        for relative in paths:
            target = root / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes((SOURCE_ROOT / relative).read_bytes())

    def test_new_scores_keep_original_capability_and_three_rounds_one_case(self):
        self.assertEqual(self.data["schema"], "math-gauge.portable-results/v3")
        self.assertEqual(self.data["view"], "alignment-selfcheck")
        expected = ((82.6342415785, 85.3489154916, 26.027222875),
                    (71.9441284938, 67.8878920807, 0))
        for model, baseline, (public, combined, lean) in zip(
                self.data["models"], self.baseline["models"], expected):
            for scope, total in (("public", public), ("combined", combined)):
                current, old = model[scope], baseline[scope]
                self.assertEqual(current["metrics"]["overall"]["exact"], total)
                self.assertEqual(current["metrics"]["lean_alignment_selfcheck"]["exact"], lean)
                self.assertEqual(current["alignment_policy"]["lean_overall_weight_percent"], 5)
                self.assertEqual(current["coverage"], old["coverage"])
                self.assertEqual(current["prior_alignment_score"]["metrics"], old["metrics"])
                for key in set(old["metrics"]) - {"neutral", "overall"}:
                    self.assertEqual(current["metrics"][key], old["metrics"][key])
                self.assertEqual(current["metrics"]["neutral_written"], old["metrics"]["neutral"])
                self.assertEqual(len(current["alignment_selfcheck"]["rounds"]), 3)
                self.assertFalse(current["formal_comparison_eligible"])
        terra, gemini = self.data["models"]
        self.assertEqual([r["score"]["exact"] for r in terra["public"]["alignment_selfcheck"]["rounds"]],
                         [0.972972973, 22, 55.1086956522])
        self.assertEqual(gemini["public"]["alignment_selfcheck"]["major_false_complete_events"]["count"], 3)
        self.assertEqual(terra["public"]["alignment_selfcheck"]["rounds"][2]["restored"], 13)
        self.assertEqual(terra["public"]["alignment_selfcheck"]["rounds"][2]["first_new"], 20)

    def test_missing_alignment_snapshot_does_not_silently_fall_back(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.copy_sources(root)
            (root / "docs/results/alignment-v0.1.0/terra-public.json").unlink()
            with self.assertRaises(FileNotFoundError):
                site.load_data(root, use_engineering_source=False)
            self.assertEqual(site.load_data(root, use_alignment_source=False)["view"], "workspace-mathematics")

    def test_extra_time_asterisk_is_bound_to_c003_and_affected_scores(self):
        terra, gemini = self.data["models"]
        self.assertEqual(terra["chapter_capability_source"],
                         {"public_case_id": "MG-C003", "complete": 18, "total": 92,
                          "extra_time_source": False})
        self.assertEqual(gemini["chapter_capability_source"],
                         {"public_case_id": "MG-C003", "complete": 74, "total": 92,
                          "extra_time_source": True})
        rendered = site.render_html(self.data)
        self.assertIn('74/92<sup><a href="#extension-note"', rendered)
        self.assertIn('id="extension-note"', rendered)
        self.assertEqual(rendered.count('href="#extension-note"'), 4)
        self.assertIn("额外一次90分钟续作", rendered)
        self.assertIn("约46分钟后收卷", rendered)
        self.assertIn("后续三轮每轮180分钟", rendered)
        original = site.render_html(site.load_data(SOURCE_ROOT, use_workspace_source=False))
        self.assertNotIn('href="#extension-note"', original)
        self.assertIn("未决（原ERROR）", original)

    def test_alignment_hash_weights_and_unrelated_changes_are_rejected(self):
        for mutation in ("binding", "weight", "capability", "coverage", "review-file"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self.copy_sources(root)
                path = root / "docs/results/alignment-v0.1.0/terra-public.json"
                doc = json.loads(path.read_text())
                if mutation == "binding":
                    doc["source_bindings"]["original_summary_sha256"] = "0" * 64
                elif mutation == "weight":
                    doc["policy"]["neutral_group_weights"]["lean_alignment"] = 4
                elif mutation == "capability":
                    doc["metrics"]["core"]["exact"] = 0
                elif mutation == "coverage":
                    doc["coverage"]["slots_planned"] = 45
                else:
                    (root / "docs/results/alignment-v0.1.0/terra-review.json").write_text("{}\n")
                path.write_text(json.dumps(doc))
                with self.assertRaises(ValueError):
                    site.load_data(root, use_engineering_source=False)

    def test_new_projection_discards_private_extras_and_raw_answers(self):
        marker = "PRIVATE-ALIGNMENT-SENTINEL-DO-NOT-EXPORT"
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.copy_sources(root)
            for model, _ in site.MODELS:
                for scope in ("public", "combined"):
                    path = root / f"docs/results/alignment-v0.1.0/{model}-{scope}.json"
                    doc = json.loads(path.read_text())
                    doc.update(full_plan=marker, raw_answer=marker, private_records=[marker],
                               local_path="/private/" + marker)
                    doc["alignment_selfcheck"]["rounds"][0]["original_response"] = marker
                    doc["metrics"]["lean_alignment_selfcheck"]["private_note"] = marker
                    path.write_text(json.dumps(doc))
            data = site.load_data(root, use_engineering_source=False)
            self.assertNotIn(marker, json.dumps(data))
            self.assertNotIn(marker, site.render_html(data))
            self.assertNotIn("CH03-D01", json.dumps(data))
            self.assertNotIn(str(SOURCE_ROOT), json.dumps(data))

    def test_mixed_source_cli_and_portable_bundle_use_alignment_view(self):
        with tempfile.TemporaryDirectory() as tmp:
            first, second = Path(tmp) / "deep path" / "results", Path(tmp) / "elsewhere"
            result = subprocess.run(
                [sys.executable, str(ROOT / "scripts/render_results_site.py"),
                 "--source-root", str(SOURCE_ROOT), "--out-dir", str(first), "--mixed-source"],
                cwd=tmp, check=False, capture_output=True, text=True,
                env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"})
            self.assertEqual(result.returncode, 0, result.stderr)
            site.build_site(SOURCE_ROOT, second, use_engineering_source=False)
            for filename in ("index.html", "data.json"):
                self.assertEqual((first / filename).read_bytes(), (second / filename).read_bytes())
            self.assertEqual(json.loads((first / "data.json").read_text()), self.data)
            rendered = (first / "index.html").read_text()
            for needle in ("82.63</strong>", "85.35</strong>", "71.94</strong>", "67.89</strong>",
                           "Lean 对齐自查 · 占总分 5%", "三轮明细", "加入 Lean 自查前的成绩（保留）"):
                self.assertIn(needle, rendered)
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


class EngineeringResultsSiteTests(unittest.TestCase):
    version = "0.2.0"
    rebalanced = False
    schema = "math-gauge.portable-results/v4"
    expected = ((93.4861010467, 94.1464271337, 37.6296296296),
                (70.9441284938, 66.8878920807, -20))

    @classmethod
    def setUpClass(cls):
        cls.data = site.load_data(SOURCE_ROOT, use_rebalanced_source=cls.rebalanced)

    def copy_sources(self, root):
        paths = {row["path"] for row in self.data["sources"]}
        paths.add(f"protocol/lean-alignment/engineering-scoring-v{self.version}.json")
        paths.update(f"docs/results/engineering-v{self.version}/{model}-review.json"
                     for model, _ in site.MODELS)
        for relative in paths:
            target = root / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes((SOURCE_ROOT / relative).read_bytes())

    def test_unified_engineering_counts_and_penalized_scores(self):
        self.assertEqual(self.data["schema"], self.schema)
        self.assertEqual(self.data["view"], "engineering-alignment")
        for model, (public, combined, lean) in zip(self.data["models"], self.expected):
            for scope, total in (("public", public), ("combined", combined)):
                result = model[scope]
                self.assertEqual(result["metrics"]["overall"]["exact"], total)
                self.assertEqual(result["metrics"]["lean_alignment_selfcheck"]["exact"], lean)
                self.assertFalse(result["formal_comparison_eligible"])
                rows = {r["case_id"]: r for r in result["lean_formalization_breakdown"]["cases"]}
                self.assertEqual((rows["MG-C003"]["complete_count"], rows["MG-C003"]["total"]), (74, 92))
        terra, gemini = self.data["models"]
        self.assertEqual([r["complete"] for r in terra["public"]["alignment_selfcheck"]["rounds"]], [74, 84, 84])
        self.assertEqual([r["complete"] for r in gemini["public"]["alignment_selfcheck"]["rounds"]], [74, 74, 74])
        self.assertEqual([r["penalty_points"] for r in gemini["public"]["alignment_selfcheck"]["rounds"]], [20, 20, 20])

    def test_clean_page_explains_correct_pass_counts_and_family_average(self):
        rendered = site.render_html(self.data)
        totals = tuple(f"{value:.2f}</strong>" for public, combined, _ in self.expected for value in (public, combined))
        for text in totals + ("正确且完整通过", "74/92", "84/92", "65.00", "80.43", "两个家族等权平均",
                     "首答总时长上限180分钟", "每轮额外扣20分", "部分等价测试继承"):
            self.assertIn(text, rendered)
        for text in ("加时", "extra opportunity", "ERROR", "fresh A1", "正式模型比较资格", "原答审核"):
            self.assertNotIn(text, rendered)
        self.assertNotIn('href="#extension-note"', rendered)

    def test_current_bound_sources_fail_closed(self):
        for mutation in ("missing", "wrong-policy", "wrong-review", "wrong-case-count", "negative-overflow"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self.copy_sources(root)
                path = root / f"docs/results/engineering-v{self.version}/gemini-public.json"
                value = json.loads(path.read_text())
                if mutation == "missing":
                    path.unlink()
                elif mutation == "wrong-policy":
                    value["policy"]["version"] = "0.1.0"
                elif mutation == "wrong-review":
                    value["source_bindings"]["alignment_review_sha256"] = "0" * 64
                elif mutation == "wrong-case-count":
                    value["lean_formalization_breakdown"]["cases"][0]["complete_count"] = 999
                else:
                    value["metrics"]["lean_alignment_selfcheck"].update(exact=-21, lower=-21, upper=-21)
                if mutation != "missing":
                    path.write_text(json.dumps(value))
                with self.assertRaises((ValueError, FileNotFoundError)):
                    site.load_data(root, use_rebalanced_source=self.rebalanced)

    def test_current_projection_omits_private_and_raw_details(self):
        marker = "PRIVATE-ENGINEERING-SENTINEL"
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.copy_sources(root)
            for model, _ in site.MODELS:
                for scope in ("public", "combined"):
                    path = root / f"docs/results/engineering-v{self.version}/{model}-{scope}.json"
                    value = json.loads(path.read_text())
                    value.update(raw_answer=marker, private_records=[marker], full_plan=marker,
                                 local_path="/private/" + marker)
                    value["alignment_selfcheck"]["rounds"][0]["raw_text"] = marker
                    path.write_text(json.dumps(value))
            data = site.load_data(root, use_rebalanced_source=self.rebalanced)
            self.assertNotIn(marker, json.dumps(data))
            self.assertNotIn(marker, site.render_html(data))
            self.assertNotIn("CH03-D01", json.dumps(data))
            self.assertNotIn(str(SOURCE_ROOT), json.dumps(data))

    def test_current_cli_is_deterministic_and_portable(self):
        with tempfile.TemporaryDirectory() as tmp:
            first, second = Path(tmp) / "nested path" / "results", Path(tmp) / "elsewhere"
            result = subprocess.run([sys.executable, str(ROOT / "scripts/render_results_site.py"),
                                     "--source-root", str(ROOT), "--out-dir", str(first)]
                                    + ([] if self.rebalanced else ["--engineering-v02"]),
                                    cwd=tmp, capture_output=True, text=True, check=False,
                                    env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"})
            self.assertEqual(result.returncode, 0, result.stderr)
            site.build_site(SOURCE_ROOT, second, use_rebalanced_source=self.rebalanced)
            for name in ("index.html", "data.json"):
                self.assertEqual((first / name).read_bytes(), (second / name).read_bytes())
            self.assertEqual(json.loads((first / "data.json").read_text()), self.data)
            parser = Links()
            parser.feed((first / "index.html").read_text())
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


class RebalancedResultsSiteTests(EngineeringResultsSiteTests):
    version = "0.3.0"
    rebalanced = True
    schema = "math-gauge.portable-results/v5"
    expected = ((91.6211151369, 91.9635064412, 37.6296296296),
                (67.4419021739, 62.8430434783, -20))

    def test_new_weights_and_labels_are_bound_to_policy(self):
        for model in self.data["models"]:
            self.assertEqual(model["public"]["profile"]["overall_weights"],
                             {"core": 70, "repeat": 5, "neutral": 15, "stance": 10})
            self.assertEqual(model["public"]["neutral_group_weights"], {"written": 1, "lean_alignment": 2})
        rendered = site.render_html(self.data)
        for text in ("能力70%", "Lean对齐自查 · 10%", "书面中性自查 · 5%", "能力分占总分70%", "公开 40%", "合并 35%"):
            self.assertIn(text, rendered)
        for text in ("能力75%", "Lean对齐自查 · 5%", "能力分占总分75%"):
            self.assertNotIn(text, rendered)

    def test_rebalanced_projection_rejects_unrelated_profile_and_metric_changes(self):
        for mutation in ("profile", "metric", "prior-binding"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self.copy_sources(root)
                path = root / "docs/results/engineering-v0.3.0/gemini-public.json"
                data = json.loads(path.read_text())
                if mutation == "profile":
                    data["profile"]["components"][0]["family_count"] = 999
                elif mutation == "metric":
                    data["metrics"]["proofs"].update(exact=99, lower=99, upper=99)
                else:
                    data["weight_change"]["previous_score_sha256"] = "0" * 64
                path.write_text(json.dumps(data))
                with self.assertRaises(ValueError):
                    site.load_data(root)


if __name__ == "__main__":
    unittest.main()
