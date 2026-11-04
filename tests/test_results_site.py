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
        cls.data = site.load_data(SOURCE_ROOT)

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
            projected = site.load_data(source_root)
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
        self.assertIn("本轮调用与专项研究已结束", rendered)
        self.assertIn("不是统计置信区间", rendered)
        self.assertIn("原 92 项首答为 ERROR", rendered)

    def test_deterministic_bundle_has_only_portable_resolvable_local_links(self):
        with tempfile.TemporaryDirectory() as tmp:
            first, second = Path(tmp) / "nested path" / "results", Path(tmp) / "elsewhere"
            site.build_site(SOURCE_ROOT, first)
            site.build_site(SOURCE_ROOT, second)
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
                 "--source-root", str(SOURCE_ROOT), "--out-dir", str(out)],
                cwd=tmp, check=False, capture_output=True, text=True,
                env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(json.loads((out / "data.json").read_text()), self.data)


if __name__ == "__main__":
    unittest.main()
