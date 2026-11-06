"""Current display consumes retained records without a parallel scoring method."""
import copy
import base64
import hashlib
import importlib.util
import json
from html.parser import HTMLParser
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("current_results_site", ROOT / "scripts/render_results_site.py")
SITE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(SITE)


class ChartBars(HTMLParser):
    def __init__(self, page, score_mode="partial"):
        super().__init__()
        self.bars = []
        self.groups = []
        self.images = []
        self.values = []
        self.tooltips = []
        self._in_value = False
        self.score_mode = score_mode
        self.feed(page)

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if attrs.get("data-score-mode", self.score_mode) != self.score_mode:
            return
        if "score-bar" in attrs.get("class", "").split():
            self.bars.append(attrs)
        if "bar-group" in attrs.get("class", "").split():
            self.groups.append(attrs)
        if "provider-logo" in attrs.get("class", "").split():
            self.images.append(attrs)
        if "chart-value" in attrs.get("class", "").split():
            self.values.append("")
            self._in_value = True
        if attrs.get("role") == "tooltip":
            self.tooltips.append(attrs)

    def handle_data(self, data):
        if self._in_value:
            self.values[-1] += data

    def handle_endtag(self, tag):
        if tag == "span":
            self._in_value = False


class CurrentSiteTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = SITE.build_data()

    def test_only_selected_current_models_and_scores_are_displayed(self):
        self.assertEqual(self.data["benchmark_version"], "0.6.0")
        self.assertEqual(self.data["schema"], "math-gauge.current-results-display/v4")
        self.assertEqual(self.data["publication_scope"], "combined")
        self.assertEqual(len(self.data["models"]), 3)
        for model in self.data["models"]:
            path = ROOT / Path(model["source_record"]).parent
            original = json.loads((path / "combined-aggregate.json").read_bytes())
            self.assertEqual(model["combined"], original)
            self.assertNotIn("public", model)
            self.assertNotIn("public", model["retry"])
            self.assertFalse(model["combined"]["formal_comparison_eligible"])

    def test_public_display_has_no_private_task_identifiers_or_raw_inputs(self):
        for model in self.data["models"]:
            combined = model["combined"]
            self.assertEqual(combined["scope"], "combined-aggregate-only")
            self.assertNotIn("slot_evidence", combined)
            self.assertNotIn("records", combined)
            self.assertEqual(combined["private_case_count"], 3)
            for result in (combined, model["retry"]["combined"]):
                for metric in result["metrics"].values():
                    self.assertEqual(set(metric),
                        {"exact", "lower", "upper", "complete", "coverage", "formal_comparison_eligible"})
        text = json.dumps(self.data)
        self.assertNotIn("math-gauge-private/", text)
        self.assertNotIn("MG-X", text)

    def test_embedded_json_cannot_close_its_script_and_labels_are_escaped(self):
        data = copy.deepcopy(self.data)
        label = '</script><script>alert("fixture")</script>&'
        data["models"][0]["label"] = label
        page = SITE.render(data)
        self.assertNotIn(label, page)
        self.assertIn("\\u003c/script>", page)
        self.assertIn("&lt;/script&gt;", page)
        payload = page.split('<script type="application/json" id="data">', 1)[1].split("</script>", 1)[0]
        self.assertEqual(json.loads(payload), data)

    def test_outputs_are_deterministic_and_only_current_results_are_exported(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            SITE.write_site(root)
            before = {str(p.relative_to(root)): p.read_bytes() for p in root.rglob("*") if p.is_file()}
            SITE.write_site(root)
            self.assertEqual(before, {str(p.relative_to(root)): p.read_bytes() for p in root.rglob("*") if p.is_file()})
            self.assertEqual(len(before), 14)
            self.assertEqual(set(before), {"index.html", "data.json", *(
                "downloads/" + model["id"] + "-" + scope + suffix + ".json"
                for model in self.data["models"] for scope in ["combined"]
                for suffix in ["", "-retry", "-strict", "-strict-retry"])})

    def test_retired_public_only_downloads_are_removed_without_deleting_unrelated_files(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            downloads = root / "downloads"
            downloads.mkdir()
            retired = [downloads / (m["id"] + suffix) for m in self.data["models"]
                       for suffix in ("-public.json", "-public-retry.json")]
            for path in retired:
                path.write_text("previous generated public-only score")
            keep = downloads / "operator-notes.txt"
            keep.write_text("Preserve this unrelated file.")
            SITE.write_site(root)
            self.assertTrue(all(not path.exists() for path in retired))
            self.assertEqual(keep.read_text(), "Preserve this unrelated file.")

    def test_solid_bars_and_only_observed_retry_increments_bind_to_the_retained_scores(self):
        page = SITE.render(self.data)
        bars = ChartBars(page).bars
        self.assertEqual(len(bars), 4)
        for model in self.data["models"]:
            for series, result in [("single_attempt", model["combined"]),
                                   ("nonlogical_retry_3", model["retry"]["combined"])]:
                matches = [b for b in bars if b["data-model"] == model["id"] and b["data-series"] == series]
                if series == "nonlogical_retry_3" and not result["retry_summary"]["slots_with_reruns"]:
                    self.assertFalse(matches)
                    continue
                self.assertEqual(len(matches), 1)
                self.assertEqual(float(matches[0]["data-score"]), result["metrics"]["earned"]["exact"])
                self.assertIn("retry-extension" if series == "nonlogical_retry_3" else "first-solid", matches[0]["class"])
                if series == "nonlogical_retry_3":
                    first = model["combined"]["metrics"]["earned"]["exact"]
                    self.assertEqual(float(matches[0]["data-start-score"]), first)
                    self.assertAlmostEqual(float(matches[0]["data-gain-score"]), result["metrics"]["earned"]["exact"] - first)
        self.assertEqual(page.count('class="chart-value"'), 6)
        self.assertEqual(ChartBars(page).values, ["62.17", "49.45", "44.73"])
        self.assertNotIn("47.45 → 49.45", page)
        self.assertIn('bottom:0%">0</span>', page)
        self.assertIn('bottom:100%">100</span>', page)
        self.assertNotIn('data-mode=', page)
        for model in self.data["models"]:
            self.assertFalse((ROOT / Path(model["source_record"]).parent / "result.json").exists())

    def test_each_model_has_its_own_theme_shared_by_the_solid_and_striped_segments(self):
        groups = ChartBars(SITE.render(self.data)).groups
        self.assertEqual(len(groups), 3)
        self.assertEqual(len({m["theme"]["color"] for m in self.data["models"]}), 3)
        for model in self.data["models"]:
            group = next(g for g in groups if g["data-model"] == model["id"])
            self.assertIn("--model-color:" + model["theme"]["color"], group["style"])

    def test_only_a_changed_model_has_first_attempt_details_on_hover(self):
        page = SITE.render(self.data)
        tips = ChartBars(page).tooltips
        self.assertEqual(len(tips), 1)
        self.assertIn("deepseek-v4.1-flash-1017", tips[0]["id"])
        self.assertIn('<dt>首次</dt><dd>47.45</dd>', page)
        self.assertIn('<dt>重跑后</dt><dd>49.45</dd>', page)
        self.assertIn('<dt>增量</dt><dd>+2.00</dd>', page)
        data = copy.deepcopy(self.data)
        ds = next(m for m in data["models"] if m["id"].startswith("deepseek"))
        ds["retry"]["combined"]["metrics"]["earned"]["exact"] = ds["combined"]["metrics"]["earned"]["exact"]
        same = ChartBars(SITE.render(data))
        self.assertEqual(same.tooltips, [])
        self.assertEqual(len(same.bars), 3)

    def test_provider_icons_are_original_local_bytes_embedded_for_offline_output(self):
        page = SITE.render(self.data)
        icons = ChartBars(page).images
        self.assertEqual(len(icons), 3)
        self.assertEqual([i["alt"] for i in icons], ["OpenAI", "DeepSeek", "Google"])
        for model in self.data["models"]:
            icon = next(i for i in icons if i["alt"] == model["logo"]["label"])
            self.assertTrue(icon["src"].startswith("data:image/svg+xml;base64,"))
            raw = base64.b64decode(icon["src"].split(",", 1)[1], validate=True)
            self.assertEqual(hashlib.sha256(raw).hexdigest(), model["logo"]["sha256"])
            local = ROOT / "site/assets/logos" / (icon["alt"].lower() + ".svg")
            self.assertEqual(raw, local.read_bytes())

    def test_lower_retry_source_is_marked_at_its_actual_endpoint_without_a_false_gain(self):
        data = copy.deepcopy(self.data)
        model = next(m for m in data["models"] if m["id"].startswith("deepseek"))
        model["retry"]["combined"]["metrics"]["earned"]["exact"] = 40.0
        overlay = next(b for b in ChartBars(SITE.render(data)).bars
                       if b["data-model"] == model["id"] and b["data-series"] == "nonlogical_retry_3")
        self.assertEqual(overlay["data-score"], "40.0")
        self.assertIn("retry-end", overlay["class"])
        self.assertIn("bottom:40.00000000%;height:0.00000000%", overlay["style"])

    def test_attempt_condition_reuses_other_models_honestly(self):
        self.assertEqual(self.data["attempt_conditions"], ["single_attempt", "nonlogical_retry_3"])
        page = SITE.render(self.data)
        self.assertIn('data-condition="nonlogical_retry_3"', page)
        self.assertIn("const mode='combined'", page)
        for model in self.data["models"]:
            for scope in ["combined"]:
                self.assertEqual(model[scope]["coverage"], model["retry"][scope]["coverage"])
                self.assertFalse(model["retry"][scope]["formal_comparison_eligible"])
                self.assertNotIn("slot_evidence", model["retry"][scope])
            if model["id"].startswith("deepseek"):
                self.assertEqual(model["retry"]["combined"]["metrics"]["earned"]["exact"], 49.4539002558)
            else:
                for scope in ["combined"]:
                    self.assertEqual(model[scope]["metrics"], model["retry"][scope]["metrics"])
                    self.assertEqual(model["retry"][scope]["retry_summary"]["slots_with_reruns"], 0)

    def test_declared_components_and_finite_states_are_present(self):
        page = SITE.render(self.data)
        for value in ["verified_complete", "incomplete_stable", "regressed", "interrupted", "unresolved"]:
            self.assertIn(value, page)
        self.assertIn("textContent", page)
        self.assertNotIn("innerHTML", page)
        self.assertNotIn('<script src="http', page)
        for model in self.data["models"]:
            for scope in ["combined"]:
                self.assertEqual(sum(c["weight"] for c in model[scope]["profile"]["subcategories"]), 100)
                self.assertEqual(model[scope]["coverage"]["tasks"], 29)

    def test_display_binds_the_unified_engineering_review_and_current_method(self):
        for model in self.data["models"]:
            path = ROOT / Path(model["source_record"]).parent
            record = json.loads((path / "record.json").read_bytes())
            for scope in ("combined",):
                self.assertEqual(model[scope]["engineering_review_sha256"], record["formalization_review"]["sha256"])
                self.assertEqual(model[scope]["scoring_method_version"], self.data["policy"]["version"])
        gemini = next(model for model in self.data["models"] if model["id"].startswith("gemini"))
        case = next(case for case in gemini["lean_formalization_breakdown"]["cases"] if case["case_id"] == "HCH02")
        self.assertEqual((case["complete_count"], case["total"]), (38, 40))
        self.assertIn('href="../docs/formalization-audit.md"', SITE.render(self.data))

    def test_strict_mode_binds_three_combined_scores_without_auxiliary_credit(self):
        expected = {"terra-6.1-max": 50.0, "deepseek-v4.1-flash-1017": 25.2941176471,
                    "gemini-3.8-flash-high": 16.3235294118}
        self.assertEqual(self.data["score_modes"], ["partial", "strict"])
        for model in self.data["models"]:
            for condition, result in model["strict"].items():
                self.assertEqual(result["primary_metric"], "earned")
                self.assertAlmostEqual(result["metrics"]["earned"]["exact"], expected[model["id"]])
                self.assertEqual(result["attempt_condition"], condition)
                self.assertEqual(result["coverage"]["tasks"], 29)
                self.assertEqual(result["coverage"]["parent_families"], 21)
                self.assertFalse(result["strict_alignment_selfcheck"]["strict_pass"])
                self.assertIsNone(result["metrics"]["overall"]["exact"])
                self.assertNotIn("tasks", result)
        chart = ChartBars(SITE.render(self.data), "strict")
        self.assertEqual(chart.values, ["50.00", "25.29", "16.32"])
        self.assertEqual(len(chart.bars), 3)
        self.assertEqual(chart.tooltips, [])
        self.assertEqual(len(chart.images), 3)

    def test_mode_switch_keeps_attempt_controls_and_changes_chart_metric_and_download(self):
        page = SITE.render(self.data)
        self.assertIn('data-score-mode="partial" aria-pressed="true"', page)
        self.assertIn('data-score-mode="strict" aria-pressed="false"', page)
        self.assertIn('id="score-chart-strict" hidden', page)
        self.assertIn('Strict 已获分', page)
        self.assertIn("m.strict[c]", page)
        self.assertNotIn("metrics.repeat", page)
        self.assertIn("建设中", page)
        self.assertIn("对齐自查", page)
        self.assertIn("背景核查", page)
        self.assertIn("命题拓展", page)
        self.assertIn("研究稿完善", page)
        self.assertIn("scoreMode==='strict'?'-strict':''", page)
        self.assertIn("button[data-score-mode]", page)


if __name__ == "__main__":
    unittest.main()
