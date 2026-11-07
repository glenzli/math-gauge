"""Current display consumes retained records without a parallel scoring method."""
import copy
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

    def test_progress_tracks_pending_built_tasks_not_failures_or_unbuilt_weight(self):
        result = {"whole_task_counts": {"planned": 3, "passed": 1, "failed": 2, "unknown": 0},
                  "capacity": {"active": 90, "under_construction": 10},
                  "metrics": {"overall": {"exact": None}}}
        self.assertEqual(SITE.evaluation_progress(result),
                         {"planned": 3, "adjudicated": 3, "pending": 0, "incomplete": False})
        result["whole_task_counts"].update(failed=1, unknown=1)
        self.assertEqual(SITE.evaluation_progress(result),
                         {"planned": 3, "adjudicated": 2, "pending": 1, "incomplete": True})

    def test_only_selected_current_models_and_scores_are_displayed(self):
        self.assertEqual(self.data["benchmark_version"], "0.6.0")
        self.assertEqual(self.data["schema"], "math-gauge.current-results-display/v5")
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
            self.assertEqual(combined["private_case_count"], 9)
            for result in (combined, model["retry"]["combined"]):
                for metric in result["metrics"].values():
                    self.assertEqual(set(metric),
                        {"exact", "lower", "upper", "complete", "coverage", "formal_comparison_eligible"}
                        | ({"confirmed"} if "confirmed" in metric else set()))
        text = json.dumps(self.data)
        self.assertNotIn("math-gauge-private/", text)
        self.assertNotIn("MG-X", text)
        self.assertNotIn("MG-TXP", text)
        self.assertNotIn("MG-BCP", text)

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
            self.assertEqual(len(before), 20)
            self.assertEqual(set(before), {"index.html", "data.json", *(
                "downloads/" + model["id"] + "-" + scope + suffix + ".json"
                for model in self.data["models"] for scope in ["combined"]
                for suffix in ["", "-retry", "-strict", "-strict-retry", "-capability", "-capability-retry"])})

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
                self.assertEqual(float(matches[0]["data-score"]), SITE.earned_value(result))
                self.assertIn("retry-extension" if series == "nonlogical_retry_3" else "first-solid", matches[0]["class"])
                if series == "nonlogical_retry_3":
                    first = SITE.earned_value(model["combined"])
                    self.assertEqual(float(matches[0]["data-start-score"]), first)
                    self.assertAlmostEqual(float(matches[0]["data-gain-score"]), SITE.earned_value(result) - first)
        self.assertEqual(page.count('class="chart-value"'), 9)
        self.assertEqual(ChartBars(page).values, [f"{max(SITE.earned_value(m['combined']), SITE.earned_value(m['retry']['combined'])):.2f}"
                                                for m in self.data["models"]])
        self.assertNotIn("46.71 → 49.80", page)
        self.assertIn('bottom:0%">0</span>', page)
        self.assertIn('bottom:100%">100</span>', page)
        self.assertNotIn('data-mode=', page)
        for model in self.data["models"]:
            self.assertFalse((ROOT / Path(model["source_record"]).parent / "result.json").exists())


    def test_only_a_changed_model_has_first_attempt_details_on_hover(self):
        page = SITE.render(self.data)
        tips = ChartBars(page).tooltips
        self.assertEqual(len(tips), 1)
        self.assertIn("deepseek-v4.1-flash-1017", tips[0]["id"])
        self.assertIn('<dt>首次</dt><dd>46.71</dd>', page)
        self.assertIn('<dt>重跑后</dt><dd>49.80</dd>', page)
        self.assertIn('<dt>增量</dt><dd>+3.09</dd>', page)
        data = copy.deepcopy(self.data)
        ds = next(m for m in data["models"] if m["id"].startswith("deepseek"))
        ds["retry"]["combined"]["metrics"]["earned"]["confirmed"] = SITE.earned_value(ds["combined"])
        same = ChartBars(SITE.render(data))
        self.assertEqual(same.tooltips, [])
        self.assertEqual(len(same.bars), 3)


    def test_lower_retry_source_is_marked_at_its_actual_endpoint_without_a_false_gain(self):
        data = copy.deepcopy(self.data)
        model = next(m for m in data["models"] if m["id"].startswith("deepseek"))
        model["retry"]["combined"]["metrics"]["earned"]["confirmed"] = 40.0
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
                self.assertAlmostEqual(SITE.earned_value(model["retry"]["combined"]), 49.7961462451)
            else:
                for scope in ["combined"]:
                    self.assertEqual(model[scope]["metrics"], model["retry"][scope]["metrics"])
                    self.assertEqual(model["retry"][scope]["retry_summary"]["slots_with_reruns"], 0)



    def test_strict_mode_binds_three_combined_scores_without_auxiliary_credit(self):
        self.assertEqual(self.data["score_modes"], ["capability", "partial", "strict"])
        for model in self.data["models"]:
            for condition, result in model["strict"].items():
                self.assertEqual(result["primary_metric"], "earned")
                folder = ROOT / Path(model["source_record"]).parent
                filename = ("strict-combined-aggregate.json" if condition == "single_attempt"
                            else "strict-retry-combined-aggregate.json")
                self.assertEqual(result, json.loads((folder / filename).read_bytes()))
                self.assertEqual(result["attempt_condition"], condition)
                self.assertEqual(result["coverage"]["tasks"], 33)
                self.assertEqual(result["coverage"]["parent_families"], 29)
                self.assertFalse(result["strict_alignment_selfcheck"]["strict_pass"])
                self.assertIsNone(result["metrics"]["overall"]["exact"])
                self.assertNotIn("tasks", result)
        chart = ChartBars(SITE.render(self.data), "strict")
        self.assertEqual(chart.values, [f"{max(SITE.earned_value(v) for v in m['strict'].values()):.2f}"
                                        for m in self.data["models"]])
        self.assertEqual(len(chart.bars), 3)
        self.assertEqual(chart.tooltips, [])
        self.assertEqual(len(chart.images), 3)

    def test_capability_uses_bound_score_views_and_reliable_is_the_default(self):
        self.assertEqual(self.data["default_score_mode"], "partial")
        self.assertEqual(self.data["score_mode_catalog"]["primary"], "partial")
        for model in self.data["models"]:
            folder = ROOT / Path(model["source_record"]).parent
            for condition, filename in [("single_attempt", "capability-combined-aggregate.json"),
                                        ("nonlogical_retry_3", "capability-retry-combined-aggregate.json")]:
                current = model["capability"][condition]
                self.assertEqual(current, json.loads((folder / filename).read_bytes()))
                reliable = model["combined"] if condition == "single_attempt" else model["retry"]["combined"]
                self.assertGreaterEqual(SITE.earned_value(current), SITE.earned_value(reliable))
                self.assertEqual(current["capacity"], reliable["capacity"])
                self.assertEqual(current["coverage"], reliable["coverage"])



if __name__ == "__main__":
    unittest.main()
