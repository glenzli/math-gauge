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
    def __init__(self, page, score_mode=None):
        super().__init__()
        self.bars = []
        self.groups = []
        self.images = []
        self.values = []
        self.tooltips = []
        self.gap_groups = []
        self.gap_bars = []
        self._in_value = False
        self.score_mode = score_mode
        self.feed(page)

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if self.score_mode is not None and attrs.get("data-score-mode", self.score_mode) != self.score_mode:
            return
        if "score-bar" in attrs.get("class", "").split():
            self.bars.append(attrs)
        if "bar-group" in attrs.get("class", "").split():
            self.groups.append(attrs)
        if "gap-model-group" in attrs.get("class", "").split():
            self.gap_groups.append(attrs['data-model'])
        if "gap-bar" in attrs.get("class", "").split():
            self.gap_bars.append(attrs)
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
        self.assertEqual(self.data["schema"], "math-gauge.current-results-display/v6")
        self.assertEqual(self.data["publication_scope"], "combined")
        self.assertEqual(len(self.data["models"]), 4)
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
            self.assertEqual(combined["private_case_count"], combined["coverage"]["private_tasks"])
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
            downloads = {
                "downloads/" + model["id"] + "-" + scope + suffix + ".json"
                for model in self.data["models"] for scope in ["combined"]
                for suffix in ["", "-retry", "-strict", "-strict-retry", "-capability", "-capability-retry"]}
            self.assertEqual({p for p in before if p.startswith('downloads/')}, downloads)
            owned = json.loads(before['generated-pages.json'])
            self.assertEqual(set(before), set(owned)|{'generated-pages.json'})
            self.assertIn('method.html',owned)
            for model in self.data['models']:
                self.assertIn('models/'+model['id']+'/index.html',owned)
                self.assertIn('models/'+model['id']+'/cases/MG-PS001.html',owned)
            self.assertFalse(any('MG-GR103' in path for path in owned))

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

    def test_three_scores_use_rule_selected_sources_without_first_attempt_bars(self):
        page = SITE.render(self.data)
        chart = ChartBars(page)
        self.assertEqual(len(chart.bars), 3*len(self.data["models"]))
        self.assertEqual(len(chart.groups), len(self.data["models"]))
        for model in self.data['models']:
            for mode in self.data['score_modes']:
                matches = [b for b in chart.bars if b['data-model'] == model['id']
                           and b['data-score-mode'] == mode]
                self.assertEqual(len(matches), 1)
                self.assertEqual(matches[0]['data-series'], 'nonlogical_retry_3')
                self.assertEqual(float(matches[0]['data-score']),
                                 SITE.earned_value(SITE.selected_result(model, mode)))
        self.assertEqual(len(chart.images), len(self.data["models"]))
        self.assertNotIn('data-condition="single_attempt"', page)

    def test_rule_selected_lower_retry_is_shown_instead_of_best_score(self):
        data = copy.deepcopy(self.data)
        model = next(m for m in data['models'] if m['id'].startswith('deepseek'))
        lower = SITE.earned_value(model['combined']) - 1
        model['retry']['combined']['metrics']['earned']['confirmed'] = lower
        bar = next(b for b in ChartBars(SITE.render(data)).bars
                   if b['data-model'] == model['id'] and b['data-score-mode'] == 'partial')
        self.assertEqual(float(bar['data-score']), lower)

    def test_gap_diagnostics_bind_retained_totals_and_keep_incomplete_coverage_unranked(self):
        diagnostic = self.data['gap_diagnostics']
        self.assertEqual(diagnostic['attempt_condition'], 'nonlogical_retry_3')
        chart = ChartBars(SITE.render(self.data))
        ordered = sorted(self.data['models'], key=lambda m: SITE.earned_value(SITE.selected_result(m)), reverse=True)
        self.assertEqual(chart.gap_groups, [m['id'] for m in ordered])
        self.assertEqual(len(chart.gap_bars), 2*len(self.data["models"]))
        for table in diagnostic['tables']:
            for row in table['rows']:
                model = next(m for m in self.data['models'] if m['id'] == row['model_id'])
                mc = SITE.earned_value(SITE.selected_result(model, 'capability'))
                target = SITE.earned_value(SITE.selected_result(model, table['target_mode']))
                self.assertEqual(row['value'], target - mc)
                self.assertEqual(row['mc'], mc)
                bar = next(b for b in chart.gap_bars if b['data-model'] == row['model_id']
                           and b['data-gap-metric'] == table['id'])
                self.assertEqual(float(bar['data-gap-value']), row['value'])
                if model['evaluation_progress']['nonlogical_retry_3']['incomplete']:
                    self.assertIsNone(row['rank'])
                    self.assertEqual(row['status'], 'partial')
                else:
                    self.assertIsNotNone(row['rank'])

    def test_gap_positive_zero_and_unknown_values_preserve_their_meaning(self):
        models = copy.deepcopy(self.data['models'][:3])
        for model, values in zip(models, ((50, 45, 60), (None, None, None), (0, 0, 0))):
            for mode, value in zip(('capability', 'partial', 'strict'), values):
                metric = SITE.selected_result(model, mode)['metrics']['earned']
                metric.update(confirmed=value, exact=value)
        diagnostic = SITE.gap_diagnostics(models)
        delivery = next(t for t in diagnostic['tables'] if t['id'] == 'DG')
        positive = next(r for r in delivery['rows'] if r['model_id'] == models[0]['id'])
        self.assertEqual(positive['value'], 10)
        self.assertEqual(positive['display'], '+10.00')
        self.assertGreaterEqual(diagnostic['axis']['maximum'], 10)
        self.assertLess(diagnostic['axis']['zero'], 100)
        positive_plot = SITE.vertical_gap_plot(positive['value'], diagnostic['axis'])
        zero_y = SITE.vertical_gap_plot(0, diagnostic['axis'])['top']
        self.assertLess(positive_plot['top'], zero_y)
        self.assertAlmostEqual(positive_plot['top'] + positive_plot['height'], zero_y)
        negative_plot = SITE.vertical_gap_plot(-5, diagnostic['axis'])
        self.assertAlmostEqual(negative_plot['top'], zero_y)
        self.assertGreater(negative_plot['endpoint'], zero_y)
        self.assertIsNone(SITE.vertical_gap_plot(None, diagnostic['axis']))
        unknown = next(r for r in delivery['rows'] if r['model_id'] == models[1]['id'])
        self.assertIsNone(unknown['value'])
        self.assertIsNone(unknown['rank'])
        self.assertIsNone(unknown['plot'])
        zero = next(r for r in delivery['rows'] if r['model_id'] == models[2]['id'])
        self.assertEqual((zero['mc'], zero['value'], zero['display']), (0, 0, '0.00'))
        for model in models:
            for mode in ('capability', 'partial', 'strict'):
                SITE.selected_result(model, mode)['metrics']['earned'].update(confirmed=0, exact=0)
        zero_axis = SITE.gap_diagnostics(models)['axis']
        self.assertLess(zero_axis['minimum'], zero_axis['maximum'])
        models[2]['evaluation_progress']['nonlogical_retry_3'].update(
            adjudicated=0, pending=37, incomplete=True)
        unrun = next(r for r in SITE.gap_diagnostics(models)['tables'][1]['rows']
                     if r['model_id'] == models[2]['id'])
        self.assertIsNone(unrun['value'])
        self.assertIsNone(unrun['rank'])

    def test_display_alias_and_harness_do_not_rewrite_source_catalog_or_claim_all_batches_share_a_version(self):
        original = json.loads((ROOT / 'protocol/score-modes.json').read_bytes())
        self.assertEqual(self.data['score_mode_catalog'], original)
        self.assertEqual(next(m for m in self.data['display_score_modes'] if m['id']=='strict')['abbreviation'], 'SMC')
        self.assertEqual(self.data['default_attempt_condition'], 'nonlogical_retry_3')
        for model in self.data['models']:
            harness = model['harness']
            self.assertTrue(harness['local_tools_allowed'])
            self.assertFalse(harness['tool_network_access'])
            if harness['version'] is not None:
                self.assertEqual(harness['version_scope'], 'MG-MCP003')
            else:
                self.assertTrue(model['id'].startswith('deepseek') or model.get('record_kind')=='native_harness')

    def test_attempt_condition_reuses_other_models_honestly(self):
        self.assertEqual(self.data["attempt_conditions"], ["single_attempt", "nonlogical_retry_3"])
        page = SITE.render(self.data)
        self.assertNotIn('button data-condition=', page)
        for model in self.data["models"]:
            for scope in ["combined"]:
                self.assertEqual(model[scope]["coverage"], model["retry"][scope]["coverage"])
                self.assertFalse(model["retry"][scope]["formal_comparison_eligible"])
                self.assertNotIn("slot_evidence", model["retry"][scope])
            if model["id"].startswith("deepseek"):
                self.assertGreater(SITE.earned_value(model["retry"]["combined"]), SITE.earned_value(model["combined"]))
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
                self.assertEqual(result["coverage"], model["combined"]["coverage"])
                self.assertEqual(result["strict_alignment_selfcheck"]["strict_pass"], model.get("record_kind")=="native_harness")
                self.assertEqual(result["metrics"]["overall"]["exact"], result["metrics"]["earned"]["exact"])
                self.assertNotIn("tasks", result)
        chart = ChartBars(SITE.render(self.data), "strict")
        self.assertEqual(chart.values, [f"{SITE.earned_value(m['strict']['nonlogical_retry_3']):.2f}"
                                        for m in sorted(self.data['models'], key=lambda m: SITE.earned_value(SITE.selected_result(m)), reverse=True)])
        self.assertEqual(len(chart.bars), len(self.data["models"]))
        self.assertEqual(chart.tooltips, [])
        self.assertEqual(len(chart.images), len(self.data["models"]))

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
    def test_claim_audit_uses_shared_aggregate_summaries_without_private_findings(self):
        for model in self.data['models']:
            result=model['combined'];summary=result['claim_penalties']
            self.assertEqual(summary['status'],'source_bound_review_applied')
            self.assertNotIn('tasks',result)
            self.assertNotIn('finding_ids',json.dumps(summary))

    def test_public_manuscript_displays_bound_review_and_keeps_unrun_answer_unknown(self):
        from scripts.results_details import public_evidence, review_markdown
        for model in self.data['models']:
            if model.get('record_kind') == 'native_harness':
                continue
            folder = ROOT / Path(model['source_record']).parent
            record = json.loads((folder / 'record.json').read_bytes())
            projection = json.loads((folder / 'public-task-scores.json').read_bytes())
            task = next(row for row in projection['views']['partial']['single_attempt']['tasks']
                        if row['case_id'] == 'MG-MCP003')
            evidence = public_evidence(folder, record, 'MG-MCP003', 'single_attempt', task)
            if model['id'].startswith('deepseek'):
                self.assertIsNone(task['completion']['exact'])
                self.assertFalse(any(s['role'] == 'answer' for s in evidence['sources']))
            else:
                self.assertEqual(evidence['review']['answer_sha256'], task['response_sha256'])
                self.assertEqual(len(evidence['review']['criteria']), 6)
                self.assertIn('M4', review_markdown(evidence['review']))


if __name__ == "__main__":
    unittest.main()
