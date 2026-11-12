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
    def __init__(self, page, score_mode=None, score_scope='overall'):
        super().__init__()
        self.bars = []
        self.groups = []
        self.images = []
        self.values = []
        self.tooltips = []
        self.gap_groups = []
        self.gap_bars = []
        self.rate_groups = []
        self._in_value = False
        self.score_mode = score_mode
        self.score_scope = score_scope
        self.feed(page)

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if attrs.get('data-score-scope', self.score_scope) != self.score_scope:
            return
        if self.score_mode is not None and attrs.get("data-score-mode", self.score_mode) != self.score_mode:
            return
        if "score-bar" in attrs.get("class", "").split():
            self.bars.append(attrs)
        if "bar-group" in attrs.get("class", "").split():
            self.groups.append(attrs)
        if "gap-model-group" in attrs.get("class", "").split():
            self.gap_groups.append(attrs['data-model'])
        if "rate-model-group" in attrs.get("class", "").split():
            self.rate_groups.append(attrs['data-model'])
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
                         {"planned": 3, "adjudicated": 3, "pending": 0, "pending_rounds": 0, "incomplete": False})
        result["whole_task_counts"].update(failed=1, unknown=1)
        self.assertEqual(SITE.evaluation_progress(result),
                         {"planned": 3, "adjudicated": 2, "pending": 1, "pending_rounds": 0, "incomplete": True})

    def test_only_selected_current_models_and_scores_are_displayed(self):
        self.assertEqual(self.data["benchmark_version"], "0.6.0")
        self.assertEqual(self.data["schema"], "math-gauge.current-results-display/v6")
        self.assertEqual(self.data["publication_scope"], "combined")
        from math_gauge.records import selected_cli_records, selected_paper_records
        selected = {model for model, folder in selected_cli_records(ROOT) + selected_paper_records(ROOT)}
        displayed = {model['id'] for model in self.data['models']
                     if model.get('record_kind') != 'native_harness'}
        self.assertEqual(displayed, selected)
        for model in self.data["models"]:
            path = ROOT / Path(model["source_record"]).parent
            original = json.loads((path / "combined-aggregate.json").read_bytes())
            self.assertEqual(model["combined"], original)
            self.assertNotIn("public", model)
            self.assertNotIn("public", model["retry"])
            self.assertFalse(model["combined"]["formal_comparison_eligible"])
            admitted = model["retry"]["combined"]
            self.assertEqual(model["lean_formalization_breakdown"], admitted["lean_formalization_breakdown"])
            self.assertEqual(model["alignment_selfcheck"], admitted["alignment_selfcheck"])

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
        projected = json.loads(payload)
        self.assertEqual(projected['models'][0]['label'], label)
        self.assertEqual([model['id'] for model in projected['models']],
                         [model['id'] for model in data['models']])
        self.assertNotIn('sources', projected)

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
            downloads.add('downloads/timing-reference.json')
            downloads.add('downloads/cost-reference.json')
            self.assertEqual({p for p in before if p.startswith('downloads/')}, downloads)
            timings=json.loads(before['downloads/timing-reference.json'])
            self.assertEqual(timings,SITE.build_reference(SITE.ROOT,display_data=self.data))
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

    def test_category_charts_use_saved_percentages_and_category_specific_order(self):
        original = copy.deepcopy(self.data)
        page = SITE.render(self.data)
        for category in self.data['category_leaderboards']:
            chart = ChartBars(page, score_scope=category['id'])
            self.assertEqual([g['data-model'] for g in chart.groups],
                             [row['model_id'] for row in category['views']['partial']])
            self.assertEqual(len(chart.bars), len(self.data['models']) * 3)
            for mode, rows in category['views'].items():
                for row in rows:
                    bar = next(b for b in chart.bars if b['data-model'] == row['model_id']
                               and b['data-score-mode'] == mode)
                    self.assertEqual(bar['data-series'], 'nonlogical_retry_3')
                    if row['value'] is None:
                        self.assertEqual(bar['data-score'], '')
                    else:
                        self.assertEqual(float(bar['data-score']), row['value'])
                    self.assertIn(f"完整分区间 {row['lower']:.2f}–{row['upper']:.2f}", page)
        self.assertEqual(self.data, original)

    def test_category_chart_preserves_negative_zero_unknown_and_scoped_incompleteness(self):
        data = copy.deepcopy(self.data)
        category = next(g for g in data['category_leaderboards'] if g['id'] == 'lean')
        negative, zero, unknown = category['views']['partial'][:3]
        negative.update(value=-2.5, lower=-2.5, upper=-2.5)
        zero.update(value=0, lower=0, upper=0)
        unknown.update(value=None, lower=-20, upper=100, incomplete=True)
        chart = ChartBars(SITE.grouped_bars(data, category), score_mode='partial', score_scope='lean')
        bars = {b['data-model']: b for b in chart.bars}
        def geometry(row):
            return {k: float(v.rstrip('%')) for k, v in
                    (pair.split(':') for pair in bars[row['model_id']]['style'].split(';'))}
        neg, zer, unk = geometry(negative), geometry(zero), geometry(unknown)
        self.assertGreater(neg['width'], 0)
        self.assertLess(neg['left'], zer['left'])
        self.assertAlmostEqual(neg['left'] + neg['width'], zer['left'])
        self.assertEqual((zer['width'], unk['width']), (0, 0))
        self.assertEqual(bars[zero['model_id']]['data-score'], '0')
        self.assertEqual(bars[unknown['model_id']]['data-score'], '')
        self.assertIn('—', chart.values)
        self.assertEqual((unknown['value'], unknown['lower'], unknown['upper']), (None, -20, 100))

    def test_gap_diagnostics_bind_retained_totals_and_keep_incomplete_coverage_unranked(self):
        diagnostic = self.data['gap_diagnostics']
        self.assertEqual(diagnostic['attempt_condition'], 'nonlogical_retry_3')
        chart = ChartBars(SITE.render(self.data))
        gaps = {r['model_id']: r['value'] for r in diagnostic['tables'][0]['rows']}
        ordered = sorted(self.data['models'], key=lambda m: (
            gaps[m['id']] is None, abs(gaps[m['id']]) if gaps[m['id']] is not None else 0, m['id']))
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

    def test_auxiliary_charts_do_not_inherit_overall_order(self):
        data = copy.deepcopy(self.data)
        before = ChartBars(SITE.render(data))
        for index, model in enumerate(data['models']):
            model['retry']['combined']['metrics']['earned']['confirmed'] = index
        after = ChartBars(SITE.render(data))
        self.assertNotEqual([g['data-model'] for g in before.groups],
                            [g['data-model'] for g in after.groups])
        self.assertEqual(after.gap_groups, before.gap_groups)
        self.assertEqual(after.rate_groups, before.rate_groups)

    def test_rate_sort_keeps_known_zero_before_unknown(self):
        data = copy.deepcopy(self.data)
        data['models'] = data['models'][:3]
        for model, value in zip(data['models'], [None, 0, 100]):
            model['content_rates']['metrics']['reliability']['observed'] = value
        chart = ChartBars(SITE.render_content_rates(data))
        self.assertEqual(chart.rate_groups,
                         [data['models'][i]['id'] for i in [2, 1, 0]])

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
        positive_plot = positive['plot']
        zero_x = diagnostic['axis']['zero']
        self.assertAlmostEqual(positive_plot['left'], zero_x)
        self.assertGreater(positive_plot['left'] + positive_plot['width'], zero_x)
        negative_plot = next(r for r in diagnostic['tables'][0]['rows']
                             if r['model_id'] == models[0]['id'])['plot']
        self.assertLess(negative_plot['left'], zero_x)
        self.assertAlmostEqual(negative_plot['left'] + negative_plot['width'], zero_x)
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
            if model.get('record_kind') != 'native_harness':
                metadata = json.loads((ROOT / 'site/harnesses.json').read_bytes())['models'][model['id']]
                self.assertEqual(harness, metadata, 'CLI and returned-paper displays must use the same source-bound harness metadata')
            self.assertTrue(harness['local_tools_allowed'])
            self.assertFalse(harness['tool_network_access'])
            if harness['version'] is not None:
                self.assertTrue(harness['version_scope'])
                self.assertEqual(harness['version_scope'],
                    json.loads((ROOT / 'site/harnesses.json').read_bytes())['models'][model['id']]['version_scope'])
            else:
                versions = harness.get('observed_versions', [])
                if versions:
                    self.assertGreaterEqual(len(set(versions)), 2)
                    self.assertTrue(harness['version_scope'])
                    for version in versions:
                        self.assertIn(version, harness['version_scope'])
                else:
                    self.assertTrue(model['id'].startswith('deepseek') or model.get('record_kind')=='native_harness')

    def test_attempt_condition_reuses_other_models_honestly(self):
        self.assertEqual(self.data["attempt_conditions"], ["single_attempt", "nonlogical_retry_3"])
        page = SITE.render(self.data)
        self.assertNotIn('button data-condition=', page)
        for model in self.data["models"]:
            for scope in ["combined"]:
                first, retry = model[scope]['coverage'], model['retry'][scope]['coverage']
                for key in ('initial_slots', 'parent_families', 'public_tasks', 'private_tasks', 'alignment_rounds'):
                    self.assertEqual(first[key], retry[key])
                self.assertFalse(model["retry"][scope]["formal_comparison_eligible"])
                self.assertNotIn("slot_evidence", model["retry"][scope])
            summary = model['retry']['combined'].get('retry_summary', {})
            reruns = summary.get('slots_with_reruns', summary.get('admitted_initial_reruns', 0))
            if reruns:
                if summary.get('selection'):
                    self.assertIn(summary['selection'],
                                  {'first_completed_delivery', 'first_normal_native_delivery'})
                else:
                    from math_gauge.records import evidence_bytes
                    folder = ROOT / Path(model['source_record']).parent
                    record = json.loads((folder / 'record.json').read_bytes())
                    selection = json.loads(evidence_bytes(folder, record['attempt_condition_sources']))
                    self.assertEqual(selection['selection'], 'first_normal_delivery_after_counted_operational_failures')
                    self.assertEqual(set(selection['conditions']), {'single_attempt', 'nonlogical_retry_3'})
            else:
                for scope in ["combined"]:
                    self.assertEqual(model[scope]["metrics"], model["retry"][scope]["metrics"])
                    self.assertEqual(model["retry"][scope].get("retry_summary", {}).get("slots_with_reruns", 0), 0)

    def test_unreviewed_fixed_rounds_keep_the_source_coverage_unknown(self):
        model = next(m for m in self.data['models'] if m['id'] == 'gemini-4-argon')
        result = copy.deepcopy(model['retry']['combined'])
        self.assertFalse(SITE.evaluation_progress(result)['incomplete'])
        result['alignment_selfcheck']['rounds'][0]['score']['exact'] = None
        progress = SITE.evaluation_progress(result)
        self.assertEqual(progress['pending'], 0, 'Unknown rounds must not invent pending A1 tasks')
        self.assertEqual(progress['pending_rounds'], 1)
        self.assertTrue(progress['incomplete'])



    def test_strict_mode_binds_three_combined_scores_without_auxiliary_credit(self):
        self.assertEqual(self.data["score_modes"], ["capability", "partial", "strict"])
        for model in self.data["models"]:
            for condition, result in model["strict"].items():
                self.assertEqual(result["primary_metric"], "earned")
                folder = ROOT / Path(model["source_record"]).parent
                record = json.loads((ROOT / model['source_record']).read_bytes())
                filename = record['strict_results'][condition]['path']
                self.assertEqual(result, json.loads((folder / filename).read_bytes()))
                self.assertEqual(result["attempt_condition"], condition)
                reliable = model['combined'] if condition == 'single_attempt' else model['retry']['combined']
                self.assertEqual(result['coverage'], reliable['coverage'])
                verdict = result['strict_alignment_selfcheck']['strict_pass']
                self.assertEqual(result['metrics']['lean-selfcheck']['exact'],
                                 None if verdict is None else 100 if verdict else 0)
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
            record = json.loads((ROOT / model['source_record']).read_bytes())
            for condition, item in record['capability_results'].items():
                filename = item['path']
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
            if task['completion']['exact'] is None:
                self.assertIsNone(task['completion']['exact'])
                self.assertFalse(any(s['role'] == 'answer' for s in evidence['sources']))
            elif task['response_sha256'] is None:
                self.assertEqual(task['completion']['exact'], 0)
                self.assertFalse(task['strict_pass'])
                self.assertIsNone(evidence['review'])
                self.assertFalse(any(s['role'] == 'answer' for s in evidence['sources']))
            else:
                review = evidence['review']
                response_hash = (review.get('answer_sha256') or
                                 review.get('binding', {}).get('response_sha256') or
                                 review.get('bindings', {}).get('answer', {}).get('sha256'))
                if response_hash is not None:
                    self.assertEqual(response_hash, task['response_sha256'])
                else:
                    # Some original review schemas pair answer/review descriptors in
                    # the source-bound record instead of repeating the answer hash.
                    row = evidence['source_row']
                    self.assertEqual(row['response']['sha256'], task['response_sha256'])
                    self.assertEqual(row['source']['response_sha256'], task['response_sha256'])
                    self.assertTrue(any(s['sha256'] == row['review']['sha256'] for s in evidence['sources']))
                self.assertEqual(len(review.get('criteria', review.get('dimensions', []))), 6)
                criterion = review.get('criteria', review.get('dimensions'))[0]
                key = next(criterion[k] for k in ('id', 'criterion_id', 'dimension_id') if k in criterion)
                self.assertIn(key, review_markdown(evidence['review']))


if __name__ == "__main__":
    unittest.main()
