"""Anonymous continuation statistics and model-specific operational evidence."""
import copy
import json
from pathlib import Path
import re
import unittest

from scripts.results_presentation import model_view
from scripts.results_anomalies import render_model_details
from math_gauge.execution_anomalies import load_public
from scripts.results_attempt_history import load_public as load_attempts
from scripts.render_results_site import render

ROOT = Path(__file__).resolve().parents[1]


class ContinuationCompletionDisplayTests(unittest.TestCase):
    def test_browser_projection_preserves_counts_and_bounds_without_task_metadata(self):
        model = copy.deepcopy(json.loads((ROOT / 'site/data.json').read_bytes())['models'][0])
        summary = {'selected': 9, 'reviewed': 8, 'delivery_failed': 0, 'pending': 1, 'settled': False,
                   'full_count': {'lower': 8, 'upper': 9, 'exact': None},
                   'full_rate': {'lower': 8 / 9, 'upper': 1, 'exact': None}}
        model['neutral_revision_completion'] = {**summary, 'private_cases': ['not-for-browser']}
        original = copy.deepcopy(model)
        projected = model_view(model)
        self.assertEqual(projected['neutral_revision_completion'], summary)
        self.assertNotIn('not-for-browser', json.dumps(projected))
        self.assertEqual(model, original)

    def test_each_recorded_model_retains_operational_evidence_without_homepage_anchor(self):
        document, attempts = load_public(ROOT), load_attempts(ROOT)
        ids = {row['model_id'] for row in document['rows']} | set(attempts['models'])
        self.assertIn('gemini-4-carbon-high', ids)
        for model_id in ids:
            with self.subTest(model=model_id):
                page = render_model_details(document, model_id, root=ROOT, attempt_reference=attempts)
                self.assertIn('docs/execution-anomalies.md', page)
                self.assertIn('downloads/execution-anomalies.json', page)
                self.assertNotIn('index.html#execution-anomalies', page)

    def test_home_includes_initial_runs_continuations_and_the_historical_sample(self):
        data = json.loads((ROOT / 'site/versions/1.1.0/data.json').read_bytes())
        current = json.loads((ROOT / 'site/data.json').read_bytes())
        resources = [model['revision_resources'] for model in current['models']]
        page = render(data, anomaly_reference=load_public(ROOT), attempt_reference=load_attempts(ROOT),
                      continuation_resources=resources, source_root=ROOT)
        self.assertIn('id="assessment-guide"', page)
        self.assertIn('id="category-leaderboards"', page)
        self.assertIn('id="downloads"', page)
        self.assertNotIn('score-structure', page)
        self.assertEqual(page.count('id="execution-anomalies"'), 1)
        self.assertIn('run-history-snapshot', page)
        self.assertIn('downloads/execution-anomalies.json', page)
        self.assertEqual(page.count('data-run-phase="initial"'), len(data['models']))
        self.assertEqual(page.count('data-run-phase="continuation"'), len(resources))

        def counts(phase, model_id):
            row = re.search(f'<tr data-run-phase="{phase}" data-run-model="{re.escape(model_id)}">(.*?)</tr>', page)
            self.assertIsNotNone(row)
            return re.findall(r'<td class="numeric">([^<]+)</td>', row[1])

        self.assertEqual(counts('initial', 'gemini-4-carbon-high'), ['62', '51', '9', '11'])
        self.assertEqual(counts('initial', 'astra-6.2-max'), ['45', '42', '0', '3'])
        self.assertEqual(counts('initial', 'dot-underlying-model-20261108'), ['—', '—', '—', '—'])
        self.assertEqual(counts('continuation', 'astra-6-max'), ['7', '6', '0', '1'])
        self.assertNotIn('@@MG_', page)


if __name__ == '__main__':
    unittest.main()
