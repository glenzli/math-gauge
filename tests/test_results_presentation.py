"""Browser projections retain source arithmetic, denominators and unknown bounds."""
import copy
import json
from pathlib import Path
import unittest

from scripts.results_presentation import project_payload

ROOT = Path(__file__).resolve().parents[1]


class BrowserProjectionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.archive = json.loads((ROOT / 'site/data.json').read_bytes())

    def assert_views(self, view, original, model_page=False):
        pairs = [(view['combined'], original['combined']),
                 (view['retry']['combined'], original['retry']['combined'])]
        for mode in ('capability', 'strict'):
            pairs.extend((view[mode][condition], result) for condition, result in original[mode].items())
        for actual, expected in pairs:
            self.assertEqual(actual['metrics']['earned'], expected['metrics']['earned'])
            self.assertEqual(actual['contributions'], expected['contributions'])
            if model_page:
                for name in ('overall', 'lean-selfcheck'):
                    self.assertEqual(actual['metrics'][name], expected['metrics'][name])

    def test_every_model_mode_and_condition_copies_values_and_fixed_denominators(self):
        home = project_payload(self.archive)
        self.assertEqual(home['schema'], 'math-gauge.browser-presentation/v1')
        self.assertEqual(home['source_schema'], self.archive['schema'])
        for model, original in zip(home['models'], self.archive['models']):
            self.assert_views(model, original)
            self.assertEqual(model['evaluation_progress'], original['evaluation_progress'])
            detailed = {**self.archive, 'model': {**original, 'public_claims': {
                condition: [] for condition in self.archive['attempt_conditions']}}, 'cases': []}
            projected = project_payload(detailed)['model']
            self.assert_views(projected, original, model_page=True)
            for condition in self.archive['attempt_conditions']:
                self.assertEqual(projected['strict'][condition]['strict_alignment_selfcheck'],
                    {'strict_pass': original['strict'][condition]['strict_alignment_selfcheck']['strict_pass']})
        self.assertEqual([row['views'] for row in home['category_leaderboards']],
                         [row['views'] for row in self.archive['category_leaderboards']])

    def test_unknown_interval_and_known_zero_remain_distinct(self):
        original = copy.deepcopy(self.archive['models'][0])
        # This contract must remain testable when every retained model is measured.
        original['retry']['combined']['metrics']['overall'].update(lower=.1, upper=.9, exact=None)
        data = {**self.archive, 'model': {**original, 'public_claims': {
            condition: [] for condition in self.archive['attempt_conditions']}}, 'cases': []}
        result = project_payload(data)['model']['retry']['combined']
        self.assertIsNone(result['metrics']['overall']['exact'])
        self.assertLess(result['metrics']['overall']['lower'], result['metrics']['overall']['upper'])
        data['model']['retry']['combined']['metrics']['earned'].update(exact=0, confirmed=0, lower=0, upper=0)
        result = project_payload(data)['model']['retry']['combined']
        self.assertEqual(result['metrics']['earned']['confirmed'], 0)
        self.assertIsNone(result['metrics']['overall']['exact'])

    def test_unused_archive_metadata_does_not_enter_or_mutate_browser_payload(self):
        data = copy.deepcopy(self.archive)
        data['sources'] = ['private-fixture-do-not-project']
        data['models'][0]['combined']['raw_evaluator_fixture'] = 'private-fixture-do-not-project'
        before = copy.deepcopy(data)
        projected = project_payload(data)
        self.assertEqual(data, before)
        self.assertNotIn('private-fixture-do-not-project', json.dumps(projected))
        self.assertLess(len(json.dumps(projected)), len(json.dumps(data)) / 5)

    def test_public_case_view_keeps_partial_unknown_and_strict_separate(self):
        value = {'completion': {'exact': None, 'lower': 0, 'upper': 1},
                 'strict_pass': None, 'response_sha256': 'evidence-byte-hash'}
        data = {**self.archive, 'model': {'id': 'fixture', 'label': 'Fixture'},
                'case': {'id': 'case', 'title': 'Case', 'category': 'proofs',
                         'views': {'partial': {'nonlogical_retry_3': value}}}}
        case = project_payload(data)['case']['views']['partial']['nonlogical_retry_3']
        self.assertEqual(case, {'completion': value['completion'], 'strict_pass': None,
                                'response_sha256': 'evidence-byte-hash'})


if __name__ == '__main__':
    unittest.main()
