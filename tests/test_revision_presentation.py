"""Continuation display preserves edition, resource and publication boundaries."""
import copy
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from scripts.results_editions import _neutral_payload, _neutral_baseline
from scripts.results_eligibility import eligibility
from scripts.results_rankings import category_rankings
from scripts.results_revision_resources import combine_costs, combine_durations, load_public, INDEX_PATH
from math_gauge.records import evidence_bytes
from scripts.timing_reference import revision_reference, CASE_IDS, DAILY_IDS

ORIGINAL_RESOURCES = dict(path='results/continuation-resources/v0.1.0/current.json',
    bytes=7411, sha256='d233c5f1dd07b642402a115024a7893fe8a0d3388d5ed3f38577349fbb08d768')


class RevisionPresentationTests(unittest.TestCase):
    def test_initial_admission_display_keeps_exact_archived_delta_parent(self):
        from math_gauge.current_assessment_admissions import project_score
        modes, conditions = ('capability','partial','strict'), ('single_attempt','nonlogical_retry_3')
        source = {mode: {condition: dict(benchmark_version='0.6.0', score_mode=mode,
            attempt_condition=condition, source_bindings=dict(private_report_sha256='a'*64))
            for condition in conditions} for mode in modes}
        displayed = {mode: {condition: project_score(report) for condition, report in refs.items()}
                     for mode, refs in source.items()}
        model = dict(initial_assessment={'assessment_kind':'initial'},
            combined=displayed['partial']['single_attempt'],
            retry=dict(combined=displayed['partial']['nonlogical_retry_3']),
            capability=displayed['capability'], strict=displayed['strict'])
        adoption = dict(base_reports={mode: {condition: dict(report=report)
            for condition, report in refs.items()} for mode, refs in source.items()})
        with patch('math_gauge.neutral_revision.document', side_effect=lambda root, ref: ref['report']):
            self.assertEqual(_neutral_baseline(Path('.'), model, adoption), source)
            self.assertEqual(model['combined']['benchmark_version'], '1.1.0')
            model['strict']['nonlogical_retry_3']['source_bindings']['private_report_sha256']='b'*64
            with self.assertRaisesRegex(ValueError,'authenticated original'):
                _neutral_baseline(Path('.'), model, adoption)

    def test_unknown_base_duration_stays_unknown_after_complete_revision(self):
        base = dict(candidate_execution_seconds=None, known_candidate_execution_seconds=200,
                    timed_calls=27, planned_calls=42)
        revision = dict(candidate_execution_seconds=100, known_candidate_execution_seconds=100,
                        timed_calls=9, planned_calls=9)
        combined = combine_durations(base, revision)
        self.assertIsNone(combined['candidate_execution_seconds'])
        self.assertEqual(combined['known_candidate_execution_seconds'], 300)
        self.assertEqual(combined['timed_calls'], 36)

    def test_full_cost_is_added_and_existing_estimate_is_retained(self):
        base = dict(status='estimated', total_usd=10, known_usd=4, estimate_range_usd=[8, 12])
        revision = dict(status='observed', total_usd=6, known_usd=6, estimate_range_usd=None)
        self.assertEqual(combine_costs(base, revision), dict(status='estimated', total_usd=16,
            known_usd=10, estimate_range_usd=[14, 18]))
        base['total_usd'] = None
        self.assertIsNone(combine_costs(base, revision)['total_usd'])
        self.assertEqual(combine_costs(base, revision)['status'], 'partial')

    def test_publication_exclusion_is_explicit_and_independent_of_score(self):
        def model(mid, value):
            metric = dict(exact=value, confirmed=value, lower=value, upper=value,
                          coverage={'adjudicated': 1}, complete=True)
            return {'id': mid, 'presentation_eligibility': eligibility(mid),
                    'scores': {mode: {'metrics': {'written': metric}} for mode in ('capability','partial','strict')}}
        models = [model('glm-5.3-max', 100), model('executed-failure', 0)]
        before = copy.deepcopy(models)
        board = category_rankings(models, [{'id':'written','title':'Written','weight':35}],
                                  result_selector=lambda model, mode: model['scores'][mode])[0]
        self.assertEqual([row['model_id'] for row in board['views']['partial']], ['executed-failure'])
        self.assertEqual(board['views']['partial'][0]['value'], 0)
        self.assertEqual(models, before)

    def test_pending_model_does_not_inherit_first_answer_score(self):
        base = {'benchmark_version':'1.1.0', 'model':{'id':'pending'}, 'cases':[]}
        result = _neutral_payload('models/pending/index.html', base,
            {'models':[], 'pending_models':[{'id':'pending'}], 'partial_models':[]}, {})
        self.assertTrue(result['edition_unavailable'])
        self.assertEqual(result['edition_fallback'], '1.1.0')
        self.assertNotIn('model', result)

    def test_typical_task_clock_adds_actual_revision_without_score_weight(self):
        rows = [dict(case_id=cid, seconds=60, strict_pass=True, delivery_status='delivered') for cid in CASE_IDS]
        base = {'models':[{'id':'fixture','rows':rows}], 'daily_weights':{cid:1 for cid in DAILY_IDS}}
        resource = {'id':'fixture', 'public_cases':[{'case_id':'MG-TX001','seconds':120}]}
        with patch('scripts.results_revision_resources.load_public', return_value={'models':[resource], 'batch_span_seconds':200}):
            result = revision_reference(Path('.'), {'models':[{'id':'fixture'}]}, base)
        model = result['models'][0]
        self.assertEqual(next(row for row in model['rows'] if row['case_id']=='MG-TX001')['seconds'], 180)
        self.assertEqual(model['summaries']['daily']['weighted_mean_seconds'], 84)
        self.assertEqual(base['models'][0]['rows'][3]['seconds'], 60)

    def test_retained_resource_projection_has_no_private_task_rows_or_paths(self):
        root = Path(__file__).resolve().parents[1]
        original = json.loads(evidence_bytes(root, ORIGINAL_RESOURCES))
        self.assertEqual((original['new_calls'], original['reused_calls'], original['selected_calls']), (19,3,22))
        resource = load_public(root)
        if (root / INDEX_PATH).is_file():
            index = json.loads((root / INDEX_PATH).read_bytes())
            documents = [json.loads(evidence_bytes(root, item)) for item in index['sources']]
            identities = [row['id'] for document in documents for row in document['models']]
            self.assertEqual(len(identities), len(set(identities)))
            self.assertEqual({row['id'] for row in resource['models']}, set(identities))
            self.assertEqual(resource['selected_calls'], sum(item['selected_calls'] for item in documents))
        else:
            self.assertEqual(resource, original)
        self.assertFalse(resource['score_weight_applied_to_resources'])
        self.assertFalse(resource['review_calls_included'])
        serialized = json.dumps(resource)
        for private in ('MG-TXP', 'MG-MCP001', 'MG-MCP002', 'MG-MCP005', '/Users/', '/private/', 'math-gauge-private'):
            self.assertNotIn(private, serialized)
        terra = next(model for model in original['models'] if model['id']=='terra-6.1-max')
        self.assertIsNone(terra['base']['candidate_execution_seconds'])
        self.assertIsNone(terra['combined']['candidate_execution_seconds'])
        self.assertEqual(terra['revision']['timed_calls'], terra['revision']['planned_calls'])


if __name__ == '__main__':
    unittest.main()
