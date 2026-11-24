"""Independent research cost scope and privacy fixtures with no model execution."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from math_gauge import independent_research_adoption as adoption
from math_gauge import independent_research_execution as execution
from scripts import results_independent_research_resources as resources
from scripts.cost_reference import independent_research_reference, render_panel

PRICE_ID = 'fixture-price'
PRICES = {PRICE_ID: {'id': PRICE_ID, 'rates_per_million': {'input': 2, 'cached_input': 0.5,
                                                          'cache_write': 3, 'output': 9}}}
PRIVATE_MARKER = 'SYNTHETIC-PRIVATE-RESOURCE-MARKER'


def tokens(input_count=0, cached=0, written=0, output=0, reasoning=0):
    return {'inputTokens': input_count, 'cachedInputTokens': cached, 'cacheWriteInputTokens': written,
            'outputTokens': output, 'reasoningOutputTokens': reasoning, 'totalTokens': input_count + output}


class NativeUsageTests(unittest.TestCase):
    def test_same_session_deltas_ignore_duplicates_and_retain_cache_discount(self):
        first = tokens(10, 5, 0, 2, 1)
        second = tokens(30, 21, 1, 7, 3)
        third = tokens(42, 27, 2, 11, 5)
        fourth = tokens(48, 31, 3, 12, 5)
        initial = dict(total=first, last=first)
        next_round = dict(total=second, last=tokens(20, 16, 1, 5, 2))
        result = resources.summarize_usage([[initial], [initial, next_round, next_round],
            [dict(total=third, last=tokens(12, 6, 1, 4, 2)), dict(total=fourth, last=tokens(6, 4, 1, 1))]],
            PRICE_ID, PRICES)
        self.assertEqual(result['coverage'], dict(planned=3, complete=3, partial=0, missing=0, not_run=0))
        self.assertEqual(result['tokens'], {'uncached_input_tokens': 14, 'cached_input_tokens': 31,
            'cache_write_input_tokens': 3, 'output_tokens': 12, 'reasoning_output_tokens': 5, 'total_tokens': 60})
        self.assertAlmostEqual(result['total_usd'], (14 * 2 + 31 * 0.5 + 3 * 3 + 12 * 9) / 1_000_000)

    def test_missing_counters_keep_known_usage_and_zero_is_observed(self):
        zero = dict(total=tokens(), last=tokens())
        empty = resources.summarize_usage([[zero], [zero], [zero]], PRICE_ID, PRICES)
        self.assertEqual(empty['status'], 'observed')
        self.assertEqual(empty['total_usd'], 0)
        self.assertEqual(empty['tokens']['total_tokens'], 0)
        missing = dict(total=tokens(12, 4, 0, 3), last={'outputTokens': 3})
        known = dict(total=tokens(20, 6, 0, 7), last=tokens(8, 2, 0, 4))
        result = resources.summarize_usage([[zero], [missing], [known]], PRICE_ID, PRICES)
        self.assertEqual(result['coverage'], dict(planned=3, complete=2, partial=0, missing=1, not_run=0))
        self.assertIsNone(result['total_usd'])
        self.assertIsNone(result['tokens'])
        self.assertEqual(result['known_tokens']['total_tokens'], 12)
        self.assertAlmostEqual(result['known_usd'], 49 / 1_000_000)

    def test_unreconciled_cumulative_receipt_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'does not reconcile'):
            resources.summarize_usage([[dict(total=tokens(10, 5, 0, 2), last=tokens(9, 5, 0, 2))]],
                                      PRICE_ID, PRICES)


class PublicResourceTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        root = Path(temp.name)
        self.public, self.archive = root / 'public', root / PRIVATE_MARKER
        self.checkpoint = self.archive / 'checkpoint.json'
        self.cost_index = self.archive / 'cost-index.json'
        self.mid = 'fixture-measured'
        self.adopted = {'schema': adoption.SCHEMA, 'edition': '1.3.0', 'kind': adoption.KIND,
            'source_binding': {'edition': '1.2.0', 'path': 'site/data.json', 'sha256': 'a' * 64},
            'policy_sha256': 'b' * 64, 'review_policy_sha256': 'c' * 64, 'batch_sha256': 'd' * 64,
            'planned_cohort': [self.mid], 'cohort': [self.mid], 'reviewer': adoption.REVIEWER,
            'models': {self.mid: {'status': 'reviewed', 'axes': {axis: {'score': 0, 'strict': False}
                for axis in ('autonomy', 'taste', 'capacity')}, 'normal_rounds': 3, 'round_dispatches': 3,
                'source_sha256': 'e' * 64}}, 'native_round_dispatches': 3, 'candidate_calls_by_adoption': 0}
        selected = self.save(self.public, resources.ADOPTION_PATH, self.adopted)
        self.freeze_archive(selected)
        price_file = self.save(self.archive, 'prices.json', {'prices': list(PRICES.values())})
        self.save(self.archive, self.cost_index.name, {'selected': price_file['path'], 'sha256': price_file['sha256']})

    def save(self, root, name, value):
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        raw = value if isinstance(value, bytes) else json.dumps(value).encode()
        path.write_bytes(raw)
        return {'path': name, 'sha256': hashlib.sha256(raw).hexdigest(), 'bytes': len(raw)}

    def freeze_archive(self, selected):
        replay = self.archive / 'replay'
        control = f'control/{self.mid}'
        app = {'model_id': self.mid, 'origin': execution.NATIVE_ORIGIN, 'outcome': 'normal-finals',
            'native_context_id': PRIVATE_MARKER, 'requested_model': 'fixture-model', 'requested_effort': 'max',
            'plan_sha256': self.adopted['batch_sha256'], 'registration_sha256': 'f' * 64, 'rounds': []}
        descriptors = {}
        for index, rid in enumerate(resources.ROUNDS, 1):
            turn = f'fixture-turn-{index}'
            request = execution.turn_request(100 + index, PRIVATE_MARKER, 'fixture-model', 'max', PRIVATE_MARKER)
            lines = [{"id": request['id'], "result": {"turn": {"id": turn}}}]
            params = {'threadId': PRIVATE_MARKER, 'turnId': turn}
            lines.extend([
                {'method': 'thread/tokenUsage/updated', 'params': {**params, 'tokenUsage':
                    dict(total=tokens(10 * index, output=2 * index), last=tokens(10, output=2))}},
                {'method': 'item/completed', 'params': {**params, 'item': {'type': 'agentMessage',
                    'phase': 'final_answer', 'text': PRIVATE_MARKER}}},
                {'method': 'turn/completed', 'params': {**params, 'turn': {'id': turn, 'status': 'completed'}}},
            ])
            raw = b''.join(execution.json_bytes(line) for line in lines)
            refs = (self.save(replay, f'{control}/{rid}.request.ndjson', request),
                    self.save(replay, f'{control}/{rid}.native.ndjson', raw))
            descriptors.update((ref['path'], ref) for ref in refs)
            entry = execution.parse_turn(request, raw.splitlines(), cutoff='native-terminal')
            entry.pop('final')
            app['rounds'].append(dict(entry, round=rid, cutoff='native-terminal', request=refs[0], wire_events=refs[1]))
        registered = self.save(replay, f'{control}/execution.json', app)
        descriptors[registered['path']] = registered
        self.save(self.archive, f'configurations/{self.mid}.json', {'model': self.mid, 'outcome': 'normal-finals',
            'execution_validation': 'passed-at-original-run-root', 'physical_round_requests': 3,
            'execution': registered, 'files': descriptors})
        summary = self.save(replay, 'batch-summary.json', {'origin': app['origin'], 'plan_sha256': app['plan_sha256'],
            'registration_sha256': app['registration_sha256'], 'cohort': [{'model_id': self.mid,
                'outcome': app['outcome'], 'execution': registered}]})
        self.save(self.archive, 'batch.json', {'files': {'batch-summary.json': summary}})
        self.save(self.archive, self.checkpoint.name, {'configurations': [self.mid],
            'files': {registered['path']: registered}, 'checkpoint_files': {
                f'repositories/public/{resources.ADOPTION_PATH}': selected}})

    def prepare(self):
        with patch.object(resources, 'load_base_resources', return_value={'models': [{'id': self.mid,
            'revision': {'price_id': PRICE_ID, 'rates_per_million': PRICES[PRICE_ID]['rates_per_million']}}]}):
            return resources.build_public(self.public, self.archive, self.checkpoint, self.cost_index)

    def test_public_projection_keeps_only_totals_and_compares_complete_scores(self):
        aggregate = self.prepare()
        self.save(self.public, resources.DATA_PATH, aggregate)
        resource = aggregate['models'][self.mid]
        self.assertEqual(resource['tokens']['total_tokens'], 36)
        def score(value, exact):
            return {'metrics': {'earned': {'confirmed': value}, 'overall': {
                'exact': value if exact else None, 'lower': value, 'upper': value if exact else value + 10}}}
        def model(mid, value, exact):
            report = score(value, exact)
            return {'id': mid, 'retry': {'combined': report}, 'strict': {'nonlogical_retry_3': report},
                    'capability': {'nonlogical_retry_3': report}}
        pending = 'fixture-pending'
        delivery = {'planned': 39, 'active_final': 39, 'complete': True}
        base = {'benchmark_version': '1.2.0', 'models': [dict(model_id=mid, total_usd=7, known_usd=7,
            status='observed', answer_delivery=delivery, coverage=dict(planned=42, complete=42,
                partial=0, missing=0, not_run=0), seconds=55, scores={}) for mid in (self.mid, pending)]}
        display = {'benchmark_version': '1.3.0', 'models': [model(self.mid, 0, True), model(pending, 83, False)]}
        shown = independent_research_reference(self.public, display, base, adoption=self.adopted)
        measured, unmeasured = shown['models']
        self.assertAlmostEqual(measured['total_usd'], 7 + resource['total_usd'])
        self.assertEqual(measured['coverage']['complete'], 45)
        self.assertEqual(measured['scores']['strict'], {'value': 0, 'complete': True, 'lower': 0, 'upper': 0})
        self.assertEqual(unmeasured['scores']['strict'], {'value': 83, 'complete': False, 'lower': 83, 'upper': 93})
        self.assertIsNone(unmeasured['total_usd'])
        self.assertEqual(unmeasured['known_usd'], 7)
        self.assertEqual(unmeasured['coverage']['not_run'], 3)
        self.assertEqual(shown['frontiers']['strict'], {'cost': [self.mid], 'time': [self.mid]})
        self.assertIsNone(shown['review_overhead']['total_usd'])
        self.assertEqual([r['seconds'] for r in shown['models']], [55, 55])
        self.assertEqual([r['answer_delivery'] for r in shown['models']], [delivery, delivery])
        self.assertEqual(base['models'][0]['total_usd'], 7)
        for document in (json.dumps(aggregate), json.dumps(shown), render_panel(shown)):
            self.assertNotIn(PRIVATE_MARKER, document)
            self.assertNotIn('native.ndjson', document)
            self.assertIn('"total_tokens": 36', document)

    def test_archive_tampering_and_public_extra_fields_are_rejected(self):
        value = self.prepare()
        resource = value['models'][self.mid]
        resource['private_path'] = PRIVATE_MARKER
        self.save(self.public, resources.DATA_PATH, value)
        with self.assertRaisesRegex(ValueError, 'Unexpected resource row fields'):
            resources.load_public(self.public, self.adopted)
        events = self.archive / 'replay' / 'control' / self.mid / 'R1.native.ndjson'
        events.write_bytes(events.read_bytes() + b'\n')
        with self.assertRaisesRegex(ValueError, 'differs from its retained descriptor'):
            self.prepare()
