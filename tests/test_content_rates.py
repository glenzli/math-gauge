"""Supplemental rates distinguish supported claims, target delivery and unknowns."""
import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from math_gauge.content_rates import project_rates, validate_public_rates, verify_sources
from math_gauge.records import load_content_rates
from math_gauge.scoring import score_content_rates

ROOT = Path(__file__).resolve().parents[1]


class ContentRateTests(unittest.TestCase):
    def fixture(self):
        policy = json.loads((ROOT / 'protocol/scoring-policy.json').read_bytes())
        descriptor = dict(repository='public', path='source.json', sha256='a' * 64)
        unit = dict(id='goal', label='A required mathematical target', delivery_weight=1,
            claim_weight=1, fulfillment='complete', aligned=True, assertion='correct',
            asserted_scope='the required target', reason='Verified original argument',
            evidence=[dict(descriptor, pointer='')])
        tasks = []
        for child in policy['subcategories']:
            if child['id'] == 'lean-selfcheck':
                continue
            count = child['public_tasks'] + child['private_tasks']
            for index in range(count):
                family = max(0, index - (count - child['families']))
                cid = child['id'] + '-' + str(index)
                tasks.append(dict(id=cid + ':A1', case_id=cid, subcategory=child['id'],
                    family_id=child['id'] + '-family-' + str(family), kind='initial',
                    measured=True, units=[copy.deepcopy(unit)]))
        chapter = next(t for t in tasks if t['subcategory'] == 'lean-formalization')
        child = next(c for c in policy['subcategories'] if c['id'] == 'lean-selfcheck')
        for index in range(3):
            tasks.append(dict(id='chapter:R' + str(index + 1), case_id=child['reuses_case_id'],
                subcategory='lean-selfcheck', family_id=chapter['family_id'], kind='selfcheck',
                measured=True, units=[copy.deepcopy(unit)]))
        review = dict(schema='math-gauge.content-rate-review/v1', version='0.1.0',
            benchmark_version='0.6.0', condition='nonlogical_retry_3', model_id='synthetic-model',
            reviewer_kind='ai', human_review='pending', formal_comparison_eligible=False,
            new_candidate_calls=0, assessment_policy_sha256='a' * 64,
            source_bindings={key: 'a' * 64 for key in ('record_sha256', 'assessment_result_sha256',
                'assessment_policy_sha256', 'method_policy_sha256')}, sources=[descriptor], tasks=tasks)
        return review, policy

    def test_honest_partial_scope_is_reliable_without_full_target_delivery(self):
        review, policy = self.fixture()
        task = review['tasks'][0]
        other = copy.deepcopy(task['units'][0])
        other.update(id='not-delivered', fulfillment='omitted', assertion='none', asserted_scope=None)
        task['units'].append(other)
        result = score_content_rates(review, policy)
        self.assertEqual(result['metrics']['reliability']['exact'], 100)
        self.assertAlmostEqual(result['categories']['written-argument']['delivery']['exact'], 100 * 11.5 / 12)
        other['assertion'] = 'unsupported'
        claimed = score_content_rates(review, policy)
        self.assertEqual(claimed['metrics']['delivery'], result['metrics']['delivery'])
        self.assertLess(claimed['metrics']['reliability']['exact'], 100)

    def test_valid_target_with_false_extra_and_wrong_alignment_are_distinct(self):
        review, policy = self.fixture()
        target = review['tasks'][0]['units'][0]
        extra = dict(copy.deepcopy(target), id='extra', delivery_weight=0,
                     assertion='incorrect', fulfillment='omitted')
        review['tasks'][0]['units'].append(extra)
        result = score_content_rates(review, policy)
        self.assertEqual(result['metrics']['delivery']['exact'], 100)
        self.assertLess(result['metrics']['reliability']['exact'], 100)
        target['aligned'] = False
        narrowed = score_content_rates(review, policy)
        self.assertEqual(narrowed['metrics']['reliability'], result['metrics']['reliability'])
        self.assertLess(narrowed['metrics']['delivery']['exact'], 100)

    def test_variants_average_before_families_and_all_selfcheck_rounds_count(self):
        review, policy = self.fixture()
        formal = [t for t in review['tasks'] if t['subcategory'] == 'lean-formalization']
        formal[-1]['units'][0].update(fulfillment='omitted', assertion='none')
        rounds = [t for t in review['tasks'] if t['kind'] == 'selfcheck']
        rounds[0]['units'][0].update(fulfillment='partial', assertion='correct')
        result = score_content_rates(review, policy)
        self.assertEqual(result['categories']['lean-formalization']['delivery']['exact'], 50)
        self.assertAlmostEqual(result['categories']['lean-selfcheck']['delivery']['exact'], 200 / 3)

    def test_unrun_tasks_retain_denominators_and_possible_claims(self):
        review, policy = self.fixture()
        for task in review['tasks']:
            if task['subcategory'] in ('background-check', 'theorem-extension', 'manuscript-completion'):
                task['measured'] = False
                task['units'][0].update(fulfillment='unknown', aligned=None,
                                        assertion='unknown', asserted_scope=None)
        result = score_content_rates(review, policy)
        delivery, reliability = result['metrics']['delivery'], result['metrics']['reliability']
        self.assertEqual((delivery['confirmed'], delivery['upper'], delivery['exact']), (70, 100, None))
        self.assertEqual((reliability['observed'], reliability['lower'], reliability['upper'], reliability['exact']),
                         (100, 70, 100, None))
        for task in review['tasks']:
            if task['measured']:
                for unit in task['units']:
                    unit['assertion'] = 'none'
                    unit['asserted_scope'] = None
        self.assertIsNone(score_content_rates(review, policy)['metrics']['reliability']['observed'])

    def test_public_projection_omits_private_rows_and_rejects_nested_leaks(self):
        review, policy = self.fixture()
        result = score_content_rates(review, policy)
        result['sources'] = [{'private_case': 'PRIVATE-SECRET'}]
        result['tasks'][0]['reason'] = 'PRIVATE-SECRET'
        public = project_rates(result)
        self.assertNotIn('PRIVATE-SECRET', json.dumps(public))
        self.assertNotIn('tasks', public)
        public['categories']['written-argument']['coverage']['PRIVATE-SECRET'] = 1
        with self.assertRaises(ValueError):
            validate_public_rates(public)

    def test_source_binding_rejects_mutation_and_path_escape(self):
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            public, private = base / 'public', base / 'private'
            public.mkdir(); private.mkdir()
            source = public / 'source.json'
            source.write_text('original')
            item = dict(repository='public', path='source.json', sha256=hashlib.sha256(source.read_bytes()).hexdigest())
            review = {'sources': [item], 'tasks': []}
            self.assertEqual(len(verify_sources(review, {'public': public, 'private': private})), 1)
            source.write_text('mutated')
            with self.assertRaises(ValueError):
                verify_sources(review, {'public': public, 'private': private})
            item['path'] = '../private/source.json'
            with self.assertRaises(ValueError):
                verify_sources(review, {'public': public, 'private': private})

    def test_rate_sidecar_is_portable_and_rejects_another_source_score(self):
        review, policy = self.fixture()
        report = project_rates(score_content_rates(review, policy))
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory) / report['model_id'] / 'record'
            folder.mkdir(parents=True)
            def write(name, value):
                path = folder / name
                path.write_text(json.dumps(value))
                return dict(path=name, bytes=path.stat().st_size,
                            sha256=hashlib.sha256(path.read_bytes()).hexdigest())
            score = write('score.json', {'retained': True})
            assessment = write('assessment.json', policy)
            method = write('content-rate-policy.json', {'version': '0.1.0'})
            record = {'assessment_results': {'nonlogical_retry_3': score}, 'assessment_policy': assessment}
            descriptor = write('record.json', record)
            report['source_bindings'].update(record_sha256=descriptor['sha256'],
                assessment_result_sha256=score['sha256'], assessment_policy_sha256=assessment['sha256'],
                method_policy_sha256=method['sha256'])
            report['assessment_policy_sha256'] = assessment['sha256']
            write('content-rates.json', report)
            self.assertEqual(load_content_rates(folder), report)
            write('score.json', {'retained': False})
            with self.assertRaises(ValueError):
                load_content_rates(folder)


if __name__ == '__main__':
    unittest.main()
