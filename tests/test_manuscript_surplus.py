"""Descriptive result counts, unchanged review evidence and public/private boundaries."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

from math_gauge.manuscript_surplus import (
    REVIEW_SCHEMA, descriptor, public_projection, validate_review, validate_sources, validate_observation_policy,
    REVIEW_ROOT_PATH, ROOT_PATH, check_pair, prepare_reuse_binding, validate_reuse_binding,
    validate_context_rebinding,
)
from math_gauge.scoring import summarize_manuscript_observations

ROOT = Path(__file__).resolve().parents[1]


class ManuscriptObservationTests(unittest.TestCase):
    def observation_policy(self):
        return json.loads((ROOT / 'protocol/manuscript-observations-policy.json').read_bytes())

    def result(self, review, source_policy):
        return summarize_manuscript_observations(review, source_policy, self.observation_policy())

    def fixture(self):
        observation_policy = self.observation_policy()
        policy = {key: copy.deepcopy(observation_policy[key]) for key in
                  ('version', 'scope', 'selection', 'main_scores_modified', 'original_completion_gate', 'accepted_gates')}
        policy['accepted_gates']['value'] = 'high'  # Frozen review label, not a current counting gate.
        policy.update(schema='math-gauge.manuscript-surplus-policy/v1',
                      excluded_scope=['required', 'necessary_auxiliary', 'direct_corollary', 'equivalent_rewrite', 'unrelated'],
                      statuses=['reviewed', 'not_run', 'delivery_failed', 'unresolved'])
        candidate = dict(id='result', group_id='one-result', title='Additional structural theorem',
            statement='A complete additional theorem with its original assumptions', scope='beyond_required',
            correctness='proved', nontrivial=True, value='high', independent_of_errors=True,
            scope_delta='Beyond the original complete goal', proof_review='Proof closes the additional theorem',
            nontrivial_step='A construction connecting the two structures', value_rationale='Solves an additional problem',
            reason='All reference gates established in the original answer', decision='accepted',
            citations=[{'source': {'path': 'answer.md', 'bytes': 8, 'sha256': 'a' * 64},
                        'start_byte': 0, 'end_byte': 8, 'quote': 'original'}])
        cases = [dict(case_id='MG-MCP003' if i == 0 else f'private-{i}', family_id=f'family-{i}',
            phase='A1', condition='nonlogical_retry_3', status='reviewed', scope_audit='Original required goals fixed',
            response_sha256='a' * 64, documents=[], candidates=[],
            original_task={'strict_pass': False, 'completion': {'exact': 0.5}, 'family_id': f'family-{i}'})
            for i in range(5)]
        cases[0]['candidates'] = [candidate]
        review = dict(schema=REVIEW_SCHEMA, version='0.1.0', model_id='fixture-model', record_id='snapshot',
            reviewer_kind='ai', human_review='pending', post_observation=True, new_candidate_calls=0,
            main_scores_modified=False, cases=cases)
        return review, policy

    def test_all_independent_groups_count_even_when_original_task_failed(self):
        review, policy = self.fixture()
        second = copy.deepcopy(review['cases'][0]['candidates'][0])
        second.update(id='second', group_id='independent-second')
        review['cases'][0]['candidates'].append(second)
        before = copy.deepcopy(review)
        result = self.result(review, policy)
        self.assertEqual(result['counts']['confirmed_groups'], 2)
        self.assertEqual(result['counts']['total_groups'], 2)
        self.assertFalse(result['families'][0]['original_task']['strict_pass'])
        self.assertEqual(review, before)

    def test_metadata_rebinding_preserves_original_math_and_history_bytes(self):
        review, _ = self.fixture()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            retained = {}
            for key in ('source_record', 'source_score', 'source_inputs'):
                path = root/(key+'.json')
                path.write_text(json.dumps({'original':key}))
                retained[key] = descriptor(path, root)
                review[key] = retained[key]
            original = root/'original-review.json'
            original.write_text(json.dumps(review))
            current = copy.deepcopy(review)
            current['record_id'] = 'current-snapshot'
            current['metadata_rebind'] = dict(
                schema='math-gauge.manuscript-observation-context/v1',
                original_review=descriptor(original, root),
                retained_original_context=retained,
                mathematical_judgments_changed=False,new_candidate_calls=0)
            validate_context_rebinding(current,root)
            current['cases'][0]['candidates'][0]['statement'] = 'Changed mathematical claim'
            with self.assertRaisesRegex(ValueError,'changed mathematical review'):
                validate_context_rebinding(current,root)

    def test_equivalent_results_are_deduplicated_within_family(self):
        review, policy = self.fixture()
        duplicate = copy.deepcopy(review['cases'][0]['candidates'][0])
        duplicate['id'] = 'corollary'
        review['cases'][0]['candidates'].append(duplicate)
        result = self.result(review, policy)
        self.assertEqual(result['counts']['confirmed_groups'], 1)
        self.assertEqual(result['counts']['total_groups'], 1)

    def test_one_task_can_deliver_more_groups_than_the_number_of_tasks(self):
        review, policy = self.fixture()
        original = review['cases'][0]['candidates'][0]
        review['cases'][0]['candidates'] = [dict(copy.deepcopy(original), id=f'result-{i}', group_id=f'group-{i}')
                                            for i in range(7)]
        result = self.result(review, policy)
        self.assertEqual(result['counts']['total_groups'], 7)
        self.assertFalse(result['is_score'])
        self.assertIsNone(result['higher_is_better'])

    def test_observation_policy_cannot_imply_higher_is_better_or_a_ceiling(self):
        for key, value in [('higher_is_better', True), ('ceiling', 100),
                           ('is_score', True), ('capability_inference', True)]:
            with self.subTest(key=key):
                policy = self.observation_policy()
                policy[key] = value
                with self.assertRaisesRegex(ValueError, 'capability score or ceiling'):
                    validate_observation_policy(policy)

    def test_unknown_retains_observed_count_without_extrapolation_or_upper_bound(self):
        review, policy = self.fixture()
        review['cases'][1]['status'] = 'not_run'
        result = self.result(review, policy)
        self.assertEqual(result['counts'], {'confirmed_groups': 1, 'total_groups': None, 'unit': 'result_groups'})
        self.assertEqual(result['coverage']['not_run'], 1)
        self.assertNotIn('metrics', result)
        self.assertNotIn('upper', result['counts'])
        for case in review['cases']:
            case.update(status='not_run', candidates=[])
        result = self.result(review, policy)
        self.assertEqual(result['counts'], {'confirmed_groups': 0, 'total_groups': None, 'unit': 'result_groups'})

    def test_delivered_failure_is_known_zero_without_a_mathematical_error(self):
        review, policy = self.fixture()
        review['cases'][0].update(status='delivery_failed', candidates=[])
        result = self.result(review, policy)
        self.assertEqual(result['counts']['total_groups'], 0)
        self.assertEqual(result['coverage']['delivery_failed'], 1)
        self.assertEqual(result['coverage']['not_run'], 0)

    def test_every_mathematical_gate_is_required(self):
        for key, value in [('scope', 'required'), ('scope', 'direct_corollary'),
                           ('correctness', 'unsupported'), ('correctness', 'incorrect'),
                           ('nontrivial', False), ('independent_of_errors', False)]:
            with self.subTest(key=key, value=value):
                review, policy = self.fixture()
                candidate = review['cases'][0]['candidates'][0]
                candidate.update({key: value}, decision='rejected')
                self.assertEqual(self.result(review, policy)['counts']['confirmed_groups'], 0)
                candidate['decision'] = 'accepted'
                with self.assertRaisesRegex(ValueError, 'contradicts'):
                    validate_review(review, policy)

    def test_contextual_value_label_does_not_control_neutral_count(self):
        review, policy = self.fixture()
        candidate = review['cases'][0]['candidates'][0]
        candidate.update(value='moderate', decision='rejected')
        result = self.result(review, policy)
        self.assertEqual(result['counts']['total_groups'], 1)
        self.assertEqual(candidate['decision'], 'rejected')

    def test_pending_groups_keep_known_count_but_leave_total_unknown(self):
        review, policy = self.fixture()
        pending = copy.deepcopy(review['cases'][0]['candidates'][0])
        pending.update(id='pending', group_id='pending', correctness='unresolved', decision='pending')
        review['cases'][0]['candidates'].append(pending)
        with self.assertRaisesRegex(ValueError, 'family unresolved'):
            validate_review(review, policy)
        review['cases'][0]['status'] = 'unresolved'
        result = self.result(review, policy)
        self.assertEqual(result['counts'], {'confirmed_groups': 1, 'total_groups': None, 'unit': 'result_groups'})
        self.assertEqual(result['coverage']['unresolved'], 1)

    def test_no_invitation_or_rescaling_and_no_unrun_fabrication(self):
        review, policy = self.fixture()
        review['cases'][0]['phase'] = 'A2'
        with self.assertRaisesRegex(ValueError, 'retained rule-selected A1'):
            validate_review(review, policy)
        review['cases'][0].update(phase='A1', status='not_run')
        with self.assertRaisesRegex(ValueError, 'Unrun/failed'):
            validate_review(review, policy)
        review['cases'][0]['status'] = 'reviewed'
        policy['scope']['families'] = 1
        with self.assertRaisesRegex(ValueError, 'five manuscript'):
            self.result(review, policy)

    def test_public_projection_whitelists_case_content_and_removes_source_paths(self):
        review, policy = self.fixture()
        candidate = review['cases'][0]['candidates'][0]
        candidate['evaluator_private_notes'] = 'SECRET'
        private = copy.deepcopy(candidate)
        private.update(title='PRIVATE-MATH', group_id='private-group')
        review['cases'][1]['candidates'].append(private)
        result = self.result(review, policy)
        public = public_projection(review, result, self.observation_policy(), public_record={}, policy_source={},
                                   private_review_sha256='b' * 64, private_baseline_sha256='c' * 64)
        text = json.dumps(public)
        for secret in ('PRIVATE-MATH', 'private-1', 'private-group', 'answer.md', 'evaluator_private_notes', 'SECRET'):
            self.assertNotIn(secret, text)
        self.assertEqual(public['counts']['confirmed_groups'], 2)
        self.assertFalse(public['is_score'])
        self.assertIsNone(public['higher_is_better'])
        self.assertNotIn('metrics', public)
        self.assertEqual(len(public['public_cases']), 1)
        self.assertIn('original', text)

    def test_exact_original_utf8_bytes_and_frozen_boundaries_are_enforced(self):
        review, policy = self.fixture()
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            def write(name, raw):
                p = root / name
                p.write_bytes(raw)
                return descriptor(p, root)
            document = write('answer.md', '前提：原文证明。'.encode())
            context = {'cases': {}}
            for key in ('record', 'score', 'inputs'):
                item = write(key + '.json', b'{}')
                review['source_' + key] = item
                context[key] = item
            baseline = {'cases': []}
            for case in review['cases']:
                case.update(documents=[dict(role='response', **document)], response_sha256=document['sha256'])
                context['cases'][case['case_id']] = dict(documents=case['documents'],
                    response_sha256=case['response_sha256'], original_task=case['original_task'], source_status='reviewed')
                baseline['cases'].append({'case_id': case['case_id'], 'family_id': case['family_id'],
                                           'materials': {'task': document}})
            review['policy'] = write('policy.json', json.dumps(policy).encode())
            review['baseline'] = write('baseline.json', json.dumps(baseline).encode())
            citation = review['cases'][0]['candidates'][0]['citations'][0]
            citation.update(source=document, start_byte=len('前提：'.encode()),
                            end_byte=len('前提：原文证明'.encode()), quote='原文证明')
            validate_sources(review, root, context, baseline, policy)
            citation['quote'] = '补写证明'
            with self.assertRaisesRegex(ValueError, 'differs from original'):
                validate_sources(review, root, context, baseline, policy)
            citation['quote'] = '原文证明'
            (root / 'answer.md').write_bytes(b'changed')
            with self.assertRaises(ValueError):
                validate_sources(review, root, context, baseline, policy)

    def reuse_fixture(self, folder):
        public, private = folder / 'public', folder / 'private'
        review, policy = self.fixture()
        review.update(model_id='fixture-model', record_id='old')
        def write(root, name, value):
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(value if isinstance(value, bytes) else json.dumps(value).encode())
            return descriptor(path, root)
        write(public, 'protocol/manuscript-observations-policy.json', self.observation_policy())
        review['policy'] = write(private, 'verification/source-policy.json', policy)
        task = write(private, 'verification/task.txt', b'frozen original task')
        baseline = {'cases': [{'case_id': c['case_id'], 'family_id': c['family_id'], 'materials': {'task': task}}
                              for c in review['cases']]}
        review['baseline'] = write(private, 'verification/baseline.json', baseline)
        for record_id in ('old', 'new'):
            relative = Path('results/v0.6.0/fixture-model') / record_id
            archive = private / relative
            inputs, scores = {'slots': []}, {'tasks': []}
            for index, case in enumerate(review['cases']):
                answer = write(archive, f'{index}-answer.md', b'original answer')
                manuscript = write(archive, f'{index}-manuscript.md', b'delivered source manuscript')
                judgment = write(archive, f'{index}-review.json', {'criterion_points': 50, 'human_review': 'pending'})
                inputs['slots'].append({'case_id': case['case_id'], 'response': answer, 'manuscript': manuscript,
                                       'review': judgment, 'points': 50, 'maximum': 100, 'complete': False})
                scores['tasks'].append({'case_id': case['case_id'], 'subcategory': 'manuscript-completion',
                    'family_id': case['original_task']['family_id'], 'strict_pass': False,
                    'completion': case['original_task']['completion'], 'response_sha256': answer['sha256'],
                    'review_sha256': judgment['sha256']})
                if record_id == 'old':
                    case['documents'] = [{'role': role, **descriptor(archive / item['path'], private)}
                                         for role, item in [('response', answer), ('manuscript', manuscript)]]
                    case['response_sha256'] = answer['sha256']
            record = {'manuscript_completion_inputs': write(archive, 'inputs.json', inputs),
                      'assessment_results': {'nonlogical_retry_3': write(archive, 'retry.json', scores)}}
            write(public, relative / 'record.json', {'model_id': 'fixture-model', 'record_id': record_id})
            item = write(archive, 'record.json', record)
            if record_id == 'old':
                review.update(source_record=descriptor(archive / item['path'], private),
                    source_score=descriptor(archive / 'retry.json', private),
                    source_inputs=descriptor(archive / 'inputs.json', private))
        cite = review['cases'][0]['candidates'][0]['citations'][0]
        document = review['cases'][0]['documents'][0]
        cite.update(source={k: v for k, v in document.items() if k != 'role'},
                    start_byte=0, end_byte=8, quote='original')
        review_path = REVIEW_ROOT_PATH / 'fixture-model/old/review.json'
        write(private, review_path, review)
        return public, private, review_path, write

    def test_reuse_checks_both_contexts_and_preserves_old_review_and_observations(self):
        from unittest.mock import patch
        from scripts.manuscript_observations import run
        from scripts.results_surplus import load_observations
        with tempfile.TemporaryDirectory() as temp:
            public, private, review_path, write = self.reuse_fixture(Path(temp))
            frozen = (private / review_path).read_bytes()
            with patch('scripts.manuscript_observations.summary_report', return_value='fixture summary'):
                run(public, private, write=True)
                old_outputs = {root: (root / ROOT_PATH / 'fixture-model/old/observation.json').read_bytes()
                               for root in (public, private)}
                binding = prepare_reuse_binding(public, private, 'fixture-model', 'old', 'new')
                item = write(private, 'verification/reuse.json', binding)
                run(public, private, write=True, reuse_bindings=[item['path']])
                run(public, private)  # Checked registration survives without an explicit option.
            for root, raw in old_outputs.items():
                self.assertEqual((root / ROOT_PATH / 'fixture-model/old/observation.json').read_bytes(), raw)
            self.assertEqual((private / review_path).read_bytes(), frozen)
            result = check_pair(public, private, 'fixture-model', 'new')
            self.assertEqual((result['record_id'], result['source_review_record_id']), ('new', 'old'))
            text = json.dumps(result)
            for secret in ('private-1', 'private-2', 'verification/reuse.json', '0-manuscript.md'):
                self.assertNotIn(secret, text)
            model = dict(id='fixture-model', source_record=result['source_record']['path'],
                         label='fixture', logo={}, theme={})
            self.assertEqual(len(load_observations(public, [model])['models']), 1)
            model['source_record'] = model['source_record'].replace('/new/', '/old/')
            with self.assertRaisesRegex(ValueError, 'selected main snapshot'):
                load_observations(public, [model])
            (private / review_path).write_bytes(frozen + b' ')
            with self.assertRaisesRegex(ValueError, 'retained contexts'):
                validate_reuse_binding(binding, public, private)

    def test_reuse_rejects_changed_answer_role_or_original_judgment(self):
        for change in ('answer', 'role', 'judgment'):
            with self.subTest(change=change), tempfile.TemporaryDirectory() as temp:
                public, private, _, write = self.reuse_fixture(Path(temp))
                archive = private / 'results/v0.6.0/fixture-model/new'
                record = json.loads((archive / 'record.json').read_bytes())
                inputs = json.loads((archive / 'inputs.json').read_bytes())
                scores = json.loads((archive / 'retry.json').read_bytes())
                original, score = inputs['slots'][0], scores['tasks'][0]
                if change == 'answer':
                    original['response'] = write(archive, 'changed-answer.md', b'a different candidate answer')
                    score['response_sha256'] = original['response']['sha256']
                elif change == 'role':
                    original.pop('manuscript')
                else:
                    original['review'] = write(archive, 'changed-review.json', {'criterion_points': 49})
                    score['review_sha256'] = original['review']['sha256']
                record['manuscript_completion_inputs'] = write(archive, 'inputs.json', inputs)
                record['assessment_results']['nonlogical_retry_3'] = write(archive, 'retry.json', scores)
                write(archive, 'record.json', record)
                with self.assertRaisesRegex(ValueError, 'changed an answer|original mathematical judgment'):
                    prepare_reuse_binding(public, private, 'fixture-model', 'old', 'new')

    def test_observations_use_admitted_manuscripts_after_a_failed_first_attempt(self):
        from unittest.mock import patch
        from math_gauge.manuscript_surplus import source_context
        with tempfile.TemporaryDirectory() as temp:
            public, private, _, write = self.reuse_fixture(Path(temp))
            archive = private / 'results/v0.6.0/fixture-model/new'
            record = json.loads((archive / 'record.json').read_bytes())
            admitted = record['manuscript_completion_inputs']
            first = json.loads((archive / admitted['path']).read_bytes())
            first['slots'][0].update(status='not_available', response=None, manuscript=None)
            record['manuscript_completion_inputs'] = write(archive, 'failed-first-inputs.json', first)
            write(archive, 'record.json', record)
            with self.assertRaisesRegex(ValueError, 'different selected answer'):
                source_context(public, private, 'fixture-model', 'new')
            record['attempt_condition_sources'] = {'path': 'validated-by-source-loader.json'}
            write(archive, 'record.json', record)
            selected = {'bindings': {'manuscript_completion_inputs': admitted}}
            with patch('math_gauge.attempt_conditions.load_sources', return_value=selected) as load:
                context = source_context(public, private, 'fixture-model', 'new')
            load.assert_called_once_with(archive, record, 'nonlogical_retry_3',
                                         public_root=public / 'results/v0.6.0/fixture-model/new')
            self.assertEqual(context['inputs']['sha256'], admitted['sha256'])
            self.assertEqual(context['cases']['MG-MCP003']['source_status'], 'reviewed')
            self.assertEqual(len(context['cases']['MG-MCP003']['documents']), 2)


if __name__ == '__main__':
    unittest.main()
