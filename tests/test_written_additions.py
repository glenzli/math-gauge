"""Synthetic private additions: source isolation, unknowns and shared penalties."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

from math_gauge.benchmarks import validate_assessment_policy
from math_gauge.records import descriptor, load_written_argument_inputs, validate_public_written_additions
from math_gauge.scoring import score_assessment_inputs
from math_gauge.written_additions import validate_inputs
import test_case_selection as legacy_selection
from test_claim_penalties import event

ROOT = Path(__file__).resolve().parents[1]


class WrittenAdditionsTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        legacy_selection.CaseSelectionTests.setUpClass()
        cls.baseline = legacy_selection.CaseSelectionTests()
        cls.policy = json.loads((ROOT / 'protocol/scoring-policy.json').read_bytes())
        cls.strict = json.loads((ROOT / 'protocol/strict-scoring-policy.json').read_bytes())
        cls.claim = json.loads((ROOT / 'protocol/claim-penalty-policy.json').read_bytes())
        cls.capability = json.loads((ROOT / 'protocol/capability-scoring-policy.json').read_bytes())

    def data(self, points=68, complete=False):
        cid = 'SYNTHETIC-PRIVATE-ADDITION'
        return {'schema': 'math-gauge.written-additions-inputs/v1', 'benchmark_version': '0.6.0',
            'model_label': self.baseline.inputs()['model_label'], 'attempt_labels': ['A1'],
            'policy': self.policy['written_argument_additions'], 'human_review': 'pending',
            'formal_comparison_eligible': False, 'case_index': [{'case_id': cid,
                'family_id': 'synthetic-private-written-family', 'component': 'exploration',
                'source_visibility': 'private', 'contract_kind': 'written_proof', 'task_kind': 'written',
                'criteria': [{'criterion_id': 'proof', 'points': 100}], 'total_weight': 100,
                'task_sha256': 'a'*64, 'contract_sha256': 'b'*64}],
            'slots': [{'case_id': cid, 'slot_id': cid+':A1', 'attempt_label': 'A1',
                'status': 'not_run' if points is None else 'response_received_execution_unverified',
                'points': points, 'complete': None if points is None else complete,
                'response': None if points is None else {'sha256': 'c'*64},
                'review': None if points is None else {'sha256': 'd'*64},
                'source_review': None if points is None else {'sha256': 'e'*64}}]}

    def score(self, data, mode='partial', claims=False):
        inputs = self.baseline.inputs()
        review = None
        if claims:
            from math_gauge.case_selection import selected_current_cases
            selected = selected_current_cases({c['case_id']: c for c in inputs['plan']['case_index']}, self.policy['case_selection'])
            rows = [{'case_id': cid, 'status': 'reviewed', 'scope_note': 'Synthetic source evidence.',
                'source_response_sha256': None, 'source_review_sha256': None,
                'sources': [], 'findings': [], 'baseline_disposition': None} for cid in selected]
            r = data['slots'][0]
            rows.append({'case_id': r['case_id'], 'status': 'not_run' if r['points'] is None else 'reviewed',
                'scope_note': 'Synthetic ordinary critical claim, no core cap.', 'sources': [],
                'source_response_sha256': None if r['response'] is None else r['response']['sha256'],
                'source_review_sha256': None if r['review'] is None else r['review']['sha256'],
                'findings': [] if r['points'] is None else [event(severity='critical')], 'baseline_disposition': None})
            review = {'schema': 'math-gauge.claim-review-condition/v1', 'policy_version': '0.1.0',
                'reviewer_kind': 'ai', 'human_review': 'pending', 'formal_comparison_eligible': False,
                'model_label': inputs['model_label'], 'cases': rows}
        return score_assessment_inputs(inputs, self.policy, self.strict, mode=mode,
            written_argument_inputs=data, claim_review=review, claim_policy=self.claim,
            capability_policy=self.capability if mode == 'capability' else None)

    def test_old_plan_is_immutable_and_new_family_uses_twelve_family_denominator(self):
        inputs = self.baseline.inputs()
        original = copy.deepcopy(inputs)
        unknown = self.score(self.data(None))
        known = self.score(self.data())
        self.assertEqual(inputs, original)
        self.assertEqual(known['metrics']['written-argument']['coverage']['planned'], 12)
        self.assertAlmostEqual(known['contributions']['written-argument']['confirmed'] -
            unknown['contributions']['written-argument']['confirmed'], 25*.68/12)
        self.assertEqual(known['capacity']['total'], 100)
        self.assertIsNone(known['metrics']['overall']['exact'])

    def test_shared_mc_rmc_and_strict_preserve_the_original_positive_credit(self):
        results = {mode: self.score(self.data(), mode, claims=True) for mode in ('capability', 'partial', 'strict')}
        task = lambda mode: next(t for t in results[mode]['tasks'] if t['case_id'].startswith('SYNTHETIC-'))
        self.assertEqual(task('capability')['completion']['exact'], .68)
        self.assertEqual(task('partial')['completion']['exact'], .48)
        self.assertFalse(task('strict')['strict_pass'])
        self.assertEqual(self.data()['slots'][0]['points'], 68)

    def test_unrun_is_unknown_and_cannot_claim_zero_or_a_strict_pass(self):
        data = self.data(None)
        result = self.score(data, claims=True)
        task = next(t for t in result['tasks'] if t['case_id'].startswith('SYNTHETIC-'))
        self.assertIsNone(task['completion']['exact'])
        self.assertIsNone(task['strict_pass'])
        for change in ({'points': 0}, {'complete': True}, {'response': {'sha256': 'c'*64}}):
            bad = copy.deepcopy(data); bad['slots'][0].update(change)
            with self.subTest(change=change), self.assertRaises(ValueError):
                validate_inputs(bad, self.policy['written_argument_additions'])

    def test_addition_cannot_replace_an_existing_source_task_or_duplicate_a_family(self):
        data = self.data()
        original = self.baseline.inputs()['plan']['case_index'][0]
        data['case_index'][0]['case_id'] = original['case_id']
        data['slots'][0].update(case_id=original['case_id'], slot_id=original['case_id']+':A1')
        with self.assertRaisesRegex(ValueError, 'replace or duplicate'):
            self.score(data)
        data = self.data(); data['case_index'][0]['family_id'] = original['family_id']
        with self.assertRaisesRegex(ValueError, 'replace or duplicate'):
            self.score(data)

    def test_policy_and_public_projection_do_not_admit_private_details(self):
        changed = copy.deepcopy(self.policy); changed['case_selection']['version'] = '0.1.0'
        with self.assertRaises(ValueError): validate_assessment_policy(changed)
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            data = {'schema': 'math-gauge.written-additions-public-evidence/v1', 'private_cases': 1,
                'source_inputs_sha256': 'a'*64, 'human_review': 'pending', 'formal_comparison_eligible': False}
            def check():
                (root/'evidence.json').write_text(json.dumps(data))
                return validate_public_written_additions(root, {'written_argument_evidence': descriptor(root,root/'evidence.json')})
            check(); data['case_id'] = 'SYNTHETIC-PRIVATE-ADDITION'
            with self.assertRaises(ValueError): check()

    def test_retained_review_cannot_change_native_answer_or_criterion_weights(self):
        import hashlib
        def digest(raw): return hashlib.sha256(raw).hexdigest()
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            def save(name, value):
                raw = value if isinstance(value, bytes) else json.dumps(value).encode()
                (root/name).write_bytes(raw)
                return descriptor(root, root/name)
            data = self.data(); case = data['case_index'][0]; row = data['slots'][0]
            task, raw = b'Synthetic task.', b'Synthetic delivered proof.'
            statement = save('task.md', task); answer = save('answer.md', raw)
            contract = save('contract.json', {'id': case['case_id'], 'kind': 'written_proof',
                'criteria': [{'id': 'proof', 'points': 100}]})
            rubric = save('rubric.json', {'task_sha256': digest(task), 'total_points': 100,
                'criteria': [{'id': 'proof', 'points': 100}]})
            reference = save('reference.md', b'Synthetic evaluator reference.')
            case.update(original_task=statement, task_sha256=statement['sha256'], contract=contract,
                contract_sha256=contract['sha256'], source_rubric=rubric, reference=reference)
            source = {'answer_sha256': answer['sha256'], 'rubric_sha256': rubric['sha256'],
                'score': 68, 'strict_pass': False, 'total_points': 100,
                'criteria': [{'id': 'proof', 'points': 68, 'max_points': 100,
                    'evidence': [{'start': 0, 'end': len(raw), 'quote': raw.decode()}]}]}
            source_file = save('source.json', source)
            review = save('review.json', {'schema': 'math-gauge.written-addition-review/v1',
                'case_id': case['case_id'], 'stage': 'A1', 'points': 68, 'complete': False,
                'answer_sha256': answer['sha256'], 'source_review_sha256': source_file['sha256']})
            candidate = save('input.md', b'Independent task.\n\n'+task)
            frozen = save('frozen.json', {'statement_sha256': statement['sha256'],
                'input_sha256': candidate['sha256'], 'rubric_sha256': rubric['sha256'],
                'reference_sha256': reference['sha256'], 'prefix_verbatim': 'Independent task.\n\n'})
            control = save('control.json', {'passed': True, 'mathematical_calls': 0,
                'plan_sha256': frozen['sha256'], 'report': dict.fromkeys(
                    ('work_file_roundtrip', 'protected_open_denied', 'tool_network_denied'), True)})
            adapter = save('adapter.json', {'passed': True, 'mathematical_requests': 0,
                'source_control_sha256': control['sha256'],
                'results': [{'passed': True, 'requested_model': 'synthetic', 'requested_effort': 'max'}]})
            execution = {'kind': 'math', 'status': 'completed', 'request_count': 1, 'exit_code': 0,
                'tool_mismatch': None, 'argv': ['synthetic-native'], 'cwd': '/historical/work',
                'requested_model': 'synthetic', 'requested_effort': 'max', 'tool_events': [],
                'artifact_hashes': {'output/response.md': answer['sha256'], 'input/task.md': candidate['sha256']}}
            plan = save('plan.json', {'client': 'codex', 'model': 'synthetic', 'effort': 'max',
                'argv': execution['argv'], 'cwd': execution['cwd'],
                'local_tool_policy': 'math-gauge.local-tools-no-search/v1', 'tool_network_access': False, 'search_allowed': False})
            settings = save('settings.json', {'web_search': 'disabled',
                'permissions.isolated-cli.network.enabled': False, 'features.shell_tool': True})
            row.update(response=answer, review=review, source_review=source_file,
                execution=save('execution.json', execution), execution_plan=plan, native_tool_settings=settings,
                native_capability_control=adapter, original_capability_control=control,
                original_test_plan=frozen, candidate_input=candidate,
                execution_track='math-gauge.local-tools-no-search/v1')
            def check():
                record = {'written_argument_inputs': save('inputs.json', data)}
                return load_written_argument_inputs(root, record)
            check()
            execution['artifact_hashes']['output/response.md'] = '0'*64
            row['execution'] = save('execution.json', execution)
            with self.assertRaisesRegex(ValueError, 'original answer'): check()
            execution['artifact_hashes']['output/response.md'] = answer['sha256']
            row['execution'] = save('execution.json', execution)
            source['criteria'][0]['max_points'] = 99
            row['source_review'] = save('source.json', source)
            review_data = json.loads((root/'review.json').read_bytes())
            review_data['source_review_sha256'] = row['source_review']['sha256']
            row['review'] = save('review.json', review_data)
            with self.assertRaisesRegex(ValueError, 'criterion review'): check()


if __name__ == '__main__': unittest.main()
