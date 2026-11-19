import copy
import hashlib
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from math_gauge.harness import _h_identity, _r_execution
from math_gauge.portable_assessment_sources import SCHEMA, PUBLIC_SCHEMA, validate_sources


class PortableFirstAssessmentSourceTests(unittest.TestCase):
    def setUp(self):
        self.objects = {}
        self.current = json.loads((Path(__file__).resolve().parents[1]
                                   / 'protocol/scoring-policy.json').read_bytes())
        self.original = dict(self.current, version='0.8.0', capability_policy_version='0.2.0',
                             submission_policy_version=None)
        # Match the actual older profile: metadata transition only.
        self.original.pop('submission_policy_version', None)
        self.ids = [f'C{i:02d}' for i in range(39)]
        self.runtime = dict(model_label='Original model', adapter_identity=dict(name='native', version='1'),
            candidate_parameters=dict(model='native-model', reasoning_effort='high'),
            budget=dict(timeout_seconds=2700), fresh_context=True,
            execution_track='math-gauge.local-tools-no-search/v1', system_prompt='Original system')
        self.execution = _r_execution(self.runtime, self.ids)
        self.cases = [dict(case_id=cid, version='1', request_sha256='a'*64,
            candidate_message_sha256=hashlib.sha256(cid.encode()).hexdigest()) for cid in self.ids]
        self.plan = dict(suite=dict(id='combined', version='1.0.0', sha256='b'*64),
            plan_sha256='c'*64, runner_sha256='d'*64, case_index=self.cases,
            profile=dict(data=dict(assessment_policy=self.original)))
        self.dataset = dict(base_plan_sha256=self.plan['plan_sha256'], suite=self.plan['suite'],
            runner_sha256=self.plan['runner_sha256'], controller_version='math-gauge.release-controller/v4',
            cases=[dict(case_id=r['case_id'], case_version=r['version'],
                        request_sha256=r['request_sha256'], candidate_message_sha256=r['candidate_message_sha256'])
                   for r in self.cases], selected_slot_ids=[cid+':A1' for cid in self.ids],
            planned=dict(all_slots=39, selected_slots=39))
        self.dataset['dataset_sha256'] = _h_identity(self.dataset)
        self.anchor = dict(release_version='1.0.0', expected_dataset_sha256=self.dataset['dataset_sha256'])
        self.run = dict(created_at='2026-11-19T00:00:00+00:00', runtime=self.runtime,
            runtime_sha256=_h_identity(self.runtime), runtime_frozen=True, preparation_only=False,
            dataset_sha256=self.dataset['dataset_sha256'], base_plan_sha256=self.plan['plan_sha256'],
            controller_version=self.dataset['controller_version'], selected_slot_ids=self.dataset['selected_slot_ids'],
            planned=self.dataset['planned'], execution=self.execution)
        self.initials = []
        for cid in self.ids:
            launch = dict(session_id=cid, cwd='/original/'+cid, resume=False,
                prompt_sha256=hashlib.sha256(cid.encode()).hexdigest(), prompt_bytes=len(cid),
                timeout_seconds=2700, started_at='2026-11-19T00:01:00+00:00')
            metadata = dict(session_id=cid, resume=False, started_at=launch['started_at'],
                init=dict(cwd=launch['cwd'], model='native-model'))
            request = dict(messages=[dict(role='system', content='Original system'), dict(role='user', content=cid)],
                           parameters=self.execution['parameters'])
            self.initials.append(dict(case_id=cid, launch=self.put(cid+'-launch', launch),
                metadata=self.put(cid+'-meta', metadata), request=self.put(cid+'-request', request),
                prompt=self.put(cid+'-prompt', cid.encode())))
        adoption = dict(post_observation=True, user_quote='Assess and retain these original answers',
                        source_benchmark_version='1.0.0', original_physical_effective_ordinals_preserved=True)
        self.proof = dict(schema=SCHEMA, version='0.1.0', model_id='test-model',
            source_benchmark_version='1.0.0', assessment_method_version='0.9.0', post_observation=True,
            source_raw_bytes_rewritten=False, prior_score_views_existed=False, new_candidate_calls=0,
            provider_identity_verified=False, effective_sandbox_verified=False,
            user_adoption=self.put('adoption', adoption), trusted_release_anchor=self.put('anchor', self.anchor),
            original_dataset_manifest=self.put('dataset', self.dataset), runs=[])
        self.record = dict(benchmark_version='1.0.0', model_id='test-model', retention=dict(user_requested=True))
        self.anchor_check = patch('math_gauge.harness.validate_release_anchor', return_value=self.plan)
        self.anchor_check.start()
        self.addCleanup(self.anchor_check.stop)
        self.rebind()

    def put(self, name, value):
        raw = value if isinstance(value, bytes) else (json.dumps(value, sort_keys=True)+'\n').encode()
        self.objects[name] = raw
        return dict(path=name, bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())

    def read(self, ref):
        raw = self.objects[ref['path']]
        if len(raw) != ref['bytes'] or hashlib.sha256(raw).hexdigest() != ref['sha256']:
            raise ValueError('Original source bytes changed')
        return raw

    def test_public_projection_retains_policy_without_private_inventory(self):
        proof = dict(schema=PUBLIC_SCHEMA, version='0.1.0', model_id='test-model',
            source_benchmark_version='1.0.0', assessment_method_version='0.9.0',
            post_observation=True, new_candidate_calls=0, private_source_proof_sha256='e'*64,
            original_assessment_policy=self.put('original-policy', self.original))
        record = dict(self.record, scope='public-answers-and-combined-aggregates',
            first_assessment_source_private_sha256='e'*64,
            first_assessment_source=self.put('public-proof', proof))
        self.assertEqual(validate_sources(record, self.current, self.read), self.original)
        proof['runs'] = []
        record['first_assessment_source'] = self.put('public-proof', proof)
        with self.assertRaises(ValueError):
            validate_sources(record, self.current, self.read)

    def test_public_projection_cannot_replace_private_verification(self):
        proof = dict(schema=PUBLIC_SCHEMA, version='0.1.0', model_id='test-model',
            source_benchmark_version='1.0.0', assessment_method_version='0.9.0',
            post_observation=True, new_candidate_calls=0, private_source_proof_sha256='e'*64,
            original_assessment_policy=self.put('original-policy', self.original))
        record = dict(self.record, scope='combined-evaluator',
            first_assessment_source_private_sha256='e'*64,
            first_assessment_source=self.put('public-proof', proof))
        with self.assertRaises(ValueError):
            validate_sources(record, self.current, self.read)
        record.update(scope='public-answers-and-combined-aggregates',
                      formalization_evidence_location='public_archive')
        with self.assertRaises(ValueError):
            validate_sources(record, self.current, self.read)

    def rebind(self):
        self.run.pop('run_sha256', None)
        self.run['run_sha256'] = _h_identity(self.run)
        self.proof['runs'] = [dict(original_run_manifest=self.put('run', self.run), native_initials=self.initials)]
        self.record['first_assessment_source'] = self.put('proof', self.proof)

    def test_original_portable_source_needs_no_invented_git_freeze_or_old_scores(self):
        self.assertEqual(validate_sources(self.record, self.current, self.read), self.original)
        self.assertNotIn('score_history', self.record)
        self.assertNotIn('source_freeze', self.proof)

    def test_resigned_late_preparation_is_rejected(self):
        self.run['created_at'] = '2026-11-19T00:02:00+00:00'
        self.rebind()
        with self.assertRaisesRegex(ValueError, 'preparation chronology'):
            validate_sources(self.record, self.current, self.read)

    def test_missing_or_borrowed_native_initial_is_rejected(self):
        self.initials[-1] = copy.deepcopy(self.initials[0])
        self.rebind()
        with self.assertRaisesRegex(ValueError, 'omitted, duplicated or borrowed'):
            validate_sources(self.record, self.current, self.read)

    def test_new_prompt_cannot_replace_released_input_even_with_updated_launch(self):
        row = self.initials[0]
        launch = json.loads(self.read(row['launch']))
        launch['prompt_sha256'] = hashlib.sha256(b'changed').hexdigest()
        launch['prompt_bytes'] = len(b'changed')
        row['launch'] = self.put('changed-launch', launch)
        row['prompt'] = self.put('changed-prompt', b'changed')
        self.rebind()
        with self.assertRaisesRegex(ValueError, 'fresh original input'):
            validate_sources(self.record, self.current, self.read)

    def test_older_method_cannot_be_presented_as_the_current_assessment(self):
        current = copy.deepcopy(self.current)
        current['version'] = '0.8.0'
        with self.assertRaises(ValueError):
            validate_sources(self.record, current, self.read)

    def test_historical_score_claim_or_unbound_source_bytes_are_rejected(self):
        self.record['score_history'] = dict(path='fake-history')
        with self.assertRaisesRegex(ValueError, 'actual1.0 source'):
            validate_sources(self.record, self.current, self.read)
        self.record.pop('score_history')
        self.objects['run'] += b' '
        with self.assertRaisesRegex(ValueError, 'Original source bytes changed'):
            validate_sources(self.record, self.current, self.read)
