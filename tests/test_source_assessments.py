import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from math_gauge.source_assessments import validate
from math_gauge.submission_evidence import original_assessment_policy


class RetainedSourceAssessmentTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.current = json.loads((Path(__file__).resolve().parents[1]/'protocol/scoring-policy.json').read_bytes())
        self.original = dict(self.current, version='0.8.0', capability_policy_version='0.2.0')
        self.original.pop('submission_policy_version')
        profile = self.put('profile.json', dict(version='0.6.0', assessment_policy=self.original))
        freeze = self.put('freeze.json', dict(benchmark_version='0.6.0', profile_sha256=profile['sha256'],
            all_initials_fresh=True, historical_answers_reused=0, mathematical_requests=0,
            utc='2026-11-12T00:00:00+00:00', initial_order=['MG-GR005'],
            requested_model='test-source-model', requested_effort='medium'))
        first = self.put('dispatch.json', dict(freeze_sha256=freeze['sha256'], physical_request_number=1,
            case_id='MG-GR005', utc='2026-11-12T00:01:00+00:00'))
        authority = self.put('adoption.json', dict(post_observation=True,user_quote='接入吧',
            source_benchmark_version='0.6.0', original_physical_effective_ordinals_preserved=True))
        execution = self.put('execution.json', dict(requested_model='test-source-model',requested_effort='medium'))
        task = self.put('task.json', {'fixture':'original task'})
        answer = self.put('answer.json', {'fixture':'original normal final'})
        native = self.put('native.json', dict(case_id='MG-GR005',phase='A1',dispatch=first,
            native_execution=execution,candidate_input=task,response=answer))
        self.proof = dict(schema='math-gauge.source-assessment-admission/v1',version='0.1.0',
            model_id='test-medium',source_benchmark_version='0.6.0',assessment_method_version='0.9.0',
            post_observation=True,new_candidate_calls=0,prior_score_views_existed=False,
            source_raw_bytes_rewritten=False,source_freeze=freeze,source_benchmark_profile=profile,
            first_dispatch=first,user_adoption=authority,first_native_admission=native)
        self.record = dict(benchmark_version='0.6.0',model_id='test-medium',retention={'user_requested':True},
            source_assessment_admission=self.put('proof.json',self.proof))
        self.native_check = patch('math_gauge.agy_evidence.validate_delivery',return_value={'delivered':True})
        self.mock = self.native_check.start()
        self.addCleanup(self.native_check.stop)

    def put(self, name, value):
        raw=(json.dumps(value,ensure_ascii=False,sort_keys=True)+'\n').encode()
        (self.root/name).write_bytes(raw)
        return dict(path=name,bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest())

    def rebind_proof(self):
        self.record['source_assessment_admission']=self.put('proof.json',self.proof)

    def test_actual_older_source_has_first_current_assessment_without_fake_views(self):
        self.assertEqual(original_assessment_policy(self.root,self.record,self.current),self.original)
        self.mock.assert_called_once()
        self.assertNotIn('score_history',self.record)

    def test_actual_first_failure_uses_failure_evidence_without_selecting_later_success(self):
        native=json.loads((self.root/'native.json').read_text())
        native['response']=None
        self.proof['first_native_admission']=self.put('first-failed-native.json',native)
        self.rebind_proof()
        with patch('math_gauge.agy_evidence.validate_failure',return_value={'outcome':'delivery_failed'}) as failure:
            self.assertEqual(validate(self.root,self.record,self.current),self.original)
        self.mock.assert_not_called()
        failure.assert_called_once()
        row=failure.call_args.args[1]
        self.assertIsNone(row['response'])
        self.assertIsNone(row['review'])
        self.assertEqual(row['evaluation']['completion'],{'lower':0,'upper':0,'exact':0})
        self.assertFalse(row['evaluation']['strict_pass'])
        self.assertEqual(row['agy_native_evidence'],self.proof['first_native_admission'])

    def test_missing_final_without_verified_native_failure_is_rejected(self):
        native=json.loads((self.root/'native.json').read_text())
        native['response']=None
        self.proof['first_native_admission']=self.put('unproved-missing-final.json',native)
        self.rebind_proof()
        with patch('math_gauge.agy_evidence.validate_failure',side_effect=ValueError('unproved native failure')):
            with self.assertRaisesRegex(ValueError,'unproved native failure'):
                validate(self.root,self.record,self.current)
        self.mock.assert_not_called()

    def test_rewriting_descriptor_does_not_allow_a_different_frozen_profile(self):
        self.proof['source_benchmark_profile']=self.put('changed-profile.json',
            dict(version='0.6.0',assessment_policy=dict(self.original,version='0.7.0')))
        self.rebind_proof()
        with self.assertRaisesRegex(ValueError,'pre-call'):
            validate(self.root,self.record,self.current)

    def test_changed_mathematical_policy_rejected(self):
        changed=copy.deepcopy(self.current)
        changed['scope']['families'] = 999
        with self.assertRaises(ValueError):
            validate(self.root,self.record,changed)

    def test_source_edition_and_original_history_cannot_be_renamed(self):
        for field,value in [('benchmark_version','1.0.0'),('score_history',{'path':'fake'}),
                            ('first_assessment_source',{'path':'fake'})]:
            record=dict(self.record,**{field:value})
            with self.subTest(field=field),self.assertRaisesRegex(ValueError,'actual edition'):
                validate(self.root,record,self.current)

    def test_later_dispatch_cannot_impersonate_first_native_call(self):
        first=json.loads((self.root/'dispatch.json').read_text())
        first['physical_request_number']=2
        self.proof['first_dispatch']=self.put('later.json',first)
        self.rebind_proof()
        with self.assertRaises(ValueError):validate(self.root,self.record,self.current)

    def test_cross_attempt_native_dispatch_and_request_model_rejected(self):
        native=json.loads((self.root/'native.json').read_text())
        native['dispatch']=self.put('other-dispatch.json',{'case_id':'other'})
        self.proof['first_native_admission']=self.put('other-native.json',native)
        self.rebind_proof()
        with self.assertRaisesRegex(ValueError,'another native'):
            validate(self.root,self.record,self.current)
        native=json.loads((self.root/'native.json').read_text())
        native['native_execution']=self.put('other-execution.json',dict(requested_model='other',requested_effort='medium'))
        self.proof['first_native_admission']=self.put('other-native.json',native)
        self.rebind_proof()
        with self.assertRaisesRegex(ValueError,'requested model'):
            validate(self.root,self.record,self.current)

    def test_missing_user_selection_and_invented_prior_views_rejected(self):
        with self.assertRaises(ValueError):validate(self.root,dict(self.record,retention={}),self.current)
        self.proof['prior_score_views_existed']=True
        self.rebind_proof()
        with self.assertRaisesRegex(ValueError,'invent migration'):
            validate(self.root,self.record,self.current)


if __name__=='__main__':unittest.main()
