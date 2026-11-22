"""First native assessment is retrospective and source-bound, never portable."""
import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import math_gauge
from math_gauge.native_assessment_sources import SCHEMA,PUBLIC_SCHEMA,validate_sources
from math_gauge.records import descriptor,load_assessment_results
from math_gauge.submission_evidence import validate_first_assessment_source
import test_current_assessment_admissions as legacy


class NativeAssessmentSourceTests(unittest.TestCase):
    def put(self,name,obj):
        raw=obj if isinstance(obj,bytes) else (json.dumps(obj,ensure_ascii=False)+'\n').encode()
        p=self.root/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)
        return descriptor(self.root,p)
    def read(self,item):
        raw=(self.root/item['path']).read_bytes()
        self.assertEqual(len(raw),item['bytes']);self.assertEqual(hashlib.sha256(raw).hexdigest(),item['sha256'])
        return raw
    def setUp(self):
        temp=tempfile.TemporaryDirectory();self.addCleanup(temp.cleanup);self.root=Path(temp.name)
        self.current=json.loads((Path(math_gauge.__file__).resolve().parents[1]/'protocol/scoring-policy.json').read_bytes())
        std=self.put('public-standard.md',b'Original public standard')
        private=self.put('private-standard.md',b'Original private standard')
        self.calibration=dict(schema='math-gauge.theorem-extension-calibration-policy/v1',source_benchmark_version='1.0.0',
            target_benchmark_version='1.1.0',standards=std,private_standards=private)
        self.calibref=self.put('calibration.json',self.calibration)
        policy=self.put('first-policy.json',self.current)
        self.proof=dict(schema=SCHEMA,version='0.1.0',kind='native_post_observation_initial',model_id='new-native-model',
            source_benchmark_version='1.0.0',initial_assessment_edition='1.1.0',assessment_method_version='0.9.0',
            post_observation=True,new_candidate_calls=0,source_raw_bytes_rewritten=False,acquisition_freezes_modified=False,
            prior_adopted_score_views_existed=False,prior_adopted_B=None,prior_adopted_R=None,prior_adopted_score_views=None,portable_execution_claimed=False,
            first_assessment_policy=policy,calibration_policy=self.calibref,
            user_adoption=self.put('adoption.json',dict(post_observation=True,user_quote='Review and adopt these actual sources',
                model_id='new-native-model',source_benchmark_version='1.0.0',original_physical_effective_ordinals_preserved=True,
                original_native_statuses_preserved=True)),normal_sources=[],first_tx_reviews=[])
        self.record=dict(model_id='new-native-model',benchmark_version='1.0.0',initial_assessment_edition='1.1.0',
            retention=dict(user_requested=True),records=[])
        tx=['MG-TX001','MG-TX002','MG-TXP001','MG-TXP002','MG-TXP003','MG-TXP004']
        ids=tx+['MG-C003']+[f'S{i:02d}' for i in range(32)]
        slots=[]
        for cid,phase in [(c,'A1') for c in ids]+[('MG-C003',f'R{n}') for n in range(1,4)]:
            sid=cid+':'+phase;answer=self.put(sid+'/final.md',(sid+' original final').encode())
            review=dict(first_formal_assessment=True,old_adopted_B=None,old_adopted_R=None,old_score_views=None,
                baseline_B=2,research_R=1,answer_sha256=answer['sha256'],policy_sha256=self.calibref['sha256'],
                standard_sha256=(std if cid in tx[:2] else private)['sha256'])
            original=self.put(sid+'/original-review.json',review)
            native=self.put(sid+'/native-evidence.json',dict(schema='math-gauge.agy-native-evidence/v2',case_id=cid,phase=phase,
                original_attempt='/original/'+cid+'/'+phase+'/physical-1',physical_request=1,response=answer))
            self.proof['normal_sources'].append(dict(id=sid,case_id=cid,response=answer,agy_native_evidence=native,mathematical_review=original))
            self.record['records'].append(dict(id=sid,case_id=cid,response=answer,agy_native_evidence=native,
                source=dict(original_mathematical_review=original)))
            if cid in tx and phase=='A1':
                projection=self.put(sid+'/review-projection.json',dict(stage='A1',B=2,R=1,answer_sha256=answer['sha256'],
                    original_review=original,metadata_projection_only=True,new_candidate_calls=0))
                self.proof['first_tx_reviews'].append(dict(case_id=cid,review_projection=projection,
                    effective_standard=std if cid in tx[:2] else private,source_fields=dict(baseline_B='/baseline_B',research_R='/research_R',
                    response_sha256='/answer_sha256',policy_sha256='/policy_sha256',standard_sha256='/standard_sha256')))
                slots.append(dict(case_id=cid,review=projection,response=answer,baseline_B=2,research_R=1))
        self.record['theorem_extension_inputs']=self.put('tx-inputs.json',dict(slots=slots))
        self.save()
    def save(self):self.record['first_assessment_source']=self.put('native-first.json',self.proof)
    def check(self):
        with patch('math_gauge.agy_evidence.validate_delivery',return_value=dict(delivered=True)) as native:
            result=validate_sources(self.record,self.current,self.read)
            self.assertEqual(native.call_count,42)
            return result
    def public(self):
        self.record.update(scope='public-answers-and-combined-aggregates',first_assessment_source_private_sha256='a'*64)
        self.proof={k:self.proof[k] for k in ['schema','version','model_id','source_benchmark_version','initial_assessment_edition',
            'assessment_method_version','post_observation','new_candidate_calls','first_assessment_policy','calibration_policy']}
        self.proof.update(schema=PUBLIC_SCHEMA,private_source_proof_sha256='a'*64);self.save()
    def test_exact_first_native_sources_need_no_fabricated_precall_policy_fields(self):
        self.assertEqual(self.check(),self.current)
        self.assertNotIn('source_freeze',self.proof)
    def test_invented_history_or_portable_identity_is_rejected(self):
        for key,value in [('prior_adopted_score_views_existed',True),('acquisition_freezes_modified',True),('portable_execution_claimed',True)]:
            old=self.proof[key];self.proof[key]=value;self.save()
            with self.assertRaises(ValueError):self.check()
            self.proof[key]=old
    def test_wrong_adopted_TX_projection_and_omitted_source_rejected(self):
        tx=json.loads(self.read(self.record['theorem_extension_inputs']));tx['slots'][0]['research_R']=3
        self.record['theorem_extension_inputs']=self.put('wrong-tx-inputs.json',tx)
        with self.assertRaisesRegex(ValueError,'original first mathematical'):self.check()
        self.proof['normal_sources'].pop();self.save()
        with self.assertRaisesRegex(ValueError,'selected39'):self.check()
    def test_public_is_opaque_and_private_hash_must_match(self):
        self.public();self.assertEqual(validate_sources(self.record,self.current,self.read),self.current)
        self.record['first_assessment_source_private_sha256']='b'*64
        with self.assertRaisesRegex(ValueError,'opaque projection'):validate_sources(self.record,self.current,self.read)
    def test_submission_bottom_loader_routes_native_proof(self):
        self.public()
        self.assertEqual(validate_first_assessment_source(self.root,self.record,self.current),self.current)
        self.record['score_history']=dict(invented=True)
        with self.assertRaisesRegex(ValueError,'absence of formal'):validate_first_assessment_source(self.root,self.record,self.current)
    def test_records_loader_reaches_same_native_gate_before_scoring(self):
        class NativeGateReached(Exception):pass
        self.public()
        minimal=dict(self.record,assessment_policy=self.put('minimal-policy.json',dict(version='0.9.0')),
            strict_scoring_policy=self.put('minimal-strict.json',{}),claim_penalty_policy=self.put('minimal-claims.json',{}))
        with patch('math_gauge.benchmarks.validate_assessment_policy',side_effect=lambda x:x), \
             patch('math_gauge.scoring.validate_strict_assessment_policy'), \
             patch('math_gauge.claim_penalties.validate_policy'), \
             patch('math_gauge.submission_evidence.validate_record_component'), \
             patch('math_gauge.native_assessment_sources.validate',side_effect=NativeGateReached):
            with self.assertRaises(NativeGateReached):load_assessment_results(self.root,minimal)
    def test_current_initial_admission_also_routes_native_proof(self):
        old=legacy.InitialAdmissionTests('test_initial_projection_changes_only_metadata_and_keeps_existing_validator')
        old.setUp();self.addCleanup(old.doCleanups)
        current=old.write(old.folder/'native-current-policy.json',self.current)
        calibration=old.write(old.folder/'native-calibration.json',old.policy)
        proof=old.write(old.folder/'native-source.json',dict(schema=PUBLIC_SCHEMA,calibration_policy=old.local(calibration)))
        old.record.update(first_assessment_source=old.local(proof),assessment_policy=old.local(current))
        old.manifest['record']=old.write(old.folder/'record.json',old.record);old.publish()
        with patch('math_gauge.native_assessment_sources.validate',return_value=self.current) as native:
            old_result=legacy.admissions.load(old.root,old.mid)
            self.assertEqual(old_result['_scores']['partial']['single_attempt']['metrics'],old.scores['partial']['single_attempt']['metrics'])
            native.assert_called_once_with(old.root/old.folder,old.record,self.current)

if __name__=='__main__':unittest.main()
