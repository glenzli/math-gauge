"""Background diagnosis, fixed denominators and privacy contracts; synthetic private tasks."""
import copy,json,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
from math_gauge.background_check import validate_inputs,validate_policy,CRITERIA
from math_gauge.benchmarks import BenchmarkProfile,build_plan
from math_gauge.catalog import Suite
from math_gauge.scoring import score_assessment_inputs
from math_gauge.records import validate_public_background_check,descriptor
from test_scoring import fixture_rows
ROOT=Path(__file__).resolve().parents[1]
class BackgroundChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.suite=Suite.load(ROOT/'cases');cls.profile=BenchmarkProfile.load(ROOT/'protocol/benchmark-profile.json',cls.suite)
        cls.plan=build_plan(cls.profile,cls.suite,runtime={'model_label':'SYNTHETIC-BACKGROUND',
            'adapter_identity':{'kind':'fixture'},'budget':{'timeout_seconds':2700},
            'execution_track':'math-gauge.local-tools-no-search/v1'})
        cls.policy=cls.profile.data['assessment_policy'];cls.strict=cls.profile.data['strict_policy']
    def data(self,levels=(2,0,3,0)):
        ids=['MG-BC001','MG-BC002','synthetic-private-a','synthetic-private-b']
        cases=[{'case_id':cid,'family_id':cid,'component':'background-check','contract_kind':'written_proof',
            'task_kind':'written','source_visibility':'public' if i<2 else 'private','total_weight':3,
            'criteria':[{'criterion_id':c,'points':1} for c in CRITERIA],
            'task_sha256':'0'*64,'contract_sha256':'0'*64} for i,cid in enumerate(ids)]
        for c in cases[:2]:c['contract_sha256']=next(x['group_contract_sha256'] for x in self.plan['case_index'] if x['case_id']==c['case_id'])
        slots=[]
        for cid,level in zip(ids,levels):
            slots.append({'slot_id':cid+':A1','case_id':cid,'attempt_label':'A1',
                'status':'not_run' if level is None else 'response_received_execution_unverified',
                'background_R':level,'complete':None if level is None else level==3,
                'false_endorsement':None if level is None else False,
                'response':None if level is None else {'sha256':'a'*64},
                'review':None if level is None else {'sha256':'b'*64}})
        return {'schema':'math-gauge.background-check-inputs/v1','benchmark_version':'0.6.0',
            'policy':self.policy['background_check'],'model_label':self.plan['model_label'],'attempt_labels':['A1'],
            'case_index':cases,'slots':slots,'human_review':'pending','formal_comparison_eligible':False}
    def score(self,data,mode='partial'):
        rows=[r for r in fixture_rows(self.plan) if not r['case_id'].startswith('MG-BC')]
        return score_assessment_inputs({'plan':self.plan,'model_label':self.plan['model_label'],'slots':rows},
            self.policy,self.strict,mode=mode,background_check_inputs=data)
    def test_diagnosis_partial_credit_is_distinct_from_complete_strict_delivery(self):
        data=self.data();r=self.score(data)
        self.assertAlmostEqual(r['contributions']['background-check']['exact'],25/6)
        self.assertEqual(self.score(data,'strict')['contributions']['background-check']['exact'],2.5)
        self.assertEqual(r['metrics']['background-check']['coverage']['planned'],4)
        self.assertEqual(r['capacity'],{'active':90,'under_construction':10,'total':100})
    def test_unrun_keeps_all_four_unknown_without_charging_math_failure(self):
        r=self.score(self.data((None,)*4))
        self.assertIsNone(r['contributions']['background-check']['exact'])
        self.assertEqual(r['contributions']['background-check']['confirmed'],0)
        self.assertEqual(r['contributions']['background-check']['upper'],10)
    def test_false_actual_endorsement_cannot_receive_diagnostic_credit(self):
        data=self.data();data['slots'][0]['false_endorsement']=True
        with self.assertRaisesRegex(ValueError,'endorsement'):validate_inputs(data,self.policy['background_check'])
    def test_policy_and_fixed_family_inventory_cannot_drift(self):
        for field,value in [('families',3),('private_cases',1),('downstream_calculation_is_research_credit',True)]:
            changed=dict(self.policy['background_check'],**{field:value})
            with self.subTest(field=field),self.assertRaises(ValueError):validate_policy(changed)
        data=self.data();data['slots'].pop()
        with self.assertRaisesRegex(ValueError,'every fixed slot'):validate_inputs(data,self.policy['background_check'])
    def test_public_evidence_rejects_private_family_and_modified_original_answer(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);(root/'answer.md').write_text('synthetic exact answer')
            import hashlib
            sha=hashlib.sha256((root/'answer.md').read_bytes()).hexdigest()
            (root/'review.json').write_text(json.dumps({'answer_sha256':sha,'background_R':2,'complete':False}))
            row={'case_id':'MG-BC001','attempt_label':'A1','background_R':2,'complete':False,
                'response':descriptor(root,root/'answer.md'),'review':descriptor(root,root/'review.json')}
            data={'schema':'math-gauge.background-check-public-evidence/v1','public_cases':2,'private_cases':2,
                'records':[row],'formal_comparison_eligible':False}
            def check():
                (root/'evidence.json').write_text(json.dumps(data))
                return validate_public_background_check(root,{'background_check_evidence':descriptor(root,root/'evidence.json')})
            check();row['case_id']='synthetic-private-a'
            with self.assertRaisesRegex(ValueError,'Private'):check()
            row['case_id']='MG-BC001';(root/'answer.md').write_text('mutated')
            with self.assertRaises(ValueError):check()
    def test_background_export_is_exact_and_excludes_evaluator_material(self):
        from math_gauge.harness import export_harness_bundle,inspect_harness_bundle
        plan=build_plan(self.profile,self.suite,['background-check'],runtime=self.plan['runtime'])
        with tempfile.TemporaryDirectory() as tmp,patch('subprocess.Popen',side_effect=AssertionError('no model call')):
            target=Path(tmp)/'bundle';export_harness_bundle(plan,self.suite,target)
            self.assertEqual(inspect_harness_bundle(target,plan=plan,suite=self.suite)['exported_slots'],2)
            self.assertFalse(any(p.name in {'reference.md','source-rubric.md','rubric.json','review.json'} for p in target.rglob('*')))
    def test_permission_ban_does_not_disable_body_score_leakage_check(self):
        from scripts.validate_protocol import check_candidate
        case=self.suite.cases['MG-BC001']
        with tempfile.TemporaryDirectory() as tmp:
            check_candidate(self.suite,case,Path(tmp)/'valid',selected_ids=())
            original=Path.read_bytes
            task=self.suite.case_file(case,case['task'])
            def poisoned(path):
                raw=original(path)
                return raw+'\n评分：3分'.encode() if path==task else raw
            with patch.object(Path,'read_bytes',poisoned),self.assertRaisesRegex(ValueError,'scoring leakage'):
                check_candidate(self.suite,case,Path(tmp)/'invalid',selected_ids=())
if __name__=='__main__':unittest.main()
