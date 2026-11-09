"""New category: exact source input, bounded claim exceptions and fixed unknowns."""
import copy
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from math_gauge.case_selection import selected_current_cases
from math_gauge.claim_penalties import assess
from math_gauge.manuscript_completion import validate_core_completion, validate_inputs, validate_system_exclusion
from math_gauge.records import descriptor, load_manuscript_completion_inputs, validate_public_manuscript_completion
from math_gauge.records import public_assessment_case_ids
from math_gauge.scoring import _aggregate_assessment_families, score_assessment_inputs
import test_case_selection as legacy
from test_claim_penalties import event

ROOT = Path(__file__).resolve().parents[1]
CID = 'SYNTHETIC-MANUSCRIPT'

class ManuscriptTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        legacy.CaseSelectionTests.setUpClass()
        cls.base = legacy.CaseSelectionTests()
        current = json.loads((ROOT/'protocol/scoring-policy.json').read_bytes())
        cls.policy = legacy.before_public_replacement(current)
        cls.policy['manuscript_completion'] = copy.deepcopy(current['manuscript_completion'])
        cls.policy['manuscript_completion'].update(version='0.1.0', private_cases=1, families=1)
        cls.policy['manuscript_completion'].pop('public_cases',None)
        cls.policy['manuscript_completion'].pop('public_case_ids',None)
        leaf = next(c for c in cls.policy['subcategories'] if c['id']=='manuscript-completion')
        leaf.update(source_components=['manuscript-completion'],private_tasks=1,families=1,status='active')
        for k in ('private_tasks','tasks','parent_families','initial_slots'):cls.policy['scope'][k]+=1
        cls.strict = json.loads((ROOT/'protocol/strict-scoring-policy.json').read_bytes())
        cls.capability = json.loads((ROOT/'protocol/capability-scoring-policy.json').read_bytes())
        cls.claim = json.loads((ROOT/'protocol/claim-penalty-policy.json').read_bytes())

    def data(self, points=70):
        return {'schema':'math-gauge.manuscript-completion-inputs/v1','benchmark_version':'0.6.0',
            'model_label':self.base.inputs()['model_label'],'attempt_labels':['A1'],
            'policy':self.policy['manuscript_completion'],'human_review':'pending','formal_comparison_eligible':False,
            'case_index':[{'case_id':CID,'family_id':'synthetic-manuscript-family','component':'manuscript-completion',
                'source_visibility':'private','contract_kind':'research_exploration','task_kind':'written',
                'criteria':[{'criterion_id':'model','points':100}],'total_weight':100,
                'task_sha256':'a'*64,'contract_sha256':'b'*64}],
            'slots':[{'case_id':CID,'slot_id':CID+':A1','attempt_label':'A1','status':'not_run' if points is None else 'response_received_execution_unverified',
                'points':points,'complete':None if points is None else False,
                'response':None if points is None else {'sha256':'c'*64},
                'review':None if points is None else {'sha256':'d'*64},
                'execution':None if points is None else {'sha256':'e'*64}}]}

    def claims(self,data):
        inputs=self.base.inputs();index=selected_current_cases({c['case_id']:c for c in inputs['plan']['case_index']},self.policy['case_selection'])
        cases=[{'case_id':cid,'status':'reviewed','scope_note':'Synthetic baseline',
            'source_response_sha256':None,'source_review_sha256':None,'sources':[],'findings':[]} for cid in index]
        findings=[event(root='regularity',severity='critical'),event(root='algebra',severity='material'),
            event(root='continuity',severity='material'),event(root='inverse',severity='material')]
        for i,row in enumerate(data['slots']):
            unknown=row['points'] is None
            cases.append({'case_id':row['case_id'],'status':'not_run' if unknown else 'reviewed','scope_note':'Synthetic manuscript',
                'source_response_sha256':None if unknown else row['response']['sha256'],
                'source_review_sha256':None if unknown else row['review']['sha256'],
                'sources':[],'findings':[] if unknown or i else findings})
        return {'schema':'math-gauge.claim-review-condition/v1','policy_version':'0.1.0','reviewer_kind':'ai',
            'human_review':'pending','formal_comparison_eligible':False,'model_label':inputs['model_label'],'cases':cases}

    def score(self,data,mode='partial'):
        return score_assessment_inputs(self.base.inputs(),self.policy,self.strict,mode=mode,
            manuscript_completion_inputs=data,claim_review=self.claims(data),claim_policy=self.claim,
            capability_policy=self.capability if mode=='capability' else None)

    def test_category_only_cap_preserves_positive_work_and_deduplicates_roots(self):
        data=self.data();results={m:self.score(data,m) for m in ('capability','partial','strict')}
        task=lambda m:next(t for t in results[m]['tasks'] if t['case_id']==CID)
        self.assertEqual(task('capability')['completion']['exact'],.7)
        self.assertEqual(task('partial')['completion']['exact'],.2)
        self.assertFalse(task('strict')['strict_pass'])
        self.assertEqual(results['partial']['contributions']['manuscript-completion']['confirmed'],2)
        claim=self.claims(data)['cases'][-1];claim['findings'].append(event(root='regularity',severity='critical'))
        self.assertEqual(assess((F(7,10),)*3,False,claim,mode='partial')[0][2],F(1,2))
        self.assertEqual(assess((F(7,10),)*3,False,claim,mode='partial',generic_cap_points=50)[0][2],F(1,5))

    def test_unrun_keeps_fixed_weight_and_full_negative_possibility_without_failure(self):
        result=self.score(self.data(None));task=next(t for t in result['tasks'] if t['case_id']==CID)
        self.assertEqual(task['completion'],{'lower':-.5,'upper':1.,'exact':None})
        self.assertIsNone(task['strict_pass']);self.assertEqual(result['capacity']['active'],100)
        self.assertEqual(result['contributions']['manuscript-completion']['confirmed'],0)
        for status in ['delivery_failed','system_interrupted']:
            data=self.data();data['slots'][0].update(status=status,points=0,complete=False)
            with self.assertRaises(ValueError):validate_inputs(data,self.policy['manuscript_completion'])

    def test_source_bound_missing_final_is_not_an_unknown_or_a_fake_review(self):
        data = self.data(0)
        row = data['slots'][0]
        row.update(status='delivery_failed', response=None, review=None,
                   delivery_failure={'path': 'original-timeout.json', 'sha256': 'a' * 64})
        validate_inputs(data, self.policy['manuscript_completion'])
        row['complete'] = True
        with self.assertRaises(ValueError):
            validate_inputs(data, self.policy['manuscript_completion'])

    def dual(self, first=97, second=100):
        policy=copy.deepcopy(self.policy)
        policy['manuscript_completion'].update(version='0.2.0',private_cases=2,families=2)
        next(c for c in policy['subcategories'] if c['id']=='manuscript-completion').update(private_tasks=2,families=2)
        for k in ('private_tasks','tasks','parent_families','initial_slots'):policy['scope'][k]+=1
        data=self.data(first);data['policy']=policy['manuscript_completion']
        case=copy.deepcopy(data['case_index'][0]);cid=CID+'-SECOND'
        case.update(case_id=cid,family_id='synthetic-second-manuscript')
        case['fidelity_policy']={'schema':'math-gauge.manuscript-fidelity-policy/v1','version':'0.2.0',
            'case_id':cid,'task_sha256':case['task_sha256'],'adjustment_cap_points':50,
            'level_adjustments':{'F_PASS':0,'P30':30,'P50':50},'strict_requires_fidelity_pass':True}
        case['fidelity_policy_source']={'sha256':'f'*64};data['case_index'].append(case)
        row=copy.deepcopy(self.data(second)['slots'][0]);row.update(case_id=cid,slot_id=cid+':A1')
        if second is not None:
            row['fidelity']={'level':'P50','adjustment_points':50,'passed':False,'reliable_acceptance':False,
                'root_cause':'object-contract','source':{'sha256':'1'*64}}
        data['slots'].append(row)
        claims=self.claims(data)
        if first==97:claims['cases'][-2]['findings']=[event(root='one-local-error',severity='local')]
        def score(mode='partial'):
            return score_assessment_inputs(self.base.inputs(),policy,self.strict,mode=mode,
                manuscript_completion_inputs=data,claim_review=claims,claim_policy=self.claim,
                capability_policy=self.capability if mode=='capability' else None)
        return data,claims,score

    def test_two_families_average_after_single_fidelity_adjustment(self):
        data,claims,score=self.dual();results={m:score(m) for m in ('capability','partial','strict')}
        for mode,expected in [('capability',9.85),('partial',7.1),('strict',0)]:
            self.assertAlmostEqual(results[mode]['contributions']['manuscript-completion']['exact'],expected)
        first=next(t for t in results['partial']['tasks'] if t['case_id']==CID)
        second=next(t for t in results['partial']['tasks'] if t['case_id']==CID+'-SECOND')
        self.assertEqual(first['completion']['exact'],.92)
        self.assertEqual(second['completion']['exact'],.5)
        self.assertEqual(second['claim_assessment']['applied_deduction'],0)
        self.assertEqual(second['fidelity_assessment']['applied_fidelity_loss_points'],50)
        self.assertFalse(second['strict_pass'])
        self.assertEqual(next(t for t in results['capability']['tasks'] if t['case_id']==CID+'-SECOND')['completion']['exact'],1)
        # Independent math errors and fidelity share the selected total budget;
        # the fidelity defect itself may not be duplicated as math-error roots.
        claims['cases'][-1]['findings']=[event(root='independent-math',severity='critical')]
        self.assertEqual(next(t for t in score()['tasks'] if t['case_id']==CID+'-SECOND')['completion']['exact'],.5)
        claims['cases'][-1]['findings']=[event(root='object-contract',severity='critical')]
        with self.assertRaisesRegex(ValueError,'same fidelity defect'):score()

    def test_second_unknown_retains_two_family_denominator_and_interval(self):
        _,_,score=self.dual(first=70,second=None)
        for mode,expected in [('capability',(3.5,8.5)),('partial',(-1.5,6)),('strict',(0,5))]:
            result=score(mode);category=result['contributions']['manuscript-completion']
            self.assertIsNone(category['exact'])
            self.assertAlmostEqual(category['lower'],expected[0]);self.assertAlmostEqual(category['upper'],expected[1])
            self.assertEqual(category['coverage']['planned'],2)
            self.assertEqual(category['coverage']['adjudicated'],1)
            self.assertEqual(category['coverage']['unknown'],1)
        data,_,_=self.dual();data['slots'][1]['fidelity']['adjustment_points']=30
        with self.assertRaises(ValueError):validate_inputs(data,data['policy'])

    def test_public_and_private_manuscripts_share_fixed_category_without_private_ids(self):
        data,_,_=self.dual()
        policy=copy.deepcopy(self.policy)
        policy['manuscript_completion'].update(version='0.3.0',public_cases=1,
            public_case_ids=['MG-MCP003'],private_cases=2,families=3)
        next(c for c in policy['subcategories'] if c['id']=='manuscript-completion').update(
            public_tasks=1,private_tasks=2,families=3)
        for key in ('tasks','initial_slots','parent_families'):policy['scope'][key]+=2
        for key in ('public_tasks','private_tasks','public_initial_slots'):policy['scope'][key]+=1
        data['policy']=policy['manuscript_completion']
        case=copy.deepcopy(data['case_index'][0]);case.update(case_id='MG-MCP003',
            family_id='synthetic-public-manuscript',source_visibility='public')
        data['case_index'].append(case)
        row=copy.deepcopy(self.data(100)['slots'][0]);row.update(case_id='MG-MCP003',
            slot_id='MG-MCP003:A1',complete=True);data['slots'].append(row)
        claims=self.claims(data);claims['cases'][-3]['findings']=[event(root='one-local',severity='local')]
        def score(mode):
            return score_assessment_inputs(self.base.inputs(),policy,self.strict,mode=mode,
                manuscript_completion_inputs=data,claim_review=claims,claim_policy=self.claim,
                capability_policy=self.capability if mode=='capability' else None)
        for mode,expected in [('capability',9.9),('partial',242/30),('strict',10/3)]:
            result=score(mode);self.assertAlmostEqual(result['contributions']['manuscript-completion']['exact'],expected)
        public=public_assessment_case_ids(policy)
        self.assertIn('MG-MCP003',public);self.assertNotIn(CID,public);self.assertNotIn(CID+'-SECOND',public)
        for i in (0,1):
            cid=data['slots'][i]['case_id'];data['slots'][i]=copy.deepcopy(self.data(None)['slots'][0])
            data['slots'][i].update(case_id=cid,slot_id=cid+':A1')
        claims=self.claims(data)
        result=score('partial')['contributions']['manuscript-completion']
        self.assertAlmostEqual(result['confirmed'],10/3)
        self.assertEqual(result['lower'],0);self.assertEqual(result['upper'],10)
        self.assertEqual({k:result['coverage'][k] for k in ('planned','adjudicated','unknown')},
            {'planned':3,'adjudicated':1,'unknown':2})
        data['case_index'][-1]['source_visibility']='private'
        with self.assertRaises(ValueError):validate_inputs(data,data['policy'])

    def test_public_evidence_is_an_opaque_projection(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);data={'schema':'math-gauge.manuscript-completion-public-evidence/v1',
                'private_cases':1,'source_inputs_sha256':'a'*64,'human_review':'pending','formal_comparison_eligible':False}
            def check():
                (root/'public.json').write_text(json.dumps(data));return validate_public_manuscript_completion(root,{'manuscript_completion_evidence':descriptor(root,root/'public.json')})
            check();data['case_id']=CID
            with self.assertRaises(ValueError):check()

    def test_four_families_keep_unrun_slot_and_equal_fixed_weight(self):
        data,_,_=self.dual()
        policy=copy.deepcopy(self.policy)
        policy['manuscript_completion'].update(version='0.4.0',public_cases=1,
            public_case_ids=['MG-MCP003'],private_cases=3,families=4)
        next(c for c in policy['subcategories'] if c['id']=='manuscript-completion').update(
            public_tasks=1,private_tasks=3,families=4)
        for k in ('tasks','initial_slots','parent_families'):policy['scope'][k]+=3
        policy['scope']['private_tasks']+=2
        for k in ('public_tasks','public_initial_slots'):policy['scope'][k]+=1
        data['policy']=policy['manuscript_completion']
        for cid,visible,points in [('MG-MCP003','public',100),(CID+'-ADDED','private',None)]:
            case=copy.deepcopy(data['case_index'][0]);case.update(case_id=cid,family_id=cid,source_visibility=visible)
            data['case_index'].append(case)
            row=copy.deepcopy(self.data(points)['slots'][0]);row.update(case_id=cid,slot_id=cid+':A1',complete=True if points==100 else None)
            data['slots'].append(row)
        claims=self.claims(data)
        result=score_assessment_inputs(self.base.inputs(),policy,self.strict,mode='capability',
            manuscript_completion_inputs=data,claim_review=claims,claim_policy=self.claim,capability_policy=self.capability)
        category=result['contributions']['manuscript-completion']
        self.assertAlmostEqual(category['confirmed'],7.425)
        self.assertAlmostEqual(category['upper'],9.925)
        self.assertEqual(category['coverage']['unknown'],1)
        self.assertNotIn(CID+'-ADDED',public_assessment_case_ids(policy))

    def five_families(self, points=99, *, complete=False, side_error=False):
        """Keep four earlier task contracts and add one source-bound core task."""
        data,_,_=self.dual()
        policy=copy.deepcopy(self.policy)
        policy['manuscript_completion'].update(version='0.5.0',public_cases=1,
            public_case_ids=['MG-MCP003'],private_cases=4,families=5)
        next(c for c in policy['subcategories'] if c['id']=='manuscript-completion').update(
            public_tasks=1,private_tasks=4,families=5)
        for k in ('tasks','initial_slots','parent_families'):policy['scope'][k]+=4
        policy['scope']['private_tasks']+=3
        for k in ('public_tasks','public_initial_slots'):policy['scope'][k]+=1
        data['policy']=policy['manuscript_completion']
        for cid,visible,score in [('MG-MCP003','public',100),(CID+'-FOURTH','private',80),
                                 (CID+'-FIFTH','private',points)]:
            case=copy.deepcopy(data['case_index'][0]);case.update(case_id=cid,family_id=cid,source_visibility=visible)
            data['case_index'].append(case)
            row=copy.deepcopy(self.data(score)['slots'][0]);row.update(case_id=cid,slot_id=cid+':A1',
                complete=complete if cid.endswith('-FIFTH') and score is not None else True if score==100 else None if score is None else False)
            data['slots'].append(row)
        case,row=data['case_index'][-1],data['slots'][-1]
        case['strict_completion_policy']={'schema':'math-gauge.manuscript-core-completion-policy/v1',
            'version':'0.2.0','case_id':case['case_id'],'task_sha256':case['task_sha256'],
            'contract_sha256':case['contract_sha256'],'required_goal_ids':['G1','G2','G3','G4'],
            'independent_side_errors_may_pass':True,'numeric_pass_threshold':None,'rmc_floor_points':0}
        case['strict_completion_policy_source']={'sha256':'2'*64}
        if points is not None:
            row['strict_completion_review']={'schema':'math-gauge.manuscript-core-completion-review/v1',
                'policy_version':'0.2.0','case_id':case['case_id'],'answer_sha256':row['response']['sha256'],
                'policy_sha256':'2'*64,'required_goals':{'G1':True,'G2':complete,'G3':True,'G4':True},
                'self_contained':True,'core_claims_and_dependencies_correct':complete,
                'no_false_completion':True,'no_material_object_substitution':True,'independent_side_errors':[]}
            row['strict_completion_review_source']={'sha256':'3'*64}
            if side_error:
                row['strict_completion_review']['independent_side_errors']=[{
                    'root_cause':'independent-side','outside_required_goals_and_dependencies':True,
                    'deletion_preserves_core':True,'not_used_for_generality':True,
                    'deletion_test':'Deleting the isolated example changes no core result.',
                    'dependency_evidence':'No core theorem or proof refers to this example.'}]
        claims=self.claims(data)
        claims['cases'][-5]['findings']=[event(root='old-local',severity='local')]
        claims['cases'][-1]['findings']=[] if points is None else [event(root='independent-side',severity='local')]
        def score(mode='partial'):
            return score_assessment_inputs(self.base.inputs(),policy,self.strict,mode=mode,
                manuscript_completion_inputs=data,claim_review=claims,claim_policy=self.claim,
                capability_policy=self.capability if mode=='capability' else None)
        return data,policy,claims,score

    def test_failed_fifth_delivery_is_zero_without_invented_core_review(self):
        data,policy,claims,score=self.five_families()
        row=data['slots'][-1]
        row.update(status='delivery_failed',points=0,complete=False,response=None,review=None,
                   delivery_failure={'sha256':'f'*64})
        row.pop('strict_completion_review');row.pop('strict_completion_review_source')
        claims['cases'][-1].update(status='delivery_failed',findings=[],
                                  source_response_sha256=None,source_review_sha256=None,sources=[])
        for mode in ('capability','partial','strict'):
            task=next(t for t in score(mode)['tasks'] if t['case_id']==row['case_id'])
            self.assertEqual(task['completion']['exact'],0)
        row['strict_completion_review']={'required_goals':{'G1':False}}
        with self.assertRaisesRegex(ValueError,'cannot acquire a core'):
            score()

    def test_fifth_family_changes_only_fixed_population_and_keeps_old_task_judgments(self):
        data,policy,claims,score=self.five_families()
        before=copy.deepcopy(data);before['case_index'].pop();before['slots'].pop()
        old_policy=copy.deepcopy(policy)
        old_policy['manuscript_completion'].update(version='0.4.0',private_cases=3,families=4)
        next(c for c in old_policy['subcategories'] if c['id']=='manuscript-completion').update(private_tasks=3,families=4)
        for k in ('private_tasks','tasks','initial_slots','parent_families'):old_policy['scope'][k]-=1
        before['policy']=old_policy['manuscript_completion']
        old_claims=copy.deepcopy(claims);old_claims['cases'].pop()
        for mode,old_points,new_points in [('capability',9.425,9.52),('partial',8.05,8.32),('strict',2.5,2)]:
            previous=score_assessment_inputs(self.base.inputs(),old_policy,self.strict,mode=mode,
                manuscript_completion_inputs=before,claim_review=old_claims,claim_policy=self.claim,
                capability_policy=self.capability if mode=='capability' else None)
            current=score(mode)
            self.assertAlmostEqual(previous['contributions']['manuscript-completion']['exact'],old_points)
            self.assertAlmostEqual(current['contributions']['manuscript-completion']['exact'],new_points)
            old_tasks=[t for t in previous['tasks'] if t['subcategory']=='manuscript-completion']
            self.assertEqual(old_tasks,[t for t in current['tasks'] if t['case_id'] in {c['case_id'] for c in before['case_index']}])
        # A task-scoped core rule cannot make a pre-existing partial task complete.
        legacy=self.data(99);legacy['slots'][0]['complete']=True
        with self.assertRaisesRegex(ValueError,'Legacy manuscript'):validate_inputs(legacy,legacy['policy'])

    def test_fifth_unknown_retains_possible_deductions_and_never_inherits_completion(self):
        data,_,_,score=self.five_families(None)
        for mode,lower,upper in [('capability',7.54,9.54),('partial',6.44,8.44),('strict',2,4)]:
            result=score(mode)['contributions']['manuscript-completion']
            self.assertIsNone(result['exact']);self.assertAlmostEqual(result['lower'],lower)
            self.assertAlmostEqual(result['upper'],upper);self.assertEqual(result['coverage']['unknown'],1)
        task=next(t for t in score()['tasks'] if t['case_id']==CID+'-FIFTH')
        self.assertEqual(task['completion'],{'lower':0.,'upper':1.,'exact':None})
        data['slots'][-1]['complete']=False
        with self.assertRaises(ValueError):validate_inputs(data,data['policy'])

    def test_task_rmc_floor_preserves_deductions_and_legacy_negative_credit(self):
        data,_,claims,score=self.five_families(10)
        data['slots'][-2]['points']=10
        findings=[event(root='a',severity='critical'),event(root='b',severity='critical'),
                  event(root='c',severity='material')]
        for claim in claims['cases'][-2:]:claim['findings']=copy.deepcopy(findings)
        original=copy.deepcopy(claims)
        result=score()
        new=next(t for t in result['tasks'] if t['case_id']==CID+'-FIFTH')
        old=next(t for t in result['tasks'] if t['case_id']==CID+'-FOURTH')
        self.assertEqual(new['completion']['exact'],0)
        self.assertEqual(old['completion']['exact'],-.4)
        detail=new['claim_assessment']
        self.assertEqual(detail['applied_deduction'],.5)
        self.assertEqual(detail['unfloored_net_completion']['exact'],-.4)
        self.assertEqual(detail['net_completion']['exact'],0)
        self.assertEqual(detail['actual_loss'],.1)
        self.assertEqual(detail['floor_adjustment_points'],40)
        self.assertEqual(claims,original)
        for task in score('capability')['tasks']:
            if task['case_id'] in {CID+'-FOURTH',CID+'-FIFTH'}:
                self.assertEqual(task['completion']['exact'],.1)

    def test_absent_new_family_has_one_floor_without_forgiving_old_missing_families(self):
        _,policy,_,_=self.five_families(None)
        families={child['id']:{} for child in policy['subcategories']}
        _,contributions=_aggregate_assessment_families(policy,families,mode='partial',
            alignment_summary=None,strict_trajectory=None)
        self.assertEqual(contributions['manuscript-completion']['lower'],-4)
        self.assertIsNone(contributions['manuscript-completion']['exact'])
        families['manuscript-completion']['present-core']=[(F(94,100),)*3]
        _,contributions=_aggregate_assessment_families(policy,families,mode='partial',
            alignment_summary=None,strict_trajectory=None,manuscript_core_family_present=True)
        self.assertAlmostEqual(contributions['manuscript-completion']['lower'],-2.12)

    def test_three_retained_new_task_scores_are_unchanged_by_its_floor(self):
        for points,findings,expected in [
                (99,[event(severity='local')],.94),
                (53,[event(severity='critical',cap=True)],0),
                (100,[event(root='a',severity='material'),event(root='b',severity='local')],.85)]:
            data,_,claims,score=self.five_families(points)
            claims['cases'][-1]['findings']=findings
            for mode,credit in [('capability',points/100),('partial',expected)]:
                task=next(t for t in score(mode)['tasks'] if t['case_id']==CID+'-FIFTH')
                self.assertEqual(task['completion']['exact'],credit)

    def test_core_completion_accepts_evidenced_noncritical_independent_side_errors(self):
        data,_,claims,score=self.five_families(99,complete=True,side_error=True)
        source=copy.deepcopy(claims)
        result=score('strict');task=next(t for t in result['tasks'] if t['case_id']==CID+'-FIFTH')
        self.assertTrue(task['strict_pass']);self.assertEqual(task['completion']['exact'],.99)
        self.assertEqual(task['claim_assessment']['task_scoped_nonblocking_roots'],['independent-side'])
        self.assertEqual(next(t for t in score()['tasks'] if t['case_id']==CID+'-FIFTH')['completion']['exact'],.94)
        self.assertEqual(claims,source)
        claims['cases'][-1]['findings']=[event(root='independent-side',severity='material')]
        material=score('strict');task=next(t for t in material['tasks'] if t['case_id']==CID+'-FIFTH')
        self.assertTrue(task['strict_pass'])
        self.assertEqual(next(t for t in score()['tasks'] if t['case_id']==CID+'-FIFTH')['completion']['exact'],.89)
        for severity,cap in [('critical',False),('critical',True)]:
            claims['cases'][-1]['findings']=[event(root='independent-side',severity=severity,cap=cap)]
            with self.assertRaisesRegex(ValueError,'non-critical independent side'):score('strict')
        claims['cases'][-1]['findings']=[event(root='other-root',severity='local')]
        with self.assertRaises(ValueError):score('strict')
        claims['cases'][-1]['findings']=source['cases'][-1]['findings']
        row=data['slots'][-1];review=row['strict_completion_review']
        review['required_goals']['G2']=False
        with self.assertRaisesRegex(ValueError,'every core goal'):score('strict')
        review['required_goals']['G2']=True;review['independent_side_errors'][0]['deletion_test']=''
        with self.assertRaises(ValueError):validate_core_completion(data['case_index'][-1],row)

    def test_edit_alias_exclusion_requires_own_path_and_no_normal_delivery(self):
        execution={'status':'failed','exit_code':-9,'cwd':'/candidate/work','failure':{
            'type':'RuntimeError','message':'Unexpected tool or permission event'},
            'tool_mismatch':{'tool':'edit_file','answer_reviewed_at_decision':False,'selection_based_on_answer':False}}
        edit={'event':'step_update','step_update':{'tool_name':'edit_file','tool_info':{'parameters':{'Path':'/candidate/work/paper.md'}}}}
        terminal={'event':'result','result':{'status':'ERROR','response':''}}
        reason='controller_local_edit_alias_false_positive'
        validate_system_exclusion(execution,[edit,terminal],reason,'')
        for path in ['/outside/paper.md','/candidate/work/../reference.md','/candidate/work-other/paper.md']:
            invalid=copy.deepcopy(edit);invalid['step_update']['tool_info']['parameters']['Path']=path
            with self.assertRaises(ValueError):validate_system_exclusion(execution,[invalid,terminal],reason,'')
        with self.assertRaises(ValueError):validate_system_exclusion(execution,[edit,{'event':'result','result':{'status':'SUCCESS','response':'A proof'}}],reason,'')

    def test_system_exclusions_require_actual_failure_and_never_hide_output_exhaustion(self):
        reason='controller_interruption_before_first_complete_answer'
        execution={'status':'failed','exit_code':-15,'failure':{
            'type':'RuntimeError','message':'Actual process policy query failed'}}
        validate_system_exclusion(execution,[],reason,'')
        for metadata,events in [
                ({**execution,'status':'output_exhausted','failure_reason':'max_output_tokens'},[]),
                (execution,[{'type':'turn.failed','error':{'code':'max_output_tokens'}}]),
                ({**execution,'failure':{'type':'RuntimeError','message':'Unknown failure'}},[]),
                (execution,[{'type':'turn.failed','error':{'code':'ordinary_error'}}])]:
            with self.assertRaises(ValueError):validate_system_exclusion(metadata,events,reason,'')
        headless={'status':'failed','exit_code':-9,'failure':{'type':'RuntimeError','message':'CLI failed or violated tools policy'}}
        terminal=[{'event':'result','result':{'status':'SUCCESS','response':''}}]
        stderr='headless mode cannot prompt, so it was auto-denied'
        validate_system_exclusion(headless,terminal,'native_empty_reply_after_headless_permission_denial',stderr)
        with self.assertRaises(ValueError):validate_system_exclusion(headless,terminal,'native_empty_reply_after_headless_permission_denial','')

    def fixture(self,root):
        def put(name,v):
            p=root/name;p.write_bytes(v if isinstance(v,bytes) else json.dumps(v).encode());return descriptor(root,p)
        task=b'Construct a careful synthetic mathematical model.';answer=b'Synthetic original complete answer.'
        data=self.data();case=data['case_index'][0];row=data['slots'][0]
        case.update(original_task=put('task.md',task),task_sha256=hashlib.sha256(task).hexdigest())
        case['contract']=put('contract.json',{'id':CID,'kind':'research_exploration','dimensions':[{'id':'model','points':100}]});case['contract_sha256']=case['contract']['sha256']
        case['source_rubric']=put('rubric.json',{'task_sha256':case['task_sha256'],'post_observation':True,'criteria':[{'id':'model','points':100}]});case['reference']=put('reference.md',b'Synthetic evaluator proof.')
        row['response']=put('answer.md',answer);row['candidate_input']=case['original_task'];row['native_request']=case['original_task'];row['native_request_origin']='/candidate/input/task.md'
        row['review']=put('review.json',{'schema':'math-gauge.manuscript-completion-review/v1','case_id':CID,'stage':'A1','reviewer_kind':'ai','human_review':'pending','formal_comparison_eligible':False,'answer_sha256':row['response']['sha256'],'rubric_sha256':case['source_rubric']['sha256'],'score':70,'strict_pass':False,'criteria':[{'id':'model','max_points':100,'points':70,'evidence':[{'start':0,'end':len(answer),'quote':answer.decode()}]}]})
        events=b'\n'.join(json.dumps(e).encode() for e in [{'type':'item.completed','item':{'type':'agent_message','text':answer.decode()}},{'type':'turn.completed'}])+b'\n'
        row['native_events']=put('events.ndjson',events)
        plan={'client':'codex','model':'synthetic','effort':'high','prompt_sha256':case['task_sha256'],'stdin_sha256':case['task_sha256'],'stdin_file':row['native_request_origin'],'local_tool_policy':'math-gauge.local-tools-no-search/v1','tool_network_access':False}
        row['execution_plan']=put('plan.json',plan)
        row['execution']=put('execution.json',{'kind':'math','request_count':1,'requested_model':'synthetic','requested_effort':'high','stdin_bytes_written':len(task),'stdin_write_calls':1,'tool_mismatch':None,'artifact_hashes':{'input/task.md':case['task_sha256'],'output/events.ndjson':row['native_events']['sha256']}})
        row['execution_result']=put('result.json',{'native_terminal_seal':{'answer_sha256':row['response']['sha256']},'tool_mismatch':None,'local_artifact_checks_passed':True})
        row['catalog_pair_check']=put('pair.json',{'passed':True,'pending':{}})
        row['native_capability_control']=put('control.json',{'passed':True,'math_requests':0,'proof':{'local_read_write':True,'outside_denied':True,'network_denied':True}})
        row['selected_physical_request']=1
        ledger={'selected_physical_request':1,'effective_model_attempt':1,'first_complete_answer_selected':True,'attempts':[{'physical_request':1,'execution':row['execution'],'native_events':row['native_events'],'response':row['response'],'first_complete_answer':True,'excluded_pure_system_failure':False,'effective_model_attempt':1}]}
        row['physical_request_ledger']=put('ledger.json',ledger)
        def check():return load_manuscript_completion_inputs(root,{'manuscript_completion_inputs':put('inputs.json',data)})
        return data,row,plan,ledger,put,check

    def test_native_input_and_first_delivery_ledger_are_mandatory(self):
        for corruption in ('stdin_hash','missing_request','unknown_client','missing_selection','earlier_delivery'):
            with self.subTest(corruption=corruption),tempfile.TemporaryDirectory() as tmp:
                data,row,plan,ledger,put,check=self.fixture(Path(tmp));check()
                if corruption=='stdin_hash':plan['prompt_sha256']='0'*64;row['execution_plan']=put('plan.json',plan)
                elif corruption=='missing_request':row.pop('native_request')
                elif corruption=='unknown_client':plan['client']='unknown';row['execution_plan']=put('plan.json',plan)
                elif corruption=='missing_selection':row.pop('selected_physical_request');ledger.pop('selected_physical_request');ledger['attempts']=[];row['physical_request_ledger']=put('ledger.json',ledger)
                else:
                    earlier=copy.deepcopy(ledger['attempts'][0]);earlier.update(first_complete_answer=False,excluded_pure_system_failure=True,effective_model_attempt=None,exclusion_reason='controller_interruption_before_first_complete_answer')
                    ledger.update(selected_physical_request=2,attempts=[earlier,{**ledger['attempts'][0],'physical_request':2}]);row['selected_physical_request']=2;row['physical_request_ledger']=put('ledger.json',ledger)
                with self.assertRaises((ValueError,KeyError)):check()

    def test_delivered_manuscript_quotes_bind_native_final_and_sealed_work(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);data,row,plan,ledger,put,check=self.fixture(root)
            final=b'Delivered paper.md.';paper=b'Synthetic proof with explicit hypotheses.'
            row['response']=put('answer.md',final);row['manuscript']=put('paper.md',paper)
            events=b'\n'.join(json.dumps(e).encode() for e in [
                {'type':'item.completed','item':{'type':'agent_message','text':final.decode()}},
                {'type':'turn.completed'}])+b'\n'
            row['native_events']=put('events.ndjson',events)
            execution=json.loads((root/row['execution']['path']).read_bytes())
            execution['artifact_hashes']['output/events.ndjson']=row['native_events']['sha256']
            row['execution']=put('execution.json',execution)
            seal={'answer_sha256':row['response']['sha256'],'normal_complete_delivery':True,
                'work':[{'path':'paper.md','sha256':row['manuscript']['sha256'],'bytes':len(paper)}]}
            row['execution_result']=put('result.json',{'schema':'math-gauge.independent-idea-native-result/v1',
                'first_terminal':seal,'normal_complete_delivery':True,'artifact_checks_passed':True,
                'prompt_sha256':data['case_index'][0]['task_sha256'],'tool_mismatch':None})
            review=json.loads((root/row['review']['path']).read_bytes())
            review.update(answer_sha256=row['response']['sha256'],manuscript_sha256=row['manuscript']['sha256'])
            review['criteria'][0]['evidence']=[{'document':'manuscript','start':0,'end':len(paper),'quote':paper.decode()}]
            row['review']=put('review.json',review)
            ledger['attempts'][0].update(execution=row['execution'],native_events=row['native_events'],response=row['response'])
            row['physical_request_ledger']=put('ledger.json',ledger);check()
            review['criteria'][0]['evidence'][0]['document']='answer';row['review']=put('review.json',review)
            with self.assertRaises(ValueError):check()
            review['criteria'][0]['evidence'][0]['document']='manuscript';row['review']=put('review.json',review)
            row['manuscript']=put('paper.md',b'A different unsealed proof.')
            with self.assertRaises(ValueError):check()

    def test_ungraded_requests_require_authorized_restart_and_cannot_hide_delivery(self):
        with tempfile.TemporaryDirectory() as tmp:
            data,row,plan,_,put,check=self.fixture(Path(tmp))
            selected=copy.deepcopy(row)
            pending_events=put('interrupted.ndjson',json.dumps({'type':'turn.failed'}).encode()+b'\n')
            pending_execution=json.loads((Path(tmp)/selected['execution']['path']).read_bytes())
            pending_execution['artifact_hashes']['output/events.ndjson']=pending_events['sha256']
            pending_execution=put('interrupted-execution.json',pending_execution)
            attempts=[]
            keys=('execution','execution_plan','execution_result','native_events','native_request','candidate_input')
            for number in (1,2):
                attempt={k:selected[k] for k in keys}
                attempt.update(physical_request=number,effective_model_attempt=number,
                    excluded_pure_system_failure=False,native_events=pending_events,
                    execution=pending_execution,response=None)
                if number==2:
                    attempt['restart_authorization']=put('authorize2.json',{
                        'kind':'user_authorized_independent_restart','physical_request':2,
                        'prior_request_excluded_as_pure_system':False,'user_quote':'Restart once.'})
                attempts.append(attempt)
            ledger={'schema':'math-gauge.manuscript-request-history/v2','attempts':attempts,
                'selected_physical_request':None,'consumed_effective_attempts':2,
                'mathematical_disposition':'ungraded_execution_authentication_failed'}
            row.update({k:attempts[-1][k] for k in keys})
            row.update(status='execution_authentication_failed',points=None,complete=None,response=None,review=None)
            row['physical_request_ledger']=put('restart-ledger.json',ledger)
            check() # Missing authentication is unknown mathematics, with both requests retained.
            attempts[-1].update(native_events=selected['native_events'],execution=selected['execution'],response=selected['response'])
            ledger.update(selected_physical_request=2,
                mathematical_disposition='first_complete_authorized_restart_delivery')
            row.update(selected)
            row.update({k:attempts[-1][k] for k in keys})
            row.update(selected_physical_request=2,physical_request_ledger=put('restart-ledger.json',ledger))
            check() # The first delivered answer can be selected after the authorized restart.
            adoption={'kind':'user_accepted_post_observation_trial_recovery','physical_request':2,
                'prior_request_excluded_as_pure_system':False,'user_quote':'Adopt this delivered trial.',
                'post_observation':True,'case_id':CID,'task_sha256':data['case_index'][0]['task_sha256'],
                'accepted_source_response_sha256':row['response']['sha256'],
                'adoption_does_not_change_original_execution':True,
                'operator_recovery_source':put('operator-recovery.json',{'original_controller_recovery':True})}
            attempts[-1]['restart_authorization']=put('adoption.json',adoption)
            row['physical_request_ledger']=put('restart-ledger.json',ledger);check()
            invalid=copy.deepcopy(adoption);invalid['accepted_source_response_sha256']='0'*64
            attempts[-1]['restart_authorization']=put('invalid-adoption.json',invalid)
            row['physical_request_ledger']=put('restart-ledger.json',ledger)
            with self.assertRaises(ValueError):check()
            attempts[-1]['restart_authorization']=put('adoption.json',adoption)
            for corruption in ('no_authorization','excluded_attempt','earlier_delivery'):
                with self.subTest(corruption=corruption):
                    invalid=copy.deepcopy(ledger)
                    if corruption=='no_authorization':invalid['attempts'][1].pop('restart_authorization')
                    elif corruption=='excluded_attempt':invalid['attempts'][0]['excluded_pure_system_failure']=True
                    else:invalid['attempts'][0]['native_events']=selected['native_events']
                    row['physical_request_ledger']=put('invalid-restart-ledger.json',invalid)
                    with self.assertRaises((ValueError,KeyError)):check()
