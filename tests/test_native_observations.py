"""Native harness math shares scoring; its evidence never becomes CLI receipts."""
import copy
import json
from pathlib import Path
import shutil
import tempfile
import unittest

import test_alignment_scoring as alignment_fixture
import test_content_rates as content_fixture
from test_claim_penalties import event
from math_gauge.harness_import import _validate_runtime
from math_gauge.native_observations import (digest, load_public_record, project_score,
    validate_math_inputs, validate_record, validate_source_supplements)
from math_gauge.records import validate_record as validate_formal_record
from math_gauge.scoring import (_alignment_trajectory, score_native_observation,
                               strict_alignment_trajectory)

ROOT = Path(__file__).resolve().parents[1]
FOLDER = ROOT/'results/v0.6.0/dot-underlying-model-20261108/20261108'


class NativeHarnessTests(unittest.TestCase):
    def core_fields(self,task):
        policy=dict(schema='math-gauge.manuscript-core-completion-policy/v1',version='0.2.0',
            case_id=task['case_id'],task_sha256='c'*64,contract_sha256='d'*64,
            required_goal_ids=['G1','G2','G3','G4'],independent_side_errors_may_pass=True,
            numeric_pass_threshold=None,rmc_floor_points=0)
        return dict(strict_completion_case=dict(case_id=task['case_id'],task_sha256='c'*64,
            contract_sha256='d'*64,strict_completion_policy=policy,
            strict_completion_policy_source={'sha256':'e'*64}),
            strict_completion_review=dict(schema='math-gauge.manuscript-core-completion-review/v1',
                policy_version='0.2.0',case_id=task['case_id'],answer_sha256=task['response']['sha256'],
                policy_sha256='e'*64,required_goals=dict.fromkeys(policy['required_goal_ids'],True),
                self_contained=True,core_claims_and_dependencies_correct=True,no_false_completion=True,
                no_material_object_substitution=True,independent_side_errors=[]),
            strict_completion_review_source={'sha256':'f'*64})

    def fixture(self):
        content, policy = content_fixture.ContentRateTests().fixture()
        align_policy = alignment_fixture.alignment_policy()
        ids = align_policy['obligation_ids']
        align_review = alignment_fixture.alignment_review(align_policy, ids,
            diagnoses=[(10,20,True,True)]*3)
        partial = _alignment_trajectory(align_review,align_policy)[0]
        capability = _alignment_trajectory(align_review,align_policy,positive_only=True)[0]
        trajectory = strict_alignment_trajectory(align_review,align_policy)
        rows,claims = [],[]
        for task in content['tasks']:
            if task['kind'] != 'initial':
                continue
            row = {k:task[k] for k in ('case_id','subcategory','family_id')}
            row.update(slot_id=task['id'],points=100,maximum=100,complete=True,
                response={'path':'answer.md','sha256':'a'*64},review={'path':'review.json','sha256':'b'*64})
            if task['subcategory']=='theorem-extension':
                row.update(baseline_B=2,research_R=3)
            if task['subcategory']=='background-check':
                row.update(background_R=3,false_endorsement=False)
            rows.append(row)
            claims.append(dict(case_id=row['case_id'],status='reviewed',scope_note='Synthetic complete result',
                sources=[],findings=[],source_response_sha256='a'*64,source_review_sha256='b'*64,
                baseline_disposition='correct' if task['subcategory']=='theorem-extension' else None))
        review=dict(schema='math-gauge.native-harness-math/v1',version='0.1.0',benchmark_version='0.6.0',
            model_label='Synthetic native harness',reviewer_kind='ai',human_review='pending',
            formal_comparison_eligible=False,transport_import_validated=False,tasks=rows,
            claim_review=dict(schema='math-gauge.claim-review-condition/v1',policy_version='0.1.0',
                model_label='Synthetic native harness',reviewer_kind='ai',human_review='pending',
                formal_comparison_eligible=False,cases=claims),alignment_review=align_review,
            alignment_source_policy=align_policy,alignment={'partial':partial,'capability':capability,'strict':trajectory},
            formalization_breakdown={'cases':[]})
        if len(rows) != 38:
            review.update(version='0.2.0', source_supplements_sha256='c'*64)
        if policy.get('manuscript_completion',{}).get('version')=='0.5.0':
            task=[row for row in rows if row['subcategory']=='manuscript-completion'][-1]
            task.update(self.core_fields(task))
        return review,policy

    def supplement_fixture(self, folder):
        def artifact(name, value):
            path = folder/name
            path.write_text(value)
            return {'path': name, 'bytes': path.stat().st_size, 'sha256': digest(path)}

        row = dict(case_id='PRIVATE-SUPPLEMENT', slot_id='PRIVATE-SUPPLEMENT:A1',
            subcategory='manuscript-completion', family_id='independent-private-family',
            visibility='private', source_kind='historical_native_delivery', rubric_timing='post_response',
            independent_family=True, post_observation=True, user_selected=True,
            execution_conditions_changed=False)
        for key in ('response','review','task','rubric','contract','provenance'):
            row[key] = artifact(key+'.txt', key+' source')
        row['prior_materials'] = [artifact('old-draft.txt', 'Earlier frozen draft')]
        row['operational_evidence'] = [artifact('native.txt', 'Native historical conditions')]
        record = json.loads((FOLDER/'native-observation.json').read_bytes())
        record.update(version='0.2.0',delivery_counts={'initial':2,'selfcheck':3},
            original_delivery_counts={'initial':1,'selfcheck':3},
            source_supplements={'private_initial_count':1,'sha256':'c'*64})
        original = {'case_id':'original','family_id':'original-family'}
        math = {'version':'0.2.0','source_supplements_sha256':'c'*64,
            'tasks':[original, {key:row[key] for key in
                ('case_id','slot_id','subcategory','family_id','response','review')}]}
        supplement = dict(schema='math-gauge.native-source-supplements/v1',version='0.1.0',
            benchmark_version='0.6.0',source_plan_sha256=record['source_plan_sha256'],
            source_run_sha256=record['source_run_sha256'],reviewer_kind='ai',human_review='pending',
            formal_comparison_eligible=False,transport_import_validated=False,tasks=[row])
        return record, math, {'case_index':[original]}, supplement

    def score(self,review,policy,mode='partial'):
        read=lambda p:json.loads((ROOT/'protocol'/p).read_bytes())
        return score_native_observation(review,policy,read('strict-scoring-policy.json'),
            read('capability-scoring-policy.json'),read('claim-penalty-policy.json'),mode=mode)

    def test_native_identity_cannot_upgrade_backend_human_or_transport_evidence(self):
        record=json.loads((FOLDER/'native-observation.json').read_bytes())
        validate_record(record)
        for key,value in (('backend_sku','verified-model'),('human_review','approved'),
                          ('formal_comparison_eligible',True),('transport_import_validated',True)):
            changed=copy.deepcopy(record);changed[key]=value
            with self.assertRaises(ValueError):validate_record(changed)
        with self.assertRaisesRegex(ValueError,'runtime frozen'):
            _validate_runtime({'runtime_frozen':False})
        with tempfile.TemporaryDirectory() as directory:
            folder=Path(directory);(folder/'record.json').write_text(json.dumps(record))
            with self.assertRaisesRegex(ValueError,'Unsupported formal result record'):
                validate_formal_record(folder)

    def test_supplement_preserves_original_batch_and_public_anonymity(self):
        record=json.loads((FOLDER/'native-observation.json').read_bytes())
        record.update(version='0.1.0',delivery_counts={'initial':38,'selfcheck':3})
        record.pop('original_delivery_counts',None);record.pop('source_supplements',None)
        validate_record(record)
        record.update(version='0.2.0',delivery_counts={'initial':39,'selfcheck':3},
            original_delivery_counts={'initial':38,'selfcheck':3},
            source_supplements={'private_initial_count':1,'sha256':'c'*64})
        validate_record(record,{'scope':{'initial_slots':39,'alignment_rounds':3}})
        for key,value in (('case_id','PRIVATE-SUPPLEMENT'),('path','private/answer.md')):
            changed=copy.deepcopy(record);changed['source_supplements'][key]=value
            with self.assertRaisesRegex(ValueError,'anonymous'):
                validate_record(changed)
        changed=copy.deepcopy(record);changed['original_delivery_counts']['initial']=39
        with self.assertRaisesRegex(ValueError,'original batch'):
            validate_record(changed)
        with self.assertRaisesRegex(ValueError,'policy population'):
            validate_record(record,{'scope':{'initial_slots':40,'alignment_rounds':3}})

    def test_historical_supplement_binds_every_source_without_extending_original_plan(self):
        with tempfile.TemporaryDirectory() as directory:
            folder=Path(directory)
            record,math,plan,supplements=self.supplement_fixture(folder)
            rows=validate_source_supplements(folder,supplements,record,math,plan)
            self.assertEqual(len(rows),1)
            self.assertEqual(len(plan['case_index']),1)
            # Reviews aggregate by the original reviewed argument's parent,
            # rather than the answer-review task's transport family.
            parent_plan=copy.deepcopy(plan)
            parent_plan['case_index'][0].update(contract_kind='answer_review',
                family_id='review-task-family',parent_family_id='original-family')
            validate_source_supplements(folder,supplements,record,math,parent_plan)
            parent_plan['case_index'][0]['parent_family_id']='another-parent'
            with self.assertRaisesRegex(ValueError,'mathematical family'):
                validate_source_supplements(folder,supplements,record,math,parent_plan)
            for descriptor in ([rows[0][key] for key in
                    ('response','review','task','rubric','contract','provenance')]
                    + rows[0]['prior_materials'] + rows[0]['operational_evidence']):
                path=folder/descriptor['path'];raw=path.read_bytes();path.write_bytes(raw+b'changed')
                with self.assertRaisesRegex(ValueError,'evidence bytes changed'):
                    validate_source_supplements(folder,supplements,record,math,plan)
                path.write_bytes(raw)
            changed=copy.deepcopy(supplements);changed['tasks'][0]['family_id']='original-family'
            with self.assertRaisesRegex(ValueError,'separate private mathematical family'):
                validate_source_supplements(folder,changed,record,math,plan)
            changed=copy.deepcopy(supplements);changed['tasks'][0]['rubric_timing']='pre_response'
            with self.assertRaisesRegex(ValueError,'historical conditions'):
                validate_source_supplements(folder,changed,record,math,plan)
            changed=copy.deepcopy(math);changed['tasks'].append({'case_id':'unbound'})
            with self.assertRaisesRegex(ValueError,'plan plus source supplements'):
                validate_source_supplements(folder,supplements,record,changed,plan)
            changed=copy.deepcopy(math);changed['tasks'][0]['strict_completion_case']={}
            with self.assertRaisesRegex(ValueError,'original completion contracts'):
                validate_source_supplements(folder,supplements,record,changed,plan)

    def test_supplement_core_verdict_is_bound_to_retained_policy_and_review_json(self):
        with tempfile.TemporaryDirectory() as directory:
            folder=Path(directory)
            record,math,plan,supplements=self.supplement_fixture(folder)
            row=math['tasks'][1];source=supplements['tasks'][0]
            def artifact(name,value):
                path=folder/name;path.write_text(json.dumps(value))
                return {'path':name,'bytes':path.stat().st_size,'sha256':digest(path)}
            policy=dict(schema='math-gauge.manuscript-core-completion-policy/v1',version='0.2.0',
                case_id=row['case_id'],task_sha256=source['task']['sha256'],
                contract_sha256=source['contract']['sha256'],required_goal_ids=['G1','G2','G3','G4'],
                independent_side_errors_may_pass=True,numeric_pass_threshold=None,rmc_floor_points=0)
            policy_source=artifact('core-policy.json',policy)
            review=dict(schema='math-gauge.manuscript-core-completion-review/v1',policy_version='0.2.0',
                case_id=row['case_id'],answer_sha256=row['response']['sha256'],
                policy_sha256=policy_source['sha256'],required_goals=dict.fromkeys(policy['required_goal_ids'],True),
                self_contained=True,core_claims_and_dependencies_correct=True,no_false_completion=True,
                no_material_object_substitution=True,independent_side_errors=[])
            row.update(points=99,maximum=100,complete=True,
                strict_completion_case=dict(case_id=row['case_id'],task_sha256=policy['task_sha256'],
                    contract_sha256=policy['contract_sha256'],strict_completion_policy=policy,
                    strict_completion_policy_source=policy_source),
                strict_completion_review=review,
                strict_completion_review_source=artifact('core-review.json',review))
            validate_source_supplements(folder,supplements,record,math,plan)
            changed=copy.deepcopy(math)
            changed['tasks'][1]['complete']=False
            changed['tasks'][1]['strict_completion_review']['self_contained']=False
            with self.assertRaisesRegex(ValueError,'retained review source'):
                validate_source_supplements(folder,supplements,record,changed,plan)
            changed=copy.deepcopy(math)
            changed['tasks'][1]['strict_completion_case']['strict_completion_policy']['unbound']='extra'
            with self.assertRaisesRegex(ValueError,'retained task contract'):
                validate_source_supplements(folder,supplements,record,changed,plan)

    def test_native_core_completion_uses_shared_contract_instead_of_numeric_threshold(self):
        review,policy=self.fixture()
        task=[row for row in review['tasks'] if row['subcategory']=='manuscript-completion'][-1]
        for key in ('strict_completion_case','strict_completion_review','strict_completion_review_source'):
            task.pop(key,None)
        task.update(points=99,complete=True)
        with self.assertRaisesRegex(ValueError,'original mathematical credit'):
            validate_math_inputs(review,policy)
        task.update(self.core_fields(task))
        validate_math_inputs(review,policy)
        task['strict_completion_review']['independent_side_errors']=[dict(root_cause='independent-side',
            outside_required_goals_and_dependencies=True,deletion_preserves_core=True,
            not_used_for_generality=True,deletion_test='Removing the aside preserves all four goals.',
            dependency_evidence='No core claim or proof uses the aside.')]
        claim=next(row for row in review['claim_review']['cases'] if row['case_id']==task['case_id'])
        claim['findings']=[dict(id='independent-side',root_cause='independent-side',kind='false_assertion',
            severity='local',strict_blocking=True,core_endorsement=False,covered_by='none',
            reason='A source-bound false independent aside.',evidence=['source'])]
        strict=self.score(review,policy,'strict')
        self.assertEqual(strict['metrics']['earned']['exact'],100)
        families=next(child['families'] for child in policy['subcategories']
            if child['id']=='manuscript-completion')
        self.assertAlmostEqual(self.score(review,policy,'capability')['metrics']['earned']['exact']
            - self.score(review,policy)['metrics']['earned']['exact'],10/families*.05)
        self.assertTrue(claim['findings'][0]['strict_blocking'])
        task['strict_completion_review']['required_goals']['G1']=False
        with self.assertRaisesRegex(ValueError,'every core goal'):
            validate_math_inputs(review,policy)

    def test_native_task_rmc_floor_matches_cli_and_keeps_unknown_unadjudicated(self):
        review,policy=self.fixture()
        manuscripts=[t for t in review['tasks'] if t['subcategory']=='manuscript-completion']
        task,old=manuscripts[-1],manuscripts[0]
        task.update(points=10,complete=False);old.update(points=10,complete=False)
        task['strict_completion_review']['required_goals']['G1']=False
        task['strict_completion_review']['core_claims_and_dependencies_correct']=False
        claims={row['case_id']:row for row in review['claim_review']['cases']}
        for row in (task,old):
            claims[row['case_id']]['findings']=[event(root='a',severity='critical'),
                event(root='b',severity='critical'),event(root='c',severity='material')]
        result=self.score(review,policy)
        actual={row['case_id']:row for row in result['tasks']}
        self.assertEqual(actual[task['case_id']]['completion']['exact'],0)
        self.assertEqual(actual[old['case_id']]['completion']['exact'],-.4)
        self.assertEqual(actual[task['case_id']]['claim_assessment']['actual_loss'],.1)
        task.update(points=None,complete=None)
        for key in ('strict_completion_review','strict_completion_review_source'):task.pop(key)
        claims[task['case_id']].update(status='unresolved',findings=[])
        actual=next(row for row in self.score(review,policy)['tasks'] if row['case_id']==task['case_id'])
        self.assertEqual(actual['completion'],{'lower':0.,'upper':1.,'exact':None})
        self.assertIsNone(actual['strict_pass'])

    def test_shared_claim_arithmetic_removes_reserve_and_deduplicates_loss(self):
        review,policy=self.fixture();task=review['tasks'][0];claim=review['claim_review']['cases'][0]
        task.update(case_id='MG-GR021',slot_id='MG-GR021:A1',points=95,complete=False)
        claim.update(case_id='MG-GR021',embedded_reliability={'criterion_id':'assertion_reliability',
            'awarded':5,'maximum':10,'total':100},findings=[dict(id='synthetic-local',root_cause='same',
                kind='unsupported_completion',severity='local',strict_blocking=True,core_endorsement=False,
                covered_by='embedded_reliability',reason='Synthetic actual unsupported claim',evidence=['source'])])
        mc=self.score(review,policy,'capability');rmc=self.score(review,policy)
        self.assertEqual(mc['tasks'][0]['completion']['exact'],1)
        self.assertEqual(rmc['tasks'][0]['completion']['exact'],.95)
        self.assertAlmostEqual(mc['metrics']['earned']['exact']-rmc['metrics']['earned']['exact'],25/12*.05)

    def test_fidelity_keeps_correct_math_without_delivering_the_requested_object(self):
        review,policy=self.fixture();task=next(t for t in review['tasks'] if t['subcategory']=='manuscript-completion')
        cid=task['case_id'];task['complete']=False
        task['fidelity_case']={'case_id':cid,'task_sha256':'a'*64,'fidelity_policy_source':{},
            'fidelity_policy':{'schema':'math-gauge.manuscript-fidelity-policy/v1','version':'0.2.0',
                'case_id':cid,'task_sha256':'a'*64,'adjustment_cap_points':50,
                'level_adjustments':{'F_PASS':0,'P30':30,'P50':50},'strict_requires_fidelity_pass':True}}
        task['fidelity']={'level':'P50','adjustment_points':50,'passed':False,'reliable_acceptance':False,
            'root_cause':'synthetic-object-bridge','source':{'sha256':'b'*64}}
        mc=self.score(review,policy,'capability');rmc=self.score(review,policy)
        families=next(child['families'] for child in policy['subcategories']
            if child['id']=='manuscript-completion')
        self.assertEqual(mc['metrics']['earned']['exact'],100)
        self.assertEqual(rmc['metrics']['earned']['exact'],100-10/families*.5)
        self.assertEqual(self.score(review,policy,'strict')['metrics']['earned']['exact'],100-10/families)

    def test_trajectory_is_recomputed_and_unresolved_task_keeps_full_denominator(self):
        review,policy=self.fixture()
        review['alignment']['partial']['metric']['exact']=101
        with self.assertRaisesRegex(ValueError,'trajectory summary'):
            self.score(review,policy)
        review,policy=self.fixture();review['tasks'][0].update(points=None,complete=None)
        review['claim_review']['cases'][0]['status']='unresolved'
        result=self.score(review,policy,'capability')
        self.assertIsNone(result['metrics']['earned']['exact'])
        self.assertEqual(result['whole_task_counts']['unknown'],1)
        self.assertLess(result['metrics']['earned']['confirmed'],100)

    def test_public_projection_and_bound_answers_do_not_accept_private_rows_or_mutation(self):
        review,policy=self.fixture();score=self.score(review,policy)
        score['tasks'][0]['secret']='PRIVATE-CASE-CONTENT'
        public=project_score(score)
        self.assertNotIn('PRIVATE-CASE-CONTENT',json.dumps(public))
        self.assertFalse(public['transport_import_validated'])
        expected=[row['case_id'] for row in json.loads((ROOT/'cases/catalog.json').read_bytes())['entries']]
        with tempfile.TemporaryDirectory() as directory:
            folder=Path(directory)/FOLDER.parent.name/FOLDER.name
            shutil.copytree(FOLDER,folder)
            record,_,_=load_public_record(folder,public_case_ids=expected)
            (folder/record['public_deliveries'][0]['response']['path']).write_text('mutated')
            with self.assertRaises(ValueError):load_public_record(folder,public_case_ids=expected)
        record=json.loads((FOLDER/'native-observation.json').read_bytes())
        record['harness']['private_source']='PRIVATE-CASE-CONTENT'
        with self.assertRaises(ValueError):validate_record(record)


if __name__=='__main__':unittest.main()
