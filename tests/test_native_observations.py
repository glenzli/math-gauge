"""Native harness math shares scoring; its evidence never becomes CLI receipts."""
import copy
import json
from pathlib import Path
import shutil
import tempfile
import unittest

import test_alignment_scoring as alignment_fixture
import test_content_rates as content_fixture
from math_gauge.harness_import import _validate_runtime
from math_gauge.native_observations import load_public_record, project_score, validate_record
from math_gauge.records import validate_record as validate_formal_record
from math_gauge.scoring import (_alignment_trajectory, score_native_observation,
                               strict_alignment_trajectory)

ROOT = Path(__file__).resolve().parents[1]
FOLDER = ROOT/'results/v0.6.0/dot-underlying-model-20261108/20261108'


class NativeHarnessTests(unittest.TestCase):
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
        return review,policy

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
        self.assertEqual(mc['metrics']['earned']['exact'],100)
        self.assertEqual(rmc['metrics']['earned']['exact'],98.75)
        self.assertEqual(self.score(review,policy,'strict')['metrics']['earned']['exact'],97.5)

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
