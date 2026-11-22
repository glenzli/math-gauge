"""Native written source projections, with synthetic normal-source delegation."""
import copy,json,unittest
from unittest.mock import patch
from pathlib import Path
import test_current_written_record_sources as legacy
from math_gauge.catalog import candidate_message
from math_gauge.native_written_sources import SCHEMA,validate_sources
from math_gauge.records import evidence_bytes,validate_current_written_reviews

class NativeWrittenSourcesTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):legacy.CurrentWrittenRecordSourceTests.setUpClass()
    def setUp(self):
        base=legacy.CurrentWrittenRecordSourceTests('test_current_plan_uses_all_its_written_sources_without_legacy_supplement');base.setUp();self.addCleanup(base.doCleanups)
        self.base=base;self.root=base.root;self.put=base.put
        self.record=copy.deepcopy(base.record);self.record['model_id']='synthetic-native'
        self.inputs=copy.deepcopy(base.inputs);self.policy=copy.deepcopy(base.policy)
        child=next(c for c in self.policy['subcategories'] if c['id']=='written-argument');child['private_tasks']=0
        self.inputs['plan']['profile']['data']['assessment_policy']=self.policy
        self.manifest=dict(schema=SCHEMA,version='0.1.0',post_observation=True,execution_freeze_claimed=False,
            mathematical_judgments_changed=False,model_id='synthetic-native',model_label=self.inputs['model_label'],
            reviewer_kind='ai',human_review='pending',formal_comparison_eligible=False,new_candidate_calls=0,
            scoring_plan_sha256=self.inputs['plan']['plan_sha256'],rows=[])
        self.scored={r['slot_id']:r for r in self.inputs['slots']}
        for row in self.record['records']:
            cid=row['case_id'];old=row['source'];raw=json.loads(evidence_bytes(self.root,row['review']));raw.pop('review_sha256',None)
            original=self.put(cid+'/native-original-review.json',raw);row['review']=original
            row['source']['original_mathematical_review']=original
            self.scored[row['id']]['review_sha256']=original['sha256']
            request=old['candidate_request'];r=json.loads(evidence_bytes(self.root,request));payload=self.put(cid+'/native-full-input.md',candidate_message(r).encode())
            native=dict(schema='math-gauge.agy-native-evidence/v2',case_id=cid,phase='A1',response=row['response'],
                acquisition_freeze=self.put(cid+'/native-freeze.json',dict(cases=[dict(case_id=cid,visibility='public')])),
                input_projection=dict(logical_request=request,candidate_message=payload))
            row['agy_native_evidence']=self.put(cid+'/native.json',native)
            contract=json.loads(evidence_bytes(self.root,old['case_contract']));key='stages' if contract['kind']=='progressive' else 'criteria'
            self.manifest['rows'].append(dict(slot_id=row['id'],case_id=cid,visibility='public',native_evidence=row['agy_native_evidence'],
                original_review=original,case_contract=old['case_contract'],source_fields=dict(response_sha256='/binding/response_sha256',
                contract_sha256='/group_contract_sha256',units='/'+key,**{k:'/'+k for k in ['decision','assumption_fidelity','proof_validity','scope_accuracy','unnecessary_restriction']})))
        self.save()
    def save(self):
        self.manifest['scoring_inputs']=self.put('native-scoring-inputs.json',self.inputs)
        self.record['native_current_written_sources']=self.put('native-written.json',self.manifest)
    def check(self,facade=False):
        # Independent plan/policy validators have their own legacy tests. These
        # fixtures keep all real mathematical criterion validation enabled.
        with patch('math_gauge.benchmarks.validate_plan',side_effect=lambda x:x),patch('math_gauge.benchmarks.validate_assessment_policy',side_effect=lambda x:x),patch('math_gauge.agy_evidence.validate_delivery',return_value=dict(delivered=True)):
            if facade:return validate_current_written_reviews(self.root,self.record,policy=self.policy,external=True)
            return validate_sources(self.root,self.record,self.manifest,policy=self.policy,external=True,evidence=evidence_bytes)
    def test_native_source_has_no_invented_original_CLI_import_or_slot(self):
        for row in self.record['records']:
            for k in ['slot_record','execution_plan_sha256','standard_import_plan']:row['source'].pop(k,None)
        self.assertEqual(len(self.check(facade=True)),8)
    def test_selected_credit_cannot_change_even_if_record_evaluation_matches_it(self):
        row=self.record['records'][0];s=self.scored[row['id']]
        wrong=dict(lower=.123,upper=.123,exact=.123);s['completion']=wrong;row['evaluation']['completion']=wrong;self.save()
        with self.assertRaisesRegex(ValueError,'actual selected scoring slot'):self.check()
    def test_original_criterion_review_cannot_be_substituted(self):
        self.manifest['rows'][0]['original_review']=self.manifest['rows'][1]['original_review'];self.save()
        with self.assertRaisesRegex(ValueError,'original criterion review'):self.check()
    def test_wrong_case_contract_and_projection_pointer_are_rejected(self):
        old=self.manifest['rows'][0]['case_contract'];self.manifest['rows'][0]['case_contract']=self.manifest['rows'][1]['case_contract'];self.save()
        with self.assertRaisesRegex(ValueError,'complete criterion contract'):self.check()
        self.manifest['rows'][0]['case_contract']=old;self.manifest['rows'][0]['source_fields']['response_sha256']='/group_contract_sha256';self.save()
        with self.assertRaisesRegex(ValueError,'original review/answer'):self.check()
    def test_missing_family_or_claimed_execution_freeze_cannot_use_this_branch(self):
        self.manifest['rows'].pop();self.save()
        with self.assertRaisesRegex(ValueError,'exactly the current written families'):self.check()
        self.manifest['execution_freeze_claimed']=True
        with self.assertRaisesRegex(ValueError,'cannot replace execution'):self.check()
    def test_normal_delivery_is_still_required(self):
        with patch('math_gauge.benchmarks.validate_plan',side_effect=lambda x:x),patch('math_gauge.benchmarks.validate_assessment_policy',side_effect=lambda x:x):
            with self.assertRaisesRegex(ValueError,'normal A1'):
                validate_sources(self.root,self.record,self.manifest,policy=self.policy,external=True,evidence=evidence_bytes,native_validator=lambda *a:dict(delivered=False))

if __name__=='__main__':unittest.main()
