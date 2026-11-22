"""Frozen native own-A1 parents survive only metadata-equivalent normalization."""
import copy,json,shutil,unittest
from pathlib import Path
from unittest.mock import patch
import test_native_assessment_sources as base_module
from math_gauge.native_assessment_sources import NEUTRAL_BRIDGE_SCHEMA,validate_neutral_parent_bridge
from math_gauge.revision_harness import BUNDLE_SCHEMA,_identity
from math_gauge.neutral_revision import load_inputs

class NativeNeutralParentBridgeTests(unittest.TestCase):
    def setUp(self):
        b=base_module.NativeAssessmentSourceTests('test_exact_first_native_sources_need_no_fabricated_precall_policy_fields');b.setUp();self.addCleanup(b.doCleanups)
        self.root=b.root;self.put=b.put;self.read=b.read;self.record=copy.deepcopy(b.record);self.cid='MG-TX001'
        self.row=next(r for r in self.record['records'] if r['id']==self.cid+':A1');self.row.update(kind='independent',parent_id=None)
        original=self.row['source']['original_mathematical_review']
        formal=dict(schema='math-gauge.theorem-extension-first-assessment-review-projection/v1',case_id=self.cid,stage='A1',B=2,R=1,
            answer_sha256=self.row['response']['sha256'],original_review=original,metadata_projection_only=True,new_candidate_calls=0)
        self.formal=formal;self.row['review']=self.put('neutral/formal-review.json',formal)
        self.first=dict(case_id=self.cid,family_id='synthetic-family',subcategory='theorem-extension',response_sha256=self.row['response']['sha256'],
            review_sha256=self.row['review']['sha256'],loss_modes=['partial','strict'],first_scores=dict(capability=1,partial=.333,strict=0))
        source={k:self.first[k] for k in ['family_id','subcategory','response_sha256']};source['review_sha256']=original['sha256']
        bundle=dict(schema=BUNDLE_SCHEMA,model_id=self.record['model_id'],tasks=[dict(task_id='R001',case_id=self.cid,status='ready',source_selection=source)])
        bundle['bundle_sha256']=_identity(bundle)
        frozen=copy.deepcopy(self.first);frozen['review_sha256']=original['sha256']
        bundle_ref=self.put('neutral/frozen-bundle.json',bundle)
        selected_ref=self.put('neutral/frozen-selection.json',dict(model_id=self.record['model_id'],selection=[frozen]))
        preparation=self.put('neutral/preparation-freeze.json',dict(model_id=self.record['model_id'],source_record=None,selected_count=1,files=[bundle_ref,selected_ref]))
        self.bridge=dict(schema=NEUTRAL_BRIDGE_SCHEMA,version='0.1.0',created_after_freeze=True,freeze_rewritten=False,
            claims_formal_record_existed_at_freeze=False,mathematical_values_changed=False,frozen_bundle=bundle_ref,frozen_selection=selected_ref,
            preparation_freeze=preparation,rows=[dict(task_id='R001',case_id=self.cid,raw_first_review=original,formal_baseline_source_review=self.row['review'],source_fields={'B':'/baseline_B','R':'/research_R'})])
        self.save_record()
    def save_record(self):self.bridge['source_record']=self.put('record.json',self.record)
    def check(self):return validate_neutral_parent_bridge(self.bridge,read=self.read,record_ref=self.bridge['source_record'],record=self.record,
        first=self.first,adoption_row=dict(case_id=self.cid,original_answer=self.row['response']))
    def test_original_parent_and_formal_metadata_are_equivalent(self):self.assertTrue(self.check())
    def test_wrong_alias_or_raw_parent_is_rejected(self):
        self.bridge['rows'][0]['task_id']='R999'
        with self.assertRaisesRegex(ValueError,'alias/case'):self.check()
        self.bridge['rows'][0]['task_id']='R001';self.bridge['rows'][0]['raw_first_review']=self.record['records'][1]['source']['original_mathematical_review']
        with self.assertRaisesRegex(ValueError,'frozen own-A1'):self.check()
    def test_changed_math_is_not_metadata_even_with_new_self_consistent_hashes(self):
        self.formal['R']=2;ref=self.put('neutral/changed-formal.json',self.formal)
        self.row['review']=ref;self.first['review_sha256']=ref['sha256'];self.bridge['rows'][0]['formal_baseline_source_review']=ref;self.save_record()
        with self.assertRaisesRegex(ValueError,'original B/R'):self.check()
    def test_dropped_math_field_and_changed_score_values_are_rejected(self):
        self.bridge['rows'][0]['source_fields'].pop('R')
        with self.assertRaisesRegex(ValueError,'original B/R'):self.check()
        self.bridge['rows'][0]['source_fields']['R']='/research_R';self.first['first_scores']['partial']=.9
        with self.assertRaisesRegex(ValueError,'mathematical values'):self.check()
    def _adoption(self, component=True):
        reports={m:dict(synthetic=m) for m in ['capability','partial','strict']}
        answer=dict(self.row['response'],scope='private')
        answer['path']=(Path(self.bridge['source_record']['path']).parent / answer['path']).as_posix()
        first=self.first;row=dict(case_id=self.cid,first_response_sha256=first['response_sha256'],first_review_sha256=first['review_sha256'],
            family_id=first['family_id'],subcategory=first['subcategory'],original_answer=answer,continuation=dict(status='not_run'))
        if component:row['source_component']=dict(self.put('neutral/source-component.json',self.bridge),scope='private')
        data=dict(schema='math-gauge.neutral-revision-inputs/v1',version='0.1.0',benchmark_version='1.2.0',source_scoring_edition='1.1.0',
            attempt_condition='nonlogical_retry_3',post_observation=True,original_bytes_rewritten=False,reviewer_kind='ai',human_review='pending',
            formal_comparison_eligible=False,adoption_new_candidate_calls=0,model_id=self.record['model_id'],record_id='fixture',model_label='fixture',
            source_record=self.bridge['source_record'],policy=self.put('neutral/policy.json',{}),base_reports={m:self.put('neutral/'+m+'.json',r) for m,r in reports.items()},rows=[row],study_sources=[])
        return self.put('neutral/adoption.json',data),reports
    def test_neutral_consumer_invokes_typed_bridge_before_adopting(self):
        class Reached(Exception):pass
        ref,reports=self._adoption()
        with patch('math_gauge.neutral_revision.load_policy'),patch('math_gauge.neutral_revision.select_revision_tasks',return_value=[self.first]), \
             patch('math_gauge.native_assessment_sources.validate_neutral_parent_bridge',side_effect=Reached):
            with self.assertRaises(Reached):load_inputs(self.root,ref,public_root=self.root,base_reports=reports)
    def test_neutral_consumer_cannot_omit_native_parent_bridge(self):
        ref,reports=self._adoption(component=False)
        with patch('math_gauge.neutral_revision.load_policy'),patch('math_gauge.neutral_revision.select_revision_tasks',return_value=[self.first]):
            with self.assertRaisesRegex(ValueError,'explicit frozen-parent'):load_inputs(self.root,ref,public_root=self.root,base_reports=reports)

    def test_nested_source_archive_uses_record_files_and_never_root_shadows(self):
        prefix=Path('results/v1.0.0')/self.record['model_id']/'20261122'
        originals=[p for p in self.root.rglob('*') if p.is_file()]
        for source in originals:
            target=self.root/prefix/source.relative_to(self.root)
            target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,target)
        self.bridge['source_record']=self.put((prefix/'record.json').as_posix(),self.record)
        ref,reports=self._adoption()
        bound=[self.record['first_assessment_source'],self.row['response'],self.row['review'],
               self.row['source']['original_mathematical_review'],self.row['agy_native_evidence']]
        saved={item['path']:(self.root/item['path']).read_bytes() for item in bound}
        for name in saved:(self.root/name).write_bytes(b'Wrong root; never source evidence')
        with patch('math_gauge.neutral_revision.load_policy'),patch('math_gauge.neutral_revision.select_revision_tasks',return_value=[self.first]):
            result=load_inputs(self.root,ref,public_root=self.root,base_reports=reports)
        self.assertIsNotNone(result)
        # A valid copy at the adoption root must not rescue damaged record bytes.
        for name,raw in saved.items():(self.root/name).write_bytes(raw)
        (self.root/prefix/self.row['source']['original_mathematical_review']['path']).write_bytes(b'Damaged record evidence')
        with patch('math_gauge.neutral_revision.load_policy'),patch('math_gauge.neutral_revision.select_revision_tasks',return_value=[self.first]):
            with self.assertRaises(ValueError):load_inputs(self.root,ref,public_root=self.root,base_reports=reports)

if __name__=='__main__':unittest.main()
