"""Dot observer clocks preserve physical selection, unknowns and common samples."""
from copy import deepcopy
import hashlib
import unittest
from unittest.mock import patch
from math_gauge import dot_rerun_timings as owner
from scripts.timing_reference import daily_summary,summarize


class DotRerunTimingTests(unittest.TestCase):
    def test_other_physical_attempt_cannot_supply_selected_clock(self):
        source=dict(path='selected/answer.md',bytes=3,sha256='a'*64)
        expected=dict(series='base',case_id='MG-C003',phase='A1',answer=source,
            context='physical-2',request=None,delivery_status='delivered')
        row=dict(series='base',case_id='MG-C003',phase='A1',selected_answer=source,
            selected_physical_context='physical-1',delivery_status='delivered')
        with self.assertRaisesRegex(ValueError,'physical request'):owner.validate_selection(row,expected)
        row['selected_physical_context']='physical-2';owner.validate_selection(row,expected)

    def test_untimed_adopted_revision_does_not_become_zero_elapsed(self):
        base=dict(series='base',phase='A1',case_id='public',seconds=30,
            selected_answer={'sha256':'a'*64},delivery_status='delivered')
        later=dict(series='neutral',phase='neutral',case_id='public',seconds=None,delivery_status='delivered')
        admission={'revised':{'_public_tasks':{'public_case_ids':['public'],'views':{'strict':{owner.CONDITION:{'tasks':[
            {'case_id':'public','response_sha256':'a'*64,'strict_pass':True}]}}}}}}
        row=owner.combined_public_rows({'rows':[base,later]},admission)[0]
        self.assertIsNone(row['seconds']);self.assertIsNone(row['revision_seconds'])
        later['seconds']=20
        self.assertEqual(owner.combined_public_rows({'rows':[base,later]},admission)[0]['seconds'],50)
        self.assertEqual(owner.combined_public_rows({'rows':[base]},admission)[0]['seconds'],30)

    def test_controller_quote_mutation_is_rejected(self):
        quote='2026-11-25T00:00:00Z selected observer event'
        raw=(quote+'\n').encode().ljust(22339,b' ');sha=hashlib.sha256(raw).hexdigest()
        event=dict(id='event-0',timestamp_text='2026-11-25T00:00:00Z',byte_start=0,byte_end=len(quote.encode()),
                   quote=quote,source={'sha256':sha})
        extract=dict(schema='math-gauge.dot-coordinator-clock-extract-proposal/v1',extraction_only=True,
            runtime_independently_verified=False,original_source={'sha256':sha},events=[event])
        with patch.object(owner,'CONTROLLER_SHA256',sha):
            owner.validate_extract(extract,raw)
            event['quote']='changed selected event'
            with self.assertRaisesRegex(ValueError,'original bytes'):owner.validate_extract(extract,raw)

    def fixture(self):
        ids=['public'+str(i)for i in range(12)];weights={cid:5 for cid in ids}
        def row(cid,seconds):return dict(case_id=cid,seconds=seconds,method=owner.METHOD if seconds is not None else None,
            base_seconds=seconds,revision_seconds=0,revision_selected=False,source_reused=False,other_runs=[],
            delivery_status='delivered',strict_pass=False)
        rows=[row(cid,60 if i<5 else None)for i,cid in enumerate(ids)]+[row('MG-C003',1729.13725)]
        report=dict(rows=rows,shared_sample=dict(case_ids=ids,weights=weights),
            summaries=dict(daily=daily_summary(rows[:-1],weights),**{'MG-C003':summarize(rows[-1:])}))
        source={'path':owner.INDEX_PATH,'bytes':1,'sha256':'c'*64}
        ref=dict(benchmark_version='1.2.0',daily_case_ids=deepcopy(ids),daily_weights=deepcopy(weights),
            cases=[dict(id=cid)for cid in ids+['MG-C003']],models=[dict(id='incumbent',summaries={'unchanged':7})],score_inputs=[{'old':True}])
        model=dict(id=owner.MODEL,label='Dot (261125)',harness_display_name='Dot native harness',theme={},logo={})
        return report,source,ref,model

    def test_append_keeps_fixed12_incumbents_and_partial_statistics(self):
        report,source,ref,model=self.fixture();before=deepcopy(ref)
        with patch.object(owner,'load_public',return_value=dict(report=report,source=source)):
            owner.append_reference('.',ref,model)
        self.assertEqual(ref['models'][:-1],before['models']);self.assertEqual(ref['daily_case_ids'],before['daily_case_ids'])
        self.assertEqual(ref['daily_weights'],before['daily_weights']);self.assertEqual(ref['score_inputs'],before['score_inputs'])
        actual=ref['models'][-1];daily=actual['summaries']['daily']
        self.assertEqual((daily['planned'],daily['timed']),(12,5))
        self.assertIsNone(daily['weighted_mean_seconds']);self.assertIsNone(daily['median_seconds'])
        chapter=next(r for r in actual['rows']if r['case_id']=='MG-C003')
        self.assertEqual(chapter['delivery_status'],'delivered');self.assertEqual(chapter['seconds'],1729.13725)
        self.assertFalse(chapter['strict_pass'],'normal delivery and SMC remain distinct')

    def test_resampled_common_subset_is_rejected(self):
        report,source,ref,model=self.fixture();ref['daily_case_ids']=ref['daily_case_ids'][:5]
        with patch.object(owner,'load_public',return_value=dict(report=report,source=source)):
            with self.assertRaisesRegex(ValueError,'resample'):owner.append_reference('.',ref,model)
        self.assertEqual(len(ref['models']),1)

    def test_partial_resource_total_stays_unknown_and_known_zero_is_retained(self):
        self.assertEqual(owner._coverage([{'seconds':0},{'seconds':None}]),
            dict(planned=2,timed=1,unknown=1,observed_wall_seconds=None))
        self.assertEqual(owner._coverage([{'seconds':0}])['observed_wall_seconds'],0)


if __name__=='__main__':unittest.main()
