"""Synthetic fresh-plan source-bridge tests. No model results or new grading."""
import copy
import json
from pathlib import Path
import unittest
from assessment_fixtures import before_submission_policy

from math_gauge.benchmarks import BenchmarkProfile, build_plan
from math_gauge.catalog import Suite
from math_gauge.scoring import (score_assessment_record_inputs, score_assessment_inputs,
    formalization_substitutions, score_alignment_trajectory, strict_alignment_trajectory)

ROOT = Path(__file__).resolve().parents[1]


class FreshRecordScoringTests(unittest.TestCase):
    def setUp(self):
        suite = Suite.load(ROOT/'cases')
        profile = BenchmarkProfile.load(ROOT/'protocol/benchmark-profile.json', suite)
        plan = build_plan(profile, suite, runtime={'model_label':'SYNTHETIC CURRENT SOURCE BRIDGE',
            'adapter_identity':{'kind':'fixture'}, 'budget':{'timeout_seconds':2700},
            'execution_track':'math-gauge.local-tools-no-search/v1'})
        self.inputs = dict(plan=plan, model_label=plan['model_label'], slots=[dict(
            slot_id=s['slot_id'], case_id=s['case_id'], response_sha256='b'*64,
            completion={'lower':0,'upper':1,'exact':None}, strict_pass=None)
            for s in plan['slots']])
        # The shared immutable mathematical policy supplies no old answers/scores.
        self.policy = json.loads((ROOT/'results/v0.6.0/terra-6.1-max/20261105/scoring-policy.json').read_bytes())
        ids = self.policy['obligation_ids']
        def snapshot(count, n):
            return dict(source_id='synthetic-archive-source-'+str(n),source_sha256=str(n+1)*64,
                source_kind='sealed_workspace',delivery_verified=True,review_evidence_sha256=['a'*64],
                obligations=[dict(id=oid,complete=i<count)for i,oid in enumerate(ids)])
        self.alignment = dict(schema='math-gauge.alignment-selfcheck-review/v1',
            scoring_version=self.policy['version'], case_id='MG-C003',case_version='0.1.1',
            model_label=plan['model_label'],reviewer_kind='ai',human_review='pending',
            formal_comparison_eligible=False,policy_sha256='c'*64,primary_source_kind='sealed_workspace',
            baseline=snapshot(24,0),rounds=[])
        for n,count in enumerate([29,34,36],1):
            s=snapshot(count,n)
            self.alignment['rounds'].append(dict(round=n,snapshot=s,diagnosis=dict(
                source_sha256=s['source_sha256'],global_points=10,localization_points=20,
                claims_complete=False,accurate=True,review_evidence_sha256=['a'*64])))
        cases=[]
        for c in plan['case_index']:
            if c['component']!='lean-formalization':continue
            items=[dict(id=s['stage_id'],complete=(i<24 if c['case_id']=='MG-C003'else True),
                        declarations=[dict(file='Synthetic.lean',name='synthetic_test_declaration')])
                   for i,s in enumerate(c['stages'])]
            cases.append(dict(case_id=c['case_id'],case_version=c['version'],slot_id=c['case_id']+':A1',
                original_response_sha256='b'*64,source_kind='sealed_workspace',
                source_sha256=self.alignment['baseline']['source_sha256']if c['case_id']=='MG-C003'else'd'*64,
                kernel_status='passed',compiled_sources={'Synthetic.lean':'e'*64},obligations=items))
        self.formal = dict(schema='math-gauge.formalization-engineering-review/v1',model_label=plan['model_label'],
            reviewer_kind='ai',human_review='pending',formal_comparison_eligible=False,cases=cases)
        self.data=copy.deepcopy(plan['profile']['data'])
        self.data['assessment_policy']=before_submission_policy(self.data['assessment_policy'])
        self.capability=json.loads((ROOT/'protocol/capability-scoring-policy.json').read_bytes())

    def score(self, mode):
        return score_assessment_record_inputs(self.inputs,self.alignment,self.policy,
            formalization_review=self.formal,assessment_policy=self.data['assessment_policy'],
            strict_policy=self.data['strict_policy'],mode=mode,
            capability_policy=self.capability if mode=='capability'else None)

    def unavailable(self, cid, disposition):
        case=next(c for c in self.formal['cases']if c['case_id']==cid)
        row=next(r for r in self.inputs['slots']if r['case_id']==cid)
        value=False if disposition=='delivery_failed'else None
        row.update(started=disposition=='delivery_failed',delivery_status=disposition,response_sha256=None,strict_pass=value,
            completion={'lower':0,'upper':0 if value is False else 1,'exact':0 if value is False else None})
        case.update(source_kind='not_available',delivery_status=disposition,source_sha256=None,
            original_response_sha256=None,compiled_sources={},kernel_status='not_run')
        for item in case['obligations']:item.update(complete=None,declarations=[])
        return case

    def test_unrun_source_needs_no_invented_lean_file_and_stays_unknown(self):
        c=self.unavailable('HCH02','not_run')
        result=self.score('partial')
        row=next(r for r in result['lean_formalization_breakdown']['cases']if r['case_id']=='HCH02')
        self.assertIsNone(row['complete_count'])
        self.assertIsNone(result['metrics']['overall']['exact'])
        c['obligations'][0]['complete']=True
        with self.assertRaisesRegex(ValueError,'Unavailable engineering source'):
            self.score('partial')

    def test_known_failed_a1_is_zero_but_unrun_selfcheck_rounds_are_unknown(self):
        self.unavailable('MG-C003','delivery_failed')
        b=self.alignment['baseline'];b.update(source_kind='not_available',delivery_status='delivery_failed',
            source_sha256=None,delivery_verified=False)
        for item in b['obligations']:item['complete']=None
        self.alignment['rounds']=[{'round':n,'snapshot':None,'diagnosis':None}for n in [1,2,3]]
        for mode in ['capability','partial','strict']:
            r=self.score(mode);case=next(t for t in r['tasks']if t['case_id']=='MG-C003')
            self.assertEqual(case['completion'],{'lower':0.0,'upper':0.0,'exact':0.0})
            self.assertFalse(case['strict_pass'])
            self.assertIsNone(r['metrics']['lean-selfcheck']['exact'])
            detail=next(t for t in r['lean_formalization_breakdown']['cases']if t['case_id']=='MG-C003')
            self.assertIsNone(detail['complete_count'])
            self.assertEqual(detail['status'],'delivery_failed')
            for round in r['alignment_selfcheck']['rounds']:
                self.assertIsNone(round['major_false_complete'])
                self.assertIsNone(round['diagnosis_points'])
        c=next(c for c in self.formal['cases']if c['case_id']=='MG-C003')
        c.update(source_kind='sealed_workspace',compiled_sources={'Invented.lean':'e'*64})
        with self.assertRaisesRegex(ValueError,'accepted original response'):
            self.score('partial')

    def test_v6_uses_the_existing_current_scorer_and_same_trajectory_in_all_modes(self):
        substitutions=formalization_substitutions(self.inputs,self.formal)
        strict=strict_alignment_trajectory(self.alignment,self.policy)
        for mode in ['capability','partial','strict']:
            actual=self.score(mode)
            # Positive-only repair arithmetic uses the established source helper.
            from math_gauge.scoring import _alignment_trajectory
            trajectory=_alignment_trajectory(self.alignment,self.policy,positive_only=mode=='capability')[0]
            expected=score_assessment_inputs(self.inputs,self.data['assessment_policy'],self.data['strict_policy'],
                mathematical_substitutions=substitutions,alignment_summary=trajectory,strict_trajectory=strict,
                mode=mode,capability_policy=self.capability if mode=='capability'else None)
            self.assertEqual(actual['metrics'],expected['metrics'])
            self.assertEqual(actual['capacity']['total'],100)
            self.assertEqual(actual['alignment_selfcheck'],trajectory)
            self.assertFalse(actual['formal_comparison_eligible'])
        counts={r['case_id']:r['complete_count']for r in self.score('partial')['lean_formalization_breakdown']['cases']}
        self.assertEqual(counts,{'LCH01':8,'LCH02':20,'HCH02':40,'MG-C003':24})

    def test_unknown_engineering_obligation_keeps_original_variant_denominator(self):
        next(c for c in self.formal['cases']if c['case_id']=='HCH02')['obligations'][0]['complete']=None
        score=self.score('partial')
        detail=score['lean_formalization_breakdown']
        family=next(v for v in detail['families'].values()if 'HCH02'in v['case_ids'])
        self.assertEqual(family['variant_count'],3)
        self.assertIsNone(family['percent'])
        self.assertIsNone(next(r for r in detail['cases']if r['case_id']=='HCH02')['complete_count'])
        self.assertIsNone(score['metrics']['overall']['exact'])

    def test_raw_format_failure_does_not_erase_verified_sealed_math_or_rebind_parent(self):
        raw=next(r for r in self.inputs['slots']if r['case_id']=='LCH02')
        raw.update(completion={'lower':0,'upper':0,'exact':0},strict_pass=False)
        actual=self.score('strict')
        task=next(t for t in actual['tasks']if t['case_id']=='LCH02')
        self.assertTrue(task['strict_pass'])
        self.assertFalse(raw['strict_pass'])
        next(c for c in self.formal['cases']if c['case_id']=='MG-C003')['source_sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'alignment-study parent'):
            self.score('partial')


if __name__=='__main__':unittest.main()
