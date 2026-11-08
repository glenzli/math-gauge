"""Synthetic commitment judgments and archive-bound regression checks."""
import copy
import json
from fractions import Fraction as F
from pathlib import Path
import unittest
from unittest.mock import patch

from math_gauge.claim_penalties import assess, positive_credit, validate_policy, validate_review
from math_gauge.records import (load_claim_review, load_assessment_results, project_assessment_score,
                                public_assessment_case_ids)

ROOT = Path(__file__).resolve().parents[1]
POLICY = json.loads((ROOT / 'protocol/claim-penalty-policy.json').read_bytes())


def event(root='root', severity='material', *, cap=False, covered='none'):
    return {'id': root + '-' + severity, 'root_cause': root,
        'severity': severity, 'kind': 'false_endorsement' if cap else 'false_assertion',
        'core_endorsement': cap, 'covered_by': covered, 'strict_blocking': True,
        'reason': 'Synthetic verified mathematical counterexample, not a score threshold.',
        'evidence': [{'source': 0, 'quote': 'synthetic'}]}


def row(*events, status='reviewed'):
    return {'case_id': 'FIXTURE', 'status': status, 'scope_note': 'Synthetic source judgment.',
        'sources': [], 'findings': list(events), 'baseline_disposition': None}


def review(r):
    return {'schema': 'math-gauge.claim-review-condition/v1', 'policy_version': '0.1.0',
        'reviewer_kind': 'ai', 'human_review': 'pending', 'formal_comparison_eligible': False,
        'model_label': 'FIXTURE', 'cases': [r]}


class ClaimPenaltyArithmeticTests(unittest.TestCase):
    def test_core_false_acceptance_keeps_capability_but_reliable_task_cannot_be_positive(self):
        r = row(event(severity='critical', cap=True))
        original = copy.deepcopy(r)
        mc, passed, _ = assess((F(45,100),)*3, True, r, mode='capability')
        reliable, strict, detail = assess((F(45,100),)*3, True, r, mode='partial')
        self.assertEqual(mc, (F(45,100),)*3)
        self.assertEqual(reliable, (F(0),)*3)
        self.assertFalse(passed); self.assertFalse(strict)
        self.assertEqual(detail['actual_loss'], .45)
        self.assertTrue(detail['core_endorsement_cap_applied'])
        self.assertEqual(r, original)

    def test_failed_actual_endorsement_can_score_below_safe_unfinished_answer(self):
        unsafe = row(event(severity='critical', cap=True))
        safe = row()
        a, _, _ = assess((F(0),)*3, False, unsafe, mode='partial')
        b, _, _ = assess((F(0),)*3, False, safe, mode='partial')
        self.assertEqual(a, (F(-1,5),)*3); self.assertEqual(b, (F(0),)*3)

    def test_root_cause_is_charged_once_and_independent_errors_have_a_task_cap(self):
        r = row(event('same','local'), event('same','material'), event('other','critical'))
        value, _, detail = assess((F(4,5),)*3, False, r, mode='partial')
        self.assertEqual(value, (F(3,5),)*3)
        self.assertEqual(detail['distinct_charged_roots'], 2)
        self.assertEqual(detail['generic_deduction'], .2)

    def test_embedded_reserve_is_removed_and_the_same_error_is_not_charged_twice(self):
        r = row(event(severity='local', covered='embedded_reliability'))
        r['embedded_reliability']={'criterion_id':'R','awarded':5,'maximum':10,'total':100}
        self.assertEqual(positive_credit((F(65,100),)*3,r),(F(2,3),)*3)
        value, _, detail = assess((F(65,100),)*3, False,r,mode='partial')
        self.assertEqual(value,(F(37,60),)*3)
        self.assertEqual(detail['generic_deduction'], .05)

    def test_source_reliability_points_are_not_free_mathematical_work(self):
        r = row();r['embedded_reliability']={'awarded':10}
        self.assertEqual(positive_credit((F(1,10),)*3,r),(F(0),)*3)
        self.assertEqual(positive_credit((F(1),)*3,r),(F(1),)*3)

    def test_research_baseline_penalty_and_generic_penalty_use_the_maximum(self):
        r=row(event(severity='critical'));r['baseline_disposition']='incorrect'
        value,_,detail=assess((F(1,3),)*3,False,r,mode='partial',baseline_deduction=F(2,3))
        self.assertEqual(value,(F(-1,3),)*3)
        self.assertAlmostEqual(detail['applied_deduction'],2/3)

    def test_honest_incompleteness_is_not_a_baseline_error_or_a_strict_pass(self):
        r=row();r['baseline_disposition']='honest_incomplete'
        value,passed,_=assess((F(0),)*3,True,r,mode='partial',baseline_deduction=F(1,3))
        self.assertEqual(value,(F(0),)*3);self.assertFalse(passed)

    def test_no_delivery_is_zero_and_unknown_is_not_an_observed_penalty(self):
        failed=row(status='delivery_failed')
        value,_,detail=assess((F(0),)*3,False,failed,mode='partial',baseline_deduction=F(2,3))
        self.assertEqual(value,(F(0),)*3);self.assertEqual(detail['applied_deduction'],0)
        unknown=row(status='not_run')
        value,passed,detail=assess((F(0),F(1),None),None,unknown,mode='partial')
        self.assertEqual(value,(F(-1,5),F(1),None));self.assertIsNone(passed)
        self.assertEqual(detail['applied_deduction'],0)

    def test_unresolved_review_keeps_an_interval_and_does_not_certify_strict(self):
        r=row(status='unresolved')
        value,passed,_=assess((F(1),)*3,True,r,mode='partial')
        self.assertEqual(value,(F(4,5),F(1),None));self.assertIsNone(passed)

    def test_policy_and_review_reject_unattributed_or_invented_errors(self):
        validate_policy(POLICY)
        with self.assertRaises(ValueError):validate_policy(dict(POLICY,generic_cap_points=30))
        for mutation in ['no_evidence','missing_delivery','cap_without_critical','duplicate_task']:
            r=row(event());v=review(r)
            if mutation=='no_evidence':r['findings'][0]['evidence']=[]
            elif mutation=='missing_delivery':r['status']='not_run'
            elif mutation=='cap_without_critical':r['findings'][0]['core_endorsement']=True
            else:v['cases'].append(copy.deepcopy(r))
            with self.subTest(mutation=mutation),self.assertRaises(ValueError):validate_review(v)


class ClaimArchiveTests(unittest.TestCase):
    def setUp(self):
        self.root=ROOT/'results/v0.6.0/gemini-3.8-flash-high/20261105'
        self.record=json.loads((self.root/'record.json').read_bytes())

    def test_review_binds_original_bytes_and_public_projection_excludes_private_cases(self):
        data=load_claim_review(self.root,self.record,'single_attempt')
        policy=json.loads((self.root/self.record['assessment_policy']['path']).read_bytes())
        self.assertEqual({row['case_id'] for row in data['cases']}, set(public_assessment_case_ids(policy)))
        ar=next(r for r in data['cases'] if r['case_id']=='MG-AR003')
        self.assertTrue(any(e['core_endorsement'] for e in ar['findings']))
        self.assertTrue(all(s['archive']=='public' for r in data['cases'] for s in r['sources']))

    def test_actual_core_endorsement_scores_zero_reliable_and_fails_strict(self):
        reliable=load_assessment_results(self.root,self.record)['single_attempt']
        strict=load_assessment_results(self.root,self.record,mode='strict')['single_attempt']
        mc=load_assessment_results(self.root,self.record,mode='capability')['single_attempt']
        self.assertEqual(reliable['claim_penalties']['status'],'source_bound_review_applied')
        self.assertGreater(mc['metrics']['earned']['confirmed'],reliable['metrics']['earned']['confirmed'])
        self.assertEqual(reliable,project_assessment_score(reliable))
        self.assertEqual(strict['score_mode'],'strict')
        data=load_claim_review(self.root,self.record,'single_attempt')
        ar=next(r for r in data['cases'] if r['case_id']=='MG-AR003')
        value,passed,detail=assess((F(45,100),)*3,False,ar,mode='partial')
        self.assertEqual(value,(F(0),)*3);self.assertFalse(passed)
        self.assertTrue(detail['core_endorsement_cap_applied'])

    def test_source_quote_or_population_tampering_is_rejected(self):
        from math_gauge.records import evidence_bytes
        original=evidence_bytes
        for kind in ['quote','population','policy']:
            def poisoned(root,item):
                raw=original(root,item)
                if item==self.record['claim_review']:
                    data=json.loads(raw);condition=data['conditions']['single_attempt']
                    if kind=='quote':
                        r=next(x for x in condition['cases'] if x['findings'])
                        r['findings'][0]['evidence'][0]['quote']='INVENTED MATHEMATICAL EVIDENCE'
                    elif kind=='population':condition['cases'].pop()
                    else:data['policy_sha256']='0'*64
                    return json.dumps(data).encode()
                return raw
            with self.subTest(kind=kind),patch('math_gauge.records.evidence_bytes',side_effect=poisoned),self.assertRaises(ValueError):
                load_claim_review(self.root,self.record,'single_attempt')


if __name__=='__main__':unittest.main()
