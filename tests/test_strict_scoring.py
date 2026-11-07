"""Whole-task/trajectory scoring keeps the 100-point frame and source identity."""
import copy
import json
from pathlib import Path
import unittest
from math_gauge.scoring import (score_record_inputs, score_strict_record_inputs,
    score_assessment_record_inputs, strict_alignment_trajectory)
from test_alignment_scoring import alignment_policy, alignment_review
from test_case_selection import before_public_replacement

ROOT = Path(__file__).resolve().parents[1]


class StrictScoringTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.folder = ROOT / 'results/v0.6.0/gemini-3.8-flash-high/20261105'
        load = lambda name: json.loads((cls.folder / name).read_bytes())
        cls.inputs, cls.review, cls.policy, cls.engineering = [load(n) for n in
            ('scoring-inputs.json', 'reviews/alignment.json', 'scoring-policy.json', 'reviews/formalization.json')]
        cls.strict_policy = json.loads((ROOT / 'protocol/strict-scoring-policy.json').read_bytes())
        cls.assessment_policy = before_public_replacement(
            json.loads((ROOT / 'protocol/scoring-policy.json').read_bytes()))

    def score(self, *, inputs=None, engineering=None, policy=None):
        return score_strict_record_inputs(self.inputs if inputs is None else inputs, self.review, self.policy,
            formalization_review=self.engineering if engineering is None else engineering,
            strict_policy=self.strict_policy if policy is None else policy, assessment_policy=self.assessment_policy)

    def test_binary_tasks_precede_family_aggregation_and_private_missing_is_unknown(self):
        r = self.score()
        self.assertAlmostEqual(r['metrics']['lean-formalization']['exact'], 100/6)
        self.assertEqual(r['whole_task_counts'], {'planned':34, 'passed':5, 'failed':15, 'unknown':14})
        self.assertIsNone(r['metrics']['earned']['exact'])
        self.assertAlmostEqual(r['metrics']['earned']['upper']-r['metrics']['earned']['lower'],25*4/12+20)
        self.assertAlmostEqual(r['metrics']['overall']['upper']-r['metrics']['earned']['upper'],10)
        self.assertIsNone(r['metrics']['overall']['exact'])
        self.assertEqual(r['capacity'], {'active':90,'under_construction':10,'total':100})
        self.assertFalse(r['strict_alignment_selfcheck']['strict_pass'])
        self.assertEqual(r['contributions']['lean-selfcheck']['exact'],0)

    def test_near_full_credit_does_not_become_strict_pass(self):
        tasks={r['case_id']:r for r in self.score()['tasks']}
        for cid in ('MG-GR022','MG-GR023','AHR04','LCH02','HCH02','MG-C003'):
            self.assertIs(tasks[cid]['strict_pass'],False,cid)
        self.assertEqual(tasks['MG-C003']['judgment_source'],'selected_sealed_engineering')

    def test_known_failure_stays_failed_when_another_requirement_is_unknown(self):
        changed=copy.deepcopy(self.engineering)
        case=next(r for r in changed['cases'] if r['case_id']=='HCH02')
        next(r for r in case['obligations'] if r['complete'])['complete']=None
        self.assertEqual(self.score(engineering=changed)['metrics'],self.score()['metrics'])

    def test_unknown_engineering_and_missing_answer_keep_fixed_denominators(self):
        changed=copy.deepcopy(self.engineering)
        next(r for r in changed['cases'] if r['case_id']=='LCH01')['obligations'][0]['complete']=None
        r=self.score(engineering=changed)
        self.assertAlmostEqual(r['metrics']['earned']['upper']-r['metrics']['earned']['lower'],25*4/12+15/2/3+20)
        changed=copy.deepcopy(self.inputs);changed['slots']=[r for r in changed['slots'] if r['slot_id']!='MG-GP001:A1']
        r=self.score(inputs=changed)
        self.assertAlmostEqual(r['metrics']['earned']['upper']-r['metrics']['earned']['lower'],25*5/12+20)
        self.assertEqual(r['whole_task_counts']['planned'],34)

    def test_a2_and_written_followups_do_not_change_current_scores(self):
        changed=copy.deepcopy(self.inputs);changed['slots']=[r for r in changed['slots'] if r['slot_id'].endswith(':A1')]
        self.assertEqual(self.score(inputs=changed)['metrics'],self.score()['metrics'])

    def test_partial_selfcheck_can_be_negative_without_renormalization(self):
        r=score_assessment_record_inputs(self.inputs,self.review,self.policy,formalization_review=self.engineering,
            assessment_policy=self.assessment_policy,strict_policy=self.strict_policy)
        self.assertEqual(r['metrics']['lean-selfcheck']['exact'],-20)
        self.assertEqual(r['contributions']['lean-selfcheck']['exact'],-2)
        self.assertIsNone(r['metrics']['overall']['exact'])

    def test_source_judgments_and_legacy_source_math_remain_unchanged(self):
        original=copy.deepcopy((self.inputs,self.review,self.policy,self.engineering))
        before=score_record_inputs(self.inputs,self.review,self.policy,formalization_review=self.engineering)
        self.score()
        self.assertEqual((self.inputs,self.review,self.policy,self.engineering),original)
        self.assertEqual(before,score_record_inputs(self.inputs,self.review,self.policy,formalization_review=self.engineering))

    def test_policy_cannot_add_numeric_cutoff_or_remove_trajectory(self):
        for key,value in [('numeric_pass_threshold',95),('include_alignment_trajectory',False),('followups_replace_A1',True),('version','unknown')]:
            with self.subTest(key=key),self.assertRaisesRegex(ValueError,'scoring policy'):
                self.score(policy=dict(self.strict_policy,**{key:value}))

    def test_contradictory_source_pass_is_rejected(self):
        changed=copy.deepcopy(self.inputs)
        next(r for r in changed['slots'] if r['slot_id']=='MG-GR023:A1')['strict_pass']=True
        with self.assertRaisesRegex(ValueError,'contradicts'):self.score(inputs=changed)


class StrictTrajectoryTests(unittest.TestCase):
    def setUp(self):
        self.policy=alignment_policy();self.ids=self.policy['obligation_ids']
    def review(self):
        return alignment_review(self.policy,self.ids[:74],round_passes=[self.ids[:83],self.ids,self.ids],
            diagnoses=[(10,20,False,True),(10,20,True,True),(10,20,True,True)])
    def score(self,r):return strict_alignment_trajectory(r,self.policy)
    def test_initial_incomplete_can_be_repaired_with_accurate_three_round_trajectory(self):
        r=self.score(self.review());self.assertTrue(r['strict_pass']);self.assertFalse(r['initial_answer_replaced'])
    def test_final_complete_does_not_erase_false_claim_diagnosis_error_or_regression(self):
        for kind in ('false_claim','diagnosis','regression','delivery'):
            r=self.review()
            if kind=='false_claim':r['rounds'][0]['diagnosis']['claims_complete']=True
            if kind=='diagnosis':r['rounds'][0]['diagnosis']['localization_points']=19
            if kind=='regression':r['rounds'][1]['snapshot']['obligations'][0]['complete']=False
            if kind=='delivery':r['rounds'][0]['snapshot']['delivery_verified']=False
            with self.subTest(kind=kind):self.assertFalse(self.score(r)['strict_pass'])
    def test_final_missing_obligation_fails_and_unknown_delivery_stays_unknown(self):
        r=self.review();r['rounds'][-1]['snapshot']['obligations'][-1]['complete']=False
        self.assertFalse(self.score(r)['strict_pass'])
        r=self.review();r['rounds'][0]['snapshot']['delivery_verified']=None
        self.assertIsNone(self.score(r)['strict_pass'])
    def test_missing_round_is_unknown_not_best_of_two(self):
        r=self.review();r['rounds'].pop();s=self.score(r)
        self.assertIsNone(s['strict_pass']);self.assertEqual(len(s['rounds']),3)
