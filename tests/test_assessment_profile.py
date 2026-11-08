"""Current hierarchy and no-followup exports; all grades here are synthetic."""
import copy
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from math_gauge.benchmarks import BenchmarkProfile,build_plan,validate_assessment_policy,select_slots
from math_gauge.catalog import Suite
from math_gauge.harness import export_harness_bundle,inspect_harness_bundle
from math_gauge.scoring import score_inputs,score_assessment_inputs,public_score_projection
from test_scoring import fixture_rows

ROOT=Path(__file__).resolve().parents[1]
class CurrentAssessmentTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.suite=Suite.load(ROOT/'cases')
        cls.profile=BenchmarkProfile.load(ROOT/'protocol/benchmark-profile.json',cls.suite)
        cls.plan=build_plan(cls.profile,cls.suite,runtime={'model_label':'SYNTHETIC-CURRENT-ASSESSMENT',
            'adapter_identity':{'kind':'fixture'},'budget':{'timeout_seconds':10800},
            'execution_track':'math-gauge.local-tools-no-search/v1'})
        cls.policy=cls.profile.data['assessment_policy'];cls.strict=cls.profile.data['strict_policy']
    def inputs(self):return {'plan':self.plan,'model_label':self.plan['model_label'],'slots':fixture_rows(self.plan)}
    def test_current_schedule_only_contains_independent_a1(self):
        self.assertEqual(self.plan['planned'],{'papers':25,'independent_slots':25,'neutral_slots':0,
            'stance_slots':0,'all_slots':25,'selected_slots':25})
        self.assertTrue(all(s['kind']=='independent' and s['attempt_label']=='A1' for s in self.plan['slots']))
        for target in ('repeat','neutral','stance'):
            with self.assertRaises(ValueError):select_slots(self.plan,[target])
        self.assertEqual(self.plan['reliability']['selection']['cases'],[])
    def test_fixed_private_denominators_survive_complete_public_answers(self):
        r=score_assessment_inputs(self.inputs(),self.policy,self.strict,
            strict_trajectory={'strict_pass':True},mode='strict')
        self.assertAlmostEqual(r['metrics']['earned']['lower'],70-25*4/12+10/5)
        self.assertEqual(r['metrics']['earned']['upper'],100)
        self.assertIsNone(r['metrics']['earned']['exact'])
        self.assertEqual(r['metrics']['overall']['upper'],100)
        self.assertEqual(r['whole_task_counts'],{'planned':39,'passed':21,'failed':0,'unknown':18})
        self.assertEqual(r['metrics']['lean-selfcheck']['exact'],100)
        self.assertEqual(r['contributions']['lean-selfcheck']['exact'],10)
    def test_empty_run_does_not_invent_completed_tasks_or_normalize_scores(self):
        r=score_inputs({'plan':self.plan,'model_label':self.plan['model_label'],'slots':[]})
        self.assertIsNone(r['metrics']['overall']['exact'])
        self.assertEqual(r['capacity'],{'total':100,'active':100,'under_construction':0})
        self.assertEqual(r['metrics']['overall']['upper'],100)
        self.assertEqual(r['whole_task_counts']['unknown'],39)
        public=public_score_projection(r,self.plan,private_aliases={})
        self.assertNotIn('tasks',public);self.assertNotIn('slot_evidence',public)
    def test_family_first_formalization_and_merged_argument_pool(self):
        inputs=self.inputs()
        next(r for r in inputs['slots'] if r['case_id']=='MG-C003')['completion']={'lower':0,'upper':0,'exact':0}
        next(r for r in inputs['slots'] if r['case_id']=='MG-C003')['strict_pass']=False
        r=score_assessment_inputs(inputs,self.policy,self.strict)
        self.assertEqual(r['metrics']['lean-formalization']['exact'],50)
        self.assertEqual(r['contributions']['lean-formalization']['exact'],7.5)
        self.assertEqual(r['metrics']['written-argument']['coverage']['planned'],12)
    def test_policy_rejects_weight_source_or_fixed_population_drift(self):
        for key in ('weight','aggregation','source_components'):
            changed=copy.deepcopy(self.policy)
            changed['subcategories'][0][key]={'weight':24,'aggregation':'task','source_components':['proofs']}[key]
            with self.subTest(key=key),self.assertRaises(ValueError):validate_assessment_policy(changed)
        changed=copy.deepcopy(self.policy);changed['scope']['tasks']=26
        with self.assertRaises(ValueError):validate_assessment_policy(changed)
    def test_portable_export_contains_only_selected_a1_and_no_evaluator_policy(self):
        plan=build_plan(self.profile,self.suite,['c003-180'],runtime=self.plan['runtime'])
        with tempfile.TemporaryDirectory() as temporary:
            path=Path(temporary)/'bundle'
            with patch('subprocess.Popen',side_effect=AssertionError('no model calls')):
                export_harness_bundle(plan,self.suite,path)
                m=inspect_harness_bundle(path,plan=plan,suite=self.suite)
            self.assertEqual(m['exported_slots'],1);self.assertEqual(m['prompts'],[])
            text=(path/'manifest.json').read_text()
            self.assertNotIn('assessment_policy',text);self.assertNotIn('strict_policy',text)
            self.assertEqual(m['planned']['all_slots'],25)
    def test_current_plan_keeps_ar_families_after_their_source_parents_exit(self):
        from math_gauge.case_selection import CANONICAL_PARENT_FAMILIES, assessment_family
        cases={case['case_id']:case for case in self.plan['case_index']}
        self.assertTrue(set(CANONICAL_PARENT_FAMILIES).isdisjoint(cases))
        self.assertEqual({case['parent_family_id'] for case in cases.values()
                          if case['contract_kind']=='answer_review'},set(CANONICAL_PARENT_FAMILIES.values()))
        self.assertEqual(len({assessment_family(case,cases,self.policy['case_selection'])
                              for case in cases.values()}),21)

if __name__=='__main__':unittest.main()
