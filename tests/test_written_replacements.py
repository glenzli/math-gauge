"""A public replacement cannot inherit a retired answer or hide an unrun slot."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from assessment_fixtures import before_submission_policy

import test_case_selection as legacy_selection
from math_gauge.records import descriptor, validate_public_written_replacements
from math_gauge.scoring import score_assessment_inputs
from math_gauge.written_replacements import validate_inputs

ROOT = Path(__file__).resolve().parents[1]


class WrittenReplacementsTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        legacy_selection.CaseSelectionTests.setUpClass()
        cls.baseline = legacy_selection.CaseSelectionTests()
        cls.policy = before_submission_policy(json.loads((ROOT/'protocol/scoring-policy.json').read_bytes()))
        cls.strict = json.loads((ROOT/'protocol/strict-scoring-policy.json').read_bytes())

    def data(self, points=94):
        return {'schema':'math-gauge.written-replacements-inputs/v1', 'benchmark_version':'0.6.0',
            'policy':self.policy['written_argument_replacements'], 'attempt_labels':['A1'],
            'model_label':self.baseline.inputs()['model_label'], 'human_review':'pending',
            'formal_comparison_eligible':False, 'case_index':[{
                'case_id':'MG-PS001', 'family_id':'density-sampling-quotient', 'replaces':'MG-GR103',
                'component':'proofs', 'source_visibility':'public', 'contract_kind':'written_proof',
                'task_kind':'written', 'criteria':[{'criterion_id':'proof','points':100}],
                'total_weight':100, 'task_sha256':'a'*64, 'contract_sha256':'b'*64}],
            'slots':[{'case_id':'MG-PS001','slot_id':'MG-PS001:A1','attempt_label':'A1',
                'status':'not_run' if points is None else 'response_received', 'points':points,
                'complete':None if points is None else points==100,
                'response':None if points is None else {'sha256':'c'*64},
                'review':None if points is None else {'sha256':'d'*64},
                'source_review':None if points is None else {'sha256':'e'*64}}]}

    def score(self, data, inputs=None, mode='partial'):
        return score_assessment_inputs(self.baseline.inputs() if inputs is None else inputs,
            self.policy, self.strict, mode=mode, written_replacement_inputs=data)

    def test_retired_full_credit_cannot_affect_replacement_or_denominator(self):
        inputs=self.baseline.inputs(); original=copy.deepcopy(inputs)
        low=copy.deepcopy(inputs)
        retired=next(r for r in low['slots'] if r['case_id']=='MG-GR103')
        retired.update(completion={'lower':0,'upper':0,'exact':0},strict_pass=False)
        for mode in ('partial','strict'):
            with self.subTest(mode=mode):
                result=self.score(self.data(),inputs,mode)
                self.assertEqual(result,self.score(self.data(),low,mode))
                self.assertNotIn('MG-GR103',{t['case_id'] for t in result['tasks']})
                self.assertEqual(result['metrics']['written-argument']['coverage']['planned'],12)
        self.assertEqual(inputs,original)

    def test_new_unrun_stays_unknown_despite_retired_success(self):
        unknown=self.score(self.data(None))
        task=next(t for t in unknown['tasks'] if t['case_id']=='MG-PS001')
        self.assertIsNone(task['completion']['exact']); self.assertIsNone(task['strict_pass'])
        known=self.score(self.data(100))
        self.assertAlmostEqual(known['contributions']['written-argument']['confirmed']-
                               unknown['contributions']['written-argument']['confirmed'],25/12)
        for update in ({'points':100},{'complete':True},{'response':{'sha256':'c'*64}}):
            data=self.data(None); data['slots'][0].update(update)
            with self.subTest(update=update),self.assertRaises(ValueError):
                validate_inputs(data,self.policy['written_argument_replacements'])

    def test_replacement_needs_its_own_bound_input_and_model(self):
        with self.assertRaisesRegex(ValueError,'replacement evidence is required'):
            self.score(None)
        data=self.data();data['model_label']='another-model'
        with self.assertRaisesRegex(ValueError,'different model'):
            self.score(data)
        data=self.data();data['case_index'][0]['family_id']=self.baseline.inputs()['plan']['case_index'][0]['family_id']
        with self.assertRaises(ValueError):self.score(data)

    def test_fresh_current_plan_binds_its_own_replacement_without_legacy_supplement(self):
        from math_gauge.benchmarks import BenchmarkProfile, build_plan
        from math_gauge.catalog import Suite
        suite=Suite.load(ROOT/'cases')
        plan=build_plan(BenchmarkProfile.load(ROOT/'protocol/benchmark-profile.json',suite),suite)
        result=score_assessment_inputs({'plan':plan,'model_label':plan['model_label'],'slots':[]},
                                       self.policy,self.strict)
        task=next(t for t in result['tasks'] if t['case_id']=='MG-PS001')
        self.assertIsNone(task['completion']['exact'])
        self.assertIsNone(task['strict_pass'])
        self.assertNotIn('MG-GR103',{t['case_id'] for t in result['tasks']})

    def test_public_projection_rejects_native_paths_and_unrun_fabrication(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            data={'schema':'math-gauge.written-replacements-public-evidence/v1',
                  'public_case_ids':['MG-PS001'],'source_inputs_sha256':'a'*64,'human_review':'pending',
                  'formal_comparison_eligible':False,'slots':[{
                      'case_id':'MG-PS001','attempt_label':'A1','status':'not_run',
                      'points':None,'complete':None,'response':None,'source_review':None}]}
            def check():
                (root/'evidence.json').write_text(json.dumps(data))
                return validate_public_written_replacements(root,{
                    'written_replacement_evidence':descriptor(root,root/'evidence.json')})
            check()
            data['slots'][0]['actual_path_checks']={'path':'private-native-probes.json'}
            with self.assertRaises(ValueError):check()
            del data['slots'][0]['actual_path_checks'];data['slots'][0]['points']=0
            with self.assertRaises(ValueError):check()


if __name__=='__main__':unittest.main()
