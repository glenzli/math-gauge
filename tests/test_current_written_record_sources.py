"""Synthetic source-chain regression tests; no candidate calls or math grades."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

from math_gauge.benchmarks import BenchmarkProfile, build_plan, identity
from math_gauge.catalog import Suite, candidate_message
from math_gauge.records import descriptor, validate_current_written_reviews, selected_cli_records
from math_gauge.reliability import _new_slot_record, compose_material
from math_gauge.reliability_review import _validate_entry, review_binding
from math_gauge.review import _stage_template

ROOT = Path(__file__).resolve().parents[1]


class CurrentWrittenRecordSourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.suite = Suite.load(ROOT/'cases')
        cls.profile = BenchmarkProfile.load(ROOT/'protocol/benchmark-profile.json', cls.suite)
        cls.plan = build_plan(cls.profile, cls.suite, runtime={
            'model_label':'SYNTHETIC SOURCE-CHAIN SOFTWARE FIXTURE',
            'adapter_identity':{'kind':'fixture'}, 'budget':{'timeout_seconds':2700},
            'execution_track':'math-gauge.local-tools-no-search/v1'})
        cls.policy = cls.profile.data['assessment_policy']

    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.inputs = {'plan':self.plan, 'model_label':self.plan['model_label'], 'slots':[]}
        self.record = {'records':[], 'evidence':[]}
        for case in self.plan['case_index']:
            if case['component'] != 'proofs':
                continue
            cid, sid = case['case_id'], case['case_id']+':A1'
            original = self.suite.cases[cid]
            contract_raw = self.suite.case_file(original, original['group_contract']).read_bytes()
            contract = json.loads(contract_raw)
            request = self.suite.request(original)
            raw = b'SYNTHETIC SOFTWARE FIXTURE; NOT A MODEL ANSWER.\n'
            response = self.put(cid+'/answer.md',raw)
            contract_source = self.put(cid+'/contract.json',contract_raw)
            request_source = self.put(cid+'/request.json',request)
            slot = next(slot for slot in self.plan['slots'] if slot['slot_id']==sid)
            native = _new_slot_record(slot,{},'fixture','synthetic-software-fixture')
            material = compose_material(slot,raw)[0]
            native.update(started=True,status='responded',attempts=[{'status':'ok'}],locked_attempt=1,
                response_path=response['path'],response_sha256=response['sha256'],material=material,
                material_sha256=material['material_sha256'])
            meta = dict(plan=self.plan,plan_sha256=self.plan['plan_sha256'],
                inputs={cid:dict(contract=contract_source['path'],request=request_source['path'])})
            binding = review_binding(meta,native)
            review = dict(schema='math-gauge.reliability-review/v1', slot_id=sid, case_id=cid,
                binding=binding, reviewer='SYNTHETIC SOURCE-CHAIN TEST FIXTURE', reviewer_kind='ai',
                decision='partial', assumption_fidelity='clean', proof_validity='valid',
                scope_accuracy='correct', unnecessary_restriction=False,
                notes='Synthetic parser/arithmetic evidence only; no mathematical adjudication.', findings=[],
                group_contract_sha256=case['group_contract_sha256'],
                format_review={'decision':'valid','notes':'Synthetic complete input container.'})
            if contract['kind']=='written_proof':
                review['criteria']=[dict(criterion_id=c['id'],score=c['points']/2,
                    notes='Synthetic bounded criterion score.')for c in contract['criteria']]
            else:
                review['stages']=[]
                for stage in contract['stages']:
                    row=_stage_template(stage)
                    row.update(decision='partial',failure_category='mathematical',
                        notes='Synthetic known incomplete mathematical stage.',
                        math_review=dict(decision='partial',assumption_fidelity='unknown',
                            proof_validity='unknown',scope_accuracy='unknown',unnecessary_restriction=False,
                            reasons=['candidate_incomplete'],notes='Synthetic incomplete math axis.'))
                    review['stages'].append(row)
            review['review_sha256'] = identity(review)
            result = _validate_entry(self.root,meta,{sid:native},review)
            original_slot=self.put(cid+'/original-slot.json',native)
            scored = dict(slot_id=sid,case_id=cid,binding=binding,response_sha256=response['sha256'],
                review_sha256=review['review_sha256'],slot_record_sha256=original_slot['sha256'],**result)
            self.inputs['slots'].append(scored)
            self.record['records'].append(dict(id=sid,case_id=cid,kind='independent',parent_id=None,
                response=response,review=self.put(cid+'/review.json',review),
                source=dict(execution_plan_sha256=self.plan['plan_sha256'],response_sha256=response['sha256'],
                    candidate_request=request_source,slot_record=original_slot,
                    candidate_input=self.put(cid+'/candidate-input.txt',candidate_message(request).encode()),
                    case_contract=contract_source),
                evaluation=dict(completion=result['completion'],strict_pass=result['strict_pass'])))
        self.save_inputs()

    def put(self, name, value):
        path = self.root/name
        path.parent.mkdir(parents=True,exist_ok=True)
        path.write_bytes(value if isinstance(value,bytes) else json.dumps(value,ensure_ascii=False).encode())
        return descriptor(self.root,path)

    def save_inputs(self):
        self.record['evidence']=[self.put('scoring-inputs.json',self.inputs)]

    def check(self):
        return validate_current_written_reviews(self.root,self.record,policy=self.policy)

    def test_current_plan_uses_all_its_written_sources_without_legacy_supplement(self):
        result=self.check()
        self.assertEqual(len(result),8)
        self.assertIn('MG-PS001',result)
        self.assertNotIn('MG-GR103',result)

    def test_rebound_task_or_answer_cannot_inherit_source_credit(self):
        for kind in ('task','answer'):
            with self.subTest(kind=kind):
                before=copy.deepcopy(self.record)
                row=self.record['records'][0]
                if kind=='task':
                    request=json.loads((self.root/row['source']['candidate_request']['path']).read_bytes())
                    request['task']+='\nSYNTHETIC ALTERED TASK'
                    row['source']['candidate_request']=self.put('altered-request.json',request)
                    row['source']['candidate_input']=self.put('altered-input.txt',candidate_message(request).encode())
                else:
                    row['response']=self.put('altered-answer.md',b'SYNTHETIC REPLACEMENT ANSWER')
                    row['source']['response_sha256']=row['response']['sha256']
                with self.assertRaises(ValueError):self.check()
                self.record=before

    def test_changed_original_criteria_cannot_keep_copied_old_score(self):
        row=next(row for row in self.record['records'] if row['case_id']=='MG-PS001')
        review=json.loads((self.root/row['review']['path']).read_bytes())
        review['criteria'][0]['score']=0
        review['review_sha256']=identity({k:v for k,v in review.items() if k!='review_sha256'})
        row['review']=self.put('revised-review.json',review)
        next(slot for slot in self.inputs['slots'] if slot['case_id']=='MG-PS001')['review_sha256']=review['review_sha256']
        self.save_inputs()
        with self.assertRaisesRegex(ValueError,'criterion review'):self.check()

    def test_missing_review_or_missing_another_written_a1_is_not_an_exemption(self):
        row=self.record['records'].pop()
        with self.assertRaisesRegex(ValueError,'independent A1'):self.check()
        self.record['records'].append(row)
        del row['review']
        with self.assertRaisesRegex(ValueError,'original criterion review'):self.check()

    def use_distinct_scoring_index(self):
        # The retained original review continues to bind its own group plan.
        descriptor = self.put('original-import-plan.json', self.plan)
        scoring = copy.deepcopy(self.plan)
        scoring['plan_id'] = 'synthetic-post-observation-scoring-index'
        scoring['post_observation'] = True
        scoring['plan_sha256'] = identity({k:v for k,v in scoring.items() if k!='plan_sha256'})
        self.inputs['plan'] = scoring
        for row in self.record['records']:
            row['source']['scoring_plan_sha256'] = scoring['plan_sha256']
            row['source']['standard_import_plan'] = descriptor
        self.save_inputs()

    def test_composition_preserves_original_group_plan_and_review_binding(self):
        self.use_distinct_scoring_index()
        self.assertEqual(len(self.check()), 8)
        original = self.record['records'][0]
        self.assertNotEqual(original['source']['scoring_plan_sha256'],
                            original['source']['execution_plan_sha256'])
        self.assertEqual(json.loads((self.root/original['review']['path']).read_bytes())
                         ['binding']['plan_sha256'], self.plan['plan_sha256'])

    def test_composed_plan_needs_its_exact_retained_bytes(self):
        self.use_distinct_scoring_index()
        row = self.record['records'][0]
        retained = row['source'].pop('standard_import_plan')
        with self.assertRaisesRegex(ValueError, 'original import plan bytes'):
            self.check()
        row['source']['standard_import_plan'] = retained
        (self.root/retained['path']).write_bytes(b'{}')
        with self.assertRaises(ValueError):
            self.check()

    def test_valid_import_plan_cannot_change_source_request_or_criteria(self):
        self.use_distinct_scoring_index()
        row = self.record['records'][0]
        altered = copy.deepcopy(self.plan)
        next(c for c in altered['case_index'] if c['case_id']==row['case_id'])['request_sha256'] = '0'*64
        altered['plan_sha256'] = identity({k:v for k,v in altered.items() if k!='plan_sha256'})
        row['source']['standard_import_plan'] = self.put('altered-import-plan.json', altered)
        row['source']['execution_plan_sha256'] = altered['plan_sha256']
        with self.assertRaisesRegex(ValueError, 'source case or A1 contract'):
            self.check()

    def test_real_serialized_slot_reconstructs_material_without_rewriting_original(self):
        # Actual runs save material.json separately; inspection hydrates it.
        row=self.record['records'][0]
        original=json.loads((self.root/row['source']['slot_record']['path']).read_bytes())
        original.pop('material')
        row['source']['slot_record']=self.put('separate-material-slot.json',original)
        next(s for s in self.inputs['slots'] if s['slot_id']==row['id'])['slot_record_sha256']=row['source']['slot_record']['sha256']
        self.save_inputs()
        before=(self.root/row['source']['slot_record']['path']).read_bytes()
        self.assertEqual(len(self.check()),8)
        self.assertEqual((self.root/row['source']['slot_record']['path']).read_bytes(),before)

    def test_rehashed_slot_cannot_replace_original_material_identity(self):
        row=self.record['records'][0]
        original=json.loads((self.root/row['source']['slot_record']['path']).read_bytes())
        original.pop('material')
        original['material_sha256']='0'*64
        row['source']['slot_record']=self.put('altered-material-slot.json',original)
        next(s for s in self.inputs['slots'] if s['slot_id']==row['id'])['slot_record_sha256']=row['source']['slot_record']['sha256']
        self.save_inputs()
        with self.assertRaisesRegex(ValueError,'original material'):
            self.check()

    def test_legacy_plan_still_requires_legacy_supplement(self):
        path=ROOT/'results/v0.6.0/terra-6.1-max/20261105/scoring-inputs.json'
        original=json.loads(path.read_bytes())
        self.record['evidence']=[self.put('scoring-inputs.json',original)]
        with self.assertRaisesRegex(ValueError,'Legacy written evidence'):
            self.check()


class SelectedResultRecordTests(unittest.TestCase):
    def test_ambiguous_snapshots_need_an_explicit_selection_not_latest_or_best(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            edition = {'version': '0.6.0', 'selected_result_models': ['model-fixture']}
            for record_id in ('20261105', '20261108'):
                folder = root / 'results/v0.6.0/model-fixture' / record_id
                folder.mkdir(parents=True)
                (folder / 'record.json').write_text('{}')
            (root / 'benchmark.json').write_text(json.dumps(edition))
            with self.assertRaisesRegex(ValueError, 'exactly one'):
                selected_cli_records(root)
            edition['selected_result_record_ids'] = {'model-fixture': '20261105'}
            (root / 'benchmark.json').write_text(json.dumps(edition))
            self.assertEqual(selected_cli_records(root), [
                ('model-fixture', (root / 'results/v0.6.0/model-fixture/20261105').resolve())])

    def test_selected_model_and_record_cannot_traverse_to_private_files(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            for model, record_id in (('../private', '20261108'), ('model-fixture', '../private')):
                edition = {'version': '0.6.0', 'selected_result_models': [model],
                           'selected_result_record_ids': {model: record_id}}
                (root / 'benchmark.json').write_text(json.dumps(edition))
                with self.assertRaisesRegex(ValueError, 'safe'):
                    selected_cli_records(root)


if __name__=='__main__':
    unittest.main()
