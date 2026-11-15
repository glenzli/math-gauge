import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from math_gauge import stage_credit_reviews
from math_gauge.reliability_review import review_binding


class SourceStageCreditTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name)
        self.contract={'schema':'math-gauge.group-contract/v2','id':'WRITTEN',
            'version':'0.1.0','kind':'progressive',
            'stages':[{'id':name,'points':points,'lean_required':False}
                      for name,points in [('objects',40),('dependencies',60),('result',70),('scope',30)]]}
        self.contract_desc=self.keep('contract.json',self.contract)
        self.answer=self.keep('answer.md',b'A verified piece of mathematical work.\n')
        case={'case_id':'WRITTEN','version':'0.1.0','component':'exploration',
              'source_suite':{'version':'0.6.0'},
              'group_contract_sha256':self.contract_desc['sha256'],'request_sha256':'a'*64}
        self.slot={'slot_id':'WRITTEN:A1','case_id':'WRITTEN','kind':'independent',
                   'attempt_label':'A1','parent_slot':None}
        plan={'case_index':[case],'slots':[self.slot],'model_label':'candidate-test',
              'reliability':{'selection':{'cases':[]}}}
        self.meta={'plan':plan,'plan_sha256':'b'*64}
        material={'parent_slot':None,'parent_response_sha256':None,'parent_material_sha256':None,
            'material_sha256':'c'*64,'body_origin':'response','body_sha256':self.answer['sha256'],
            'rationale_sha256':None,'status':'resolved','mode':'INITIAL'}
        record={'case_id':'WRITTEN','slot_id':'WRITTEN:A1','evidence_id':'test',
            'response_sha256':self.answer['sha256'],'history_sha256':'d'*64,
            'projected_request_sha256':'e'*64,'prompt_sha256':'f'*64,'material':material}
        self.records={'WRITTEN:A1':record}
        self.original={'schema':stage_credit_reviews.SOURCE_SCHEMA,'case_id':'WRITTEN',
            'model_label':'candidate-test','reviewer_kind':'ai','human_review':'pending',
            'formal_comparison_eligible':False,'source_kind':'first_normal_native_final',
            'original_case_version':'0.1.0','frozen_case_contract_sha256':self.contract_desc['sha256'],
            'original_source':self.answer,
            'original_execution':{'sha256':'1'*64},'terminal_seal':{'sha256':'2'*64},
            'native_terminal':{'sha256':'3'*64},
            'credit_units':[{'id':s['id'],'maximum':s['points'],
                'earned':15 if s['id']=='scope' else s['points'],
                'reason':'Specific original proof and scope judgment for '+s['id']}
                for s in self.contract['stages']],
            'complete':False,'findings':[],'original_quotes':['verified piece'],
            'notes':'Original full proof review retains a partial scope result.'}
        self.original_desc=self.keep('original-review.json',self.original)
        self.review=stage_credit_reviews.build_review(self.original,
            original_review=self.original_desc,contract_sha256=self.contract_desc['sha256'],
            binding=review_binding(self.meta,record))
        self.admission={'native_execution':{'sha256':'1'*64},
            'native_terminal_seal':{'sha256':'2'*64},'native_terminal_event':{'sha256':'3'*64}}
        self.row={'response':self.answer,'source':{'case_contract':self.contract_desc},
            'agy_native_evidence':self.keep('admission.json',self.admission)}

    def keep(self,name,value):
        raw=value if isinstance(value,bytes) else json.dumps(value).encode()
        p=self.root/name;p.write_bytes(raw)
        return {'path':name,'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()}

    @staticmethod
    def read(root,d):
        b=(root/d['path']).read_bytes()
        if len(b)!=d['bytes'] or hashlib.sha256(b).hexdigest()!=d['sha256']:
            raise ValueError('Evidence bytes changed')
        return b

    def replay(self):
        with patch('math_gauge.agy_evidence.validate_delivery',return_value={'delivered':True}) as native:
            result=stage_credit_reviews.validate_entry(self.root,self.meta,self.records,self.review,
                source_row=self.row,evidence_reader=self.read)
            native.assert_called_once_with(self.root,self.row,self.read)
            return result

    def test_fractional_original_credit_is_not_rounded_to_binary(self):
        result=self.replay()
        self.assertEqual(result['completion'],{'lower':0.925,'upper':0.925,'exact':0.925})
        self.assertFalse(result['strict_pass'])
        self.assertEqual(result['group_diagnostic']['completed_weight'],185.0)
        self.assertEqual(result['group_diagnostic']['total_weight'],200)
        self.assertEqual(json.loads(self.read(self.root,self.contract_desc)),self.contract)

    def test_modified_credit_maximum_order_or_strict_is_rejected(self):
        for field in ['earned','maximum','order','strict','findings']:
            with self.subTest(field=field):
                original=copy.deepcopy(self.review)
                if field in {'earned','maximum'}:self.review['credit_units'][-1][field]+=1
                elif field=='order':self.review['credit_units'].reverse()
                elif field=='strict':self.review['complete']=True
                else:self.review['findings']=[{'reason':'invented source blocker'}]
                with self.assertRaises(ValueError):self.replay()
                self.review=original

    def test_contract_response_and_import_binding_are_preserved(self):
        for field in ['contract','response','binding']:
            with self.subTest(field=field):
                original=copy.deepcopy(self.review)
                if field=='contract':self.review['group_contract_sha256']='0'*64
                elif field=='response':self.review['source_answer_sha256']='0'*64
                else:self.review['binding']['history_sha256']='0'*64
                with self.assertRaises(ValueError):self.replay()
                self.review=original

    def test_false_quote_and_non_normal_final_are_rejected(self):
        self.review['original_quotes']=['invented quote']
        with self.assertRaises(ValueError):self.replay()
        self.review['original_quotes']=self.original['original_quotes']
        with patch('math_gauge.agy_evidence.validate_delivery',return_value={'delivered':False}):
            with self.assertRaises(ValueError):
                stage_credit_reviews.validate_entry(self.root,self.meta,self.records,self.review,
                    source_row=self.row,evidence_reader=self.read)

    def test_full_core_with_original_extra_false_claim_keeps_strict_false(self):
        self.original['credit_units'][-1]['earned']=30
        self.original['findings']=[{'kind':'false_assertion','reason':'An original independent false extra theorem.'}]
        self.original_desc=self.keep('original-review.json',self.original)
        self.review=stage_credit_reviews.build_review(self.original,original_review=self.original_desc,
            contract_sha256=self.contract_desc['sha256'],binding=review_binding(self.meta,self.records['WRITTEN:A1']))
        result=self.replay()
        self.assertEqual(result['completion']['exact'],1.0)
        self.assertFalse(result['strict_pass'])
        self.assertEqual(result['whole_math']['reasons'],['mathematical_error'])

    def test_ordinary_binary_review_cannot_enter_exception_schema(self):
        self.original['credit_units'][-1]['earned']=0
        self.original_desc=self.keep('original-review.json',self.original)
        self.review=stage_credit_reviews.build_review(self.original,original_review=self.original_desc,
            contract_sha256=self.contract_desc['sha256'],binding=review_binding(self.meta,self.records['WRITTEN:A1']))
        with self.assertRaisesRegex(ValueError,'Ordinary binary'):self.replay()

    def test_logical_alias_preserves_original_model_and_native_attempt(self):
        self.meta['plan']['model_label']='Logical Candidate Alias'
        self.review['logical_model_label']='Logical Candidate Alias'
        self.assertEqual(self.replay()['completion']['exact'],0.925)
        self.assertEqual(self.review['source_model_label'],'candidate-test')
        self.assertFalse(self.review['backend_identity_inferred'])
        for field in ['native_execution','native_terminal_seal','native_terminal_event']:
            with self.subTest(field=field):
                changed=copy.deepcopy(self.admission);changed[field]['sha256']='9'*64
                self.row['agy_native_evidence']=self.keep('admission.json',changed)
                with self.assertRaisesRegex(ValueError,'another native'):self.replay()
        self.row['agy_native_evidence']=self.keep('admission.json',self.admission)


if __name__=='__main__':
    unittest.main()
