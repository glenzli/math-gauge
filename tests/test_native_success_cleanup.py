"""Synthetic source admission cases, not candidate calls or mathematics."""
import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from math_gauge.records import descriptor, _native_research_completed

class NativeSuccessCleanupTests(unittest.TestCase):
    def setUp(self):
        t=tempfile.TemporaryDirectory();self.addCleanup(t.cleanup);self.root=Path(t.name)
        def put(name,data):
            p=self.root/name;p.write_bytes(data if isinstance(data,bytes)else(json.dumps(data)+'\n').encode());return descriptor(self.root,p)
        self.put=put
        task=put('task.md',b'SYNTHETIC TASK');answer=put('answer.md',b'SYNTHETIC ANSWER')
        self.event={'event':'result','result':{'status':'SUCCESS','response':'SYNTHETIC ANSWER'}}
        self.terminal=put('terminal.json',self.event)
        events=put('events.ndjson',(json.dumps(self.event)+'\n').encode())
        self.seal=put('seal.json',dict(native_status='SUCCESS',normal_complete_delivery=True,answer_sha256=answer['sha256'],raw_terminal_sha256=self.terminal['sha256']))
        qual=put('qualification.json',dict(collection_status='qualified',answer_sha256=answer['sha256'],checks={k:True for k in ['native_success','first_native_terminal_exact','native_final_text_exact_utf8','input_matches_frozen_candidate_message']}))
        self.execution=dict(status='failed',exit_code=-9,kind='math',request_count=1,tool_mismatch=None,failure={'message':'CLI failed or violated tools policy'},artifact_hashes={'input/task.md':task['sha256'],'output/events.ndjson':events['sha256']})
        ed=put('execution.json',self.execution)
        self.row=dict(response=answer,original_input=task,execution=ed,execution_plan=put('plan.json',{'client':'agy'}))
        self.receipt=dict(schema='math-gauge.native-success-cleanup-admission/v1',post_observation=True,source_raw_bytes_rewritten=False,native_execution=ed,candidate_input=task,answer_sha256=answer['sha256'],native_events=events,native_terminal_event=self.terminal,native_terminal_seal=self.seal,collection_qualification=qual)
        self.save()
    def save(self):self.row['native_delivery_receipt']=self.put('receipt.json',self.receipt)
    def test_exact_native_success_does_not_rewrite_failed_cleanup(self):
        before=(self.root/'execution.json').read_bytes()
        self.assertTrue(_native_research_completed(self.root,self.row,self.execution))
        self.assertEqual((self.root/'execution.json').read_bytes(),before)
        self.assertEqual(self.execution['exit_code'],-9)
    def test_readable_error_done_or_different_final_bytes_never_qualify(self):
        for status in ['ERROR','DONE']:
            event=copy.deepcopy(self.event);event['result']['status']=status
            self.receipt['native_terminal_event']=self.put('terminal.json',event)
            self.receipt['native_events']=self.put('events.ndjson',(json.dumps(event)+'\n').encode())
            self.execution['artifact_hashes']['output/events.ndjson']=self.receipt['native_events']['sha256'];self.save()
            with self.subTest(status=status),self.assertRaises(ValueError):_native_research_completed(self.root,self.row,self.execution)
        self.row['response']=self.put('different-answer.md',b'UNRELATED READABLE ANSWER');self.save()
        with self.assertRaises(ValueError):_native_research_completed(self.root,self.row,self.execution)
    def test_no_receipt_preserves_legacy_completed_exit_zero_rule(self):
        self.row.pop('native_delivery_receipt')
        self.assertFalse(_native_research_completed(self.root,self.row,self.execution))
        self.assertTrue(_native_research_completed(self.root,self.row,dict(self.execution,status='completed',exit_code=0)))

if __name__=='__main__':unittest.main()
