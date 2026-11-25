from copy import deepcopy
import hashlib
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

from math_gauge import dot_evidence_timing as now, dot_rerun_timings as old
from scripts import cost_reference


class ReplacementTimingTests(unittest.TestCase):
    root=Path(__file__).resolve().parents[1]

    def test_exact_same_call_timing_and_alternate_transport_binding(self):
        answer=b'raw'
        response=b'readable'
        request=b'frozen request'
        events=(dict(case='GP001',event=event,timestamp_utc='2026-11-25T15:00:'+stamp+'Z',
                         notes=hashlib.sha256(answer).hexdigest() if event=='terminal_observed' else '')
                for event,stamp in [('dispatch_begin','00'),('dispatch_ack','02'),('terminal_observed','40')])
        observed='\n'.join(map(json.dumps,events)).encode()
        native=dict(start_utc='2026-11-25T15:00:01Z',finish_utc='2026-11-25T15:00:39Z',
            start_monotonic_ns=4,finish_monotonic_ns=38_000_000_004,
            request_sha256=hashlib.sha256(request).hexdigest(),answer_sha256=hashlib.sha256(answer).hexdigest())
        with self.assertRaisesRegex(ValueError,'another submission'):
            now.read_receipt('MG-GP001:A1','GP001',observed,old.encoded(native),request,response)
        item=now.read_receipt('MG-GP001:A1','GP001',observed,old.encoded(native),request,response,prior_capture=answer)
        self.assertEqual((item['seconds'],item['native_work_seconds']),(40,38))
        self.assertNotEqual(item['answer_sha256'],item['physical_capture_sha256'])
        native['finish_utc']='2026-11-25T15:00:41Z'
        with self.assertRaisesRegex(ValueError,'outside'):
            now.read_receipt('MG-GP001:A1','GP001',observed,old.encoded(native),request,answer)

    def fixture(self):
        prior=now._read_prior(self.root)
        used=[]
        receipts={}
        for i,slot in enumerate(sorted(now.SLOTS),1):
            receipts[slot]=dict(answer_sha256=f'{i:064x}',
                seconds=None if slot==now.A1 else 80+i,bounds_seconds=[1357,1399] if slot==now.A1 else None,
                native_work_seconds=None if slot==now.A1 else 70+i)
        for record in prior['rows']:
            cid=record['case_id']
            item=receipts.get(cid+':A1')
            used.append(dict(case_id=cid,response_sha256=item['answer_sha256'] if item else record['answer_sha256'],
                            strict_pass=True if cid=='MG-C003' else record['strict_pass']))
        admission={'selection':{'sha256':'a'*64},'public_source':{'private_source_sha256':'b'*64},
            'revised':{'_public_tasks':{'views':{'strict':{old.CONDITION:{'tasks':used}}}}}}
        receipt=dict(subjects=receipts,private_ledger_sha256='b'*64,authorization_sha256='c'*64)
        return prior,admission,receipt

    def test_source_locked_projection_preserves_five_and_chapter_stays_a_range(self):
        if not (self.root/old.INDEX_PATH).is_file(): self.skipTest('preexisting Dot timing source not staged')
        prior,admission,receipt=self.fixture()
        new=now.prepare(self.root,admission,receipt)
        payload=json.loads(new[now.REPORT])
        self.assertEqual(payload['summaries']['daily']['timed'],12)
        self.assertIsNotNone(payload['summaries']['daily']['weighted_mean_seconds'])
        self.assertIsNone(payload['summaries']['MG-C003']['median_seconds'])
        for row in prior['rows']:
            if row['case_id'] in prior['shared_sample']['case_ids'] and row['seconds'] is not None:
                self.assertEqual(row,next(x for x in payload['rows'] if x['case_id']==row['case_id']))
        with TemporaryDirectory() as folder:
            folder=Path(folder)
            for key,val in {**new,old.INDEX_PATH:(self.root/old.INDEX_PATH).read_bytes(),
                old.DIRECTORY+'/timings.json':(self.root/old.DIRECTORY/'timings.json').read_bytes()}.items():
                path=folder/key;path.parent.mkdir(exist_ok=True,parents=True);path.write_bytes(val)
            chosen=now.load_public(folder,admission)
            self.assertEqual(chosen['chapter_bounds_seconds'],[1357,1399])
            self.assertEqual(chosen['cost']['total_usd'],0)
            bad=deepcopy(admission); bad['selection']['sha256']='d'*64
            with self.assertRaisesRegex(ValueError,'current exact'):
                now.load_public(folder,bad)

    def test_cost_appends_only_dot_and_does_not_impute_tokens(self):
        metric=dict(earned={'confirmed':66},overall=dict(exact=66,lower=66,upper=66))
        report={'metrics':metric}
        model=dict(id=old.MODEL,label=old.LABEL,theme={},logo={},retry={'combined':report},
                   capability={old.CONDITION:report},strict={old.CONDITION:report})
        costs=dict(benchmark_version='1.2.0',models=[dict(model_id='incumbent',presentation_eligibility={'ranked':False})])
        timing=dict(models=[dict(id=old.MODEL,summaries=dict(daily=dict(weighted_mean_seconds=95)))])
        selection=dict(cost=dict(total_usd=0,basis=now.COST_BASIS),source={'sha256':'d'*64})
        with patch.object(old,'load_public',return_value=selection):
            cost_reference.append_dot_subscription_cost('.',costs,timing,model)
        self.assertEqual(costs['models'][0],dict(model_id='incumbent',presentation_eligibility={'ranked':False}))
        self.assertEqual(costs['models'][-1]['total_usd'],0)
        self.assertEqual(costs['models'][-1]['seconds'],95)
        self.assertEqual(costs['models'][-1]['token_usage'],'unknown')
