"""Named frontend provenance checks; synthetic metadata never establishes Lean passes."""
import copy
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
import math_gauge.lean_frontend as frontend
from math_gauge.catalog import digest_bytes,write_json
from math_gauge.execution import _candidate_policy

class LakeFrontendTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup);self.root=Path(self.temp.name).resolve()
        self.lean=self.root/'toolchain/bin/lean';self.lean.parent.mkdir(parents=True);self.lean.write_bytes(b'synthetic lean')
        self.plugin=self.root/'toolchain/lib/lean/libLake_shared.dylib';self.plugin.parent.mkdir(parents=True);self.plugin.write_bytes(b'synthetic trusted plugin')
        self.addCleanup(patch.stopall);patch.object(frontend,'LEAN_SHA256',digest_bytes(self.lean.read_bytes())).start();patch.object(frontend,'PLUGIN_SHA256',digest_bytes(self.plugin.read_bytes())).start()
        stage,build,scratch=[self.root/n for n in ['sources','build','scratch']]
        self.dep={'lean':str(self.lean),'lean_sha256':frontend.LEAN_SHA256,'search_paths':[]}
        self.env={'stage':str(stage),'build':str(build),'scratch':str(scratch),'LEAN_PATH':str(build)}
        (self.root/'compiler.sb').write_text(_candidate_policy(stage,build,scratch,self.dep))
        failure=b'error: elaboration function for `Lake.DSL.packageCommand` has not been implemented\n';(self.root/'failure.log').write_bytes(failure)
        previous={'module':'Main','source_sha256':'1'*64,'exit_code':0,'timeout':False,'argv':['ordinary-compiler'],'log_sha256':'2'*64,'olean_sha256':'3'*64}
        failed={'module':'lakefile','source_sha256':'4'*64,'exit_code':1,'timeout':False,'argv':['ordinary-compiler'],'log_sha256':digest_bytes(failure)}
        old={'schema':'math-gauge.candidate-lean/v1','case_id':'SYNTHETIC','status':'compile_error','source_repaired':False,'response_sha256':'5'*64,'request_sha256':'6'*64,'dependency':self.dep,'modules':[previous,failed]}
        write_json(self.root/'old.json',old)
        report=copy.deepcopy(old);report.update(status='passed',isolation={'fixture_only':True},audit={'fixture_only':True})
        reused=dict(previous,reused_original_compilation=True)
        adapted=[]
        for name in ['lakefile','GaugeCandidateAudit_fixture']:
            argv=['/usr/bin/sandbox-exec','-f',str(self.root/'actual-policy.sb'),str(self.lean),'--plugin='+str(self.plugin),'--root='+str(stage),'-o',str(build/(name+'.olean')),str(stage/(name+'.lean'))]
            adapted.append({'module':name,'source_sha256':'4'*64,'exit_code':0,'timeout':False,'argv':argv,'log_sha256':'7'*64,'olean_sha256':'8'*64,'reused_original_compilation':False})
        report['modules']=[reused,*adapted]
        source=Path(frontend.__file__).resolve().parents[1]/'scripts/formal/lake_frontend_adapter.py'
        value={'schema':frontend.SCHEMA,'name':frontend.NAME,'source_sha256':digest_bytes(source.read_bytes()),'plugin_path':str(self.plugin),'plugin_sha256':frontend.PLUGIN_SHA256,'original_failed_report':{'path':'old.json','sha256':digest_bytes((self.root/'old.json').read_bytes())},'original_failure_log':{'path':'failure.log','sha256':digest_bytes(failure)},'reused_module_names':['Main'],'environment':self.env,'policy_argument':str(self.root/'actual-policy.sb'),'script_executions':0,'candidate_calls':0,'source_bytes_changed':False,'base_engine_files_unchanged':True}
        trace={'schema':'math-gauge.named-frontend-diagnostic/v1','status':'passed','source_report_sha256':value['original_failed_report']['sha256'],'source_response_sha256':report['response_sha256'],'base_engine_identity':None,'environment':self.env,'isolation':report['isolation'],'audit':report['audit'],'source_repaired':False,'candidate_calls':0,'script_executions':0,'adapter':{k:value[k] for k in ['name','source_sha256','plugin_path','plugin_sha256']},'modules':report['modules']}
        write_json(self.root/'diagnostic.json',trace);value['diagnostic_receipt']={'path':'diagnostic.json','sha256':digest_bytes((self.root/'diagnostic.json').read_bytes())};report['frontend_adapter']=value;self.receipt=report

    def test_named_metadata_binds_original_failure_reuse_and_actual_plugin_argv(self):
        frontend.validate_frontend_adapter(self.root,self.receipt)
        legacy={'modules':[{'argv':['ordinary-compiler']} ]}
        frontend.validate_frontend_adapter(self.root,legacy)

    def test_no_anonymous_plugin_or_unrecognized_adapter_can_be_accepted(self):
        for change in [lambda r:r.pop('frontend_adapter'),lambda r:r['frontend_adapter'].update(name='arbitrary-plugin'),lambda r:r['frontend_adapter'].update(source_sha256='0'*64)]:
            row=copy.deepcopy(self.receipt);change(row)
            with self.subTest(change=change),self.assertRaises(ValueError):frontend.validate_frontend_adapter(self.root,row)

    def test_plugin_replacement_or_unsafe_argv_is_rejected(self):
        for change in [lambda r:r['frontend_adapter'].update(plugin_path='/tmp/untrusted-plugin'),lambda r:r['modules'][-2]['argv'].append('--run'),lambda r:r['frontend_adapter']['environment'].update(LEAN_PATH='/tmp/untrusted'),lambda r:r['frontend_adapter'].update(script_executions=1)]:
            row=copy.deepcopy(self.receipt);change(row)
            with self.subTest(change=change),self.assertRaises(ValueError):frontend.validate_frontend_adapter(self.root,row)
        self.plugin.write_bytes(b'replaced plugin')
        with self.assertRaises(ValueError):frontend.validate_frontend_adapter(self.root,self.receipt)

    def test_original_failure_or_reused_module_or_diagnostic_drift_is_rejected(self):
        for change in [lambda r:r['frontend_adapter']['original_failed_report'].update(sha256='0'*64),lambda r:r['modules'][0].update(olean_sha256='0'*64),lambda r:r['frontend_adapter']['diagnostic_receipt'].update(sha256='0'*64),lambda r:r['frontend_adapter'].update(reused_module_names=[])]:
            row=copy.deepcopy(self.receipt);change(row)
            with self.subTest(change=change),self.assertRaises(ValueError):frontend.validate_frontend_adapter(self.root,row)

    def test_policy_relaxation_is_rejected(self):
        with (self.root/'compiler.sb').open('a') as file:file.write('(allow network*)\n')
        with self.assertRaisesRegex(ValueError,'strict compiler policy'):frontend.validate_frontend_adapter(self.root,self.receipt)
