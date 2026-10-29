"""Synthetic archive/replay fixtures. Never real CLI, model or mathematical results."""
import contextlib
import io
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
import supplement_preflight as preflight

import r005_supplement as s
import supplement_archive as a
from test_r005_supplement import fixture
from math_gauge.review import compare_models


class ArchiveTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory(prefix="math-gauge-supplement-synthetic-",dir="/private/tmp")
        self.addCleanup(self.tmp.cleanup)
        self.base=Path(self.tmp.name);self.root=self.base/"temporary-run"
        original,_=fixture(self.base)
        self.suite=s.snapshot_suite(original,self.root/"frozen-suites/public")
        self.cid=s.CASE
        self.request=self.suite.request(self.suite.cases[self.cid])
        self.message=s.candidate_message(self.request)
        self.item={"case_id":self.cid,"version":s.VERSION,"task_kind":"written","family_id":"synthetic",
                   "section":"synthetic","author_lean_coverage":"synthetic-only","suite_root":str(self.suite.root),
                   "suite_sha256":self.suite.sha256,"request_sha256":s.text_digest(json.dumps(self.request,ensure_ascii=False,sort_keys=True)),
                   "candidate_message_sha256":s.text_digest(self.message),"sessions":{}}
        self.runs={};self.receipts={};self.final=[];self.events=[]
        for model in s.MODELS:self.model_fixture(model)
        s.save(self.root/"runtime/model-runs.json",{"model_runs":self.runs,"execution_receipts":self.receipts})
        s.save(self.root/"runtime/catalog.frozen.json",{"synthetic":True})
        s.save(self.root/"preflight/qualification.json",{"passed":True,"mathematical_requests":0,"bindings":[]})
        s.save(self.root/"adoption.json",{"synthetic":True,"all_reviews_included":True})
        self.freeze={"schema":"math-gauge.comparison-freeze/v1","experiment":"r005-clarified-supplement",
            "cases":[self.item],"model_order":list(s.MODELS),"timeout_seconds":2700,"automatic_retry":False,
            "planned_mathematical_requests":2,"effective_parallel_per_model":1,
            "supplement_script_sha256":s.digest(s.__file__),"catalog_path":str(self.root/"runtime/catalog.frozen.json"),
            "catalog_sha256":s.digest(self.root/"runtime/catalog.frozen.json"),"code_identity":s.code_identity(),
            "runner_sha256":s.runner_fingerprint(),"preflight_bindings":[s.bound(self.root/"adoption.json")],
            "suite_snapshots":[{"root":str(self.suite.root),"suite_sha256":self.suite.sha256}],
            "adoption_gate":s.bound(self.root/"adoption.json")}
        s.save(self.root/"runtime/snapshot-plan.json",self.freeze)
        s.save(self.root/"runtime/freeze.json",self.freeze)
        s.save(self.root/"runtime/root-release.json",{"schema":"math-gauge.comparison-release/v1","released_by":"/root",
            "allow_mathematical_requests":True,"freeze_sha256":s.digest(self.root/"runtime/freeze.json"),
            "catalog_sha256":self.freeze["catalog_sha256"],"model_order":list(s.MODELS),"synthetic_test_only":True})
        s.save(self.root/"runtime/queue-start.json",{"release_sha256":s.digest(self.root/"runtime/root-release.json"),
            "freeze_sha256":s.digest(self.root/"runtime/freeze.json")})
        s.save(self.root/"runtime/queue-final.json",{"completed":True,"results":self.final})
        s.save(self.root/"runtime/queue-status.json",{"results":self.final})
        (self.root/"runtime/progress.ndjson").write_text(''.join(json.dumps(x)+'\n' for x in self.events))
        self.comparison=self.base/"results/comparison.json"
        s.save(self.comparison,compare_models([self.item],self.runs,execution_receipts=self.receipts))
        self.review_manifest=self.base/"results/reviews/manifest.json"
        review=self.review_manifest.parent/"primary.json";s.save(review,{"synthetic":True,"note":"not a real mathematical judgment"})
        s.save(self.review_manifest,{"schema":"math-gauge.supplement-review-manifest/v1","all_reviews_included":True,
                                    "files":[{"path":"primary.json","sha256":s.digest(review)}]})

    def model_fixture(self,model):
        session=self.root/"sessions"/model/self.cid;self.item["sessions"][model]=str(session)
        label="synthetic-"+model+"/none"
        run=self.root/"records"/model/self.cid
        response="Synthetic local transport fixture, never a model answer."
        command=[sys.executable,"-c","import json,sys;json.load(sys.stdin);sys.stdout.write("+repr(response)+")"]
        meta=s.runner_run(self.suite,run,ids=[self.cid],command=command,model=label)
        record=s.load(run/self.cid/"record.json")
        for sub in ("input","output","runtime"):(session/sub).mkdir(parents=True,exist_ok=True)
        (session/"input/task.md").write_text(self.message)
        (session/"output/response.md").write_text(response)
        (session/"output/events.ndjson").write_text(json.dumps({"type":"turn.completed","synthetic":True})+'\n')
        (session/"output/stderr.txt").write_text('')
        identity=self.root/"identity"/model/"identity.json"
        s.save(identity,{"sha256":"synthetic-executable","commands":[],"synthetic":True})
        s.save(session/"runtime/cli-identity.json",s.load(identity))
        s.save(self.root/"config"/(model+".json"),{"cli_identity":str(identity),"model":"synthetic-"+model,"effort":"none"})
        s.save(session/"runtime/plan.json",{"client":"codex","model":"synthetic-"+model,"effort":"none","credential_links":[],"stdin_file":str(session/"input/task.md"),"synthetic":True})
        s.save(session/"runtime/attempt-ledger.json",{"attempts":[{"kind":"math","request_count":1,"synthetic":True}]})
        for name in ("parent-pid-check.json","worker-pid-check.json","open-probe.json","network-probe.json"):
            s.save(session/"runtime"/name,{"passed":True,"synthetic":True})
        hashes={name:s.digest(session/name) for name in ("input/task.md","output/response.md","output/events.ndjson","output/stderr.txt")}
        execution={"status":"completed","request_count":1,"requested_model":"synthetic-"+model,"requested_effort":"none",
            "observed_model":None,"observed_effort":None,"artifact_hashes":hashes,"tool_mismatch":None,"tool_events":[],
            "stdin_write_calls":1,"stdin_bytes_written":len(self.message.encode()),"parent_pid":123,
            "parent_identity":{"pid":123,"executable_sha256":"synthetic-executable"},
            "workers":[{"policy_evidence":str(session/"runtime/worker-pid-check.json")}],"synthetic":True}
        s.save(session/"runtime/execution.json",execution)
        receipt=run/self.cid/"execution-assessment.json"
        s.save(receipt,{"schema":"math-gauge.execution-assessment/v1","case_id":self.cid,"run_id":meta["run_id"],"model_label":label,
            "response_sha256":record["response_sha256"],"request_sha256":record["request_sha256"],
            "candidate_message_sha256":record["candidate_message_sha256"],"mathematical_request_count":1,
            "valid_for_comparison":True,"requested_model":"synthetic-"+model,"requested_effort":"none",
            "observed_model":None,"observed_effort":None,"outcome":"synthetic-test-only",
            "evidence":{"execution_sha256":s.digest(session/"runtime/execution.json"),"raw_artifacts":hashes,
                "local_audit":{"files":[{"path":"input/task.md","sha256":hashes["input/task.md"]}]}},"synthetic":True})
        s.save(run/"reviews.json",{self.cid:{"response_sha256":record["response_sha256"],"reviewer":"Synthetic test fixture",
            "reviewer_kind":"ai","decision":"pass","assumption_fidelity":"clean","proof_validity":"valid",
            "scope_accuracy":"correct","unnecessary_restriction":False,"notes":"Synthetic only; not a real math score."}})
        self.runs[label]=[str(run)];self.receipts[label]={self.cid:str(receipt)}
        self.final.append({"model":model,"case_id":self.cid,"record_root":str(run),"status":"completed","request_count":1})
        self.events.extend([{"model":model,"status":status,**({"case_id":self.cid} if status in ("starting","completed") else {})}
                            for status in ("model-phase-started","starting","completed","model-phase-completed")])

    def build_archive(self):
        target=self.base/"evidence-final"
        a.archive(self.root,target,self.comparison,self.review_manifest)
        return target

    def replay(self,archive,name):
        return subprocess.run([sys.executable,"-B",str(archive/"tools/supplement_replay.py"),"--archive",str(archive),"--output",str(self.base/name)],capture_output=True,text=True)

    def test_complete_pipeline_then_delete_source_and_replay_saved_code(self):
        report=a.audit(self.root)
        self.assertEqual(report["planned"],2);self.assertEqual(report["valid_executions"],2)
        self.assertTrue(report["global_integrity_passed"])
        archive=self.build_archive()
        manifest=s.load(archive/"manifest.json");names={x["path"] for x in manifest["files"]}
        self.assertTrue({"tools/supplement_archive.py","scoring/reviews/primary.json","preflight/qualification.json"}.issubset(names))
        self.assertEqual(sum(x.endswith('/reviews.json') for x in names),2)
        self.assertFalse(any('state' in Path(x).parts for x in names))
        hashes={str(p.relative_to(archive)):s.digest(p) for p in archive.rglob('*') if p.is_file()}
        shutil.rmtree(self.root);self.assertFalse(self.root.exists())
        result=self.replay(archive,"replayed")
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        check=s.load(self.base/"replayed/verification.json")
        self.assertTrue(check["matched"]);self.assertTrue(all(check["checks"].values()))
        self.assertEqual(hashes,{str(p.relative_to(archive)):s.digest(p) for p in archive.rglob('*') if p.is_file()})

    def test_missing_evidence_count_stays_unknown(self):
        session=Path(self.item['sessions']['terra'])
        (session/'runtime/execution.json').unlink()
        # No release-bound artifact was changed; this is the intentional missing evidence test.
        report=a.audit(self.root)
        row=next(x for x in report['rows'] if x['model']=='terra')
        self.assertIsNone(row['request_count']);self.assertFalse(row['valid_execution'])
        with self.assertRaises(ValueError):self.build_archive()

    def test_archive_rejects_missing_review_and_stale_score(self):
        label=next(iter(self.runs));review=Path(self.runs[label][0])/'reviews.json'
        data=s.load(review);data[self.cid]['decision']='fail';s.save(review,data)
        with self.assertRaisesRegex(ValueError,'Final comparison differs'):self.build_archive()

    def test_tampering_detected_before_offline_output(self):
        archive=self.build_archive();victim=archive/'records/terra'/self.cid/self.cid/'response.md'
        victim.write_text('tampered synthetic')
        result=self.replay(archive,'tampered-out')
        self.assertNotEqual(result.returncode,0);self.assertIn('Archive hash mismatch',result.stderr)
        self.assertFalse((self.base/'tampered-out').exists())

    def test_declared_preflight_proxy_and_capability_bytes_are_preserved(self):
        canary=self.root/'preflight/terra-disabled-synthetic'
        s.save(canary/'runtime/plan.json',{'synthetic':True})
        s.save(canary/'runtime/capability-verdict.json',{'passed':True,'synthetic':True})
        (canary/'output').mkdir();(canary/'output/events.ndjson').write_text('{"synthetic":true}\n')
        proxy=self.root/'preflight/proxy/https.json';s.save(proxy,{'synthetic':True,'passed':True})
        config_path=self.root/'config/terra.json';config=s.load(config_path);config['proxy_exception']={'evidence':[s.bound(proxy)]};s.save(config_path,config)
        s.save(self.root/'preflight/qualification.json',{'bindings':[s.bound(canary/'runtime/capability-verdict.json')]})
        archive=self.build_archive()
        self.assertEqual((archive/'preflight/proxy/https.json').read_bytes(),proxy.read_bytes())
        self.assertEqual((archive/'preflight/terra-disabled-synthetic/output/events.ndjson').read_bytes(),(canary/'output/events.ndjson').read_bytes())
        self.assertFalse((archive/'preflight-evidence').exists())

    def test_inherited_controls_need_no_new_canary_and_archive_raw_evidence(self):
        old=self.base/'original-control-archive';old_root=self.base/'deleted-old-controls';names=set()
        for model in s.MODELS:
            current_id=self.root/'identity'/model/'identity.json'
            identity=s.load(current_id);identity.update(client='codex',version='synthetic')
            s.save(current_id,identity)
            s.save(self.root/'preflight'/(model+'-model-inventory.json'),{'request_count':0,'synthetic':True})
            for mode in ('disabled','enabled'):
                relative=Path('preflight')/(model+'-'+mode)/'runtime'
                source=old/relative/'execution.json'
                execution={'status':'completed','request_count':1,'requested_model':'synthetic-'+model,'requested_effort':'none',
                           'tool_events':[{'name':'search_web'}] if mode=='enabled' else [],'synthetic':True}
                s.save(source,execution);s.save(old/relative/'cli-identity.json',identity)
                events=old/relative.parent/'output/events.ndjson';events.parent.mkdir(parents=True);events.write_text('{"synthetic":true}\n')
                s.save(old/'preflight'/(model+'-'+mode+'-verdict.json'),{'passed':True,'execution_path':str(old_root/relative/'execution.json'),
                         'execution_sha256':s.digest(source),'synthetic':True})
        for path in old.rglob('*'):
            if path.is_file():names.add(str(path.relative_to(old)))
        s.save(old/'manifest.json',{'synthetic':True})
        (self.root/'preflight/qualification.json').unlink()
        with patch.object(preflight,'original',return_value=(old,{'source_root':str(old_root)},names)),patch.object(s,'same_config',side_effect=lambda root,archive,old_root,model:s.load(root/'config'/(model+'.json'))):
            preflight.qualify(self.root,old)
        qualification=s.load(self.root/'preflight/qualification.json')
        self.assertEqual(qualification['non_math_requests'],0)
        self.assertEqual(qualification['inherited_control_requests'],len(s.MODELS)*2)
        self.assertTrue(any(x['path'].endswith('events.ndjson') for x in qualification['bindings']))
        archive=self.build_archive()
        mapping=s.load(archive/'binding-map.json')
        self.assertTrue(all(str(path) in mapping for path in old.rglob('events.ndjson')))
        self.assertTrue((archive/'preflight/control-reuse.json').is_file())

    def test_state_credentials_symlinks_and_unlisted_files_excluded(self):
        excluded=self.root/'state/auth.json';s.save(excluded,{'synthetic_private':'never-copy'})
        (self.root/'unlisted.txt').write_text('not declared')
        archive=self.build_archive()
        self.assertFalse((archive/'state').exists());self.assertFalse((archive/'unlisted.txt').exists())
        with self.assertRaises(ValueError):a.Whitelist(self.root).add(excluded)
        link=self.root/'link.txt';link.symlink_to(self.root/'unlisted.txt')
        with self.assertRaises(ValueError):a.Whitelist(self.root).add(link)


if __name__=='__main__':unittest.main()
