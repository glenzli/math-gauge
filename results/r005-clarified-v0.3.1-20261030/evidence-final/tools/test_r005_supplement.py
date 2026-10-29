"""Synthetic orchestration checks only. No real session or model request."""
import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import r005_supplement as s


def fixture(base):
    root = base / "suite"
    ids = [s.CASE, "MG-X"]
    s.save(root / "suite.json", {"schema":"math-gauge.suite/v1", "id":"synthetic", "version":"0.4.1", "visibility":"public", "cases":[x+"/case.json" for x in ids]})
    s.save(root / "sources.json", {"fixture":{"title":"Synthetic transport fixture"}})
    for cid in ids:
        s.save(root / cid / "case.json", {"schema":"math-gauge.case/v1", "id":cid, "version":s.VERSION,
               "title":"Synthetic only", "language":"en", "track":"exploration", "visibility":"public",
               "status":"draft", "review":{"human":"pending"}, "sources":["fixture"],
               "task":cid+"/task.md", "reference":cid+"/reference.md", "rubric":cid+"/rubric.json",
               "solver_files":[], "evaluator_files":[], "lean_checks":[], "candidate_instruction":""})
        s.save(root / cid / "rubric.json", {"schema":"math-gauge.rubric/v1", "expected":"open", "required_evidence":["Synthetic"], "critical_errors":["Synthetic"]})
        (root/cid/"task.md").write_text("Synthetic transport only; no mathematics.\n")
        (root/cid/"reference.md").write_text("Hidden fixture")
    suite=s.Suite.load(root)
    entry={"case_id":s.CASE,"version":s.VERSION,"task_kind":"written","family_id":"synthetic","section":"fixture","author_lean_coverage":"fixture","suite_sha256":suite.sha256}
    cat={"schema":"math-gauge.exercise-catalog/v1","snapshot_status":"final-catalog-snapshot","suites":[{"root":"suite","cases":[s.CASE],"suite_sha256":suite.sha256}],"case_entries":[entry]}
    s.save(base/"catalog.json",cat)
    return suite,cat


class SupplementTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory(prefix="math-gauge-r005-synthetic-", dir="/private/tmp")
        self.addCleanup(self.tmp.cleanup)
        self.base=Path(self.tmp.name)
        self.suite,self.catalog=fixture(self.base)

    def queue_fixture(self):
        root=self.base/"run"
        sessions={}
        for model in s.MODELS:
            session=root/"sessions"/model/s.CASE
            s.save(session/"runtime/attempt-ledger.json",{"attempts":[]})
            sessions[model]=str(session)
            model_name,effort=s.MODELS[model]
            s.save(root/"config"/(model+".json"),{"model":model_name,"effort":effort})
        row={"case_id":s.CASE,"version":s.VERSION,"suite_root":str(self.suite.root),"sessions":sessions}
        freeze={"experiment":"r005-clarified-supplement","cases":[row],"model_order":list(s.MODELS),
                "timeout_seconds":2700,"automatic_retry":False,"planned_mathematical_requests":2,
                "supplement_script_sha256":s.digest(s.__file__)}
        s.save(root/"runtime/freeze.json",freeze)
        release=root/"runtime/root-release.json"
        s.save(release,{"experiment":freeze["experiment"],"planned_mathematical_requests":2})
        return root,release,freeze

    def test_one_case_selects_from_multi_case_suite(self):
        with patch.object(s,"REPO",self.base):
            _,suite,entry=s.single_catalog(self.base/"catalog.json")
        self.assertEqual(len(suite.cases),2)
        self.assertEqual(entry["case_id"],s.CASE)

    def test_rejects_old_version_extra_case_and_changed_fingerprint(self):
        for mutation in (lambda c:c["case_entries"][0].update(version="0.3.0"),
                         lambda c:c["suites"][0].update(cases=[s.CASE,"MG-X"]),
                         lambda c:c["suites"][0].update(suite_sha256="0"*64)):
            c=json.loads(json.dumps(self.catalog));mutation(c);s.save(self.base/"bad.json",c)
            with patch.object(s,"REPO",self.base),self.assertRaises(ValueError):
                s.single_catalog(self.base/"bad.json")

    def test_prepare_does_not_create_session_without_adoption(self):
        with patch.object(s,"prerequisites",side_effect=ValueError("No archive/adoption")),patch.object(s,"prepare_session") as prepare:
            with self.assertRaises(ValueError):s.prepare(self.base/"new",self.base/"catalog.json",self.base/"missing.json")
            prepare.assert_not_called()

    def test_shared_runner_single_case_projection_is_actual(self):
        from math_gauge.execution import run
        self.assertIs(s.runner_run,run)
        command=[s.sys.executable,"-c","import json,sys; r=json.load(sys.stdin); assert r['case_id']=='MG-R005'; sys.stdout.write('synthetic transport only')"]
        result=s.runner_run(self.suite,self.base/"transport",ids=[s.CASE],command=command,model="synthetic/no-model")
        self.assertEqual(result["execution_failures"],0)
        self.assertEqual([x["id"] for x in result["cases"]],[s.CASE])
        self.assertFalse((self.base/"transport/MG-X").exists())

    def test_two_stages_order_exact_adapter_and_timeout(self):
        root,release,freeze=self.queue_fixture();calls=[]
        def fake_run(suite,destination,**kwargs):
            calls.append(kwargs)
            s.save(destination/"run.json",{"synthetic":True})
            return {"execution_failures":0}
        with patch.object(s,"verify_release",return_value=freeze),patch.object(s,"runner_run",side_effect=fake_run),patch.object(s,"audit_case",return_value={"request_count":1,"valid_execution":True,"synthetic":True}),contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(s.run_queue(root,release),0)
        self.assertEqual([x["model"] for x in calls],["/".join(v) for v in s.MODELS.values()])
        self.assertTrue(all(x["ids"]==[s.CASE] and x["timeout"]==2790 for x in calls))
        self.assertTrue(all("scripts/benchmark/cli_adapter.py" in x["command"][2] for x in calls))
        self.assertTrue(s.load(root/"runtime/queue-final.json")["completed"])
        events=[json.loads(line) for line in (root/"runtime/progress.ndjson").read_text().splitlines()]
        self.assertEqual([(x["model"],x["status"]) for x in events],[(m,status) for m in s.MODELS for status in ("model-phase-started","starting","completed","model-phase-completed")])
        self.assertEqual(s.load(root/"runtime/queue-start.json")["release_sha256"],s.digest(release))
        with patch.object(s,"verify_release",return_value=freeze),patch.object(s,"runner_run") as no_retry:
            with self.assertRaises((ValueError,FileExistsError)):s.run_queue(root,release)
            no_retry.assert_not_called()

    def test_first_failure_stops_second_and_missing_count_unknown(self):
        root,release,freeze=self.queue_fixture()
        with patch.object(s,"verify_release",return_value=freeze),patch.object(s,"runner_run",side_effect=RuntimeError("synthetic failure")) as run,contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(s.run_queue(root,release),1)
        self.assertEqual(run.call_count,1)
        rows=s.load(root/"runtime/queue-final.json")["results"]
        self.assertIsNone(rows[0]["request_count"])
        self.assertEqual(rows[1]["request_count"],0)
        self.assertEqual(rows[1]["status"],"not-started-after-operational-failure")

    def test_release_and_script_guards_before_runner(self):
        root,release,freeze=self.queue_fixture()
        with patch.object(s,"verify_release",side_effect=ValueError("not released")),patch.object(s,"runner_run") as run:
            with self.assertRaises(ValueError):s.run_queue(root,release)
            run.assert_not_called()
        freeze["supplement_script_sha256"]="changed"
        with self.assertRaises(ValueError):s.check_plan(freeze)

    def test_prior_attempt_rejected(self):
        root,release,freeze=self.queue_fixture()
        s.save(Path(freeze["cases"][0]["sessions"]["terra"])/"runtime/attempt-ledger.json",{"attempts":[{"kind":"math"}]})
        with patch.object(s,"verify_release",return_value=freeze),patch.object(s,"runner_run") as run:
            with self.assertRaises(ValueError):s.run_queue(root,release)
            run.assert_not_called()


if __name__ == "__main__":unittest.main()
