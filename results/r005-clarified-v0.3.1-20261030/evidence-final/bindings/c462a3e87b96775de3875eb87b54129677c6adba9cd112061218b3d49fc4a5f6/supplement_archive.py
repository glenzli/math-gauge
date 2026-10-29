"""Supplement-only audit and explicit-whitelist final archive; no model calls."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import sys

HERE=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
sys.path.insert(0,str(HERE))
import r005_supplement as supplement
from common import REPO, Suite, digest, load, now, verify_release
from math_gauge.review import compare_models
from postprocess import (audit_case, OUTPUT_NAMES, QUEUE_NAMES, RUNTIME_NAMES,
                         SECRET_PATTERNS, read_if, write_new)
from replay_comparison import normalized, safe_child

TOOLS=("r005_supplement.py","supplement_archive.py","supplement_replay.py","supplement_preflight.py",
       "postprocess.py","replay_comparison.py","R005-SUPPLEMENT.md",
       "test_r005_supplement.py","test_supplement_archive.py")
PREFLIGHT_RUNTIME={"capability-verdict.json","inventory-summary.json"}
PREFLIGHT_RAW={"command.json","report.json","stdout.txt","stderr.txt","agy.log"}
FORBIDDEN={"state","auth.json","credentials.json","antigravity-oauth-token","jetski-standalone-oauth-token"}


def audit(root):
    root=Path(root).resolve()
    freeze=verify_release(root/"runtime",root/"runtime/root-release.json")
    supplement.check_plan(freeze)
    final=read_if(root/"runtime/queue-final.json")
    final_rows={(x["model"],x["case_id"]):x for x in final["results"]} if final else {}
    planned={(m,x["case_id"]) for m in freeze["model_order"] for x in freeze["cases"]}
    start=load(root/"runtime/queue-start.json")
    checks={"queue_start_bound":start.get("release_sha256")==digest(root/"runtime/root-release.json") and start.get("freeze_sha256")==digest(root/"runtime/freeze.json")}
    events=[json.loads(x) for x in (root/"runtime/progress.ndjson").read_text().splitlines()]
    active=set();started=set();finished=set();phases=[];sequence=True
    for event in events:
        model,status=event["model"],event["status"];key=(model,event.get("case_id"))
        if status=="model-phase-started":
            i=len(phases)
            sequence &= i<len(freeze["model_order"]) and model==freeze["model_order"][i] and not active
            if i:sequence &= all((m,c["case_id"]) in finished for m in phases for c in freeze["cases"])
            phases.append(model)
        elif status=="starting":
            sequence &= key in planned and key not in started and phases and phases[-1]==model
            active.add(key);started.add(key)
            sequence &= len(active)<=freeze.get("effective_parallel_per_model",1)
        elif status in {"completed","failed","launcher-failed"}:
            sequence &= key in active
            active.discard(key)
            if status=="completed":finished.add(key)
        elif status=="model-phase-completed":
            sequence &= not active and all((model,c["case_id"]) in finished for c in freeze["cases"])
    checks["unique_starts_sequential_phases"]=bool(sequence and phases and phases==freeze["model_order"][:len(phases)])
    if final:
        checks["all_planned_rows_once"]=len(final["results"])==len(final_rows)==len(planned) and set(final_rows)==planned
        checks["no_active_cases"]=not active
        checks["queue_index_present"]=(root/"runtime/model-runs.json").is_file()
    rows=[]
    for model,cid in sorted(planned):
        item=next(x for x in freeze["cases"] if x["case_id"]==cid)
        try:row=audit_case(root,item,model,final_rows.get((model,cid)))
        except (OSError,ValueError,KeyError,TypeError) as error:
            row={"case_id":cid,"model":model,"request_count":None,"valid_execution":False,
                 "status":"audit-evidence-error","integrity_errors":[type(error).__name__+": "+str(error)]}
        rows.append(row)
    ids=[x["run_id"] for x in rows if x.get("run_id")]
    checks["unique_run_ids"]=len(ids)==len(set(ids))
    if final:
        index=load(root/"runtime/model-runs.json")
        indexed=[str(Path(p).resolve()) for ps in index["model_runs"].values() for p in ps]
        actual=[str(p.parent.resolve()) for p in (root/"records").glob("*/*/run.json")]
        checks["run_index_complete_unique"]=len(indexed)==len(set(indexed)) and set(indexed)==set(actual)
    return {"schema":"math-gauge.runtime-integrity-audit/v1","experiment":freeze["experiment"],
        "utc":now(),"queue_terminal":final is not None,"planned":len(planned),"planned_cases":len(freeze["cases"]),
        "known_request_count":sum(x["request_count"] for x in rows if x["request_count"] is not None),
        "unknown_request_count_rows":sum(x["request_count"] is None for x in rows),
        "valid_executions":sum(x["valid_execution"] for x in rows),
        "integrity_error_rows":sum(bool(x["integrity_errors"]) for x in rows),
        "global_checks":checks,"global_integrity_passed":all(checks.values()),
        "statuses":dict(Counter(x["status"] for x in rows)),"rows":rows,
        "postprocessor_sha256":digest(__file__),"mathematical_scoring_performed":False}


class Whitelist:
    def __init__(self,root):
        self.root=Path(root).resolve();self.files={};self.mapping={}

    def add(self,path,target=None,*,required=True,expected=None):
        path=Path(path)
        if any(x in FORBIDDEN for x in path.parts):raise ValueError("State/credential source excluded")
        if path.is_symlink():raise ValueError("Symlink excluded: "+str(path))
        if not path.is_file():
            if required:raise ValueError("Required evidence missing: "+str(path))
            return
        resolved=path.resolve()
        if any(parent.is_symlink() for parent in path.parents):raise ValueError("Symlink parent excluded")
        if target is None:
            if not resolved.is_relative_to(self.root):raise ValueError("External evidence requires explicit mapping")
            target=str(resolved.relative_to(self.root))
        target=Path(target)
        if target.is_absolute() or ".." in target.parts or any(x in FORBIDDEN for x in target.parts):
            raise ValueError("Unsafe archive target")
        if expected and digest(path)!=expected:raise ValueError("Declared evidence hash changed")
        old=self.files.get(str(target))
        if old and old!=resolved and digest(old)!=digest(resolved):raise ValueError("Archive name collision")
        if not old:self.files[str(target)]=resolved
        self.mapping[str(resolved)]=str(target)

    def local_binding(self,item):
        path=Path(item["path"]).resolve()
        if "state" in path.parts:
            # The only frozen state file is an exact duplicate of strict task settings.
            if path.parts[-3:]!=("state","antigravity-cli","settings.json"):
                raise ValueError("Unrecognized state binding")
            replacement=path.parents[2]/"runtime/task-settings.json"
            self.add(replacement,expected=item["sha256"])
            self.mapping[str(path)]=str(replacement.relative_to(self.root))
            return
        target=None if path.is_relative_to(self.root) else "bindings/"+item["sha256"]+"/"+path.name
        if path.suffix not in {".json",".md",".py",".txt",".log",".sb",".ndjson"}:
            raise ValueError("Binding is not an allowed textual artifact")
        self.add(path,target,expected=item["sha256"])


def session_files(w,session):
    session=Path(session)
    safe_child(w.root,session.relative_to(w.root))
    for name in RUNTIME_NAMES|PREFLIGHT_RUNTIME:
        w.add(session/"runtime"/name,required=False)
    for p in (session/"runtime").glob("*-pid-check*.json"):
        if re.fullmatch(r"(parent|worker)-pid-check(?:-\d+)?\.json",p.name):w.add(p)
    for name in PREFLIGHT_RAW:w.add(session/"runtime/preflight"/name,required=False)
    for name in OUTPUT_NAMES:w.add(session/"output"/name,required=False)
    for name in ("input/task.md","work/.agents/agents/text-only.md"):
        w.add(session/name,required=False)


def collect(root,freeze,comparison,review_manifest):
    w=Whitelist(root)
    for name in QUEUE_NAMES:w.add(root/"runtime"/name,required=name!="queue-console.log")
    for model in freeze["model_order"]:
        config_path=root/"config"/(model+".json");w.add(config_path);config=load(config_path)
        identity=Path(config["cli_identity"]);w.add(identity)
        for n in range(len(load(identity).get("commands",[]))):
            for suffix in ("stdout","stderr"):w.add(identity.parent/(str(n)+"-"+suffix+".txt"),required=False)
        for item in config.get("proxy_exception",{}).get("evidence",[]):w.local_binding(item)
        for item in freeze["cases"]:
            cid=item["case_id"];session_files(w,Path(item["sessions"][model]))
            run=root/"records"/model/cid
            if not (run/"run.json").is_file():continue
            for name in ("run.json","reviews.json","summary.json"):w.add(run/name,required=name=="run.json")
            for name in ("response.md","stderr.txt","record.json","execution-assessment.json"):
                w.add(run/cid/name,required=False)
            for name in ("request.json","prompt.md"):w.add(run/cid/"solver"/name,required=False)
            request=read_if(run/cid/"solver/request.json")
            if request:
                for file in request["files"]:w.add(safe_child(run/cid/"solver",file["name"]))
            w.add(root/"runtime"/(model+"-execution-audit.json"),required=False)
    for snapshot in freeze["suite_snapshots"]:
        suite=Suite.load(snapshot["root"])
        if suite.sha256!=snapshot["suite_sha256"]:raise ValueError("Snapshot changed")
        names={"suite.json","sources.json",*suite.metadata["cases"]}
        for case in suite.cases.values():
            names.update(case[k] for k in ("task","reference","rubric"))
            names.update(case.get("evaluator_files",[]));names.update(case["lean_checks"])
            names.update(x["source"] for x in case["solver_files"])
        for name in names:w.add(safe_child(suite.root,name))
    # Only paths from this supplement's qualification and session plans are used.
    qualification=root/"preflight/qualification.json";w.add(qualification)
    for item in load(qualification)["bindings"]:w.local_binding(item)
    for item in freeze["preflight_bindings"]+freeze.get("session_bindings",[]):w.local_binding(item)
    w.local_binding(freeze["adoption_gate"])
    for plan in (root/"preflight").glob("*/runtime/plan.json"):session_files(w,plan.parent.parent)
    for p in (root/"preflight/invocations").glob("*.json"):w.add(p)
    for name in ("canary-prompt.md","inventory-unused-prompt.md","early-attempt-notes.json"):
        w.add(root/"preflight"/name,required=False)
    for relative,expected in freeze["code_identity"].items():
        w.add(safe_child(REPO,relative),"source-code/"+relative,expected=expected)
    for p in (REPO/"math_gauge").glob("*.py"):w.add(p,"source-code/math_gauge/"+p.name)
    for name in TOOLS:w.add(HERE/name,"tools/"+name)
    w.add(comparison,"scoring/comparison.json")
    reviews=load(review_manifest)
    if (reviews.get("schema")!="math-gauge.supplement-review-manifest/v1"
            or reviews.get("all_reviews_included") is not True):
        raise ValueError("An explicit complete review inventory is required")
    w.add(review_manifest,"scoring/review-manifest.json")
    for row in reviews["files"]:
        p=safe_child(Path(review_manifest).resolve().parent,row["path"])
        if p.suffix not in {".json",".md",".txt"}:raise ValueError("Review evidence must be text")
        w.add(p,"scoring/reviews/"+row["path"],expected=row["sha256"])
    return w


def comparison_report(root):
    root=Path(root).resolve()
    freeze=verify_release(root/"runtime",root/"runtime/root-release.json")
    supplement.check_plan(freeze)
    if not (root/"runtime/queue-final.json").is_file():raise ValueError("Queue is not terminal")
    index=load(root/"runtime/model-runs.json")
    return compare_models(freeze["cases"],index["model_runs"],execution_receipts=index["execution_receipts"],lean_reports={})


def archive(root,destination,comparison,review_manifest):
    root,destination=Path(root).resolve(),Path(destination).resolve()
    if destination.exists() or destination.is_relative_to(root):
        raise ValueError("Archive must be new and survive removal of the temporary root")
    if not (root/"runtime/queue-final.json").is_file():raise ValueError("Queue is not terminal")
    report=audit(root)
    if not report["global_integrity_passed"] or report["integrity_error_rows"]:
        raise ValueError("Integrity audit did not pass; retain original evidence and investigate")
    freeze=load(root/"runtime/freeze.json");index=load(root/"runtime/model-runs.json")
    actual=compare_models(freeze["cases"],index["model_runs"],execution_receipts=index["execution_receipts"],lean_reports={})
    if normalized(actual)!=normalized(load(comparison)):
        raise ValueError("Final comparison differs from the retained run reviews and receipts")
    for row in report["rows"]:
        if row["valid_execution"] and not (root/"records"/row["model"]/row["case_id"]/"reviews.json").is_file():
            raise ValueError("Successful execution has no retained final review")
    w=collect(root,freeze,Path(comparison),Path(review_manifest))
    prepared=[]
    for relative,source in sorted(w.files.items()):
        data=source.read_bytes()
        if any(pattern.search(data) for _,pattern in SECRET_PATTERNS):
            raise ValueError("Sensitive-value scan blocked "+relative)
        prepared.append((relative,source,data,hashlib.sha256(data).hexdigest()))
    destination.mkdir(parents=True)
    files=[]
    for relative,source,data,sha in prepared:
        if digest(source)!=sha:raise ValueError("Source changed while archiving")
        target=destination/relative;target.parent.mkdir(parents=True,exist_ok=True)
        with target.open("xb") as stream:stream.write(data)
        files.append({"path":relative,"source":str(source),"bytes":len(data),"sha256":sha})
    for name,data in (("integrity-audit.json",report),("binding-map.json",w.mapping)):
        write_new(destination/name,data)
        files.append({"path":name,"source":"generated-from-frozen-evidence","bytes":(destination/name).stat().st_size,"sha256":digest(destination/name)})
    manifest={"schema":"math-gauge.final-execution-archive/v1","experiment":freeze["experiment"],
        "utc":now(),"source_root":str(root),"queue_terminal":True,"files":files,
        "planned_cases":len(freeze["cases"]),"planned_runs":len(freeze["cases"])*len(freeze["model_order"]),
        "global_integrity_passed":report["global_integrity_passed"],"integrity_error_rows":report["integrity_error_rows"],
        "unknown_request_count_rows":report["unknown_request_count_rows"],
        "state_credentials_binaries_excluded":True,"mathematics_regraded":False,
        "comparison_sha256":digest(destination/"scoring/comparison.json"),
        "integrity_audit_sha256":digest(destination/"integrity-audit.json")}
    write_new(destination/"manifest.json",manifest)
    return {"archive":str(destination),"manifest_sha256":digest(destination/"manifest.json"),"files":len(files),"model_requests":0}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action",choices=["audit","report","archive"])
    parser.add_argument("--root",type=Path,required=True)
    parser.add_argument("--output",type=Path,required=True)
    parser.add_argument("--comparison",type=Path)
    parser.add_argument("--review-manifest",type=Path)
    args=parser.parse_args()
    if args.action=="audit":
        result=audit(args.root);write_new(args.output,result)
        print(json.dumps({k:result[k] for k in ("planned","valid_executions","global_integrity_passed","integrity_error_rows")}))
    elif args.action=="report":
        result=comparison_report(args.root);write_new(args.output,result)
        print(json.dumps({"complete":result["complete"],"planned_cases":result["planned_cases"],"model_requests":0}))
    else:
        if not args.comparison or not args.review_manifest:parser.error("archive requires comparison and explicit complete review inventory")
        print(json.dumps(archive(args.root,args.output,args.comparison,args.review_manifest)))


if __name__=="__main__":main()
