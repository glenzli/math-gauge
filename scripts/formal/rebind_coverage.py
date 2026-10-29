#!/usr/bin/env python3
"""Bind a replacement coverage ledger to unchanged, already compiled Lean evidence.

This preserves the original compilation report and compiled manifest. The only
permitted manifest change is coverage.sha256. All sources, audit source, frozen
inputs, compiler, dependencies and compiled evidence are checked before writes.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import shutil
import sys
import verify as v

def bytes_json(value):
    return (json.dumps(value,ensure_ascii=False,indent=2)+'\n').encode('utf-8')

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--manifest',type=Path,required=True)
    p.add_argument('--compiled-manifest',type=Path,required=True)
    p.add_argument('--compiled-report',type=Path,required=True)
    p.add_argument('--coverage',type=Path,required=True)
    p.add_argument('--dependency-root',type=Path,required=True)
    p.add_argument('--lean',type=Path)
    p.add_argument('--history-dir',type=Path,required=True)
    p.add_argument('--receipt',type=Path,required=True)
    a=p.parse_args()
    try:
        current,root,sources,audit,external=v.validate_case(a.manifest)
        old=v.load(a.compiled_manifest);report=v.load(a.compiled_report)
        v.require(current==old,'Current manifest has changes beyond the original compilation binding')
        v.require(report['status']=='passed','Original compilation did not pass')
        v.require(v.digest(a.compiled_manifest)==report['manifest_sha256'],'Compiled manifest does not match original report')
        v.require(v.digest(root/'verification-report.json')==v.digest(a.compiled_report),'Case report differs from original compilation evidence')
        dep=v.inspect_dependencies(a.dependency_root,a.lean)
        v.require(dep==report['dependency'],'Compiler or dependency identity changed; fresh compilation is required')
        v.require(v.resolve_imports(external,dep)==report['direct_external_imports'],'Dependency olean identity changed')
        expected={row['module']:row['sha256'] for row in sources}
        actual={row['module']:row['source_sha256'] for row in report['modules']}
        v.require(expected==actual,'Compiled source inventory differs from current case')
        audit_command=report['audit']['command']
        v.require(v.digest(audit)==audit_command['source_sha256'],'Current audit source changed')
        compiled_artifacts=[]
        for command in [*report['modules'],audit_command]:
            argv=command['argv'];olean=Path(argv[argv.index('-o')+1]);source=Path(argv[-1]);log=Path(a.compiled_report).parent/command['log']
            v.require(v.digest(source)==command['source_sha256'],'Staged source changed: '+command['module'])
            v.require(v.digest(olean)==command['olean_sha256'],'Compiled olean changed: '+command['module'])
            v.require(v.digest(log)==command['log_sha256'],'Compilation log changed: '+command['module'])
            compiled_artifacts.append({'module':command['module'],'source_sha256':command['source_sha256'],'olean_sha256':command['olean_sha256'],'log_sha256':command['log_sha256']})
        new_coverage=a.coverage.read_bytes();new_hash=hashlib.sha256(new_coverage).hexdigest()
        v.require(new_hash!=old['coverage']['sha256'],'Coverage bytes are unchanged; no rebinding is needed')
        updated=copy.deepcopy(old);updated['coverage']['sha256']=new_hash
        old_without_hash=copy.deepcopy(old);new_without_hash=copy.deepcopy(updated)
        old_without_hash['coverage'].pop('sha256');new_without_hash['coverage'].pop('sha256')
        v.require(old_without_hash==new_without_hash,'Only coverage.sha256 may change')
        v.require(not a.receipt.exists() and not a.history_dir.exists(),'Rebinding receipt/history must be fresh')
        receipt={'schema':'math-gauge.coverage-evidence-reuse/v1','recorded_utc':v.now(),'case_id':old['case_id'],'status':'passed','reason':'Coverage ledger presentation changed; all Lean compilation inputs and validated dependency artifacts are identical. No mathematical source or frozen case input changed.','old_manifest_sha256':v.digest(a.compiled_manifest),'new_manifest_sha256':hashlib.sha256(bytes_json(updated)).hexdigest(),'only_manifest_field_changed':'coverage.sha256','old_coverage_sha256':old['coverage']['sha256'],'new_coverage_sha256':new_hash,'original_compilation_report_sha256':v.digest(a.compiled_report),'original_compilation_report_preserved':True,'mathematical_modules_recompiled':False,'frozen_inputs':old['frozen_inputs'],'compiled_artifacts_rechecked':compiled_artifacts,'compiler_and_dependency_unchanged':True,'dependency_receipt_sha256':hashlib.sha256(json.dumps(dep,sort_keys=True).encode()).hexdigest(),'mathlib_tracked_state':dep['mathlib_tracked_state'],'source_side_oleans_used':False,'script_sha256':v.digest(Path(__file__).resolve()),'human_approval':False}
        a.history_dir.mkdir(parents=True)
        shutil.copyfile(a.compiled_manifest,a.history_dir/'compiled-manifest.json')
        shutil.copyfile(root/'COVERAGE.md',a.history_dir/'COVERAGE.md')
        shutil.copyfile(root/'current-formal.json',a.history_dir/'current-formal.json')
        # All guards have passed. Only ledger, its binding and explicit current metadata change.
        (root/'COVERAGE.md').write_bytes(new_coverage)
        a.manifest.write_bytes(bytes_json(updated))
        v.validate_case(a.manifest)
        a.receipt.parent.mkdir(parents=True,exist_ok=True);v.save(a.receipt,receipt)
        meta=v.load(root/'current-formal.json')
        meta.update(source_manifest_sha256=receipt['new_manifest_sha256'],compiled_manifest_sha256=receipt['old_manifest_sha256'],coverage_binding_reused_without_recompilation=True,evidence_reuse_receipt=a.receipt.name,evidence_reuse_receipt_sha256=v.digest(a.receipt))
        v.save(root/'current-formal.json',meta)
        print(json.dumps({'case_id':old['case_id'],'status':'passed','receipt':str(a.receipt),'source_manifest_sha256':receipt['new_manifest_sha256']}))
        return 0
    except (v.VerificationError,OSError,ValueError,KeyError) as error:
        print(str(error),file=sys.stderr);return 1
if __name__=='__main__':raise SystemExit(main())
