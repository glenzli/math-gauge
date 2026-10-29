#!/usr/bin/env python3
"""Verify the explicitly indexed case manifests in separate fresh directories."""
import argparse
from concurrent.futures import ThreadPoolExecutor,as_completed
from pathlib import Path
import sys
import verify

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dependency-root',type=Path,required=True)
    parser.add_argument('--lean',type=Path)
    parser.add_argument('--out',type=Path,required=True)
    parser.add_argument('--jobs',type=int,choices=(1,2,3),default=2)
    parser.add_argument('--suite',type=Path,default=Path(__file__).with_name('suite.json'))
    args=parser.parse_args();out=args.out.resolve()
    if out.exists():parser.error('--out must not exist')
    out.mkdir(parents=True);started=verify.now()
    report={'schema':'math-gauge.formal-suite-verification/v1','started_utc':started,'status':'running','jobs':args.jobs,'cases':[]}
    verify.save(out/'report.json',report)
    try:
        index=verify.load(args.suite);repo=Path(__file__).resolve().parents[2]
        verify.require(index.get('schema')=='math-gauge.formal-suite/v1','Invalid formal suite')
        verify.require(not index.get('pending_cases'),'Suite still has pending cases')
        manifests=[verify.safe_relative(repo,row['manifest']) for row in index['cases']]
        validated=[verify.validate_case(path) for path in manifests]
        ids=[row[0]['case_id'] for row in validated]
        verify.require(len(ids)==len(set(ids)),'Duplicate case id')
        dependency=verify.inspect_dependencies(args.dependency_root,args.lean)
        report['dependency']=dependency
        report['manifest_sha256']={row[0]['case_id']:verify.digest(path) for row,path in zip(validated,manifests)}
        verify.save(out/'report.json',report)
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            futures={pool.submit(verify.verify_case,path,dependency,out):cid for path,cid in zip(manifests,ids)}
            for future in as_completed(futures):
                cid=futures[future]
                try:
                    case=future.result();summary=case.get('audit',{}).get('summary') or {}
                    row={'case_id':cid,'status':case['status'],'source_module_count':len(case['modules']),'generated_audit_module_count':1,'dynamic_declaration_count':summary.get('declaration_count'),'axiom_union':summary.get('axiom_union'),'report':cid+'/report.json','manifest_sha256':case['manifest_sha256']}
                except Exception as error:row={'case_id':cid,'status':'failed','error':str(error)}
                report['cases'].append(row);report['cases'].sort(key=lambda row:row['case_id']);verify.save(out/'report.json',report)
        report['status']='passed' if all(row['status']=='passed' for row in report['cases']) and len(report['cases'])==len(manifests) else 'failed'
    except Exception as error:
        report['status']='failed';report['error']=str(error);print(str(error),file=sys.stderr)
    report['finished_utc']=verify.now();verify.save(out/'report.json',report)
    return 0 if report['status']=='passed' else 1
if __name__=='__main__':raise SystemExit(main())
