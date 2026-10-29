#!/usr/bin/env python3
"""Verify the explicitly indexed case manifests in separate fresh directories."""
import argparse
from concurrent.futures import ThreadPoolExecutor,as_completed
from pathlib import Path
import sys
import verify

def indexed_manifests(suite_path):
    """Use the canonical benchmark catalog; no second maintained case list."""
    suite_path = Path(suite_path).resolve()
    index = verify.load(suite_path)
    verify.require(index.get('schema') == 'math-gauge.suite/v1', 'Invalid benchmark suite')
    cases = [verify.safe_relative(suite_path.parent, name) for name in index['cases']]
    verify.require(len(cases) == len(set(cases)) and bool(cases), 'Duplicate or empty benchmark suite')
    return [verify.safe_relative(case.parent, 'formal/manifest.json') for case in cases]


def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dependency-root',type=Path,required=True)
    parser.add_argument('--lean',type=Path)
    parser.add_argument('--out',type=Path,required=True)
    parser.add_argument('--jobs',type=int,choices=(1,2,3),default=2)
    parser.add_argument('--suite',type=Path,default=Path(__file__).resolve().parents[2]/'cases/suite.json')
    parser.add_argument('--profile',choices=verify.PROFILES,default=verify.DEFAULT_PROFILE,
                        help='Compile only cases with this pinned dependency profile')
    args=parser.parse_args(argv);out=args.out.resolve()
    if out.exists():parser.error('--out must not exist')
    out.mkdir(parents=True);started=verify.now()
    report={'schema':'math-gauge.formal-suite-verification/v1','started_utc':started,'status':'running','jobs':args.jobs,'cases':[]}
    verify.save(out/'report.json',report)
    try:
        all_manifests=indexed_manifests(args.suite)
        all_validated=[verify.validate_case(path) for path in all_manifests]
        all_ids=[row[0]['case_id'] for row in all_validated]
        verify.require(len(all_ids)==len(set(all_ids)),'Duplicate case id')
        selected=[(path,row) for path,row in zip(all_manifests,all_validated)
                  if verify.manifest_profile(row[0])==args.profile]
        verify.require(bool(selected),'No cases use the selected verification profile')
        manifests=[path for path,_ in selected];validated=[row for _,row in selected]
        ids=[row[0]['case_id'] for row in validated]
        report.update(verification_profile=args.profile,suite_case_count=len(all_ids),
                      selected_case_count=len(ids),
                      excluded_cases=[cid for cid in all_ids if cid not in ids])
        dependency=verify.inspect_dependencies(args.dependency_root,args.lean,args.profile)
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
