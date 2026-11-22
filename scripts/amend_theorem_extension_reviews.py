#!/usr/bin/env python3
"""Adopt an explicitly adjudicated TX review packet; never grade or call models."""
from copy import deepcopy
import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from math_gauge.neutral_revision import (
    descriptor, document, read, _source_report_refs, load_transition,
    load_inputs as load_revision_inputs, project_public_tasks,
)
from math_gauge.theorem_extension_calibration import (
    MODES, CONDITIONS, PUBLIC_CASES, _source_rows, _source_descriptor, require,
)
from math_gauge.theorem_extension_amendments import (
    DIRECTORY, INDEX_PATH, load_inputs, project_score, load_public,
)
from math_gauge.records import project_public_task_view, public_assessment_case_ids
from math_gauge.scoring import (
    score_theorem_extension_calibration_overlay, score_neutral_revision_after_review_amendment,
)


def write(root, path, value):
    raw = value if isinstance(value, bytes) else (json.dumps(value,ensure_ascii=False,indent=2)+'\n').encode()
    target = Path(root) / path
    if target.is_file() and target.read_bytes() != raw:
        raise ValueError('Refusing to overwrite retained review evidence: '+str(target))
    target.parent.mkdir(parents=True,exist_ok=True)
    target.write_bytes(raw)
    return descriptor(root,target)


def prepare(public_root, private_root, packet_path):
    p, q = Path(public_root).resolve(), Path(private_root).resolve()
    packet = json.loads(Path(packet_path).read_bytes())
    require(packet['schema'] == 'math-gauge.uniform-tx-review-adjudication/v1', "TX review amendment failed its source integrity check")
    require(packet['human_review'] == 'pending' and packet['new_candidate_calls'] == 0, "TX review amendment failed its source integrity check")
    require(packet['scoring_rules_changed'] is False, "TX review amendment failed its source integrity check")
    policy_ref = descriptor(p,p/'protocol/theorem-extension-calibration.json')
    standard_ref = descriptor(q,q/'protocol/theorem-extension-calibration.md')
    policy = document(p,policy_ref)
    assessment = json.loads((p/'protocol/scoring-policy.json').read_bytes())
    public_ids = public_assessment_case_ids(assessment)
    transition = load_transition(p)
    audit = write(q,DIRECTORY+'/uniform-audit-20261122.json',packet)
    by_model = {}
    for row in packet['rows']:
        by_model.setdefault(row['model_id'],[]).append(row)
    selected, changes = {}, []
    for mid, audited in by_model.items():
        if not any(row['new_R'] != row['old_R'] for row in audited):
            continue
        public, private, source_ref = _source_report_refs(p,q,mid)
        parent_inputs = document(q,private['inputs'])
        record_ref = parent_inputs.get('source_record',private.get('record'))
        record = document(q,record_ref)
        record_path = Path(record_ref['path']); folder=record_path.parent
        source_input = next(record[k] for k in ('theorem_extension_inputs','mathematical_inputs','mathematical_input') if record.get(k))
        source_input = _source_descriptor(folder,source_input)
        base = {m:{c:document(q,r) for c,r in refs.items()} for m,refs in private['scores'].items()}
        base_public = {m:{c:document(p,r) for c,r in refs.items()} for m,refs in public['scores'].items()}
        destination = DIRECTORY+'/'+mid+'/'+folder.name
        rows, public_reviews = {}, {}
        for condition in CONDITIONS:
            rows[condition], public_reviews[condition] = [], []
            originals, _, _ = _source_rows(q,record,folder,source_input,condition,base['partial'][condition],p)
            current_rows = {r['case_id']:r for r in parent_inputs['conditions'][condition]}
            tasks = {r['case_id']:r for r in base['partial'][condition]['tasks'] if r['subcategory']=='theorem-extension'}
            grades = {r['case_id']:r for r in audited if r['condition']==condition}
            require(set(grades) == set(tasks) and len(grades)==6, "TX review amendment failed its source integrity check")
            for cid, task in tasks.items():
                grade, old = grades[cid], originals[cid]
                response = _source_descriptor(folder,old.get('response'))
                old_review = (current_rows[cid]['new_review'] if 'new_review' in current_rows[cid]
                              else _source_descriptor(folder,old.get('review')))
                require(grade['response_sha256'] == task.get('response_sha256'), "TX review amendment failed its source integrity check")
                require(grade['old_B'] == grade['new_B'] == task['research']['baseline_B'], "TX review amendment failed its source integrity check")
                require(grade['old_R'] == task['research']['research_R'], "TX review amendment failed its source integrity check")
                require((old_review or {}).get('sha256') == task.get('review_sha256'), "TX review amendment failed its source integrity check")
                answer = b'' if response is None else read(q,response)
                citations = []
                for quote in grade['quotes']:
                    quote = quote['quote'] if isinstance(quote,dict) else quote
                    raw = quote.encode(); start=answer.index(raw)
                    citations.append(dict(quote=quote,start_byte=start,end_byte=start+len(raw)))
                review = dict(schema='math-gauge.theorem-extension-calibration-review/v1',version='0.1.0',
                    case_id=cid,answer_sha256=(response or {}).get('sha256'),
                    source_review_sha256=(old_review or {}).get('sha256'),baseline_B=grade['new_B'],
                    old_R=grade['old_R'],new_R=grade['new_R'],policy_sha256=policy_ref['sha256'],
                    standard_sha256=(policy['standards']['sha256'] if cid in PUBLIC_CASES else policy['private_standards']['sha256']),
                    reviewer_kind='ai',reviewer=grade['reviewers'],human_review='pending',post_observation=True,
                    status='reviewed' if response else grade['status'],reason=grade['reason'],
                    attained=grade['attained'],not_attained=grade['not_attained'],citations=citations)
                rel=destination+'/reviews/'+condition+'/'+cid+'.json'
                new_review=write(q,rel,review)
                if cid in PUBLIC_CASES:
                    public_reviews[condition].append(dict(case_id=cid,review=write(p,rel,review)))
                rows[condition].append(dict(case_id=cid,response=response,source_review=old_review,
                    baseline_B=grade['new_B'],old_R=grade['old_R'],new_R=grade['new_R'],new_review=new_review))
                if grade['old_R'] != grade['new_R']:
                    changes.append(dict(model_id=mid,condition=condition,old_R=grade['old_R'],new_R=grade['new_R']))
        inputs = dict(schema='math-gauge.theorem-extension-review-amendment-inputs/v1',version='0.1.0',
            model_id=mid,model_label=base['partial']['nonlogical_retry_3']['model_label'],
            source_assessment=source_ref,source_record=record_ref,base_reports=private['scores'],
            policy=policy_ref,private_standards=standard_ref,conditions=rows,reviewer_kind='ai',
            human_review='pending',new_candidate_calls=0,scoring_rules_changed=False,original_bytes_rewritten=False,
            uniform_audit=audit)
        input_ref=write(q,destination+'/inputs.json',inputs)
        validated=load_inputs(p,q,input_ref,source=(public,private,source_ref))
        baseline, full_baseline, pub_baseline = {}, {}, {}
        for mode in MODES:
            baseline[mode],full_baseline[mode],pub_baseline[mode] = {},{},{}
            for condition in CONDITIONS:
                score=score_theorem_extension_calibration_overlay(base[mode][condition],assessment,
                    calibration=validated,mode=mode,condition=condition)
                baseline[mode][condition]=score
                name=destination+'/baseline-'+mode+'-'+condition+'.json'
                full_baseline[mode][condition]=write(q,name,score)
                projected=project_score(score)
                projected['source_bindings']['private_report_sha256']=full_baseline[mode][condition]['sha256']
                pub_baseline[mode][condition]=write(p,name,projected)
        first_projection=dict(schema='math-gauge.public-task-scores/v1',benchmark_version='1.1.0',
            model_label=inputs['model_label'],public_case_ids=public_ids,views={},
            human_review='pending',formal_comparison_eligible=False)
        for mode in MODES:
            first_projection['views'][mode]={c:project_public_task_view(baseline[mode][c],public_ids,
                full_baseline[mode][c]['sha256']) for c in CONDITIONS}
        projections=dict(baseline=write(p,destination+'/public-tasks-baseline.json',first_projection))
        original_adoption=transition['adoptions'].get(mid)
        revised, full_revised, pub_revised = None,None,None
        if original_adoption is not None:
            original_public=document(p,original_adoption)
            original_private=document(q,descriptor(q,q/original_adoption['path'].replace('public.json','private.json')))
            revision=load_revision_inputs(q,original_private['inputs'],public_root=p,
                base_reports={m:base[m]['nonlogical_retry_3'] for m in MODES})
            revised,full_revised,pub_revised = {},{},{}
            for mode in MODES:
                score=score_neutral_revision_after_review_amendment(base[mode]['nonlogical_retry_3'],
                    baseline[mode]['nonlogical_retry_3'],assessment,revision=revision,mode=mode)
                revised[mode]=score
                name=destination+'/revised-'+mode+'.json'
                full_revised[mode]=write(q,name,score)
                projected=project_score(score)
                projected['source_bindings']['private_report_sha256']=full_revised[mode]['sha256']
                pub_revised[mode]=write(p,name,projected)
            projections['revised']=write(p,destination+'/public-tasks-revised.json',
                project_public_tasks(revised,public_ids,{m:full_revised[m]['sha256'] for m in MODES}))
        private_manifest=write(q,destination+'/private.json',dict(
            schema='math-gauge.theorem-extension-review-amendment-private/v1',version='0.1.0',
            model_id=mid,inputs=input_ref,baseline=full_baseline,revised=full_revised,
            original_adoption=original_adoption))
        selected[mid]=write(p,destination+'/public.json',dict(
            schema='math-gauge.theorem-extension-review-amendment-public/v1',version='0.1.0',
            model_id=mid,record_id=folder.name,policy=policy_ref,source_assessment=source_ref,
            original_adoption=original_adoption,original_baseline=public['scores'],
            baseline=pub_baseline,revised=pub_revised,public_tasks=projections,public_reviews=public_reviews,
            private_manifest_sha256=private_manifest['sha256'],private_inputs_sha256=input_ref['sha256'],
            reviewer_kind='ai',human_review='pending',new_candidate_calls=0,scoring_rules_changed=False))
        print(mid,'review amendment prepared',flush=True)
    index=dict(schema='math-gauge.theorem-extension-review-amendment-index/v1',version='0.1.0',
        models=selected,reviewer_kind='ai',human_review='pending',new_candidate_calls=0,
        scoring_rules_changed=False,reviewed_condition_slots=len(packet['rows']),
        private_audit_sha256=audit['sha256'])
    write(p,INDEX_PATH,index)
    write(q,INDEX_PATH,dict(index,private_audit=audit))
    return check(p,q)


def check(public_root,private_root):
    p,q=Path(public_root),Path(private_root)
    index=json.loads((p/INDEX_PATH).read_bytes())
    assessment=json.loads((p/'protocol/scoring-policy.json').read_bytes())
    for mid,ref in index['models'].items():
        source=_source_report_refs(p,q,mid)
        public=load_public(p,mid)
        private_ref=descriptor(q,q/ref['path'].replace('public.json','private.json'))
        private=document(q,private_ref)
        require(private_ref['sha256']==public['private_manifest_sha256'], "TX review amendment failed its source integrity check")
        require(private['inputs']['sha256']==public['private_inputs_sha256'], "TX review amendment failed its source integrity check")
        inputs=load_inputs(p,q,private['inputs'],source=source)
        retained_inputs=document(q,private['inputs'])
        for condition,rows in public['public_reviews'].items():
            chosen={r['case_id']:r for r in retained_inputs['conditions'][condition]}
            for entry in rows:
                require(entry['review']==chosen[entry['case_id']]['new_review'], "TX review amendment failed its source integrity check")
                require(read(p,entry['review'])==read(q,entry['review']), "TX review amendment failed its source integrity check")
        base={m:{c:document(q,r) for c,r in refs.items()} for m,refs in source[1]['scores'].items()}
        corrected={m:{c:score_theorem_extension_calibration_overlay(base[m][c],assessment,
            calibration=inputs,mode=m,condition=c) for c in CONDITIONS} for m in MODES}
        for mode in MODES:
            for c in CONDITIONS:
                require(document(q,private['baseline'][mode][c])==corrected[mode][c], "TX review amendment failed its source integrity check")
                expected=project_score(corrected[mode][c])
                expected['source_bindings']['private_report_sha256']=private['baseline'][mode][c]['sha256']
                require(document(p,public['baseline'][mode][c])==expected, "TX review amendment failed its source integrity check")
        first_projection=dict(schema='math-gauge.public-task-scores/v1',benchmark_version='1.1.0',
            model_label=base['partial']['nonlogical_retry_3']['model_label'],
            public_case_ids=public_assessment_case_ids(assessment),views={},
            human_review='pending',formal_comparison_eligible=False)
        ids=first_projection['public_case_ids']
        for mode in MODES:
            first_projection['views'][mode]={c:project_public_task_view(corrected[mode][c],ids,
                private['baseline'][mode][c]['sha256']) for c in CONDITIONS}
        require(public['_public_tasks']['baseline']==first_projection, "TX review amendment failed its source integrity check")
        if private['revised'] is not None:
            parent=document(q,descriptor(q,q/private['original_adoption']['path'].replace('public.json','private.json')))
            revision=load_revision_inputs(q,parent['inputs'],public_root=p,
                base_reports={m:base[m]['nonlogical_retry_3'] for m in MODES})
            revised={}
            for mode in MODES:
                score=score_neutral_revision_after_review_amendment(base[mode]['nonlogical_retry_3'],
                    corrected[mode]['nonlogical_retry_3'],assessment,revision=revision,mode=mode)
                require(document(q,private['revised'][mode])==score, "TX review amendment failed its source integrity check")
                expected=project_score(score)
                expected['source_bindings']['private_report_sha256']=private['revised'][mode]['sha256']
                require(document(p,public['revised'][mode])==expected, "TX review amendment failed its source integrity check")
                revised[mode]=score
            require(public['_public_tasks']['revised']==project_public_tasks(revised,ids,
                {m:private['revised'][m]['sha256'] for m in MODES}), "TX review amendment failed its source integrity check")
    return dict(corrected_models=len(index['models']),reviewed_condition_slots=index['reviewed_condition_slots'],new_candidate_calls=0)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action',choices=['prepare','check'])
    parser.add_argument('--private-root',type=Path,required=True)
    parser.add_argument('--packet',type=Path)
    args=parser.parse_args()
    print(json.dumps(prepare(ROOT,args.private_root,args.packet) if args.action=='prepare'
                     else check(ROOT,args.private_root),ensure_ascii=False))


if __name__=='__main__':
    main()
