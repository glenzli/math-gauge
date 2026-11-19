#!/usr/bin/env python3
"""Bind completed AI TX reviews to unchanged source answers and shared scores.

Preparation consumes an explicit evaluator review packet; it does not grade
prose or call any model. Check is read-only. Private mathematical material is
never copied into the public projection.
"""
import argparse
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from math_gauge.records import evidence_bytes, project_assessment_score, project_public_task_view
from math_gauge.theorem_extension_calibration import (
    MODES, CONDITIONS, PUBLIC_CASES, load_policy, load_inputs, load_private, load_public, verify_pair, project_score)
from math_gauge.scoring import score_theorem_extension_calibration_overlay

PREFIX = Path('results/edition-reassessments/v1.1.0')
REVIEW_PREFIX = Path('results/theorem-extension-reviews/v0.1.0')


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def descriptor(root, path):
    path = Path(path)
    raw = path.read_bytes()
    return dict(path=path.relative_to(root).as_posix(), bytes=len(raw), sha256=sha(raw))


def write_json(root, relative, value):
    path = root / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')
    return descriptor(root, path)


def rooted(folder, item):
    return None if item is None else dict(item, path=(folder / item['path']).as_posix())


def actual_source_record(model):
    return Path(model['source_record'])


def source_views(model):
    return {'capability':model['capability'],
            'partial':{'single_attempt':model['combined'],
                       'nonlogical_retry_3':model['retry']['combined']},
            'strict':model['strict']}


def selected_report_refs(public_root, record, folder, model):
    fields = {'capability':'capability_results','partial':'assessment_results','strict':'strict_results'}
    refs = {mode:{c:rooted(folder,record[field][c]) for c in CONDITIONS}
            for mode,field in fields.items()}
    for supplement in ('harness_correction','c003_continuation'):
        selected = model.get(supplement)
        if selected is None:
            continue
        manifest = json.loads(evidence_bytes(public_root, selected['manifest']))
        for mode in MODES:
            refs[mode]['nonlogical_retry_3'] = rooted(folder,manifest['scores'][mode])
    return refs


def selected_private_refs(private_root, record, folder, model):
    if model.get('record_kind') == 'native_harness':
        refs={mode:{c:descriptor(private_root,private_root/folder/(mode+'-'+(
            'retry-' if c=='nonlogical_retry_3' else '')+'result.json')) for c in CONDITIONS} for mode in MODES}
    else:
        fields={'capability':'capability_results','partial':'assessment_results','strict':'strict_results'}
        refs={mode:{c:rooted(folder,record[field][c]) for c in CONDITIONS} for mode,field in fields.items()}
    if model.get('harness_correction'):
        edition=json.loads((private_root/'benchmark.json').read_bytes())
        supplement=json.loads(evidence_bytes(private_root,edition['result_corrections'][model['id']]))
        for mode in MODES:
            refs[mode]['nonlogical_retry_3']=rooted(folder,supplement['scores'][mode])
    if model.get('c003_continuation'):
        index=json.loads((private_root/'results/current-c003-continuations.json').read_bytes())
        selection=index['selections'][model['id']]
        registry=json.loads(evidence_bytes(private_root,selection['registry']))
        registry_folder=Path(selection['registry']['path']).parent
        for mode in MODES:
            refs[mode]['nonlogical_retry_3']=rooted(registry_folder,registry['private_scores'][mode])
    return refs


def make_review(grade, row, policy, *, policy_sha256, primary_reviewer):
    results = grade['accepted_results']
    citations = []
    for result in results:
        for item in result['evidence']:
            citations.append(dict(quote=item['quote'], start_byte=item['utf8_start'], end_byte=item['utf8_end']))
    return {
        'schema':'math-gauge.theorem-extension-calibration-review/v1','version':'0.1.0',
        'case_id':row['case_id'],'answer_sha256':row['response_sha256'],
        'source_review_sha256':(row['review'] or {}).get('sha256'),
        'baseline_B':row['old_B'],'old_R':row['old_R'],'new_R':grade['new_R'],
        'policy_sha256':policy_sha256,
        'standard_sha256':(policy['standards']['sha256'] if row['case_id'] in PUBLIC_CASES
                           else policy['private_standards']['sha256']),
        'reviewer_kind':'ai','reviewer':[primary_reviewer,'Codex coordinator: source verification and cross-case adjudication'],
        'human_review':'pending','post_observation':True,
        'status':('reviewed' if row['response'] is not None else
                  'not_run' if row['source_status']=='not_run' else 'delivery_failed'),
        'reason':grade['rationale'],
        'attained':('\n\n'.join(r['statement']+'\n范围：'+r['scope']+'\n核验：'+r['correctness_check']
                                for r in results) or '无可审核的选定最终答卷；保持原状态。'),
        'not_attained':grade['next_level_gap'], 'citations':citations,
    }


def prepare(public_root, private_root, packet, *, only_models=None, revision=None):
    """Create additive evidence and all six views; original archives stay intact."""
    from math_gauge.current_results import load_source_assessment, selected_source_record_paths
    from math_gauge.editions import source_edition, load_assessment_transition
    public_root, private_root = Path(public_root).resolve(), Path(private_root).resolve()
    policy_ref = descriptor(public_root,public_root/'protocol/theorem-extension-calibration.json')
    policy = load_policy(public_root,policy_ref)
    assessment = json.loads((public_root/'protocol/scoring-policy.json').read_bytes())
    original=source_edition(public_root)
    if original['version']!='1.0.0':
        raise ValueError('Prepare requires the explicitly bound unchanged1.0 source edition')
    official=selected_source_record_paths(public_root)
    if only_models is not None and not set(only_models)<=set(official):
        raise ValueError('Only officially selected source models may be reassessed')
    if revision is not None:
        import re
        if not re.fullmatch('[a-zA-Z0-9][a-zA-Z0-9._-]*',revision):
            raise ValueError('Unsafe local reassessment revision')
    base_models=[]
    for mid,path in official.items():
        if only_models is not None and mid not in only_models:
            continue
        record,scores,_,correction,c003=load_source_assessment(public_root,mid,path)
        m={'id':mid,'source_record':path,'record_kind':record.get('record_kind') or (
            'native_harness' if Path(path).name=='native-observation.json' else None),
            'capability':scores['capability'],'strict':scores['strict'],
            'combined':scores['partial']['single_attempt'],
            'retry':{'combined':scores['partial']['nonlogical_retry_3']}}
        if correction is not None:m['harness_correction']={'manifest':correction['_selection']}
        if c003 is not None:m['c003_continuation']={'manifest':c003['_selection']}
        base_models.append(m)
    grades, rows = packet['grades'], packet['rows']
    grade_index = {(g['case_id'],g['model_id'],g['response_sha256']):g for g in grades}
    if len(grade_index) != len(grades):
        raise ValueError('Duplicate mathematical reassessment')
    row_index = {(r['model_id'],r['condition'],r['case_id']):r for r in rows}
    if len(row_index) != len(rows) or len(rows) != len(official)*6*2:
        raise ValueError('Reassessment must bind all selected TX slots in both conditions')
    transition=load_assessment_transition(public_root)
    selections = {} if transition is None else deepcopy(transition['calibrations'])
    for model in base_models:
        mid, record_rel = model['id'],actual_source_record(model)
        folder, recid = record_rel.parent,record_rel.parent.name
        public_record = json.loads(evidence_bytes(public_root,descriptor(public_root,public_root/record_rel)))
        private_record = json.loads(evidence_bytes(private_root,descriptor(private_root,private_root/record_rel)))
        bases = source_views(model)
        refs = selected_report_refs(public_root,public_record,folder,model)
        full_refs_source = selected_private_refs(private_root,private_record,folder,model)
        destination = PREFIX/mid/recid
        if revision is not None:destination=destination/revision
        public_bases, private_bases = {},{}
        private_scores = {}
        for mode in MODES:
            public_bases[mode],private_bases[mode],private_scores[mode] = {},{},{}
            for condition in CONDITIONS:
                public_bytes = evidence_bytes(public_root,refs[mode][condition])
                if json.loads(public_bytes) != bases[mode][condition]:
                    raise ValueError('Source public path lost its effective report')
                full_ref=full_refs_source[mode][condition]
                full_bytes=evidence_bytes(private_root,full_ref)
                if sha(full_bytes)!=bases[mode][condition]['source_bindings']['private_report_sha256']:
                    raise ValueError('Effective private report does not match its public source binding: '+mid+'/'+mode+'/'+condition)
                for root,body,mapping in ((public_root,public_bytes,public_bases),(private_root,full_bytes,private_bases)):
                    path=root/destination/('base-'+mode+'-'+condition+'.json')
                    path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(body)
                    mapping[mode][condition]=descriptor(root,path)
                private_scores[mode][condition]=json.loads(full_bytes)
        condition_rows, review_refs = {},{}
        for condition in CONDITIONS:
            condition_rows[condition],review_refs[condition]=[],[]
            for old in sorted((r for r in rows if r['model_id']==mid and r['condition']==condition),key=lambda r:r['case_id']):
                key=old['case_id'],mid,old['response_sha256']
                grade=grade_index[key]
                if grade['baseline_B']!=old['old_B'] or grade['old_R']!=old['old_R']:
                    raise ValueError('Reassessment changed its old baseline/research source')
                # Identical answers may have distinct original review bindings
                # across conditions; share mathematics without overwriting either chain.
                suffix=sha(json.dumps([old['response_sha256'],(old['review'] or {}).get('sha256'),
                    old['old_B'],old['old_R'],grade['new_R'],old['source_status']],sort_keys=True).encode())[:20]
                relative=REVIEW_PREFIX/mid/recid/(old['case_id']+'-'+suffix+'.json')
                review=make_review(grade,old,policy,policy_sha256=policy_ref['sha256'],primary_reviewer=grade['_reviewer'])
                private_review=write_json(private_root,relative,review)
                if old['case_id'] in PUBLIC_CASES:
                    public_review=write_json(public_root,relative,review)
                    if public_review!=private_review:
                        raise ValueError('Public and private public-case new reviews differ')
                    review_refs[condition].append({'case_id':old['case_id'],'review':public_review})
                condition_rows[condition].append({'case_id':old['case_id'],
                    'source_inputs':rooted(folder,old['source_inputs']),
                    'response':rooted(folder,old['response']), 'source_review':rooted(folder,old['review']),
                    'baseline_B':old['old_B'],'old_R':old['old_R'],'new_R':grade['new_R'],'new_review':private_review})
        inputs={'schema':'math-gauge.theorem-extension-calibration-inputs/v1','version':'0.1.0',
            'benchmark_version':'1.1.0','model_id':mid,'model_label':private_scores['partial']['nonlogical_retry_3']['model_label'],
            'record_id':recid,'source_record':descriptor(private_root,private_root/record_rel),
            'policy':policy_ref,'private_standards':descriptor(private_root,private_root/'protocol/theorem-extension-calibration.md'),
            'base_reports':private_bases,'conditions':condition_rows,'reviewer_kind':'ai','human_review':'pending',
            'post_observation':True,'formal_comparison_eligible':False,'new_candidate_calls':0,'source_raw_bytes_rewritten':False}
        inputs_ref=write_json(private_root,destination/'inputs.json',inputs)
        validated=load_inputs(private_root,inputs_ref,public_root=public_root,policy=policy,effective_scores=private_scores)
        derived,full_refs,public_refs={}, {},{}
        projection={'schema':'math-gauge.public-task-scores/v1','benchmark_version':'1.1.0',
            'model_label':inputs['model_label'],'public_case_ids':[], 'views':{},'human_review':'pending','formal_comparison_eligible':False}
        ids=sorted(json.loads((public_root/'cases/catalog.json').read_bytes())['entries'],key=lambda e:e['case_id'])
        public_ids=[e['case_id'] for e in ids]
        projection['public_case_ids']=public_ids
        old_projection=dict(deepcopy(projection),benchmark_version='1.0.0')
        for mode in MODES:
            derived[mode],full_refs[mode],public_refs[mode],projection['views'][mode],old_projection['views'][mode] = {},{},{},{},{}
            for condition in CONDITIONS:
                current=score_theorem_extension_calibration_overlay(private_scores[mode][condition],assessment,
                    calibration=validated,mode=mode,condition=condition)
                derived[mode][condition]=current
                full_refs[mode][condition]=write_json(private_root,destination/(mode+'-'+condition+'.json'),current)
                aggregate=project_score(current)
                aggregate['source_bindings']['private_report_sha256']=full_refs[mode][condition]['sha256']
                public_refs[mode][condition]=write_json(public_root,destination/(mode+'-'+condition+'.json'),aggregate)
                projection['views'][mode][condition]=project_public_task_view(current,public_ids,full_refs[mode][condition]['sha256'])
                old_projection['views'][mode][condition]=project_public_task_view(private_scores[mode][condition],public_ids,
                    private_bases[mode][condition]['sha256'])
        manifest={'schema':'math-gauge.theorem-extension-calibration-private/v1','version':'0.1.0','benchmark_version':'1.1.0',
            'model_id':mid,'record_id':recid,'inputs':inputs_ref,'scores':full_refs}
        private_manifest=write_json(private_root,destination/'calibration.json',manifest)
        load_private(private_root,private_manifest,public_root=public_root,policy=policy,effective_scores=private_scores,assessment_policy=assessment)
        public_manifest={'schema':'math-gauge.theorem-extension-calibration-public/v1','version':'0.1.0','benchmark_version':'1.1.0',
            'model_id':mid,'record_id':recid,'source_record':descriptor(public_root,public_root/record_rel),
            'policy':policy_ref,'private_inputs_sha256':inputs_ref['sha256'],'private_manifest_sha256':private_manifest['sha256'],
            'base_reports':public_bases,'base_public_tasks':write_json(public_root,destination/'base-public-tasks.json',old_projection),
            'scores':public_refs,'public_tasks':write_json(public_root,destination/'public-tasks.json',projection),
            'public_reviews':review_refs,'human_review':'pending','formal_comparison_eligible':False,'new_candidate_calls':0,'post_observation':True}
        public_manifest_ref=write_json(public_root,destination/'calibration.json',public_manifest)
        load_public(public_root,public_manifest_ref,policy=policy,effective_scores=bases,source_record=public_record)
        verify_pair(public_root,private_root,public_manifest_ref,private_manifest,
            policy=policy,assessment_policy=assessment,public_effective_scores=bases,
            private_effective_scores=private_scores,source_record=public_record,public_case_ids=public_ids)
        selections[mid]=public_manifest_ref
        print(mid,'prepared',flush=True)
    return selections


def check(public_root, private_root=None):
    """Read original source chains and verify the selected current public/private views."""
    from math_gauge.current_results import load_source_assessment, selected_source_record_paths
    from math_gauge.editions import load_assessment_transition, verify_compatibility
    public_root = Path(public_root).resolve()
    private_root = None if private_root is None else Path(private_root).resolve()
    edition = verify_compatibility(public_root)
    transition = load_assessment_transition(public_root,edition)
    if transition is None:
        return {'selected':False,'candidate_calls':0}
    policy = load_policy(public_root,transition['policy'])
    assessment=json.loads((public_root/'protocol/scoring-policy.json').read_bytes())
    verified=[]
    official=selected_source_record_paths(public_root)
    for mid, public_ref in transition['calibrations'].items():
        manifest=json.loads(evidence_bytes(public_root,public_ref))
        if (manifest.get('model_id')!=mid
                or manifest['source_record']['path']!=official.get(mid)):
            raise ValueError('Current TX reassessment must bind its officially selected model and source record')
        record,scores,_,correction,c003=load_source_assessment(public_root,mid,manifest['source_record']['path'])
        current=load_public(public_root,public_ref,policy=policy,effective_scores=scores,source_record=record)
        if private_root is not None:
            record_rel=Path(manifest['source_record']['path'])
            private_record=json.loads((private_root/record_rel).read_bytes())
            model={'id':mid,'record_kind':record.get('record_kind') or (
                'native_harness' if record_rel.name=='native-observation.json' else None)}
            if correction is not None: model['harness_correction']={}
            if c003 is not None: model['c003_continuation']={}
            # Presence selects the named original supplement. Its evidence is
            # validated by the shared source composition above, not inferred.
            if correction is not None: model['harness_correction']=correction
            if c003 is not None: model['c003_continuation']=c003
            refs=selected_private_refs(private_root,private_record,record_rel.parent,model)
            full={mode:{c:json.loads(evidence_bytes(private_root,ref)) for c,ref in view.items()}
                  for mode,view in refs.items()}
            for mode in MODES:
                for condition in CONDITIONS:
                    if refs[mode][condition]['sha256']!=scores[mode][condition]['source_bindings']['private_report_sha256']:
                        raise ValueError('Current private source report differs from its original public binding')
            private_ref=descriptor(private_root,private_root/public_ref['path'])
            verify_pair(public_root,private_root,public_ref,private_ref,policy=policy,
                assessment_policy=assessment,public_effective_scores=scores,private_effective_scores=full,
                source_record=record)
        verified.append({'model_id':mid,'views':len(MODES)*len(CONDITIONS),
                         'source_record_sha256':manifest['source_record']['sha256']})
    return {'selected':True,'benchmark_version':edition['version'],'models':verified,
            'paired_private_recomputed':private_root is not None,'candidate_calls':0}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action',choices=('prepare','check'),nargs='?',default='prepare')
    parser.add_argument('--public-root',type=Path,default=ROOT)
    parser.add_argument('--private-root',type=Path,required=True)
    parser.add_argument('--review-packet',type=Path)
    parser.add_argument('--selection-output',type=Path)
    parser.add_argument('--model',action='append')
    parser.add_argument('--revision')
    args=parser.parse_args()
    if args.action=='check':
        print(json.dumps(check(args.public_root,args.private_root),ensure_ascii=False))
        return
    if args.review_packet is None or args.selection_output is None:
        parser.error('prepare requires an explicit --review-packet and --selection-output')
    selections=prepare(args.public_root,args.private_root,json.loads(args.review_packet.read_bytes()),
                       only_models=args.model,revision=args.revision)
    args.selection_output.write_text(json.dumps(selections,ensure_ascii=False,indent=2)+'\n')


if __name__=='__main__':
    main()
