#!/usr/bin/env python3
"""Adopt already completed neutral study deliveries through the shared scorer.

No candidate calls or new mathematical judgments. Writes only additive 1.2
manifests/reports and their public projection. Check is entirely read-only.
"""
import argparse
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from math_gauge.neutral_revision import (MODES, CONDITION, DIRECTORY, TARGET, SOURCE,
    VERSION, POLICY_PATH, TRANSITION_PATH, SOURCE_EDITION_PATH, descriptor, load_policy,
    load_model_selection, load_inputs, load_public, load_transition, project_score,
    project_public_tasks, verify_pair, read, document, require)
from math_gauge.records import public_assessment_case_ids
from math_gauge.scoring import score_neutral_revision_overlay

STUDY = 'studies/general-standards-recovery-20261120'
MODELS = ('sol-6.1-max','sol-6.2-max','terra-6.1-max')


def write(root, relative, value):
    path = Path(root) / relative
    raw = value if isinstance(value, bytes) else (json.dumps(value,ensure_ascii=False,indent=2)+'\n').encode()
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_bytes(raw)
    return descriptor(root,path)


def scoped_absolute(item, public_root, private_root):
    path = Path(item['path'])
    scope, root = (('public', public_root) if path.is_relative_to(public_root) else ('private', private_root))
    require(path.is_relative_to(root), 'Study source is outside the actual retained repositories')
    ref = {k:item[k] for k in ('path','bytes','sha256')}
    ref['path'] = path.relative_to(root).as_posix()
    read(root, ref)
    return dict(scope=scope, **ref)


def prepare(public_root, private_root, *, models=MODELS):
    public_root, private_root = Path(public_root).resolve(),Path(private_root).resolve()
    study = private_root / STUDY
    archive_ref = descriptor(private_root, study/'final-archive-manifest.json')
    archive = document(private_root, archive_ref)
    require(archive.get('private_only') is True and archive.get('study_id') == Path(STUDY).name,
            'Expected the retained completed private study archive')
    archived = {r['path']:r for r in archive['files']}

    def study_ref(relative):
        require(relative in archived, 'Study artifact was not in its final archive: ' + relative)
        item = archived[relative]
        ref = dict(path=STUDY+'/'+relative, bytes=item['bytes'], sha256=item['sha256'])
        read(private_root, ref)
        return ref

    summary_ref = study_ref('summary.json')
    summary = document(private_root,summary_ref)
    require(summary.get('is_official_benchmark_result') is False
            and summary.get('main_benchmark_modified') is False
            and summary.get('scoring_edition') == SOURCE and summary.get('selected_loss_cells') == 22
            and summary.get('new_calls') == 19 and summary.get('reused_neutral_cells') == 3
            and summary.get('candidate_received_external_previous_grade') is False
            and summary.get('candidate_received_case_specific_review') is False
            and summary.get('candidate_received_reference_answer') is False,
            'Original study scope/conditions must remain unchanged at adoption')
    source_map = document(private_root,study_ref('source-map.json'))
    originals = {(r['model_id'],r['case_id']):r for r in source_map['source_cells']}
    freeze_ref = study_ref('pre-run-freeze.json')
    packet_ref = study_ref('packet-index-evaluator-only.json')
    packets = document(private_root,packet_ref)
    packet_rows = {(r['model_id'],r['case_id']):r for r in packets['cells']}
    policy = load_policy(public_root)
    policy_ref = descriptor(public_root,public_root/POLICY_PATH)
    assessment = json.loads((public_root/'protocol/scoring-policy.json').read_bytes())
    public_ids = public_assessment_case_ids(assessment)
    entries = {(r['model_id'],r['case_id']):r for r in summary['cells']}
    require(len(entries) == len(summary['cells']), 'Duplicate completed study cell')
    adoptions, output = {},[]
    resource_path = public_root/'results/continuation-resources/v0.1.0/current.json'
    resources = descriptor(public_root,resource_path) if resource_path.is_file() else None
    for mid in models:
        source = load_model_selection(public_root,private_root,mid)
        selected = source['selection']
        require({cid for model,cid in entries if model == mid} == {r['case_id'] for r in selected},
                'Completed study does not cover exactly the current known loss tasks')
        rows = []
        for first in selected:
            cid, key = first['case_id'], (mid,first['case_id'])
            cell = entries[key]
            old,new = cell['original'],cell['new']
            require(old['answer_sha256'] == first['response_sha256']
                    and old['review_sha256'] == first['review_sha256']
                    and all(old['source_reports'][mode] == source['base_reports'][mode]['sha256'] for mode in MODES),
                    'Study first answer/review/report hashes differ from current adopted source')
            require(first['original_answer'] is not None, 'Original answer source is not recoverable')
            expected_old = dict(capability=old['MC']/100,partial=old['RMC']/100,strict=int(old['SMC']))
            require(all(abs(expected_old[m]-first['first_scores'][m]) < 1e-12 for m in MODES),
                    'Study original mathematical scores differ from the source report')
            original = originals.get(key)
            original_task = first['source_case']
            original_answer = first['original_answer']
            original_review = first['original_review']
            source_component = None
            if original is not None:
                original_task = scoped_absolute(original['original_task'],public_root,private_root)
                require(original['previous_answer']['sha256'] == first['response_sha256'],
                        'Study supplied a different previous answer')
                # Read both the original retained answer and exact candidate copy.
                original_answer = scoped_absolute(original['previous_answer'],public_root,private_root)
                read(private_root,study_ref('candidate/'+mid+'/'+cid+'/previous-answer.md'))
                source_component = scoped_absolute(original['source_component'],public_root,private_root)
            answer_ref,input_ref,review_ref = (study_ref(new[key]) for key in ('answer','input','review'))
            require(answer_ref['sha256'] == new['answer_sha256']
                    and input_ref['sha256'] == new['input_sha256']
                    and review_ref['sha256'] == new['review_sha256'],
                    'Study summary substituted retained input/answer/review bytes')
            attachments = []
            delivered = new.get('delivery_source')
            if isinstance(delivered,dict) and delivered.get('explicit_file'):
                attached = study_ref(delivered['explicit_file'])
                declared_hash = delivered.get('explicit_file_sha256') or delivered.get('sha256')
                require(declared_hash is None or attached['sha256'] == declared_hash,
                        'Explicit delivered file hash differs')
                raw = read(private_root,answer_ref)
                require(Path(attached['path']).name.encode() in raw
                        and delivered.get('no_unmentioned_workspace_added') is True,
                        'Unmentioned workspace content cannot supplement a delivered continuation')
                attachments.append(attached)
            if new['reused']:
                reuse_ref = study_ref(new['source_binding'])
                reuse = document(private_root,reuse_ref)
                require(reuse.get('arm') == 'neutral' and reuse.get('not_a_new_candidate_call') is True
                        and reuse['selection_contract']['original_response_sha256'] == first['response_sha256']
                        and reuse['selection_contract']['new_response_sha256'] == answer_ref['sha256'],
                        'Historical pilot is not the selected neutral continuation of this first answer')
                collection = scoped_absolute(reuse['native_evidence_source_bindings']['runtime/collection.json'],
                    public_root,private_root)
                collection_ref = {k:collection[k] for k in ('path','bytes','sha256')}
                extra_sources = [reuse_ref]
                for item in [reuse['source_pre_run_freeze'],*reuse['native_evidence_source_bindings'].values()]:
                    bound = scoped_absolute(item,public_root,private_root)
                    extra_sources.append({k:bound[k] for k in ('path','bytes','sha256')})
            else:
                packet = packet_rows[key]
                require(packet['input_sha256'] == input_ref['sha256'], 'Frozen packet changed before adoption')
                raw = read(private_root,input_ref)
                for segment in packet['segments']:
                    raw_segment = raw[segment['utf8_start']:segment['utf8_end']]
                    require(hashlib.sha256(raw_segment).hexdigest() == segment['source_sha256'],
                            'Actual input changed a frozen original task/history/material segment')
                session = 'engineering/sessions/'+mid+'--'+cid+'/'
                collection_ref = study_ref(session+'runtime/collection.json')
                native_response = study_ref(session+'output/response.md')
                require(native_response['sha256'] == answer_ref['sha256'],
                        'Review answer differs from actual collected complete final')
                extra_sources = [study_ref(session+'runtime/'+name) for name in
                    ('execution.json','plan.json','seal.json','attempt-ledger.json')]
                terminal = session+'runtime/terminal-output-observation.json'
                if terminal in archived:
                    extra_sources.append(study_ref(terminal))
            scores = dict(capability=new['MC']/100,partial=new['RMC']/100,strict=int(new['SMC']))
            rows.append(dict(case_id=cid,family_id=first['family_id'],subcategory=first['subcategory'],
                first_response_sha256=first['response_sha256'], first_review_sha256=first['review_sha256'],
                original_task=original_task,original_answer=original_answer,original_review=original_review,
                source_component=source_component,continuation=dict(status='reviewed',input=input_ref,
                answer=answer_ref,review=review_ref,collection=collection_ref,attachments=attachments,
                sources=extra_sources,reused=new['reused'],scores=scores)))
        destination = Path(DIRECTORY)/mid/source['record_id']
        original_record_ref = descriptor(private_root,private_root/source['source_record']['path'])
        inputs = dict(schema='math-gauge.neutral-revision-inputs/v1',version=VERSION,
            benchmark_version=TARGET,source_scoring_edition=SOURCE,attempt_condition=CONDITION,
            model_id=mid,record_id=source['record_id'],model_label=source['reports']['partial']['model_label'],
            source_record=original_record_ref,policy=policy_ref,base_reports=source['base_reports'],rows=rows,
            study_sources=[archive_ref,summary_ref,freeze_ref,packet_ref,study_ref('source-map.json')],
            post_observation=True,original_bytes_rewritten=False,reviewer_kind='ai',human_review='pending',
            formal_comparison_eligible=False,adoption_new_candidate_calls=0)
        inputs_ref = write(private_root,destination/'inputs.json',inputs)
        validated = load_inputs(private_root,inputs_ref,public_root=public_root,base_reports=source['reports'])
        full_scores,private_scores,public_scores = {},{},{}
        for mode in MODES:
            score = score_neutral_revision_overlay(source['reports'][mode],assessment,revision=validated,mode=mode)
            full_scores[mode] = score
            private_scores[mode] = write(private_root,destination/(mode+'-'+CONDITION+'.json'),score)
            projected = project_score(score)
            projected['source_bindings']['private_report_sha256'] = private_scores[mode]['sha256']
            public_scores[mode] = write(public_root,destination/(mode+'-'+CONDITION+'.json'),projected)
        manifest = dict(schema='math-gauge.neutral-revision-private/v1',version=VERSION,benchmark_version=TARGET,
            model_id=mid,record_id=source['record_id'],inputs=inputs_ref,scores=private_scores)
        private_ref = write(private_root,destination/'private.json',manifest)
        task_ref = write(public_root,destination/'public-tasks.json',project_public_tasks(full_scores,public_ids,
            {m:private_scores[m]['sha256'] for m in MODES}))
        public_continuations = []
        for row in rows:
            if row['case_id'] not in public_ids:
                continue
            copied = dict(case_id=row['case_id'],attachments=[])
            for field,filename in [('answer','answer.md'),('review','review.json'),('input','input.md')]:
                copied[field] = write(public_root,destination/'public-continuations'/row['case_id']/filename,
                    read(private_root,row['continuation'][field]))
            for attached in row['continuation']['attachments']:
                copied['attachments'].append(write(public_root,
                    destination/'public-continuations'/row['case_id']/Path(attached['path']).name,
                    read(private_root,attached)))
            public_continuations.append(copied)
        public = dict(schema='math-gauge.neutral-revision-public/v1',version=VERSION,benchmark_version=TARGET,
            source_scoring_edition=SOURCE,attempt_condition=CONDITION,model_id=mid,record_id=source['record_id'],
            source_record=source['source_record'],policy=policy_ref,base_reports=source['public_base_reports'],
            scores=public_scores,public_tasks=task_ref,public_continuations=public_continuations,
            private_inputs_sha256=inputs_ref['sha256'],private_manifest_sha256=private_ref['sha256'],
            revision_counts=dict(selected=len(rows),reviewed=len(rows),delivery_failed=0,pending=0,
                source_new_calls=sum(not r['continuation']['reused'] for r in rows),
                reused_neutral_calls=sum(r['continuation']['reused'] for r in rows)),
            post_observation=True,reviewer_kind='ai',human_review='pending',formal_comparison_eligible=False,
            adoption_new_candidate_calls=0)
        if resources is not None:
            public['revision_resources'] = resources
        public_ref = write(public_root,destination/'public.json',public)
        verify_pair(public_root,private_root,public_ref,private_ref,
                    base_reports=source['reports'],assessment_policy=assessment)
        adoptions[mid] = public_ref
        output.append(dict(model_id=mid,selected=len(rows),scores={mode:full_scores[mode]['metrics']['earned']['confirmed']
            for mode in MODES},deltas={mode:full_scores[mode]['metrics']['earned']['confirmed']-
            source['reports'][mode]['metrics']['earned']['confirmed'] for mode in MODES}))
    current = json.loads((public_root/'benchmark.json').read_bytes())
    if current['version'] == TARGET:
        old_transition = load_transition(public_root,current)
        old = old_transition['_source_edition']
        adoptions = dict(old_transition['adoptions'],**adoptions)
    else:
        require(current['version'] == SOURCE, 'Neutral adoption starts with current 1.1 assessment')
        old = current
    source_ref = write(public_root,SOURCE_EDITION_PATH,old)
    all_models = set(old['selected_result_models']) | set(old.get('current_assessment_admissions',{})) | {
        'dot-underlying-model-20261108'}
    transition = dict(schema='math-gauge.neutral-revision-transition/v1',version=VERSION,
        source_scoring_edition=SOURCE,target_scoring_edition=TARGET,task_suite_version='1.0.0',
        attempt_condition=CONDITION,post_observation=True,adoption_new_candidate_calls=0,
        original_bytes_rewritten=False,human_review='pending',formal_comparison_eligible=False,
        source_edition=source_ref,policy=policy_ref,adoptions=adoptions,pending_models=sorted(all_models-set(adoptions)))
    transition_ref = write(public_root,TRANSITION_PATH,transition)
    edition = dict(deepcopy(old),version=TARGET,status='local-assessment-candidate',
        source_state='Local1.2.0 source-bound neutral continuation adoption; original1.1 assessments and1.0 tasks retained.',
        neutral_revision_transition=transition_ref)
    write(public_root,'benchmark.json',edition)
    load_transition(public_root)
    return dict(benchmark_version=TARGET,adoption_new_candidate_calls=0,models=output,pending_models=len(transition['pending_models']))


def check(public_root,private_root=None):
    transition = load_transition(public_root)
    require(transition is not None,'No neutral revision transition selected')
    assessment = json.loads((Path(public_root)/'protocol/scoring-policy.json').read_bytes())
    result = []
    for mid,ref in transition['adoptions'].items():
        public = load_public(public_root,ref)
        if private_root is not None:
            source = load_model_selection(public_root,private_root,mid)
            private_ref = descriptor(private_root,Path(private_root)/Path(ref['path']).parent/'private.json')
            verify_pair(public_root,private_root,ref,private_ref,
                        base_reports=source['reports'],assessment_policy=assessment)
        result.append(dict(model_id=mid,scores={m:public['_scores'][m]['metrics']['earned']['confirmed'] for m in MODES}))
    return dict(benchmark_version=TARGET,models=result,pending_models=len(transition['pending_models']),adoption_new_candidate_calls=0)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action',choices=['prepare','check'])
    parser.add_argument('--public-root',type=Path,default=ROOT)
    parser.add_argument('--private-root',type=Path)
    args = parser.parse_args()
    if args.action == 'prepare':
        if args.private_root is None:
            parser.error('prepare requires --private-root')
        result = prepare(args.public_root,args.private_root)
    else:
        result = check(args.public_root,args.private_root)
    print(json.dumps(result,ensure_ascii=False,indent=2))


if __name__ == '__main__':
    main()
