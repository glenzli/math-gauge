"""Source-bound observer clocks for the separately admitted2026-11-25 Dot run.

No CLI/native-observation record is synthesized. Existing timing validators and
summaries consume authenticated measurements; costs and mathematical scores
remain outside this component. Public output is an explicit additive source.
"""
from copy import deepcopy
from pathlib import Path
import hashlib
import json
import math
import re

from . import timings
from .dot_rerun_admission import MODEL, LABEL, load_public as load_admission
from .dot_rerun_sources import validate as validate_native
from .dot_rerun_neutral import verify_replays
from .dot_rerun_independent import verify_review as verify_independent
from .theorem_extension_calibration import document, read, require
from .mathematical_profile import source_bytes

VERSION = '0.1.0'
DIRECTORY = 'results/dot-native-timings/v0.1.0/dot-20261125'
INDEX_PATH = DIRECTORY + '/index.json'
POLICY_PATH = 'protocol/dot-native-timings.md'
SOURCE_ROOT = 'results/dot-native-profiles/v0.1.0/dot-20261125/source'
CONTROLLER = SOURCE_ROOT + '/CONTROLLER.md'
CONTROLLER_SHA256 = '76adeb826f2ea6a74db3e69c51af500e5a20c41626c114361555bb04d9e89d39'
METHOD = 'coordinator_observed_wall'
QUALITY = 'approximate coordinator launch-to-completion observation; not a native inference clock'
CONDITION = 'nonlogical_retry_3'
BOUNDARIES = dict(new_candidate_calls=0, scores_modified=False, costs_included=False,
                  native_timing_independently_verified=False)


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2, allow_nan=False)+'\n').encode()


def reference(path, raw):
    return dict(path=str(path), bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())


def _ref(item):
    return {key:item[key] for key in ('path','bytes','sha256')}


def _native_ref(item):
    return dict(_ref(item), path=SOURCE_ROOT+'/'+item['path'])


def _json(root, path):
    return json.loads((Path(root)/path).read_bytes())


def _text(value):
    return isinstance(value,str) and bool(value.strip()) and '\0' not in value


def _same_source(left, right):
    return _ref(left) == _ref(right)


def authenticate(public_root, private_root):
    """Authenticate selected physical answers; no profile grades are consulted."""
    public_root, private_root = Path(public_root), Path(private_root)
    admission = load_admission(public_root, historical=True)
    require(admission is not None, 'Dot clocks require the exact admitted native run')
    native = private_root/SOURCE_ROOT
    ledger_path = native/'admission-build/inputs/native-source-ledger.json'
    ledger_raw = ledger_path.read_bytes()
    require(hashlib.sha256(ledger_raw).hexdigest() == admission['public_source']['private_source_sha256'],
            'Clock native source differs from the selected public admission')
    ledger = json.loads(ledger_raw)
    selected = validate_native(native, native/'dataset/benchmark-v1.0.0', ledger,
                               include_evaluator_bindings=True)['selected']
    neutral_raw = (native/'admission-build/neutral/private-inputs.json').read_bytes()
    require(hashlib.sha256(neutral_raw).hexdigest() == admission['revised']['private_inputs_sha256'],
            'Clock continuation source differs from the adopted neutral input')
    neutral = json.loads(neutral_raw)
    verify_replays(public_root,native,ledger,neutral)
    reg_ref = _json(native,'admission-build/research/registration-descriptor.json')
    require(reg_ref['sha256'] == admission['research']['private_research_sha256'],
            'Clock research trajectory belongs to another native run')
    # This existing gate authenticates designated files and their trajectory.
    # Its mathematical values are not timing inputs.
    verify_independent(public_root,native,reg_ref)
    registration = document(native,reg_ref)
    expected = {}
    for slot,binding in selected.items():
        call = ledger['slots'][slot]['physical_calls'][-1]
        case,phase = slot.split(':')
        expected[slot] = dict(series='base',case_id=case,phase=phase,answer=binding['response'],
            context=call['context_id'],request=call['request'],delivery_status='delivered')
    for row in neutral['rows']:
        continuation = row['continuation'];observations=[]
        for ref in continuation['sources']:
            if ref['path'].endswith('.json'):
                candidate=document(native,ref)
                if candidate.get('schema')=='math-gauge.dot-neutral-replay-observation/v1':observations.append(candidate)
        require(len(observations)==1,'One actual native continuation observation is required')
        observed=observations[0]
        expected[row['case_id']+':neutral']=dict(series='neutral',case_id=row['case_id'],phase='neutral',
            answer=continuation.get('answer')or continuation['cutoff_content'],context=observed['context_id'],
            request=observed['request'],delivery_status='delivered'if continuation['status']=='reviewed'else'delivery_failed')
    for phase,ref in registration['round_observations'].items():
        observed=document(native/registration['source_root'],ref)
        raw=(native/'open-research'/phase/'answer.md').read_bytes()
        answer=reference('open-research/'+phase+'/answer.md',raw)
        require(answer['sha256']==observed['answer_sha256'],'Clock research final differs from the admitted file')
        expected['MG-MT001:'+phase]=dict(series='independent',case_id='MG-MT001',phase=phase,
            answer=answer,context=registration['context_id'],request=None,delivery_status='delivered')
    require(len(expected)==51,'Dot clocks require42base,6neutral and3independent slots')
    return dict(admission=admission,expected=expected,private_root=private_root)


def validate_extract(extract, controller):
    require(extract.get('schema')=='math-gauge.dot-coordinator-clock-extract-proposal/v1'
            and extract.get('extraction_only')is True and extract.get('runtime_independently_verified')is False
            and extract['original_source']['sha256']==CONTROLLER_SHA256
            and len(controller)==22339 and hashlib.sha256(controller).hexdigest()==CONTROLLER_SHA256,
            'Clock extraction changed its original observer source or runtime boundary')
    events=extract.get('events',[])
    require(isinstance(events,list)and len({e['id']for e in events})==len(events),
            'Observer clock events need unique original identities')
    for event in events:
        start,end=event.get('byte_start'),event.get('byte_end')
        require(type(start)is int and type(end)is int and 0<=start<end<=len(controller)
                and _text(event.get('quote'))and controller[start:end]==event['quote'].encode()
                and event['source']['sha256']==CONTROLLER_SHA256
                and event['quote'].startswith(event['timestamp_text']),
                'Observer clock quote or timestamp differs from exact original bytes')
        timings._stamp(event['timestamp_text'])
    return events


def validate_selection(row, expected):
    require(all(row.get(k)==expected[k]for k in ('series','case_id','phase','delivery_status'))
            and _same_source(row['selected_answer'],expected['answer'])
            and row.get('selected_physical_context')==expected['context'],
            'Clock belongs to another selected answer or physical request')
    require((row.get('selected_request')is None)==(expected['request']is None)
            and(expected['request']is None or _same_source(row['selected_request'],expected['request'])),
            'Clock request differs from the selected physical source')


def validate_private(public_root,private_root,admission_manifest,*,timing_root=None):
    require(admission_manifest.get('schema')=='math-gauge.dot-native-timing-admission/v1'
            and admission_manifest.get('model_id')==MODEL
            and all(admission_manifest.get(k)==v for k,v in BOUNDARIES.items()),
            'Invalid native observer-clock admission')
    context=authenticate(public_root,private_root)
    require(admission_manifest['source_admission']==context['admission']['selection']
            and admission_manifest['controller']['path']==CONTROLLER
            and admission_manifest['controller']['sha256']==CONTROLLER_SHA256,
            'Observer clocks lost their exact native admission or controller')
    controller=read(private_root,admission_manifest['controller'])
    folder=Path(timing_root)if timing_root is not None else Path(private_root)/DIRECTORY
    ledger=document(folder,admission_manifest['ledger']);extract=document(folder,admission_manifest['extract'])
    events=validate_extract(extract,controller)
    require(ledger.get('schema')=='math-gauge.dot-native-clock-audit-proposal/v1'
            and ledger.get('model_id')==MODEL and ledger.get('new_candidate_calls')==0
            and ledger.get('scores_modified')is False and ledger['cost']['status']=='excluded_by_user'
            and ledger['cost']['participates']is False,
            'Clock audit cannot infer costs, change scores or create candidate calls')
    rows=ledger.get('rows',[]);expected=context['expected']
    require(len(rows)==len(expected)and {r['id']for r in rows}==set(expected),
            'Clock ledger omitted, duplicated or substituted a selected slot')
    base=[]
    for row in rows:
        validate_selection(row,expected[row['id']])
        read(private_root,_native_ref(row['selected_answer']))
        if row.get('selected_request')is not None:read(private_root,_native_ref(row['selected_request']))
        for ref in row.get('selection_evidence',[]):read(private_root,_native_ref(ref))
        require(row.get('native_timing_independently_verified')is False
                and row.get('applied_wait_deduction_seconds')==0 and row.get('excluded_wait_seconds')is None
                and _text(row.get('note')), 'Observed clocks cannot invent native certification or wait deductions')
        if row['availability']=='unknown':
            require(row.get('seconds')is None and row.get('method')is None and row.get('time_binding')is None,
                    'Missing clock cannot be replaced by zero, a budget or a minute midpoint')
        else:
            require(row['availability']=='known'and row['method']==METHOD and timings._seconds(row['seconds']),
                    'A known Dot clock must be an explicitly observed coordinator interval')
            binding=row['time_binding']
            require(binding.get('kind')=='timestamp_difference','Observer clocks require the actual retained timestamp pair')
            for side in ('start','end'):
                endpoint=binding[side]
                require(endpoint['source']==admission_manifest['extract']
                        and re.fullmatch(r'/events/(0|[1-9][0-9]*)/timestamp_text',endpoint['pointer'])is not None,
                        'Clock timestamp pair borrowed an unselected source')
                event=events[int(endpoint['pointer'].split('/')[2])]
                require(event.get('precision')!='minute'and re.search(r'T\d\d:\d\d:\d\d',event['timestamp_text']),
                        'Minute-only observations must retain an unknown scalar')
            seconds,start,end=timings._bound_seconds(folder,binding,METHOD)
            require(timings._seconds(seconds)and abs(seconds-row['seconds'])<0.000002
                    and row['started_at']==start and row['ended_at']==end,
                    'Observer duration differs from its original timestamp pair')
        if row['series']=='base':
            base.append(dict(id=row['id'],case_id=row['case_id'],phase=row['phase'],
                answer_sha256=row['selected_answer']['sha256'],delivery_status=row['delivery_status'],
                availability=row['availability'],seconds=row['seconds'],method=row['method'],
                time_binding=row['time_binding'],started_at=row.get('started_at'),ended_at=row.get('ended_at'),
                note=row['note'],evidence=[]))
    # Reuse the timing owner's full42-slot byte/measurement validator. This is
    # an in-memory validation view, not a fabricated transport/record artifact.
    normalized=dict(schema=timings.SCHEMA,version='0.1.0',visibility='private',
        new_candidate_calls=0,scores_modified=False,rows=base,summary=timings.summaries(base))
    timings.validate_private(normalized,folder,{r['id']:r['answer_sha256']for r in base})
    return context,ledger


def combined_public_rows(ledger,admission):
    tasks=admission['revised']['_public_tasks']
    source_tasks={r['case_id']:r for r in tasks['views']['strict'][CONDITION]['tasks']}
    originals={r['case_id']:r for r in ledger['rows']if r['series']=='base'and r['phase']=='A1'}
    revisions={r['case_id']:r for r in ledger['rows']if r['series']=='neutral'}
    rows=[]
    for cid in tasks['public_case_ids']:
        base=originals[cid];later=revisions.get(cid)
        base_seconds=base['seconds'];revision_seconds=0 if later is None else later['seconds']
        seconds=None if base_seconds is None or revision_seconds is None else base_seconds+revision_seconds
        require(base['selected_answer']['sha256']==source_tasks[cid]['response_sha256'],
                'Public timing row changed the selected native first answer')
        rows.append(dict(case_id=cid,answer_sha256=base['selected_answer']['sha256'],
            base_seconds=base_seconds,revision_seconds=revision_seconds,seconds=seconds,
            revision_selected=later is not None,
            delivery_status='delivery_failed'if later is not None and later['delivery_status']=='delivery_failed'else base['delivery_status'],
            strict_pass=source_tasks[cid]['strict_pass'],method=METHOD if seconds is not None else None,
            source_reused=False,other_runs=[]))
    return rows


def _coverage(rows):
    known=[r for r in rows if r['seconds']is not None]
    return dict(planned=len(rows),timed=len(known),unknown=len(rows)-len(known),
                observed_wall_seconds=math.fsum(r['seconds']for r in known)if len(known)==len(rows)else None)


def project_public(ledger,admission,private_manifest_sha256,ledger_sha256,extract_sha256,policy_ref):
    from scripts.timing_reference import daily_summary,summarize
    rows=combined_public_rows(ledger,admission)
    sample=ledger['reference_admission']['current_common_sample']
    ids=sample['case_ids'];weights=sample['weights'];by_id={r['case_id']:r for r in rows}
    require(len(ids)==len(set(ids))==12 and set(weights)==set(ids)and set(ids)<=set(by_id)
            and all(type(v)in(int,float)and math.isfinite(v)and v>0 for v in weights.values()),
            'Dot observer clocks cannot shrink or replace the fixed12-task common sample')
    known={cid for cid in ids if by_id[cid]['seconds']is not None}
    require(known==set(sample['known_cases']), 'Shared observed clock coverage differs from the source audit')
    daily=daily_summary([by_id[cid]for cid in ids],weights)
    chapter=summarize([by_id['MG-C003']])
    neutral=[r for r in ledger['rows']if r['series']=='neutral']
    independent=[r for r in ledger['rows']if r['series']=='independent']
    base=[r for r in ledger['rows']if r['series']=='base']
    public_ids=set(by_id)
    public_neutral=[dict(case_id=r['case_id'],answer_sha256=r['selected_answer']['sha256'],seconds=r['seconds'],
        method=r['method'],delivery_status=r['delivery_status'])for r in neutral if r['case_id']in public_ids]
    return dict(schema='math-gauge.dot-native-timings/v1',version=VERSION,model_id=MODEL,record_id='20261125',
        source_admission=admission['selection'],policy=policy_ref,private_admission_sha256=private_manifest_sha256,
        private_ledger_sha256=ledger_sha256,private_extract_sha256=extract_sha256,controller_sha256=CONTROLLER_SHA256,
        method=METHOD,quality=QUALITY,
        public_case_ids=sorted(public_ids),rows=rows,public_neutral_rows=public_neutral,
        public_selfcheck_rows=[dict(id=r['id'],case_id='MG-C003',phase=r['phase'],
            answer_sha256=r['selected_answer']['sha256'],seconds=r['seconds'],method=r['method'],
            delivery_status=r['delivery_status'])for r in base if r['phase']!='A1'],
        independent_rounds=[dict(phase=r['phase'],seconds=r['seconds'],method=r['method'])for r in independent],
        shared_sample=dict(case_ids=deepcopy(ids),weights=deepcopy(weights)),
        summaries=dict(daily=daily,**{'MG-C003':chapter}),
        coverage=dict(base42=_coverage(base),neutral6=_coverage(neutral),independent3=_coverage(independent),all51=_coverage(ledger['rows'])),
        **BOUNDARIES)


def prepare(public_root,private_root,admission_ref,*,timing_root=None):
    manifest=(document(timing_root,dict(admission_ref,path='admission.json'))if timing_root is not None
              else document(private_root,admission_ref))
    context,ledger=validate_private(public_root,private_root,manifest,timing_root=timing_root)
    policy_raw=(Path(public_root)/POLICY_PATH).read_bytes()
    policy_ref=reference(POLICY_PATH,policy_raw)
    value=project_public(ledger,context['admission'],admission_ref['sha256'],manifest['ledger']['sha256'],
                         manifest['extract']['sha256'],policy_ref)
    raw=encoded(value);projection=reference(DIRECTORY+'/timings.json',raw)
    index=dict(schema='math-gauge.dot-native-timing-index/v1',version=VERSION,model_id=MODEL,
        source_admission=context['admission']['selection'],policy=policy_ref,projection=projection,
        private_admission_sha256=admission_ref['sha256'],**BOUNDARIES)
    return {projection['path']:raw,INDEX_PATH:encoded(index)}


def load_public(root):
    root=Path(root)
    from .dot_evidence_timing import INDEX as REPLACEMENT_INDEX, load_public as load_replacement
    if (root/REPLACEMENT_INDEX).is_file():
        return load_replacement(root,load_admission(root))
    if not(root/INDEX_PATH).is_file():return None
    raw=(root/INDEX_PATH).read_bytes();index=json.loads(raw);admission=load_admission(root)
    fixed=dict(schema='math-gauge.dot-native-timing-index/v1',version=VERSION,model_id=MODEL,**BOUNDARIES)
    require(set(index)==set(fixed)|{'source_admission','policy','projection','private_admission_sha256'}
            and all(type(index.get(k))is type(v)and index[k]==v for k,v in fixed.items())
            and admission is not None and index['source_admission']==admission['selection']
            and timings._sha(index['private_admission_sha256']), 'Invalid additive Dot clock source index')
    require(index['policy']==reference(POLICY_PATH,(root/POLICY_PATH).read_bytes())
            and set(index['projection'])=={'path','bytes','sha256'}
            and index['projection']['path']==DIRECTORY+'/timings.json', 'Dot clock source changed its selected policy or aggregate layer')
    report=json.loads(source_bytes(root,index['projection']))
    validate_public(report,admission,index)
    return dict(report=report,source=reference(INDEX_PATH,raw))


def validate_public(report,admission,index):
    from scripts.timing_reference import daily_summary,summarize
    fields={'schema','version','model_id','record_id','source_admission','policy','private_admission_sha256',
        'private_ledger_sha256','private_extract_sha256','controller_sha256','method','quality','public_case_ids','rows',
        'public_neutral_rows','public_selfcheck_rows','independent_rounds','shared_sample','summaries','coverage',*BOUNDARIES}
    require(set(report)==fields and report['schema']=='math-gauge.dot-native-timings/v1'
            and report['model_id']==MODEL and report['version']==VERSION and report['record_id']=='20261125'
            and report['source_admission']==admission['selection']and report['policy']==index['policy']
            and report['private_admission_sha256']==index['private_admission_sha256']
            and all(report[k]==v for k,v in BOUNDARIES.items())
            and report['method']==METHOD and report['quality']==QUALITY and report['controller_sha256']==CONTROLLER_SHA256
            and all(timings._sha(report[k])for k in('private_ledger_sha256','private_extract_sha256')),
            'Unsafe public Dot clock projection or changed runtime/cost boundary')
    selected={r['case_id']:r for r in admission['revised']['_public_tasks']['views']['strict'][CONDITION]['tasks']}
    rows=report['rows'];ids=report['public_case_ids']
    require(len(rows)==len(ids)==len(set(ids))==25 and set(ids)==set(selected)
            and {r['case_id']for r in rows}==set(ids),'Dot public clocks exposed a private or duplicate task')
    row_fields={'case_id','answer_sha256','base_seconds','revision_seconds','seconds','revision_selected',
                'delivery_status','strict_pass','method','source_reused','other_runs'}
    by_id={}
    for row in rows:
        cid=row['case_id']
        require(set(row)==row_fields and row['answer_sha256']==selected[cid]['response_sha256']
                and row['strict_pass']is selected[cid]['strict_pass']
                and row['delivery_status']in timings.DELIVERIES and type(row['revision_selected'])is bool
                and row['source_reused']is False and row['other_runs']==[], 'Public clock row changed its selected mathematical/delivery source')
        for key in('base_seconds','revision_seconds','seconds'):
            require(row[key]is None or timings._seconds(row[key]),'Invalid public observed duration')
        total=None if row['base_seconds']is None or row['revision_seconds']is None else row['base_seconds']+row['revision_seconds']
        require(row['seconds']==total and row['method']==(METHOD if total is not None else None)
                and(row['revision_selected']or row['revision_seconds']==0), 'An adopted but untimed continuation cannot become zero elapsed')
        by_id[cid]=row
    frame=report['shared_sample'];sample=frame['case_ids'];weights=frame['weights']
    require(set(frame)=={'case_ids','weights'}and len(sample)==len(set(sample))==12
            and set(sample)<=set(ids)and set(weights)==set(sample)
            and all(type(v)in(int,float)and math.isfinite(v)and v>0 for v in weights.values())
            and report['summaries']==dict(daily=daily_summary([by_id[c]for c in sample],weights),
                **{'MG-C003':summarize([by_id['MG-C003']])}), 'Dot clock summaries lost the fixed common sample or unknown propagation')
    coverage=report['coverage'];require(set(coverage)=={'base42','neutral6','independent3','all51'},'Public clock coverage contains unsupported source details')
    for key,n in [('base42',42),('neutral6',6),('independent3',3),('all51',51)]:
        value=coverage[key]
        require(set(value)=={'planned','timed','unknown','observed_wall_seconds'}and value['planned']==n
                and all(type(value[k])is int and value[k]>=0 for k in('planned','timed','unknown'))
                and value['timed']+value['unknown']==n
                and(value['observed_wall_seconds']is None if value['unknown']else timings._seconds(value['observed_wall_seconds'])),
                'Partial clock coverage cannot claim a complete total')
    for row in report['public_neutral_rows']:
        require(set(row)=={'case_id','answer_sha256','seconds','method','delivery_status'}and row['case_id']in ids
                and row['seconds']==by_id[row['case_id']]['revision_seconds'], 'Private or mismatched continuation clock in public projection')
    rounds=report['public_selfcheck_rows']
    require(len(rounds)==3 and {r['id']for r in rounds}=={'MG-C003:R1','MG-C003:R2','MG-C003:R3'},
            'Public selfcheck timing rows must retain exactly the three prescribed public rounds')
    for row in rounds:
        require(set(row)=={'id','case_id','phase','answer_sha256','seconds','method','delivery_status'}
                and row['case_id']=='MG-C003'and row['id']=='MG-C003:'+row['phase']
                and timings._sha(row['answer_sha256'])and row['delivery_status']=='delivered'
                and(row['seconds']is None or timings._seconds(row['seconds']))
                and row['method']==(None if row['seconds']is None else METHOD),
                'A public selfcheck clock exposed private evidence or changed its delivery')
    independent=report['independent_rounds']
    require(len(independent)==3 and {r['phase']for r in independent}=={'R1','R2','R3'},
            'Independent-study timing detail keeps three anonymous rounds')
    for row in independent:
        require(set(row)=={'phase','seconds','method'}and(row['seconds']is None or timings._seconds(row['seconds']))
                and row['method']==(None if row['seconds']is None else METHOD),
                'Independent-study clock detail contains unsupported private fields')
    require(_coverage(independent)==coverage['independent3'],
            'Independent-study total differs from its three observed intervals')
    return report


def append_reference(root,reference_data,model):
    """Append after common-sample/cost construction; never recompute the cohort."""
    selected=load_public(root)
    if selected is None:return
    require(reference_data.get('benchmark_version')=='1.2.0'and model['id']==MODEL,
            'Dot clocks append only to the already-computed current timing reference')
    report=selected['report'];frame=report['shared_sample']
    require(reference_data['daily_case_ids']==frame['case_ids']and reference_data['daily_weights']==frame['weights'],
            'Dot clocks cannot shrink or resample the settled common12-task frame')
    require(not any(row['id']==MODEL for row in reference_data['models']),'Dot clock addition cannot replace an existing model row')
    by_id={r['case_id']:r for r in report['rows']}
    cases=[case['id']for case in reference_data['cases']]
    require(cases==[*frame['case_ids'],'MG-C003'],'Timing chart changed its separate chapter/sample selection')
    row=dict(id=MODEL,label=model['label'],record_id='20261125',harness=model['harness_display_name'],
        theme=deepcopy(model['theme']),logo=deepcopy(model['logo']),
        presentation_eligibility=deepcopy(model.get('presentation_eligibility',{})),
        rows=[dict(deepcopy(by_id[cid]),source=deepcopy(selected['source']))for cid in cases],
        summaries=deepcopy(report['summaries']),timing_source=deepcopy(selected['source']))
    if selected.get('chapter_bounds_seconds') is not None:
        row['chapter_bounds_seconds']=deepcopy(selected['chapter_bounds_seconds'])
    reference_data['models'].append(row)
    reference_data.setdefault('additions',[]).append(deepcopy(selected['source']))


def detail_section(root):
    selected=load_public(root)
    if selected is None:return ''
    report=selected['report'];daily=report['summaries']['daily'];chapter=report['summaries']['MG-C003']['median_seconds']
    mt=report['coverage']['independent3']['observed_wall_seconds']
    chapter_text='未知 / unknown'if chapter is None else f'约 {chapter/60:.1f} 分钟 / about {chapter/60:.1f} min'
    bounds=selected.get('chapter_bounds_seconds')
    if chapter is None and bounds:
        upper_minutes = bounds[1] / 60
        chapter_text = f'约 {upper_minutes:.1f} 分钟（上界） / about {upper_minutes:.1f} min (upper bound)'
    mean,median=daily['weighted_mean_seconds'],daily['median_seconds']
    sample_text=('加权均值和中位数未知 / weighted mean and median unknown.'
                if mean is None or median is None else
                f'加权均值 / Weighted mean: {mean/60:.2f} min; 中位数 / Median: {median/60:.2f} min.')
    cost_text=('<p>本轮订阅内额外费用 $0。 / $0 extra for this run under the existing subscription.</p>'
               if selected.get('cost') else '')
    mt_text='未知 / unknown'if mt is None else f'约 {mt/60:.1f} 分钟 / about {mt/60:.1f} min'
    known=''.join(f'<li>{row["case_id"]}: {row["seconds"]/60:.1f} min</li>'for row in report['rows']
                  if row['case_id']in report['shared_sample']['case_ids']and row['seconds']is not None)
    return('<section id="observed-timings"><h2>答题耗时参考 / Observed answer times</h2>'
        f'<p>整章形式化 / Whole chapter: {chapter_text}. '
        f'共有公开题 / Shared public sample: {daily["timed"]}/{daily["planned"]}; '
        f'{sample_text}</p>{cost_text}'
        '<p>协调者记录的开始至完成观察，可能含轮询和等待，并非原生推理时钟。 '
        'Coordinator launch-to-completion observations may include polling and waits; these are not native inference clocks.</p>'
        f'<details><summary>已知样本与独立研究 / Known sample and independent study</summary><ul>{known}</ul>'
        f'<p>独立研究三轮合计 / Three independent-study rounds: {mt_text}. '
        '完整资源总量仍未知 / Full resource totals remain unknown.</p></details>'
        '<p><a href="../../index.html#answer-times">耗时表 / Timing table</a> · '
        '<a href="../../index.html?edition=1.3.0&amp;profile-models=dot-20261125#mathematical-profile">数学画像 / Mathematical profile</a> · '
        '<a href="../../downloads/dot-20261125-timings.json">JSON</a></p></section>')
