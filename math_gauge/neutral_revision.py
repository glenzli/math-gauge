"""Evaluator-only, source-bound adoption of neutral non-Lean continuations.

This owner authenticates retained material and selection. All score arithmetic
is in scoring.py. The original study remains non-scoring and byte unchanged.
"""
from copy import deepcopy
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path

from .benchmarks import identity
from .theorem_extension_calibration import _descriptor, _hash, read, document, require

VERSION = '0.1.0'
SOURCE = '1.1.0'
TARGET = '1.2.0'
CONDITION = 'nonlogical_retry_3'
MODES = ('capability', 'partial', 'strict')
DIRECTORY = 'results/edition-reassessments/v1.2.0'
TRANSITION_PATH = DIRECTORY + '/transition.json'
SOURCE_EDITION_PATH = DIRECTORY + '/source-assessment-edition.json'
POLICY_PATH = 'protocol/neutral-revision.json'
ELIGIBLE = frozenset({'written-argument', 'argument-review', 'theorem-extension',
                      'background-check', 'manuscript-completion'})


def descriptor(root, path):
    path, root = Path(path), Path(root)
    raw = path.read_bytes()
    return dict(path=path.relative_to(root).as_posix(), bytes=len(raw),
                sha256=hashlib.sha256(raw).hexdigest())


def validate_policy(policy):
    fixed = dict(schema='math-gauge.neutral-revision-policy/v1', version=VERSION,
        source_scoring_edition=SOURCE, target_scoring_edition=TARGET,
        baseline_weight=0.8, revision_weight=0.2, attempt_condition=CONDITION,
        selection='any_known_nonfull_nonlean_task', selected_modes=list(MODES),
        full_task_exemption='all_modes_full', allow_signed_decrease=True,
        lean_included=False, weights_changed=False, original_bytes_rewritten=False,
        post_observation=True, reviewer_kind='ai', human_review='pending',
        formal_comparison_eligible=False, adoption_new_candidate_calls=0)
    require(isinstance(policy, dict) and all(type(policy.get(k)) is type(v)
        and policy[k] == v for k, v in fixed.items()), 'Unsupported neutral revision policy')
    return policy


def load_policy(root, ref=None):
    ref = descriptor(root, Path(root) / POLICY_PATH) if ref is None else ref
    require(ref['path'] == POLICY_PATH, 'Neutral revision policy has a noncanonical path')
    policy = validate_policy(document(root, ref))
    for key in ('standards','invitation','protocol'):
        read(root, policy[key])
    return policy


def load_transition(root, edition=None):
    root = Path(root)
    edition = json.loads((root / 'benchmark.json').read_bytes()) if edition is None else edition
    if edition.get('version') != TARGET:
        require('neutral_revision_transition' not in edition,
                'Neutral revision transition belongs only to edition 1.2.0')
        return None
    transition = document(root, edition.get('neutral_revision_transition'))
    fixed = dict(schema='math-gauge.neutral-revision-transition/v1', version=VERSION,
        source_scoring_edition=SOURCE, target_scoring_edition=TARGET, task_suite_version='1.0.0',
        attempt_condition=CONDITION, post_observation=True, adoption_new_candidate_calls=0,
        original_bytes_rewritten=False, human_review='pending', formal_comparison_eligible=False)
    fields = set(fixed) | {'source_edition', 'policy', 'adoptions', 'pending_models'}
    require(isinstance(transition, dict) and set(transition) in
        (fields, fields | {'withdrawn_models'}) and all(
        type(transition.get(k)) is type(v) and transition[k] == v for k,v in fixed.items()),
        'Invalid neutral revision edition transition')
    require(edition['neutral_revision_transition']['path'] == TRANSITION_PATH,
            'Neutral revision transition has a noncanonical path')
    source = document(root, transition['source_edition'])
    require(transition['source_edition']['path'] == SOURCE_EDITION_PATH
            and source.get('version') == SOURCE and source.get('status') == 'local-assessment-candidate',
            'Neutral revision needs its unchanged 1.1 source edition')
    excluded = {'version', 'status', 'source_state', 'neutral_revision_transition'}
    require({k:v for k,v in edition.items() if k not in excluded}
            == {k:v for k,v in source.items() if k not in excluded},
            'Neutral revision changed the retained source selection or contracts')
    load_policy(root, transition['policy'])
    adoptions, pending, withdrawn = (transition['adoptions'], transition['pending_models'],
                                      transition.get('withdrawn_models', []))
    require(isinstance(adoptions, dict) and all(isinstance(mid, str) for mid in adoptions)
            and all(isinstance(group, list) and all(isinstance(mid, str) for mid in group)
                    and len(group) == len(set(group)) for group in (pending, withdrawn)),
            'Neutral revision needs explicit unique model identities')
    adopted_ids, pending_ids, withdrawn_ids = set(adoptions), set(pending), set(withdrawn)
    from .editions import NATIVE_MODEL
    retained_ids = (set(source['selected_result_models'])
                    | set(source.get('current_assessment_admissions', {})) | {NATIVE_MODEL})
    require(not (adopted_ids & pending_ids or adopted_ids & withdrawn_ids or pending_ids & withdrawn_ids)
            and adopted_ids | pending_ids | withdrawn_ids == retained_ids,
            'Neutral revision adopted, pending and withdrawn models must partition the retained source cohort')
    for mid, ref in adoptions.items():
        _descriptor(ref)
        require(ref['path'].startswith(DIRECTORY + '/' + mid + '/')
                and ref['path'].endswith('/public.json'), 'Unsafe neutral revision adoption path')
    return dict(transition, _source_edition=source)


def current_model_ids(transition):
    '''Return the explicitly selected target-edition cohort, independent of scores.'''
    require(transition is not None, 'Current revision models require a selected neutral transition')
    return frozenset(transition['adoptions']) | frozenset(transition['pending_models'])


def source_assessment_edition(root, edition=None):
    edition = json.loads((Path(root) / 'benchmark.json').read_bytes()) if edition is None else edition
    transition = load_transition(root, edition)
    return edition if transition is None else transition['_source_edition']


def select_revision_tasks(reports, *, model_id=None):
    """Select whole tasks by known loss in any mode; unknown is never a loss.

    This mapping is evaluator-side. A candidate projection must exclude scores,
    loss_modes, external reviews and all private source metadata.
    """
    require(isinstance(reports, dict) and set(reports) == set(MODES),
            'Neutral selection requires the same three source score modes')
    indexed = {}
    for mode in MODES:
        report = reports[mode]
        require(report.get('attempt_condition') == CONDITION and report.get('score_mode') == mode
                and isinstance(report.get('tasks'), list),
                'Neutral selection needs complete rule-selected source task reports')
        indexed[mode] = {row['case_id']:row for row in report['tasks']}
        require(len(indexed[mode]) == len(report['tasks']), 'Duplicate source task in neutral selection')
    require(all(set(indexed[mode]) == set(indexed['partial']) for mode in MODES),
            'Neutral selection cannot combine different source task populations')
    result = []
    for cid, task in sorted(indexed['partial'].items()):
        if task['subcategory'] not in ELIGIBLE:
            continue
        rows = {mode:indexed[mode][cid] for mode in MODES}
        require(all(all(rows[mode].get(key) == task.get(key) for key in
            ('case_id','family_id','subcategory','response_sha256')) for mode in MODES),
            'Neutral continuation must use one source answer for all score modes')
        values = {mode:(int(rows[mode]['strict_pass']) if rows[mode]['strict_pass'] is not None else None)
                  if mode == 'strict' else rows[mode]['completion']['exact'] for mode in MODES}
        loss = [mode for mode in MODES if values[mode] is not None and values[mode] < 1]
        if not loss:
            continue
        result.append(dict(model_id=model_id, case_id=cid, family_id=task['family_id'],
            subcategory=task['subcategory'], response_sha256=task.get('response_sha256'),
            review_sha256=task.get('review_sha256'), loss_modes=loss, first_scores=values,
            original_submission_status=(task.get('submission_assessment') or {}).get('classification'),
            original_answer_attachments=[]))
    return result


def _root_ref(folder, item):
    return None if item is None else dict(_descriptor(item), path=(folder / item['path']).as_posix())


def _walk_descriptors(value):
    if isinstance(value, dict):
        if {'path','bytes','sha256'} <= set(value) and _hash(value.get('sha256')):
            yield {k:value[k] for k in ('path','bytes','sha256')}
        for child in value.values():
            yield from _walk_descriptors(child)
    elif isinstance(value, list):
        for child in value:
            yield from _walk_descriptors(child)


def _artifact_bound(value, *, name, sha256):
    if isinstance(value, dict):
        path = value.get('path', value.get('filename', value.get('original_relative_path')))
        if isinstance(path, str) and Path(path).name == name and value.get('sha256') == sha256:
            return True
        return any(_artifact_bound(child,name=name,sha256=sha256) for child in value.values())
    if isinstance(value,list):
        return any(_artifact_bound(child,name=name,sha256=sha256) for child in value)
    return False


def _source_report_refs(public_root, private_root, model_id):
    """Use the retained 1.1 manifests, never display-rounded score readouts."""
    from .editions import load_assessment_transition
    source = source_assessment_edition(public_root)
    initial = source.get('current_assessment_admissions', {}).get(model_id)
    ref = initial or load_assessment_transition(public_root, source)['calibrations'].get(model_id)
    require(ref is not None, 'No selected 1.1 assessment for neutral continuation')
    public = document(public_root, ref)
    private_ref = descriptor(private_root, Path(private_root) / ref['path'])
    require(private_ref['sha256'] == public['private_manifest_sha256'],
            'Neutral source private manifest differs from its public binding')
    private = document(private_root, private_ref)
    return public, private, ref


def load_model_selection(public_root, private_root, model_id):
    """Load trusted current score rows and reconstruct candidate-safe source pointers."""
    from .catalog import Suite
    public_root, private_root = Path(public_root).resolve(), Path(private_root).resolve()
    public, private, public_ref = _source_report_refs(public_root, private_root, model_id)
    refs = {mode:private['scores'][mode][CONDITION] for mode in MODES}
    reports = {mode:document(private_root, refs[mode]) for mode in MODES}
    for mode in MODES:
        projected = document(public_root, public['scores'][mode][CONDITION])
        require(projected['source_bindings']['private_report_sha256'] == refs[mode]['sha256'],
                'Neutral continuation source report is not the adopted private report')
    source_record = public.get('source_record', public.get('record'))
    original_record = document(private_root, descriptor(private_root, private_root / source_record['path']))
    folder = Path(source_record['path']).parent
    descriptors = list(_walk_descriptors(original_record))
    components = []
    for field in ('theorem_extension_inputs','background_check_inputs','manuscript_completion_inputs',
                  'written_argument_inputs','written_replacement_inputs','submission_evidence','claim_review',
                  'mathematical_input','mathematical_inputs'):
        item = original_record.get(field)
        if item is not None:
            component = document(private_root / folder, item)
            components.append(component)
            descriptors.extend(_walk_descriptors(component))
    for item in original_record.get('evidence', []):
        if 'source-index' in item.get('path',''):
            descriptors.extend(_walk_descriptors(document(private_root / folder, item)))
    suites = [(scope, Suite.load(root / 'cases')) for scope,root in
              (('public',public_root),('private',private_root))]
    selected = select_revision_tasks(reports, model_id=model_id)
    for row in selected:
        cid = row['case_id']
        scope, suite = next((scope,suite) for scope,suite in suites if cid in suite.cases)
        task = suite.cases[cid]
        task_path = suite.case_file(task, task['task'])
        task_root = public_root if scope == 'public' else private_root
        row['source_case'] = dict(scope=scope, **descriptor(task_root, task_path))
        candidates = [item for item in descriptors if item['sha256'] == row['response_sha256']]
        row['original_answer'] = None
        for item in candidates:
            try:
                ref = _root_ref(folder, item)
                read(private_root, ref)
                row['original_answer'] = dict(scope='private', **ref)
                break
            except (ValueError, FileNotFoundError):
                continue
        record_rows = [r for r in original_record.get('records', []) if r.get('case_id') == cid]
        raw_review = next((r.get('review') for r in record_rows if r.get('review')), None)
        row['original_review'] = None if raw_review is None else dict(scope='private',
            **_root_ref(folder, raw_review))
        if row['original_review'] is not None:
            read(private_root, {k:row['original_review'][k] for k in ('path','bytes','sha256')})
        for component in components:
            for source in component.get('slots', []):
                manuscript = source.get('manuscript')
                if (source.get('case_id') == cid and manuscript is not None
                        and (source.get('response') or {}).get('sha256') == row['response_sha256']
                        and row['original_answer'] is not None):
                    raw = read(private_root, {k:row['original_answer'][k] for k in ('path','bytes','sha256')})
                    if Path(manuscript['path']).name.encode() in raw:
                        ref = _root_ref(folder, manuscript)
                        read(private_root, ref)
                        row['original_answer_attachments'].append(dict(scope='private', **ref))
        row['source_record'] = dict(scope='private', **descriptor(private_root,
            private_root / source_record['path']))
        submissions = next((component.get('conditions',{}).get(CONDITION) for component in components
            if component.get('schema') == 'math-gauge.submission-source-index/v1'
            or component.get('conditions',{}).get(CONDITION,{}).get('schema') == 'math-gauge.submission-evidence/v1'),None)
        if submissions is not None:
            submitted = next((r for r in submissions.get('initials',[]) if r['case_id']==cid),None)
            if submitted is not None:
                row['original_failure_evidence'] = [dict(scope='private',**_root_ref(folder,
                    {key:item[key] for key in ('path','bytes','sha256')}))
                    for item in submitted.get('evidence',[])]
                if submitted.get('classification') == 'forced_content' and submitted.get('work_review'):
                    review_ref = _root_ref(folder,submitted['work_review'])
                    work = document(private_root,review_ref)
                    work_sources = work.get('original_work_sources',[])
                    if work.get('original_work') is not None:
                        work_sources = [work['original_work'],*[r for r in work.get('evidence',[])
                            if str(r.get('path','')).endswith('.lean')]]
                    retained = []
                    for item in work_sources:
                        candidate = _root_ref(folder,item)
                        read(private_root,candidate)
                        retained.append(dict(scope='private',**candidate))
                    if retained:
                        row['original_answer'] = retained[0]
                        row['original_answer_attachments'] = retained[1:]
                        row['original_answer_kind'] = 'selected_cutoff_original_work'
                        row['original_review'] = dict(scope='private',**review_ref)
        row['completed_adoption'] = None
    transition = load_transition(public_root)
    adopted = None if transition is None else transition['adoptions'].get(model_id)
    if adopted is not None:
        for row in selected:
            row['completed_adoption'] = adopted
    return dict(model_id=model_id, record_id=folder.name, source_record=source_record,
        base_reports=refs, reports=reports, selection=selected, source_manifest=public_ref,
        public_base_reports=public['scores'])


@dataclass(frozen=True)
class RevisionInputs:
    _payload: bytes

    def for_score(self, base, *, mode):
        data = json.loads(self._payload)
        require(mode in MODES and base.get('score_mode') == mode
                and base.get('attempt_condition') == CONDITION
                and identity(base) == data['base_identities'][mode],
                'Neutral continuation lost the exact mode/condition/source report')
        return data


def _interval_shape(value):
    require(isinstance(value, dict) and set(value) == {'lower','upper','exact'}
            and all(v is None or type(v) in {int,float} and -1 <= v <= 1 for v in value.values())
            and value['lower'] is not None and value['upper'] is not None
            and value['lower'] <= value['upper'] and (value['exact'] is None
                or value['lower'] == value['upper'] == value['exact']),
            'Invalid signed neutral score interval')
    return value


def load_inputs(root, ref, *, public_root, base_reports):
    """Authenticate additive adoption; source reviews remain immutable evidence."""
    data = document(root, ref)
    fixed = dict(schema='math-gauge.neutral-revision-inputs/v1', version=VERSION,
        benchmark_version=TARGET, source_scoring_edition=SOURCE, attempt_condition=CONDITION,
        post_observation=True, original_bytes_rewritten=False, reviewer_kind='ai',
        human_review='pending', formal_comparison_eligible=False, adoption_new_candidate_calls=0)
    require(isinstance(data, dict) and set(data) == set(fixed) | {'model_id','record_id',
        'model_label','source_record','policy','base_reports','rows','study_sources'}
        and all(type(data.get(k)) is type(v) and data[k] == v for k,v in fixed.items()),
        'Invalid neutral revision adoption input contract')
    load_policy(public_root, data['policy'])
    source_record = document(root, data['source_record'])
    from .native_assessment_sources import (SCHEMA as NATIVE_INITIAL, NEUTRAL_BRIDGE_SCHEMA,
        validate_neutral_parent_bridge, record_relative_reference)
    first_source = source_record.get('first_assessment_source')
    native_initial = (first_source is not None and document(root,
        record_relative_reference(data['source_record'], first_source)).get('schema') == NATIVE_INITIAL)
    require(set(base_reports) == set(MODES) and set(data['base_reports']) == set(MODES),
            'Neutral adoption requires all three source reports')
    for mode in MODES:
        require(document(root, data['base_reports'][mode]) == base_reports[mode],
                'Neutral adoption replaced its 1.1 baseline report')
    selected = select_revision_tasks(base_reports, model_id=data['model_id'])
    rows = data['rows']
    require(isinstance(rows, list) and [r.get('case_id') for r in rows] ==
        [r['case_id'] for r in selected], 'Neutral adoption must retain every and only selected loss task')
    for item in data['study_sources']:
        read(root, item)
    normalized = []
    for row, first in zip(rows, selected):
        require(row.get('first_response_sha256') == first['response_sha256']
                and row.get('first_review_sha256') == first['review_sha256']
                and row.get('family_id') == first['family_id']
                and row.get('subcategory') == first['subcategory'],
                'Neutral continuation changed its first answer/review/family')
        for field in ('original_task','original_answer','original_review','source_component'):
            item = row.get(field)
            if item is not None:
                source_root = public_root if item.get('scope') == 'public' else root
                read(source_root, {k:item[k] for k in ('path','bytes','sha256')})
        if row.get('original_answer') is not None:
            require(row['original_answer']['sha256'] == first['response_sha256'],
                    'Neutral continuation original answer has different bytes')
        if native_initial:
            component = row.get('source_component')
            require(component is not None and component.get('scope') == 'private',
                    'Native initial neutral adoption needs its explicit frozen-parent source bridge')
            bridge = document(root, {k:component[k] for k in ('path','bytes','sha256')})
            require(bridge.get('schema') == NEUTRAL_BRIDGE_SCHEMA,
                    'Native initial neutral adoption cannot merely read an unvalidated parent note')
            validate_neutral_parent_bridge(bridge, read=lambda item:read(root,item),
                record_ref=data['source_record'], record=source_record, first=first, adoption_row=row)
        continuation = row['continuation']
        require(continuation.get('status') in {'reviewed','delivery_failed','not_run'},
                'Unknown continuation status must not masquerade as delivery failure')
        scores = continuation.get('scores')
        source_documents = []
        for item in continuation.get('sources', []):
            raw = read(root, item)
            if item['path'].endswith('.json'):
                source_documents.append(json.loads(raw))
        if continuation['status'] == 'reviewed':
            answer = read(root, continuation['answer'])
            read(root, continuation['input'])
            review = document(root, continuation['review'])
            require(review.get('response_sha256') == continuation['answer']['sha256']
                    and review.get('human_review') == 'pending',
                    'Neutral continuation judgment does not bind the exact delivered answer')
            if 'MC' in review:
                expected = dict(capability=review['MC']/100, partial=review['RMC']/100,
                                strict=int(review['SMC']))
                require(review.get('mathematical_verdict_finalized') is True,
                        'Unfinalized study review cannot become a selected score')
            else:
                require(review.get('arm') == 'neutral' and review.get('baseline_B') == 2
                        and review.get('research_R') == 3 and review.get('strict_mathematics') is True
                        and not review.get('claims'), 'Reused pilot is not the verified neutral full result')
                expected = dict.fromkeys(MODES, 1)
            require(scores == expected and type(scores['strict']) is int and scores['strict'] in {0,1},
                    'Neutral adoption changed its original mathematical review')
            for attachment in continuation.get('attachments', []):
                read(root, attachment)
            native = document(root, continuation['collection'])
            require(native.get('normal_final_delivered') is True
                    and native.get('response_sha256') == continuation['answer']['sha256'],
                    'Neutral continuation lacks its actual normal-final evidence')
            for attachment in continuation.get('attachments', []):
                require(any(_artifact_bound(item,name=Path(attachment['path']).name,
                    sha256=attachment['sha256']) for item in [native,*source_documents]),
                    'Delivered attachment is not bound to the actual terminal/cutoff evidence')
            require(answer, 'A normal continuation delivery cannot be empty')
        else:
            require(scores is None, 'Missing continuation cannot receive invented mathematical scores')
            if continuation['status'] == 'delivery_failed':
                failure = document(root, continuation['failure_evidence'])
                require(failure.get('normal_final_delivered') is False,
                        'Known continuation delivery failure needs native evidence')
                cutoff = continuation.get('cutoff_review')
                if cutoff is not None:
                    review = document(root, cutoff)
                    require(review.get('schema') == 'math-gauge.neutral-revision-cutoff-review/v1'
                            and review.get('case_id') == row['case_id']
                            and review.get('failure_evidence_sha256') == continuation['failure_evidence']['sha256']
                            and review.get('reviewer_kind') == 'ai' and review.get('human_review') == 'pending'
                            and review.get('original_work_unmodified') is True
                            and review.get('no_normal_final') is True
                            and review.get('no_cross_attempt_union') is True,
                            'Cutoff MC needs a separate source-bound original-work review')
                    content = continuation.get('cutoff_content')
                    if content is not None:
                        read(root, content)
                        require(review.get('content_sha256') == content['sha256'],
                                'Cutoff MC review binds different original content')
                    else:
                        require(review.get('content_sha256') is None and review.get('no_content') is True
                                and review.get('capability_completion') == dict(lower=0,upper=0,exact=0),
                                'No-content cutoff zero needs its explicit verified judgment')
                    _interval_shape(review.get('capability_completion'))
                    continuation['cutoff_capability'] = review['capability_completion']
                else:
                    continuation['cutoff_capability'] = None
        normalized.append(deepcopy(row))
    payload = dict(model_id=data['model_id'], record_id=data['record_id'], model_label=data['model_label'],
        rows=normalized, base_identities={mode:identity(base_reports[mode]) for mode in MODES},
        base_sha256={mode:data['base_reports'][mode]['sha256'] for mode in MODES},
        inputs_sha256=ref['sha256'], policy_sha256=data['policy']['sha256'])
    return RevisionInputs(json.dumps(payload, ensure_ascii=False, sort_keys=True,
        separators=(',',':')).encode())


def project_score(score):
    from .records import project_assessment_score
    result = project_assessment_score(score)
    result['neutral_revision'] = deepcopy(score['neutral_revision'])
    return result


def project_public_tasks(scores, public_ids, private_hashes):
    from .records import project_public_task_view
    result = dict(schema='math-gauge.neutral-revision-public-tasks/v1', version=VERSION,
        benchmark_version=TARGET, model_label=scores['partial']['model_label'],
        public_case_ids=sorted(public_ids), views={})
    for mode in MODES:
        view = project_public_task_view(scores[mode], public_ids, private_hashes[mode])
        full = {r['case_id']:r for r in scores[mode]['tasks']}
        for row in view['tasks']:
            if 'neutral_revision' in full[row['case_id']]:
                row['neutral_revision'] = deepcopy(full[row['case_id']]['neutral_revision'])
        result['views'][mode] = {CONDITION:view}
    return result


def load_public(root, ref, *, base_scores=None):
    """Read anonymous aggregate scores plus the explicitly public task projection."""
    data = document(root, ref)
    fixed = dict(schema='math-gauge.neutral-revision-public/v1', version=VERSION,
        benchmark_version=TARGET, source_scoring_edition=SOURCE, attempt_condition=CONDITION,
        post_observation=True, reviewer_kind='ai', human_review='pending',
        formal_comparison_eligible=False, adoption_new_candidate_calls=0)
    fields = set(fixed) | {'model_id','record_id','source_record','policy','base_reports','scores',
        'public_tasks','public_continuations','private_inputs_sha256','private_manifest_sha256','revision_counts'}
    require(isinstance(data, dict) and fields <= set(data) <= fields | {'revision_resources'}
            and all(type(data.get(k)) is type(v) and data[k] == v for k,v in fixed.items()),
            'Invalid neutral revision public privacy contract')
    load_policy(root, data['policy'])
    read(root, data['source_record'])
    require(all(_hash(data[k]) for k in ('private_inputs_sha256','private_manifest_sha256'))
            and set(data['scores']) == set(MODES), 'Neutral public score needs opaque private bindings')
    scores = {}
    for mode in MODES:
        old = {condition:document(root, item) for condition,item in data['base_reports'][mode].items()}
        require(set(old) == {'single_attempt',CONDITION}, 'Neutral adoption retains both original condition views')
        if base_scores is not None:
            require(old == base_scores[mode], 'Neutral public adoption substituted its current 1.1 source')
        score = document(root, data['scores'][mode])
        metadata = score.get('neutral_revision', {})
        require(score.get('schema') == 'math-gauge.assessment-score-aggregate/v1'
                and score.get('benchmark_version') == TARGET and score.get('score_mode') == mode
                and score.get('attempt_condition') == CONDITION and metadata.get('version') == VERSION
                and metadata.get('source_scoring_edition') == SOURCE
                and metadata.get('inputs_sha256') == data['private_inputs_sha256']
                and metadata.get('policy_sha256') == data['policy']['sha256']
                and metadata.get('base_report_sha256') == old[CONDITION]['source_bindings']['private_report_sha256']
                and score.get('whole_task_counts') == old[CONDITION].get('whole_task_counts')
                and not {'tasks','rows','selection','continuations'}.intersection(score),
                'Neutral public score lost its exact baseline or private arithmetic binding')
        for field in ('metrics','contributions'):
            for child in ('lean-audit','lean-formalization','lean-selfcheck','lean'):
                require(score[field].get(child) == old[CONDITION][field].get(child),
                        'Neutral continuation changed a Lean score')
        scores[mode] = score
    tasks = document(root, data['public_tasks'])
    from .theorem_extension_calibration import _public_case_ids
    ids = _public_case_ids(root, None)
    require(tasks.get('schema') == 'math-gauge.neutral-revision-public-tasks/v1'
            and tasks.get('benchmark_version') == TARGET and tasks.get('public_case_ids') == ids
            and set(tasks.get('views', {})) == set(MODES), 'Invalid neutral public task projection')
    for mode in MODES:
        require(set(tasks['views'][mode]) == {CONDITION}, 'Continuation cannot migrate to another source condition')
        view = tasks['views'][mode][CONDITION]
        require(view['source_report_sha256'] == scores[mode]['source_bindings']['private_report_sha256']
                and [row.get('case_id') for row in view['tasks']] == ids,
                'Neutral public task rows lost their private report binding')
        for row in view['tasks']:
            require(set(row) <= {'case_id','completion','strict_pass','response_sha256','review_sha256','neutral_revision'},
                    'Private task evidence leaked into neutral public projection')
            _interval_shape(row['completion'])
    require(isinstance(data['public_continuations'], list)
            and all(row.get('case_id') in ids and set(row) == {'case_id','answer','review','input','attachments'}
                    for row in data['public_continuations']), 'Only public continuation evidence may be published')
    for row in data['public_continuations']:
        for field in ('answer','review','input'):
            read(root, row[field])
        for item in row['attachments']:
            read(root, item)
    if 'revision_resources' in data:
        read(root, data['revision_resources'])
    return dict(data, _selection=ref, _scores=scores, _public_tasks=tasks)


def verify_pair(public_root, private_root, public_ref, private_ref, *, base_reports, assessment_policy):
    from .scoring import score_neutral_revision_overlay
    public = load_public(public_root, public_ref)
    private = document(private_root, private_ref)
    require(private_ref['sha256'] == public['private_manifest_sha256']
            and private['inputs']['sha256'] == public['private_inputs_sha256']
            and private.get('model_id') == public['model_id'], 'Neutral adoption public/private manifests differ')
    inputs = load_inputs(private_root, private['inputs'], public_root=public_root, base_reports=base_reports)
    scores = {}
    for mode in MODES:
        expected = score_neutral_revision_overlay(base_reports[mode], assessment_policy,
                                                   revision=inputs, mode=mode)
        actual = document(private_root, private['scores'][mode])
        require(actual == expected, 'Neutral revision report differs from shared scorer')
        projected = project_score(actual)
        projected['source_bindings']['private_report_sha256'] = private['scores'][mode]['sha256']
        require(public['_scores'][mode] == projected, 'Neutral public aggregate differs from private scorer')
        scores[mode] = actual
    require(public['_public_tasks'] == project_public_tasks(scores,
        public['_public_tasks']['public_case_ids'], {m:private['scores'][m]['sha256'] for m in MODES}),
        'Neutral public task projection differs from private scorer')
    return dict(public=public, private=private, inputs=inputs, scores=scores)
