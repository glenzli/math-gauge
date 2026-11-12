"""Source-bound submission classes and nonfinal work; arithmetic stays in scoring.py.

An active final, an operator-collected work artifact and a provisional blank are
different observations. This module never turns retained work into a native
response and never executes candidate code or scripts.
"""
import hashlib
import json
import re
from fractions import Fraction
from pathlib import Path
from .evidence_retention import read_bytes as retained_bytes

VERSION = '0.1.0'
POLICY_SCHEMA = 'math-gauge.submission-scoring-policy/v1'
REVIEW_SCHEMA = 'math-gauge.submission-evidence/v1'
WORK_SCHEMA = 'math-gauge.nonfinal-work-review/v1'
NORMAL_SCHEMA = 'math-gauge.normal-final-math-review/v1'
CONDITIONS = ('single_attempt', 'nonlogical_retry_3')
CLASSES = {'active_final', 'forced_content', 'blank', 'not_run'}


def validate_descriptor(item):
    require(isinstance(item, dict) and {'path', 'bytes', 'sha256'} <= set(item),
            'Evidence needs a retained byte descriptor')
    path = item['path']
    require(isinstance(path, str) and path and not Path(path).is_absolute()
            and all(part not in {'.', '..'} for part in Path(path).parts)
            and type(item['bytes']) is int and item['bytes'] >= 0
            and isinstance(item['sha256'], str)
            and re.fullmatch(r'[0-9a-f]{64}', item['sha256']),
            'Invalid retained evidence descriptor')
    return item


def load_review_completion(folder, record):
    """Read a later source-recovery receipt without rewriting frozen judgments."""
    folder = Path(folder)
    path = folder / 'review-completion.json'
    if not path.is_file():
        return None
    data = json.loads(path.read_bytes())
    fields = {'schema', 'version', 'model_id', 'record_id', 'record', 'submission_evidence',
              'status', 'scope', 'reviewed_at', 'initial_tasks_reviewed',
              'resolved_public_cases', 'resolved_private_count', 'resolved_pending_count',
              'unexecuted_selfcheck_rounds', 'private_review_sha256', 'reviewer_kind',
              'human_review', 'scores_modified', 'new_candidate_calls'}
    require(set(data) == fields and data['schema'] == 'math-gauge.source-review-completion/v1'
            and data['version'] == '0.1.0' and data['status'] == 'complete'
            and data['scope'] == 'retained_initial_answers_and_source_recovery'
            and data['reviewer_kind'] == 'ai' and data['human_review'] == 'pending'
            and data['scores_modified'] is False and data['new_candidate_calls'] == 0,
            'Invalid source-review completion receipt')
    require(data['model_id'] == folder.parent.name and data['record_id'] == folder.name
            and json.loads(_read(folder, data['record'])) == record
            and data['record']['path'] == 'record.json'
            and data['submission_evidence'] == record['submission_evidence'],
            'Source-review completion binds another retained record')
    require(isinstance(data['private_review_sha256'], str)
            and re.fullmatch(r'[0-9a-f]{64}', data['private_review_sha256']),
            'Source-review completion lost its private evidence')
    archive = json.loads(_read(folder, data['submission_evidence']))
    current = archive['conditions']['nonlogical_retry_3']
    resolved = {r['case_id'] for r in current['public_initials'] if r['pending_original_record_review']}
    require(data['resolved_public_cases'] == sorted(resolved)
            and data['resolved_private_count'] == current['private_pending_original_record_review']
            and data['resolved_pending_count'] == len(resolved) + data['resolved_private_count']
            == current['summary']['pending_original_record_review']
            and data['initial_tasks_reviewed'] == current['summary']['planned'] == 39
            and current['summary']['pending'] == 0,
            'Source-review completion changed the fixed review population')
    require(data['unexecuted_selfcheck_rounds'] == [1, 2, 3]
            and record['execution_summary']['blocked_selfcheck_rounds'] == 3
            and record['execution_summary']['delivered_selfcheck_rounds'] == 0,
            'Source review cannot invent selfcheck delivery')
    return data


def _evidence(items):
    require(isinstance(items, list) and items, 'Original byte evidence is required')
    for item in items:
        validate_descriptor(item)


def require(value, message):
    if not value:
        raise ValueError(message)


def validate_policy(policy):
    expected = dict(schema=POLICY_SCHEMA, version=VERSION, benchmark_version='0.6.0',
        assessment_method_version='0.9.0', capability_method_version='0.3.0',
        active_final_scores='existing_mathematical_review', nonfinal_rmc=0,
        nonfinal_smc=0, nonfinal_mc='verified_positive_work_only',
        attempt_selection='first_normal_final_else_fixed_last_effective_attempt',
        best_of=False, cross_attempt_union=False, numerical_scripts_are_proofs=False,
        hidden_reasoning_is_answer=False, forced_content_requires_positive_score=False,
        active_and_forced_counts_mutually_exclusive=True, missing_records_provisional_zero=True,
        new_candidate_calls=0)
    require(isinstance(policy, dict) and all(policy.get(k) == v for k, v in expected.items()),
            'Unsupported active-submission and nonfinal-work scoring policy')
    return policy


def _number(value):
    require(type(value) in (int, float), 'Work credit must be a finite number')
    try:
        return Fraction(str(value))
    except (ValueError, ZeroDivisionError) as error:
        raise ValueError('Work credit must be finite') from error


def validate_work(review, case, condition):
    require(isinstance(review, dict) and review.get('schema') == WORK_SCHEMA
            and review.get('version') == VERSION and review.get('case_id') == case['case_id']
            and review.get('phase') == 'A1' and review.get('attempt_condition') == condition
            and review.get('reviewer_kind') == 'ai' and review.get('source_repaired') is False
            and review.get('new_candidate_calls') == 0 and review.get('candidate_scripts_executed') is False
            and review.get('selection') == 'fixed_last_effective_attempt_within_condition'
            and review.get('deadline_existence_verified') is True,
            'Nonfinal capability credit needs the fixed, deadline-bound original work review')
    return _validate_credit_units(review,case)


def _validate_credit_units(review, case):
    expected_hash = case.get('contract_sha256', case.get('group_contract_sha256'))
    require(isinstance(expected_hash,str) and re.fullmatch(r'[0-9a-f]{64}',expected_hash)
            and review.get('case_contract_sha256') == expected_hash,
            'Work review changed the frozen mathematical contract')
    definitions = case.get('criteria') or case.get('stages')
    require(isinstance(definitions, list) and definitions, 'Work needs frozen criterion or obligation units')
    maxima = {r.get('criterion_id', r.get('stage_id', r.get('id'))):
              _number(r.get('points', r.get('weight', 1))) for r in definitions}
    rows = review.get('credit_units')
    require(isinstance(rows, list) and len(rows) == len(maxima)
            and {r.get('id') for r in rows} == set(maxima),
            'Work review must retain every original credit unit exactly once')
    for row in rows:
        require(_number(row.get('maximum')) == maxima[row['id']]
                and 0 <= _number(row.get('earned')) <= maxima[row['id']]
                and isinstance(row.get('reason'), str) and row['reason'].strip(),
                'Nonfinal work credit exceeds or changes its original unit')
        if case.get('stages'):
            require(row['earned'] in (0, row['maximum']),
                    'Formalization obligations keep their original binary unit judgments')
    _evidence(review.get('evidence'))
    return review


def validate_normal_math(review, case, condition, response_sha256):
    require(isinstance(review,dict) and review.get('schema')==NORMAL_SCHEMA
            and review.get('source_response_sha256')==response_sha256
            and response_sha256 is not None and type(review.get('complete')) is bool
            and case.get('component')=='lean-formalization'
            and review.get('version')==VERSION and review.get('case_id')==case['case_id']
            and review.get('phase')=='A1' and review.get('attempt_condition')==condition
            and review.get('reviewer_kind')=='ai' and review.get('source_repaired') is False
            and review.get('new_candidate_calls')==0 and review.get('candidate_scripts_executed') is False
            and review.get('original_final_existence_verified') is True,
            'Normal mathematics must belong to the selected actual final')
    # Historical normal finals do not acquire an invented deadline receipt.
    _validate_credit_units(review,case)
    require(not review['complete'] or all(u['earned']==u['maximum'] for u in review['credit_units']),
            'Normal whole-task completion contradicts its fixed obligation review')
    return review


def validate_condition(data, *, model_label=None, case_ids=None, response_hashes=None):
    require(isinstance(data, dict) and data.get('schema') == REVIEW_SCHEMA
            and data.get('version') == VERSION and data.get('attempt_condition') in CONDITIONS
            and (model_label is None or data.get('model_label') == model_label),
            'Submission evidence belongs to a different model or attempt condition')
    rows = data.get('initials')
    require(isinstance(rows, list) and len({r.get('case_id') for r in rows}) == len(rows),
            'Submission evidence repeats an initial task')
    if case_ids is not None:
        require({r.get('case_id') for r in rows} == set(case_ids),
                'Submission evidence changed the fixed task population')
    for row in rows:
        classification = row.get('classification')
        require(classification in CLASSES and isinstance(row.get('reason'), str) and row['reason'].strip(),
                'Each submission needs an explicit, explained class')
        _evidence(row.get('evidence'))
        if response_hashes is not None:
            require(row.get('source_response_sha256') == response_hashes.get(row['case_id']),
                    'Submission class binds a different selected original response')
        if classification == 'active_final':
            require(isinstance(row.get('source_response_sha256'), str)
                    and re.fullmatch(r'[0-9a-f]{64}', row['source_response_sha256'])
                    and row.get('work_review') is None,
                    'Active final cannot be manufactured from work artifacts')
        if row.get('normal_review') is not None:
            validate_descriptor(row['normal_review'])
            require(classification=='active_final', 'A normal review cannot relabel a failed delivery')
        if row.get('normal_math') is not None:
            require(classification=='active_final' and row.get('normal_review') is not None,
                    'Normal mathematics requires its retained original review descriptor')
        if row.get('work_review') is not None:
            validate_descriptor(row['work_review'])
            require(classification == 'forced_content'
                    and row.get('mathematical_source') == 'nonfinal_work',
                    'Work credit is exclusive of the retained final/body scoring source')
        if row.get('work') is not None:
            require(classification=='forced_content' and row.get('work_review') is not None
                    and row.get('mathematical_source')=='nonfinal_work',
                    'An embedded work review cannot bypass the source descriptor or submission class')
        if classification == 'forced_content':
            require(row.get('reviewable_content_verified') is True
                    and row.get('mathematical_source') in {'retained_formal_body', 'retained_engineering', 'nonfinal_work'},
                    'A timeout, progress line, environment or numerical script is not forced mathematical content')
        if row.get('work_review_pending'):
            require(classification=='forced_content' and row.get('work_review') is None,
                    'Pending mathematics cannot replace an existing adjudicated work review')
        if row.get('pending_original_record_review'):
            require(classification == 'blank' and row.get('provisional_zero_authorized') is True,
                    'Missing records need an explicit provisional-zero decision, not an invented terminal')
    rounds = data.get('rounds', [])
    require(len(rounds) == 3 and {r.get('round') for r in rounds} == {1, 2, 3},
            'Submission evidence must keep the separate three-round population')
    require(all(r.get('classification') in CLASSES for r in rounds), 'Invalid selfcheck submission class')
    for row in rounds:
        _evidence(row.get('evidence'))
        require(isinstance(row.get('reason'), str) and row['reason'].strip(),
                'Each selfcheck class needs its original evidence and explanation')
        require(row.get('work') is None and row.get('work_review') is None,
                'A1 work credit cannot be reused as a selfcheck round')
    return {r['case_id']: r for r in rows}


def descriptors(value):
    if isinstance(value, dict):
        if {'path', 'bytes', 'sha256'} <= set(value):
            yield value
        else:
            for child in value.values():
                yield from descriptors(child)
    elif isinstance(value, list):
        for child in value:
            yield from descriptors(child)


def _read(folder, item):
    validate_descriptor(item)
    folder = Path(folder).resolve()
    path = folder / item['path']
    require(not any(p.is_symlink() for p in (path, *path.parents) if p != folder and folder in p.parents)
            and path.resolve().is_relative_to(folder), 'Submission evidence escapes its retained archive')
    try:
        raw = retained_bytes(path)
    except FileNotFoundError as error:
        raise ValueError('Submission evidence is missing from its retained archive') from error
    require(len(raw) == item['bytes'] and hashlib.sha256(raw).hexdigest() == item['sha256'],
            'Submission evidence bytes changed')
    return raw


def load_condition(folder, record, condition):
    descriptor = record.get('submission_evidence')
    if descriptor is None:
        return None
    archive = json.loads(_read(folder, descriptor))
    require(archive.get('schema') == 'math-gauge.submission-archive/v1'
            and archive.get('version') == VERSION and set(archive.get('conditions', {})) == set(CONDITIONS),
            'A private submission archive needs both fixed attempt conditions')
    for item in descriptors(archive):
        _read(folder, item)
    require(all(archive['conditions'][key].get('attempt_condition')==key for key in CONDITIONS),
            'Submission archive keys and attempt conditions disagree')
    data = archive['conditions'][condition]
    require('normal_alignment' not in data
            and all('work' not in row and 'normal_math' not in row for row in data.get('initials', [])),
            'Serialized work must be loaded from its byte-bound review descriptor')
    validate_condition(data)
    for row in data['initials']:
        if row.get('work_review'):
            row['work'] = json.loads(_read(folder, row['work_review']))
            for item in descriptors(row['work']):
                _read(folder, item)
        if row.get('normal_review'):
            row['normal_math']=json.loads(_read(folder,row['normal_review']))
            for item in descriptors(row['normal_math']):
                _read(folder,item)
    if data.get('normal_alignment_review'):
        data['normal_alignment']=json.loads(_read(folder,data['normal_alignment_review']))
        selected=data['normal_alignment']
        require(selected.get('source_selection_component_version')==VERSION
                and selected.get('primary_source_kind')=='submission_selected'
                and selected.get('model_label')==data['model_label']
                and condition in selected.get('attempt_conditions',[]),
                'Normal-final trajectory lost its model, condition or source policy')
        selected_rounds={r['round']:r for r in selected.get('rounds',[])}
        for row in data['rounds']:
            snapshot=selected_rounds.get(row['round'],{}).get('snapshot') or {}
            require(snapshot.get('source_response_sha256')==row.get('source_response_sha256'),
                    'Normal-final trajectory borrowed a different round response')
        _evidence(selected.get('evidence'))
        for item in descriptors(data['normal_alignment']):
            _read(folder,item)
    return data


def summary(data):
    """Count mutually exclusive observations; mathematical points are irrelevant."""
    rows = data['initials']
    count = {key: sum(r['classification'] == key for r in rows) for key in CLASSES}
    return dict(planned=len(rows), active_final=count['active_final'],
        forced_content=count['forced_content'], blank=count['blank'], pending=count['not_run'],
        pending_original_record_review=sum(bool(r.get('pending_original_record_review')) for r in rows))


def load_policy(folder, record):
    item = record.get('submission_policy')
    return None if item is None else validate_policy(json.loads(_read(folder, item)))


def project_archive(archive, public_ids, *, source_sha256):
    """Expose counts and public classes, without private names or source paths."""
    public_ids = set(public_ids)
    result = dict(schema='math-gauge.submission-projection/v1', version=VERSION,
        source_sha256=source_sha256, conditions={})
    for condition, data in archive['conditions'].items():
        validate_condition(data)
        result['conditions'][condition] = dict(summary=summary(data),
            public_initials=[dict(case_id=r['case_id'],classification=r['classification'],
                pending_original_record_review=bool(r.get('pending_original_record_review')))
                for r in data['initials'] if r['case_id'] in public_ids],
            private_pending_original_record_review=sum(bool(r.get('pending_original_record_review'))
                for r in data['initials'] if r['case_id'] not in public_ids),
            rounds=[dict(round=r['round'],classification=r['classification']) for r in data['rounds']])
    return result


def validate_record_component(folder, record, *, public=False, public_ids=None):
    """Read every retained input; public archives bind an opaque private hash."""
    policy = load_policy(folder, record)
    require(policy is not None and record.get('submission_evidence') is not None,
            'Current scoring needs its retained submission policy and observations')
    if public:
        data = json.loads(_read(folder, record['submission_evidence']))
        require(data.get('schema') == 'math-gauge.submission-projection/v1'
                and data.get('version') == VERSION
                and data.get('source_sha256') == record.get('submission_evidence_source_sha256')
                and set(data.get('conditions', {})) == set(CONDITIONS),
                'Public submission counts lost their private source binding')
        require(set(data)=={'schema','version','source_sha256','conditions'},
                'Public submission projection contains unsupported evidence or content')
        if public_ids is None:
            catalog=next((p/'cases/catalog.json' for p in Path(folder).resolve().parents
                          if (p/'cases/catalog.json').is_file()),None)
            require(catalog is not None,'Public submission validation needs a trusted public catalog')
            public_ids={r['case_id'] for r in json.loads(catalog.read_bytes())['entries']}
        public_ids=set(public_ids)
        require(len(public_ids)==25,'Public submission population must be the trusted25 tasks')
        for condition in data['conditions'].values():
            require(set(condition)=={'summary','public_initials','private_pending_original_record_review','rounds'},
                    'Public submission condition contains private evidence or content')
            counts = condition['summary']
            require(set(counts)=={'planned','active_final','forced_content','blank','pending','pending_original_record_review'}
                    and all(type(v) is int and v>=0 for v in counts.values())
                    and counts['planned']==39
                    and counts['planned'] == sum(counts[k] for k in ('active_final','forced_content','blank','pending')),
                    'Submission counts overlap or change the denominator')
            rows=condition['public_initials']
            require(isinstance(rows,list) and len(rows)==25
                    and {r.get('case_id') for r in rows}==public_ids
                    and all(set(r)=={'case_id','classification','pending_original_record_review'}
                        and r['classification'] in CLASSES
                        and type(r['pending_original_record_review']) is bool for r in rows),
                    'Public submission rows expose private IDs, paths or answer content')
            require(type(condition['private_pending_original_record_review']) is int
                    and 0<=condition['private_pending_original_record_review']<=14,
                    'Private pending sources may expose only an anonymous count')
            rounds=condition['rounds']
            require(isinstance(rounds,list) and len(rounds)==3
                    and {r.get('round') for r in rounds}=={1,2,3}
                    and all(set(r)=={'round','classification'} and r['classification'] in CLASSES for r in rounds),
                    'Public round projection contains unsupported evidence or content')
        return data
    for condition in CONDITIONS:
        load_condition(folder, record, condition)
    return json.loads(_read(folder, record['submission_evidence']))


def validate_history(folder, record):
    item = record.get('score_history')
    if item is None:
        return None
    data = json.loads(_read(folder, item))
    require(data.get('schema') == 'math-gauge.score-history/v1'
            and data.get('assessment_method_version') == '0.8.0'
            and data.get('capability_method_version') == '0.2.0',
            'Earlier scoring must retain its original method identities')
    original_policy=None
    views=set()
    for descriptor in data.get('files', []):
        raw=_read(folder, descriptor)
        if descriptor['sha256']==data.get('original_policy_sha256'):
            original_policy=json.loads(raw)
        if descriptor['path'].endswith('.json'):
            saved=json.loads(raw)
            if saved.get('schema') in {'math-gauge.assessment-score/v1','math-gauge.assessment-score-aggregate/v1'}:
                require(saved.get('scoring_method_version')=='0.8.0'
                        and (saved.get('score_mode')!='capability' or saved.get('capability_method_version')=='0.2.0'),
                        'A historical score changed its original method identity')
                views.add((saved.get('score_mode'),saved.get('attempt_condition')))
    require(original_policy is not None and original_policy.get('version')=='0.8.0'
            and views=={(m,c) for m in ('capability','partial','strict') for c in CONDITIONS},
            'Score history must retain its actual original policy and all six score views')
    return data


def original_assessment_policy(folder, record, current):
    """Bind inherited v6 inputs to the exact policy kept in method history."""
    history = validate_history(folder, record)
    require(history is not None, 'Inherited current inputs need their original policy history')
    item = next(row for row in history['files']
                if row['sha256'] == history['original_policy_sha256'])
    original = json.loads(_read(folder, item))
    expected = dict(original, version='0.9.0', capability_policy_version='0.3.0',
                    submission_policy_version='0.1.0')
    require(current == expected,
            'Submission method transition changed the frozen mathematical policy')
    return original
