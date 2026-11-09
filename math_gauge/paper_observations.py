"""Source-bound returned papers, without CLI or native-runtime authentication.

This module validates retained bytes and selects operator-reported deliveries.
Mathematical arithmetic, including all penalties and family weights, stays in
scoring.py. A returned paper cannot manufacture a runtime receipt.
"""
import copy
import hashlib
import json
import re
from pathlib import Path

from . import claim_penalties

SCHEMA = 'math-gauge.paper-observation-record/v1'
MATH_SCHEMA = 'math-gauge.paper-observation-math/v1'
CLAIM_SCHEMA = 'math-gauge.paper-observation-claims/v1'
VERSION = '0.1.0'
MODES = ('capability', 'partial', 'strict')
CONDITIONS = ('single_attempt', 'nonlogical_retry_3')
RESULT_FIELDS = dict(capability='capability_results', partial='assessment_results', strict='strict_results')
FAILURES = {'max_output_tokens', 'service_error', 'execution_interrupted', 'operator_reported_failure'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def _sha(value):
    return isinstance(value, str) and re.fullmatch(r'[0-9a-f]{64}', value) is not None


def _unqualified(data):
    require(data.get('reviewer_kind') == 'ai' and data.get('human_review') == 'pending'
            and data.get('formal_comparison_eligible') is False
            and data.get('transport_import_validated') is False
            and data.get('runtime_evidence_verified') is False,
            'Paper observation cannot certify human review, transport or runtime evidence')


def _descriptors(value):
    if isinstance(value, dict):
        if {'path', 'sha256', 'bytes'} <= set(value):
            yield value
        else:
            for key, item in value.items():
                # These are exact embedded copies of original case-scoped
                # policies. Their own paths remain relative to that source
                # case; the retained policy file is checked independently.
                if key not in {'fidelity_policy', 'strict_completion_policy'}:
                    yield from _descriptors(item)
    elif isinstance(value, list):
        for item in value:
            yield from _descriptors(item)


def _public_only(value, public_ids, *, family=False):
    """Reject private identifiers and source paths at every public nesting level."""
    if isinstance(value, dict):
        for key, item in value.items():
            _public_only(item, public_ids, family=key == 'family_id')
    elif isinstance(value, list):
        for item in value:
            _public_only(item, public_ids)
    elif isinstance(value, str):
        require(not re.search(r'(?i)(?:math-gauge-private|legacy-private|(?:^|/)private/(?:MG-|cases/|responses/|reviews/))', value),
                'Paper public projection contains a private source path')
        require(family or set(re.findall(r'\bMG-[A-Z]+[0-9]{3}\b', value)) <= set(public_ids),
                'Paper public projection contains a private/unselected case identifier')


def validate_math_inputs(data, policy):
    """Keep judgments, delivery failures and unresolved evidence separate."""
    from .manuscript_completion import validate_core_completion, validate_fidelity
    from .records import public_assessment_case_ids
    require(data.get('schema') == MATH_SCHEMA and data.get('version') == VERSION
            and data.get('benchmark_version') == '0.6.0', 'Unsupported paper mathematical review')
    _unqualified(data)
    require(isinstance(data.get('model_label'), str) and data['model_label'].strip(),
            'Paper observation needs its attributed model label')
    tasks = data.get('tasks')
    require(isinstance(tasks, list) and len(tasks) == policy['scope']['initial_slots']
            and len({t.get('case_id') for t in tasks}) == len(tasks),
            'Paper review must retain every distinct current A1 task')
    children = {c['id']: c for c in policy['subcategories'] if c['aggregation'] != 'trajectory'}
    public_ids = set(public_assessment_case_ids(policy))
    require({t['case_id'] for t in tasks if t.get('visibility') == 'public'} == public_ids,
            'Paper review changed the selected public/private membership')
    for category, child in children.items():
        rows = [t for t in tasks if t.get('subcategory') == category]
        require(len(rows) == child['public_tasks'] + child['private_tasks']
                and len({t['family_id'] for t in rows}) == child['families']
                and sum(t.get('visibility') == 'public' for t in rows) == child['public_tasks'],
                'Paper review changed a fixed category or family denominator')
    claims = claim_penalties.validate_review(data['claim_review'], model_label=data['model_label'])
    require(set(claims) == {t['case_id'] for t in tasks}, 'Paper claims must retain all current A1 tasks')
    for task in tasks:
        cid, status = task['case_id'], task.get('status')
        require(task.get('slot_id') == cid + ':A1' and task.get('subcategory') in children
                and task.get('visibility') in {'public', 'private'}, 'Invalid paper task identity')
        require(status in {'reviewed', 'delivery_failed', 'unresolved'}, 'Unknown paper delivery status')
        maximum, points = task.get('maximum'), task.get('points')
        require(type(maximum) is int and maximum > 0
                and (points is None or type(points) in (int, float) and 0 <= points <= maximum),
                'Paper mathematical points exceed their original criterion scale')
        require(task.get('complete') is None or type(task['complete']) is bool,
                'Paper completeness must be explicit or unknown')
        attempts = task.get('attempts')
        require(isinstance(attempts, list) and len(attempts) <= 3,
                'Paper observations retain at most three effective attempts')
        delivered = False
        for number, attempt in enumerate(attempts, 1):
            require(attempt.get('attempt') == number and type(attempt['attempt']) is int
                    and not delivered, 'Paper attempts must be contiguous and stop at first delivery')
            delivered = attempt.get('status') == 'delivered'
            require(delivered and attempt.get('reason') is None
                    or attempt.get('status') == 'delivery_failed' and attempt.get('reason') in FAILURES,
                    'Paper retry cannot be admitted for a mathematical error')
        if status == 'reviewed':
            require(delivered and points is not None and type(task.get('complete')) is bool
                    and isinstance(task.get('response'), dict) and isinstance(task.get('review'), dict)
                    and claims[cid]['status'] == 'reviewed',
                    'Reviewed paper needs original response, review and first delivered attempt')
            require(claims[cid].get('source_response_sha256') == task['response']['sha256']
                    and claims[cid].get('source_review_sha256') == task['review']['sha256'],
                    'Paper claims changed their original answer or review binding')
        elif status == 'delivery_failed':
            require(bool(attempts) and not delivered and points == 0 and task.get('complete') is False
                    and claims[cid]['status'] == 'delivery_failed' and not claims[cid]['findings'],
                    'Observed delivery failure is zero delivery, not a mathematical penalty')
        else:
            require(not attempts and points is None and task.get('complete') is None
                    and claims[cid]['status'] == 'unresolved' and not claims[cid]['findings'],
                    'Unresolved paper must remain unknown without invented attempts or findings')
        if len(attempts) > 1 or status == 'delivery_failed':
            require(isinstance(task.get('attempt_evidence'), dict),
                    'Operator-reported retry or failure needs its retained source declaration')
        core = None
        if task.get('strict_completion_case') is not None:
            require(task['subcategory'] == 'manuscript-completion', 'Core rule belongs to its manuscript task')
            core = validate_core_completion(task['strict_completion_case'], task)
        require(task.get('complete') is not True or points == maximum or core is not None
                or task['subcategory'] in {'background-check', 'lean-audit'},
                'Paper strict completeness contradicts its mathematical credit')
        if task.get('fidelity') is not None:
            require(task['subcategory'] == 'manuscript-completion', 'Fidelity belongs to its manuscript task')
            validate_fidelity(task['fidelity_case'], task)
        if status == 'reviewed' and task['subcategory'] == 'theorem-extension':
            require(task.get('baseline_B') in (0, 1, 2) and task.get('research_R') in (0, 1, 2, 3),
                    'Paper extension needs separate original B and R judgments')
        if status == 'reviewed' and task['subcategory'] == 'background-check':
            require(task.get('background_R') in (0, 1, 2, 3)
                    and type(task.get('false_endorsement')) is bool
                    and (not task['false_endorsement'] or task['background_R'] == 0),
                    'Paper background review needs separate substantive level and endorsement judgment')
    require(isinstance(data.get('sources'), list), 'Paper observation needs a retained source inventory')
    return data


def select_inputs(data, condition):
    """Project a first-attempt view; never choose by mathematical score."""
    require(condition in CONDITIONS, 'Unknown paper attempt condition')
    selected = copy.deepcopy(data)
    claims = {r['case_id']: r for r in selected['claim_review']['cases']}
    if condition == 'single_attempt':
        for task in selected['tasks']:
            if task['status'] == 'reviewed' and task['attempts'][0]['status'] == 'delivery_failed':
                task.update(status='delivery_failed', points=0, complete=False, response=None, review=None)
                for key in ('fidelity', 'fidelity_case', 'strict_completion_review', 'strict_completion_review_source'):
                    task.pop(key, None)
                claims[task['case_id']] = dict(case_id=task['case_id'], status='delivery_failed',
                    scope_note='First observed attempt failed to deliver; later mathematics is excluded.',
                    sources=[], findings=[])
    selected['claim_review']['cases'] = list(claims.values())
    return selected


def unknown_alignment(mode):
    return {'metric': {'lower': -20 if mode == 'partial' else 0, 'upper': 100, 'exact': None},
            'rounds': [{'round': n, 'complete': None, 'status': 'not_run'} for n in (1, 2, 3)],
            'major_false_complete_events': {'count': 0}, 'state': 'unresolved'}


def validate_record(record, policy=None, *, private=False):
    require(record.get('schema') == SCHEMA and record.get('version') == VERSION
            and record.get('record_kind') == 'paper_observation'
            and record.get('benchmark_version') == '0.6.0', 'Unsupported paper observation record')
    _unqualified(record)
    allowed = {'schema', 'version', 'record_kind', 'benchmark_version', 'model_id', 'model_label',
        'source_alias', 'source_effort', 'backend_sku', 'reviewer_kind', 'human_review',
        'formal_comparison_eligible', 'transport_import_validated', 'runtime_evidence_verified',
        'retention', 'comparison_note', 'harness', 'mathematical_input_sha256',
        'assessment_policy', 'strict_scoring_policy', 'capability_scoring_policy', 'claim_penalty_policy',
        'assessment_results', 'capability_results', 'strict_results', 'public_task_scores',
        'public_case_ids', 'public_deliveries', 'public_claim_review', 'selfcheck_rounds', 'trajectory',
        'content_rates_status'}
    require(set(record) == allowed | ({'mathematical_inputs'} if private else set()),
            'Paper record contains unsupported fields or private source data')
    require(record.get('backend_sku') is None and _sha(record.get('mathematical_input_sha256'))
            and record.get('retention') == {'user_requested': True}
            and record.get('content_rates_status') == 'not_reviewed',
            'Paper record cannot infer backend identity or inherit prior content rates')
    require(isinstance(record['source_alias'], str) and record['source_alias'].strip()
            and (record['source_effort'] is None or isinstance(record['source_effort'], str))
            and re.fullmatch(r'[a-z0-9][a-z0-9._-]*', record.get('model_id', '')),
            'Paper observation needs the unchanged attributed source identity')
    harness = record['harness']
    require(set(harness) == {'name', 'version', 'detail', 'tool_usage', 'local_tools_allowed',
                            'search_allowed', 'tool_network_access', 'runtime_verified'}
            and harness['name'] in {'Returned paper observation', 'Codex CLI'} and harness['version'] is None
            and harness['runtime_verified'] is False and harness['local_tools_allowed'] is True
            and harness['search_allowed'] is False and harness['tool_network_access'] is False,
            'Paper harness cannot fabricate runtime validation or a CLI/native identity')
    for field in RESULT_FIELDS.values():
        require(set(record[field]) == set(CONDITIONS), 'Paper record needs all six score reports')
    require(record['selfcheck_rounds'] == [dict(round=n, status='not_run', response=None, review=None)
                                         for n in (1, 2, 3)],
            'Unrun paper selfcheck rounds cannot inherit old completion')
    ids = record['public_case_ids']
    require(isinstance(ids, list) and ids == sorted(set(ids)) and len(ids) == 25
            and len(record['public_deliveries']) == 25
            and {r.get('case_id') for r in record['public_deliveries']} == set(ids),
            'Paper public record must project exactly the selected 25 public tasks')
    if policy is not None:
        from .records import public_assessment_case_ids
        require(ids == public_assessment_case_ids(policy), 'Paper public projection includes a private/unselected case')
    if not private:
        _public_only(record, ids)
    for row in record['public_deliveries']:
        require(set(row) == {'case_id', 'status', 'response', 'review'}
                and row['status'] in {'reviewed', 'delivery_failed', 'unresolved'},
                'Paper public delivery contains unsupported or private fields')
        require(row['status'] != 'reviewed' or all(isinstance(row[k], dict) for k in ('response', 'review')),
                'Reviewed public paper needs its retained answer and criterion review')
    return record


def _read(root, item):
    from .records import evidence_bytes
    return json.loads(evidence_bytes(root, item))


def _claim_quotes(root, claims, descriptors):
    from .records import evidence_bytes
    indexed = {(item['path'], item['sha256']): item for item in descriptors}
    for row in claims:
        for finding in row['findings']:
            for quote in finding['evidence']:
                source = indexed.get((quote.get('path'), quote.get('sha256')))
                require(source is not None, 'Paper claim quote names an unretained original source')
                raw = evidence_bytes(root, source)
                start, end = quote.get('byte_start'), quote.get('byte_end')
                require(type(start) is int and type(end) is int and 0 <= start <= end <= len(raw)
                        and raw[start:end] == quote.get('quote', '').encode('utf-8'),
                        'Paper claim quote differs from original UTF-8 bytes')


def _policies(folder, record):
    from .scoring import validate_assessment_policy, validate_strict_assessment_policy, validate_capability_policy
    policies = tuple(_read(folder, record[key]) for key in
                     ('assessment_policy', 'strict_scoring_policy', 'capability_scoring_policy', 'claim_penalty_policy'))
    for validator, policy in zip((validate_assessment_policy, validate_strict_assessment_policy,
                                 validate_capability_policy, claim_penalties.validate_policy), policies):
        validator(policy)
    return policies


def project_score(score):
    from .records import project_assessment_score
    result = project_assessment_score(score)
    result.update(record_kind='paper_observation', transport_import_validated=False,
                  runtime_evidence_verified=False, backend_sku=None)
    return result


def _score_bindings(record):
    return {'mathematical_input_sha256': record['mathematical_input_sha256'],
            **{key + '_sha256': record[key]['sha256'] for key in
               ('assessment_policy', 'strict_scoring_policy', 'capability_scoring_policy', 'claim_penalty_policy')}}


def load_public_record(folder, *, public_case_ids=None):
    """Verify public hashes and opaque private bindings, without claiming replay."""
    from .records import evidence_bytes, PUBLIC_TASK_FIELDS
    folder = Path(folder)
    record = json.loads((folder / 'record.json').read_bytes())
    policy, strict, capability, claims_policy = _policies(folder, record)
    validate_record(record, policy)
    require(record['model_id'] == folder.parent.name, 'Paper record belongs to another model')
    if public_case_ids is not None:
        require(set(record['public_case_ids']) == set(public_case_ids), 'Paper projection changed the public catalog')
    for item in _descriptors(record):
        evidence_bytes(folder, item)
    for row in record['public_deliveries']:
        if row['review'] is not None:
            _public_only(_read(folder, row['review']), record['public_case_ids'])
    scores = {}
    for mode, field in RESULT_FIELDS.items():
        scores[mode] = {}
        for condition in CONDITIONS:
            score = _read(folder, record[field][condition])
            require(score.get('schema') == 'math-gauge.assessment-score-aggregate/v1'
                    and score.get('score_mode') == mode and score.get('attempt_condition') == condition
                    and score.get('record_kind') == 'paper_observation'
                    and score.get('formal_comparison_eligible') is False
                    and score.get('transport_import_validated') is False
                    and score.get('runtime_evidence_verified') is False
                    and score.get('source_bindings', {}).get('mathematical_input_sha256') == record['mathematical_input_sha256']
                    and _sha(score.get('source_bindings', {}).get('private_report_sha256')),
                    'Paper aggregate lost its source, mode or incomplete runtime identity')
            require({k: v for k, v in score['source_bindings'].items() if k != 'private_report_sha256'}
                    == _score_bindings(record), 'Paper aggregate changed its retained source policy bindings')
            require('tasks' not in score and 'case_index' not in score and 'claim_review' not in score,
                    'Paper public aggregate cannot contain private task evidence')
            _public_only(score, record['public_case_ids'])
            scores[mode][condition] = score
    tasks = _read(folder, record['public_task_scores'])
    require(tasks.get('schema') == 'math-gauge.public-task-scores/v1'
            and tasks.get('public_case_ids') == record['public_case_ids']
            and tasks.get('model_label') == record['model_label'] and set(tasks.get('views', {})) == set(MODES),
            'Invalid paper public task projection')
    for mode in MODES:
        require(set(tasks['views'][mode]) == set(CONDITIONS), 'Paper task projection needs both attempt conditions')
        for condition, view in tasks['views'][mode].items():
            require(set(view) == {'source_report_sha256', 'tasks'}
                    and view['source_report_sha256'] == scores[mode][condition]['source_bindings']['private_report_sha256']
                    and [r.get('case_id') for r in view['tasks']] == record['public_case_ids']
                    and all(set(r) == set(PUBLIC_TASK_FIELDS) for r in view['tasks']),
                    'Paper task projection crossed its public-only source binding')
    claims = _read(folder, record['public_claim_review'])
    _public_only(claims, record['public_case_ids'])
    require(set(claims) == {'schema', 'benchmark_version', 'model_label', 'human_review',
                            'formal_comparison_eligible', 'conditions'}
            and claims['schema'] == CLAIM_SCHEMA and claims['benchmark_version'] == '0.6.0'
            and claims['model_label'] == record['model_label'] and claims['human_review'] == 'pending'
            and claims['formal_comparison_eligible'] is False and set(claims['conditions']) == set(CONDITIONS),
            'Invalid paper public claim projection')
    for condition in CONDITIONS:
        rows = claim_penalties.validate_review(claims['conditions'][condition], model_label=record['model_label'])
        require(set(rows) == set(record['public_case_ids']), 'Paper public claims include a private or unselected case')
        for item in _descriptors(claims['conditions'][condition]):
            evidence_bytes(folder, item)
        _claim_quotes(folder, rows.values(), _descriptors(claims['conditions'][condition]))
    return record, scores, None


def load_private_inputs(folder, record, policy):
    """Bind every copied source, original review and quoted assertion byte."""
    from .records import evidence_bytes
    data = _read(folder, record['mathematical_inputs'])
    require(record['mathematical_inputs']['sha256'] == record['mathematical_input_sha256'],
            'Paper mathematical input hash differs from the selected record')
    validate_math_inputs(data, policy)
    retained = {}
    for item in _descriptors(data):
        raw = evidence_bytes(folder, item)
        retained[(item['sha256'], item['bytes'])] = raw
    for task in data['tasks']:
        if task['status'] != 'reviewed':
            continue
        source = _read(folder, task['review'])
        require(source.get('case_id', task['case_id']) == task['case_id'], 'Paper review belongs to another task')
        if 'raw_points' in source:
            require(source['raw_points'] == task['points'] and source['raw_max'] == task['maximum'],
                    'Paper credit differs from the original mathematical criterion review')
            if isinstance(source.get('criteria'), list):
                criteria = source['criteria']
                earned = [c.get('earned', c.get('points')) for c in criteria]
                maxima = [c.get('max', c.get('max_points')) for c in criteria]
                if all(type(v) in (int, float) for v in earned + maxima):
                    require(sum(earned) == source['raw_points'] and sum(maxima) == source['raw_max'],
                            'Paper criterion points do not sum to their retained source total')
        if 'strict_pass' in source:
            require(source['strict_pass'] is task['complete'], 'Paper Strict changed the original review judgment')
        for key in ('baseline_B', 'research_R', 'background_R'):
            if key in source:
                require(task.get(key) == source[key], 'Paper research level changed its original review')
        for item in _descriptors(source):
            require((item['sha256'], item['bytes']) in retained,
                    'Paper original review references an unretained source')
        for key, embedded in (('strict_completion_review_source', 'strict_completion_review'),):
            if task.get(key) is not None:
                require(_read(folder, task[key]) == task[embedded], 'Paper core completion review changed its source bytes')
        for key in ('strict_completion_case', 'fidelity_case'):
            case = task.get(key)
            if case:
                for embedded, descriptor in (('strict_completion_policy', 'strict_completion_policy_source'),
                                              ('fidelity_policy', 'fidelity_policy_source')):
                    if case.get(embedded) is not None:
                        require(_read(folder, case[descriptor]) == case[embedded],
                                'Paper manuscript contract differs from its retained policy')
                        for item in _descriptors(case[embedded]):
                            require((item['sha256'], item['bytes']) in retained,
                                    'Paper manuscript policy references an unretained source')
    _claim_quotes(folder, data['claim_review']['cases'], _descriptors(data))
    return data


def check_record(folder, *, public_folder=None):
    """Recompute private reports and compare all anonymous/public projections."""
    from .records import evidence_bytes, project_public_task_view
    from .scoring import score_paper_observation
    folder = Path(folder)
    record = json.loads((folder / 'record.json').read_bytes())
    if 'mathematical_inputs' not in record:
        _, scores, _ = load_public_record(folder)
    else:
        policies = _policies(folder, record)
        validate_record(record, policies[0], private=True)
        data = load_private_inputs(folder, record, policies[0])
        public = Path(public_folder) if public_folder is not None else None
        public_record, public_scores, _ = load_public_record(public) if public is not None else (None, None, None)
        if public_record is not None:
            require({k: v for k, v in record.items() if k not in {*RESULT_FIELDS.values(), 'mathematical_inputs'}}
                    == {k: v for k, v in public_record.items() if k not in RESULT_FIELDS.values()},
                    'Paper private/public records differ in common source metadata')
            projected_claims = _read(public, public_record['public_claim_review'])['conditions']
            for condition in CONDITIONS:
                original = select_inputs(data, condition)['claim_review']
                original['cases'] = [r for r in original['cases'] if r['case_id'] in public_record['public_case_ids']]
                require(projected_claims[condition] == original,
                        'Paper public claims differ from their original selected source review')
        scores = {}
        for mode, field in RESULT_FIELDS.items():
            scores[mode] = {}
            for condition in CONDITIONS:
                score = _read(folder, record[field][condition])
                derived = score_paper_observation(data, *policies, mode=mode, condition=condition)
                require(all(score.get(k) == value for k, value in derived.items()),
                        'Paper report differs from the shared mathematical scorer')
                require(score.get('source_bindings') == _score_bindings(record),
                        'Paper report changed its retained source policy bindings')
                for task in data['tasks']:
                    legacy = task.get('legacy_sources', {}).get(mode, task.get('legacy_source'))
                    if legacy is None:
                        continue
                    old = _read(folder, legacy)
                    prior = next((r for r in old['tasks'] if r['case_id'] == task['case_id']), None)
                    current = next(r for r in score['tasks'] if r['case_id'] == task['case_id'])
                    keys = ('completion', 'strict_pass', 'response_sha256', 'family_id', 'subcategory')
                    if old.get('score_mode') != mode:
                        keys = keys[1:]
                    original_review = task.get('legacy_original_review', task.get('review'))
                    require(prior is not None and all(prior[k] == current[k] for k in keys)
                            and original_review is not None and prior['review_sha256'] == original_review['sha256'],
                            'Retained legacy paper changed its original selected judgment or source bytes')
                scores[mode][condition] = score
                if public is not None:
                    projected = project_score(score)
                    projected['source_bindings']['private_report_sha256'] = record[field][condition]['sha256']
                    require(projected == public_scores[mode][condition],
                            'Paper public aggregate differs from its private shared-scorer report')
                    view = _read(public, public_record['public_task_scores'])['views'][mode][condition]
                    require(view == project_public_task_view(score, public_record['public_case_ids'],
                                                            record[field][condition]['sha256']),
                            'Paper public task view differs from its private shared-scorer report')
    return {'passed': True, 'record_kind': 'paper_observation', 'model': record['model_id'],
            'earned': {m: {c: s['metrics']['earned'].get('confirmed') for c, s in rows.items()}
                       for m, rows in scores.items()}, 'candidate_calls': 0,
            'runtime_evidence_verified': False}


def retain_scores(private_folder, public_folder):
    """Write six reports from already retained evidence; never call a candidate."""
    from .records import descriptor, project_public_task_view
    from .scoring import score_paper_observation
    private, public = Path(private_folder), Path(public_folder)
    records = [json.loads((folder / 'record.json').read_bytes()) for folder in (private, public)]
    source, projection = records
    policies = _policies(private, source)
    data = load_private_inputs(private, source, policies[0])
    public_ids = projection['public_case_ids']
    task_views = dict(schema='math-gauge.public-task-scores/v1', benchmark_version='0.6.0',
        model_label=data['model_label'], public_case_ids=public_ids, human_review='pending',
        formal_comparison_eligible=False, views={})
    public_claims = dict(schema=CLAIM_SCHEMA, benchmark_version='0.6.0', model_label=data['model_label'],
        human_review='pending', formal_comparison_eligible=False, conditions={})
    def write(path, value):
        path.write_text(json.dumps(value, ensure_ascii=False, indent=2, allow_nan=False) + '\n')
    for condition in CONDITIONS:
        claims = select_inputs(data, condition)['claim_review']
        claims['cases'] = [r for r in claims['cases'] if r['case_id'] in public_ids]
        public_claims['conditions'][condition] = claims
    # Public claim sources are copied by identity, without changing claim quotes.
    from .records import evidence_bytes
    for item in _descriptors(public_claims):
        target = public / item['path']
        target.parent.mkdir(parents=True, exist_ok=True)
        raw = evidence_bytes(private, item)
        if target.exists():
            require(target.read_bytes() == raw, 'Public paper claim source already has different bytes')
        else:
            target.write_bytes(raw)
    for mode, field in RESULT_FIELDS.items():
        task_views['views'][mode] = {}
        for condition in CONDITIONS:
            score = score_paper_observation(data, *policies, mode=mode, condition=condition)
            score['source_bindings'] = _score_bindings(source)
            retry = condition == 'nonlogical_retry_3'
            private_name = {'capability': ('capability-result.json', 'capability-retry-result.json'),
                'partial': ('result.json', 'retry-result.json'),
                'strict': ('strict-result.json', 'strict-retry-result.json')}[mode][retry]
            public_name = {'capability': ('capability-combined-aggregate.json', 'capability-retry-combined-aggregate.json'),
                'partial': ('combined-aggregate.json', 'retry-combined-aggregate.json'),
                'strict': ('strict-combined-aggregate.json', 'strict-retry-combined-aggregate.json')}[mode][retry]
            write(private / private_name, score)
            source[field][condition] = descriptor(private, private / private_name)
            aggregate = project_score(score)
            report_hash = source[field][condition]['sha256']
            aggregate['source_bindings']['private_report_sha256'] = report_hash
            write(public / public_name, aggregate)
            projection[field][condition] = descriptor(public, public / public_name)
            task_views['views'][mode][condition] = project_public_task_view(score, public_ids, report_hash)
    for filename, value, field in (('public-task-scores.json', task_views, 'public_task_scores'),
                                    ('public-claim-review.json', public_claims, 'public_claim_review')):
        for folder, record in zip((private, public), records):
            write(folder / filename, value)
            record[field] = descriptor(folder, folder / filename)
    for folder, record in zip((private, public), records):
        write(folder / 'record.json', record)
    return check_record(private, public_folder=public)
