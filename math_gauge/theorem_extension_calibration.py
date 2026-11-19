"""Source-bound, evaluator-only reassessment of the six TX research tiers.

This component reads original evidence and new attributed reviews.  It never
changes source records, selects another attempt, executes a candidate, or owns
score arithmetic.  The shared scorer consumes only validated CalibrationInputs.
"""
from dataclasses import dataclass
from pathlib import Path
import json
import re

from .benchmarks import identity
from . import claim_penalties, submission_evidence


VERSION = '0.1.0'
TARGET = '1.1.0'
MODES = ('capability', 'partial', 'strict')
CONDITIONS = ('single_attempt', 'nonlogical_retry_3')
PUBLIC_CASES = ('MG-TX001', 'MG-TX002')
POLICY_SCHEMA = 'math-gauge.theorem-extension-calibration-policy/v1'
INPUT_SCHEMA = 'math-gauge.theorem-extension-calibration-inputs/v1'
REVIEW_SCHEMA = 'math-gauge.theorem-extension-calibration-review/v1'
PRIVATE_SCHEMA = 'math-gauge.theorem-extension-calibration-private/v1'
PUBLIC_SCHEMA = 'math-gauge.theorem-extension-calibration-public/v1'
REVIEW_FIELDS = {'schema', 'version', 'case_id', 'answer_sha256', 'source_review_sha256',
    'baseline_B', 'old_R', 'new_R', 'policy_sha256', 'standard_sha256', 'reviewer_kind',
    'reviewer', 'human_review', 'post_observation', 'status', 'reason', 'attained',
    'not_attained', 'citations'}


def require(value, message):
    if not value:
        raise ValueError(message)


def _hash(value):
    return isinstance(value, str) and re.fullmatch(r'[0-9a-f]{64}', value) is not None


def _descriptor(item):
    require(isinstance(item, dict) and set(item) == {'path', 'bytes', 'sha256'}
            and isinstance(item['path'], str) and item['path']
            and not Path(item['path']).is_absolute() and '\\' not in item['path']
            and all(part not in {'', '.', '..'} for part in item['path'].split('/'))
            and type(item['bytes']) is int and item['bytes'] >= 0 and _hash(item['sha256']),
            'TX calibration needs a safe exact retained-byte descriptor')
    return item


def read(root, item):
    from .records import evidence_bytes
    return evidence_bytes(root, _descriptor(item))


def document(root, item):
    return json.loads(read(root, item))


def _complete_views(views):
    return (isinstance(views, dict) and set(views) == set(MODES)
            and all(isinstance(views[mode], dict) and set(views[mode]) == set(CONDITIONS)
                    for mode in MODES))


def validate_policy(policy):
    required = dict(schema=POLICY_SCHEMA, version=VERSION,
        source_benchmark_version='1.0.0', target_benchmark_version=TARGET,
        base_theorem_extension_version='0.2.0', assessment_method_version='0.9.0',
        review_scope='research_R_only', public_case_ids=list(PUBLIC_CASES),
        private_cases=4, families=6, component_weight=10, research_levels=[0, 1, 2, 3],
        strict_requirements=dict(baseline_B=2, research_R=3), strict_is_binary=True,
        alternative_routes_allowed=True, proof_internal_contributions_allowed=True,
        reference_checklist_required=False, baseline_judgments_changed=False,
        claim_judgments_changed=False, submission_selection_changed=False,
        weights_changed=False, original_bytes_rewritten=False, post_observation=True,
        existing_answers_used_as_design_reference=True, new_candidate_calls=0,
        reviewer_kind='ai', human_review='pending', formal_comparison_eligible=False)
    require(isinstance(policy, dict) and all(policy.get(k) == v for k, v in required.items()),
            'Unsupported TX calibration policy or changed mathematical scope')
    _descriptor(policy.get('standards'))
    private = policy.get('private_standards')
    require(isinstance(private, dict) and set(private) == {'bytes', 'sha256'}
            and type(private['bytes']) is int and private['bytes'] >= 0 and _hash(private['sha256']),
            'Private TX standards must remain an opaque size/hash binding')
    contracts = policy.get('public_case_contracts', [])
    require(isinstance(contracts, list) and [row.get('case_id') for row in contracts] == list(PUBLIC_CASES)
            and all(set(row) == {'case_id', 'task', 'contract'} for row in contracts),
            'TX calibration must bind exactly the two public source contracts')
    for row in contracts:
        _descriptor(row['task'])
        _descriptor(row['contract'])
    return policy


def load_policy(root, item):
    policy = validate_policy(document(root, item))
    read(root, policy['standards'])
    for row in policy['public_case_contracts']:
        read(root, row['task'])
        read(root, row['contract'])
    return policy


def _tier(value, maximum, *, nullable=False):
    return value is None and nullable or type(value) is int and value in range(maximum + 1)


def validate_review(review, *, row, policy_sha256, standard_sha256, answer):
    require(isinstance(review, dict) and set(review) == REVIEW_FIELDS
            and review['schema'] == REVIEW_SCHEMA and review['version'] == VERSION
            and review['case_id'] == row['case_id']
            and review['answer_sha256'] == (row['response'] or {}).get('sha256')
            and review['source_review_sha256'] == (row['source_review'] or {}).get('sha256')
            and all(review[key] == row[key] for key in ('baseline_B', 'old_R', 'new_R'))
            and review['policy_sha256'] == policy_sha256 and review['standard_sha256'] == standard_sha256
            and review['reviewer_kind'] == 'ai' and review['human_review'] == 'pending'
            and review['post_observation'] is True and review['status'] in
                {'reviewed', 'not_run', 'delivery_failed'}
            and isinstance(review['reviewer'], list) and review['reviewer']
            and all(isinstance(x, str) and x.strip() for x in review['reviewer'])
            and all(isinstance(review[key], str) and review[key].strip()
                    for key in ('reason', 'attained', 'not_attained')),
            'TX reassessment lost its answer, old judgment, standard or attribution')
    require(_tier(row['baseline_B'], 2, nullable=True)
            and _tier(row['old_R'], 3, nullable=True) and _tier(row['new_R'], 3, nullable=True),
            'TX reassessment tiers must be integers or original unknowns')
    citations = review['citations']
    require(isinstance(citations, list), 'TX reassessment needs explicit source citations')
    if answer is None:
        require(review['status'] != 'reviewed' and not citations
                and row['new_R'] == row['old_R'],
                'Missing TX delivery cannot acquire an invented mathematical tier')
    else:
        require(review['status'] == 'reviewed' and row['baseline_B'] is not None
                and row['new_R'] is not None and citations,
                'A delivered TX reassessment needs its actual reviewed answer')
    for cite in citations:
        require(isinstance(cite, dict) and set(cite) in
                ({'quote'}, {'quote', 'start_byte', 'end_byte'})
                and isinstance(cite.get('quote'), str) and cite['quote'],
                'TX review citation must quote exact answer text')
        raw = cite['quote'].encode('utf-8')
        require(answer is not None and raw in answer, 'TX review quoted different answer bytes')
        if 'start_byte' in cite:
            start, end = cite['start_byte'], cite['end_byte']
            require(type(start) is int and type(end) is int and 0 <= start < end <= len(answer)
                    and answer[start:end] == raw, 'TX citation byte range changed')
    return review


def _source_descriptor(folder, item):
    if item is None:
        return None
    return dict(_descriptor(item), path=(folder / item['path']).as_posix())


def _source_rows(root, record, folder, source_inputs, condition, base, public_root):
    """Resolve original judgments without manufacturing another harness receipt."""
    from .records import load_claim_review
    source = document(root, source_inputs)
    binding = base.get('source_bindings', {})
    if source.get('schema') == 'math-gauge.theorem-extension-inputs/v1':
        require(binding.get('theorem_extension_inputs_sha256') == source_inputs['sha256'],
                'TX input descriptor is not the effective selected source')
        claims = load_claim_review(root / folder, record, condition,
                                  public_root=Path(public_root) / folder)
        originals = {row['case_id']: row for row in source['slots']}
    else:
        require(source.get('schema') in {'math-gauge.paper-observation-math/v1',
                                        'math-gauge.native-harness-math/v1'}
                and binding.get('mathematical_input_sha256') == source_inputs['sha256'],
                'TX observed input descriptor is not its native/paper source')
        expected_kind = ('paper_observation' if source['schema'] == 'math-gauge.paper-observation-math/v1'
                         else 'native_harness')
        require(base.get('record_kind') == expected_kind,
                'TX calibration cannot reinterpret a native/paper source as another harness')
        if source['schema'] == 'math-gauge.paper-observation-math/v1':
            from .paper_observations import select_inputs
            source = select_inputs(source, condition)
        claims = source['claim_review']
        originals = {row['case_id']: row for row in source['tasks']}
    claim_rows = claim_penalties.validate_review(claims, model_label=base['model_label'])
    submissions = submission_evidence.load_condition(root / folder, record, condition)
    require(submissions is not None
            and binding.get('submission_evidence_sha256') == record['submission_evidence']['sha256'],
            'TX calibration needs the original selected submission evidence')
    submission_rows = submission_evidence.validate_condition(submissions,
                                                            model_label=base['model_label'])
    return originals, claim_rows, submission_rows


@dataclass(frozen=True)
class CalibrationInputs:
    """Immutable source-validated payload; only the evidence loader constructs it."""
    _payload: bytes

    def for_score(self, base, *, mode, condition):
        data = json.loads(self._payload)
        require(mode in MODES and condition in CONDITIONS
                and base.get('score_mode') == mode and base.get('attempt_condition') == condition
                and identity(base) == data['base_identities'][mode][condition]
                and base.get('model_label') == data['model_label'],
                'TX calibration cannot cross a model, condition or effective source report')
        return dict(data, rows=data['conditions'][condition])


def load_inputs(root, item, *, public_root, policy=None, effective_scores):
    """Read a private input packet after ordinary source/correction validation."""
    root, public_root = Path(root).resolve(), Path(public_root).resolve()
    data = document(root, item)
    fields = {'schema', 'version', 'benchmark_version', 'model_id', 'model_label', 'record_id',
        'source_record', 'policy', 'private_standards', 'base_reports', 'conditions', 'reviewer_kind',
        'human_review', 'post_observation', 'formal_comparison_eligible', 'new_candidate_calls',
        'source_raw_bytes_rewritten'}
    require(isinstance(data, dict) and set(data) == fields and data['schema'] == INPUT_SCHEMA
            and data['version'] == VERSION and data['benchmark_version'] == TARGET
            and data['reviewer_kind'] == 'ai' and data['human_review'] == 'pending'
            and data['post_observation'] is True and data['formal_comparison_eligible'] is False
            and data['new_candidate_calls'] == 0 and data['source_raw_bytes_rewritten'] is False
            and isinstance(data['model_id'], str)
            and re.fullmatch(r'[a-z0-9][a-z0-9._-]*', data['model_id'])
            and isinstance(data['record_id'], str)
            and re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9._-]*', data['record_id'])
            and _complete_views(data['base_reports']) and _complete_views(effective_scores)
            and set(data['conditions']) == set(CONDITIONS),
            'Invalid source-bound TX calibration input packet')
    selected_policy = load_policy(public_root, data['policy'])
    require(policy is None or selected_policy == policy, 'TX packet binds a different selected calibration policy')
    policy = selected_policy
    private = _descriptor(data['private_standards'])
    require({k: private[k] for k in ('bytes', 'sha256')} == policy['private_standards'],
            'TX private standards differ from the opaque public binding')
    read(root, private)
    record = document(root, data['source_record'])
    folder = Path(data['source_record']['path']).parent
    require(folder.name == data['record_id'] and folder.parent.name == data['model_id'],
            'TX calibration relocated another original model/record')
    original_version = record.get('benchmark_version')
    require(original_version in {'0.6.0', '1.0.0'}
            or original_version is None and record.get('schema') == 'math-gauge.native-harness-private/v1',
            'TX calibration cannot infer or rewrite an unknown execution source edition')
    payload = dict(model_id=data['model_id'], model_label=data['model_label'], record_id=data['record_id'],
        source_benchmark_version=original_version,
        policy_sha256=data['policy']['sha256'], inputs_sha256=item['sha256'],
        base_identities={}, base_sha256={}, conditions={})
    bases = {}
    for mode in MODES:
        bases[mode], payload['base_identities'][mode], payload['base_sha256'][mode] = {}, {}, {}
        for condition in CONDITIONS:
            base = document(root, data['base_reports'][mode][condition])
            require(base == effective_scores[mode][condition]
                    and base.get('schema') == 'math-gauge.assessment-score/v1'
                    and base.get('score_mode') == mode and base.get('attempt_condition') == condition
                    and base.get('model_label') == data['model_label']
                    and 'tx_calibration' not in base and base.get('scoring_method_version') == '0.9.0',
                    'TX calibration base differs from its fully selected source report')
            bases[mode][condition] = base
            payload['base_identities'][mode][condition] = identity(base)
            payload['base_sha256'][mode][condition] = data['base_reports'][mode][condition]['sha256']
    row_fields = {'case_id', 'source_inputs', 'response', 'source_review',
                  'baseline_B', 'old_R', 'new_R', 'new_review'}
    for condition in CONDITIONS:
        base = bases['partial'][condition]
        source_tasks = {row['case_id']: row for row in base['tasks']
                        if row['subcategory'] == 'theorem-extension'}
        rows = data['conditions'][condition]
        require(len(source_tasks) == policy['families'] and set(PUBLIC_CASES) <= set(source_tasks)
                and isinstance(rows, list) and len(rows) == policy['families']
                and {row.get('case_id') for row in rows} == set(source_tasks),
                'TX calibration must retain all six selected families in both conditions')
        normalized, source_cache = [], {}
        for row in rows:
            require(set(row) == row_fields, 'Unexpected private TX calibration row fields')
            cid = row['case_id']
            original_task = source_tasks[cid]
            inputs_ref = _descriptor(row['source_inputs'])
            require(Path(inputs_ref['path']).is_relative_to(folder), 'TX inputs left the selected original archive')
            key = inputs_ref['sha256']
            if key not in source_cache:
                source_cache[key] = _source_rows(root, record, folder, inputs_ref, condition, base, public_root)
            originals, claims, submissions = source_cache[key]
            require(cid in originals and cid in claims and cid in submissions,
                    'TX source input lost a selected original family')
            old = originals[cid]
            source_document = document(root, inputs_ref)
            source_schema = source_document.get('schema')
            if source_schema == 'math-gauge.native-harness-math/v1':
                # The private native manifest can bind a historical public
                # predecessor.  Read the explicit math-input edition instead;
                # its exact bytes have already matched the effective report's
                # mathematical_input_sha256 in _source_rows above.
                if original_version is None:
                    version = source_document.get('benchmark_version')
                    require(version in {'0.6.0', '1.0.0'}
                            and payload['source_benchmark_version'] in {None, version},
                            'Native TX source lacks a consistent explicitly bound edition')
                    payload['source_benchmark_version'] = version
                # The native owner originally has no per-task status field;
                # its source scorer treats that omission as reviewed.
                observed = old.get('status', 'reviewed') == 'reviewed'
            elif source_schema == 'math-gauge.paper-observation-math/v1':
                observed = old.get('status') == 'reviewed'
            else:
                observed = old.get('status') == 'response_received_execution_unverified'
            source_B = old.get('baseline_B') if observed else None
            source_R = old.get('research_R') if observed else (None if old.get('status') == 'not_run' else 0)
            require(row['baseline_B'] == source_B and row['old_R'] == source_R
                    and row['response'] == _source_descriptor(folder, old.get('response'))
                    and row['source_review'] == _source_descriptor(folder, old.get('review'))
                    and original_task.get('response_sha256') == (row['response'] or {}).get('sha256')
                    and original_task.get('review_sha256') == (row['source_review'] or {}).get('sha256'),
                    'TX reassessment replaced its original answer or baseline/research judgment')
            if original_task.get('research') is not None:
                research = original_task['research']
                require(research['baseline_B'] == row['baseline_B'] and research['research_R'] == row['old_R'],
                        'TX base score and original B/R judgment disagree')
            answer = None if row['response'] is None else read(root, row['response'])
            if row['source_review'] is not None:
                read(root, row['source_review'])
            standard_hash = (policy['standards']['sha256'] if cid in PUBLIC_CASES
                             else private['sha256'])
            review = validate_review(document(root, row['new_review']), row=row,
                policy_sha256=data['policy']['sha256'], standard_sha256=standard_hash, answer=answer)
            submission = submissions[cid]
            if submission['classification'] != 'active_final':
                require(row['new_R'] == row['old_R'],
                        'TX calibration cannot reselect or expand a nonfinal submission')
            source_case = next((case for case in source_document.get('case_index', [])
                                if case.get('case_id') == cid), None)
            if source_case is None:
                source_case = dict(case_id=cid, component='theorem-extension')
            require(source_case.get('component') == 'theorem-extension',
                    'TX calibration borrowed a work-credit contract from another component')
            normalized.append(dict(row, review_sha256=row['new_review']['sha256'],
                claim=claims[cid], submission=submission, case=source_case, status=review['status']))
        payload['conditions'][condition] = normalized
    require(payload['source_benchmark_version'] in {'0.6.0', '1.0.0'},
            'TX calibration needs an explicitly bound original source edition')
    return CalibrationInputs(json.dumps(payload, ensure_ascii=False, sort_keys=True,
                                        separators=(',', ':')).encode())


def load_private(root, item, *, public_root, policy=None, effective_scores, assessment_policy):
    """Verify derived private reports by replaying the single shared scorer."""
    from .scoring import score_theorem_extension_calibration_overlay
    data = document(root, item)
    require(set(data) == {'schema', 'version', 'benchmark_version', 'model_id', 'record_id', 'inputs', 'scores'}
            and data['schema'] == PRIVATE_SCHEMA and data['version'] == VERSION
            and data['benchmark_version'] == TARGET and _complete_views(data['scores']),
            'Invalid private TX calibration result manifest')
    inputs = load_inputs(root, data['inputs'], public_root=public_root, policy=policy,
                         effective_scores=effective_scores)
    scores = {}
    for mode in MODES:
        scores[mode] = {}
        for condition in CONDITIONS:
            expected = score_theorem_extension_calibration_overlay(effective_scores[mode][condition],
                assessment_policy, calibration=inputs, mode=mode, condition=condition)
            actual = document(root, data['scores'][mode][condition])
            require(actual == expected, 'TX calibration report differs from the shared source scorer')
            scores[mode][condition] = actual
    payload = json.loads(inputs._payload)
    require(data['model_id'] == payload['model_id'] and data['record_id'] == payload['record_id'],
            'Private TX calibration manifest changed the selected record')
    return dict(data, _inputs=inputs, _scores=scores)


def _public_case_ids(root, requested):
    """Public membership comes from the trusted catalog, never a projection."""
    root = Path(root).resolve()
    path = root / 'cases/catalog.json'
    require(path.is_file() and not any(p.is_symlink() for p in (path, *path.parents))
            and path.resolve().is_relative_to(root),
            'A trusted canonical public catalog is required for TX calibration')
    catalog = json.loads(path.read_bytes())
    entries = catalog.get('entries', [])
    require(catalog.get('schema') == 'math-gauge.case-catalog/v1' and isinstance(entries, list)
            and len(entries) == 25 and all(isinstance(row, dict)
                and isinstance(row.get('case_id'), str) for row in entries),
            'TX calibration requires the canonical 25-case public catalog')
    ids = [row['case_id'] for row in entries]
    require(len(set(ids)) == 25 and set(PUBLIC_CASES) <= set(ids)
            and (requested is None or isinstance(requested, (list, tuple, set, frozenset))
                 and len(requested) == 25 and set(requested) == set(ids)),
            'TX public membership differs from the canonical public catalog')
    return sorted(ids)


def _public_task_projection(data, *, public_ids, scores, benchmark_version=TARGET):
    from .records import PUBLIC_TASK_FIELDS
    require(set(data) == {'schema', 'benchmark_version', 'model_label', 'public_case_ids', 'views',
                          'human_review', 'formal_comparison_eligible'}
            and data['schema'] == 'math-gauge.public-task-scores/v1'
            and data['benchmark_version'] == benchmark_version and data['public_case_ids'] == sorted(public_ids)
            and data['human_review'] == 'pending' and data['formal_comparison_eligible'] is False
            and _complete_views(data['views']), 'Invalid public TX-calibrated task projection')
    for mode in MODES:
        for condition in CONDITIONS:
            view = data['views'][mode][condition]
            require(set(view) == {'source_report_sha256', 'tasks'}
                    and view['source_report_sha256'] == scores[mode][condition]['source_bindings']['private_report_sha256']
                    and data['model_label'] == scores[mode][condition]['model_label']
                    and [row.get('case_id') for row in view['tasks']] == sorted(public_ids)
                    and all(set(row) == set(PUBLIC_TASK_FIELDS) for row in view['tasks']),
                    'Public TX task rows lost their canonical private-report binding')
            for row in view['tasks']:
                require(row['strict_pass'] is None or type(row['strict_pass']) is bool,
                        'Public TX task projection invented a completion decision')
                require(isinstance(row['completion'], dict)
                        and set(row['completion']) == {'lower', 'upper', 'exact'}
                        and all(v is None or type(v) in {int, float} and -1 <= v <= 1
                                for v in row['completion'].values())
                        and all(row[k] is None or _hash(row[k])
                                for k in ('response_sha256', 'review_sha256')),
                        'Public TX task projection has invalid bounds or source hashes')
    return data


def _public_answer(root, folder, record, *, cid, condition, response_sha256):
    """Find exact selected text only in source-bound public evidence indexes."""
    if response_sha256 is None:
        return None
    candidates = []
    for field in ('public_deliveries', 'records'):
        candidates.extend(row.get('response') for row in record.get(field, [])
                          if row.get('case_id') == cid and row.get('response') is not None)
    condition_component = record.get('attempt_condition_sources')
    if condition_component is not None:
        selections = document(Path(root) / folder, condition_component)
        selected = selections.get('conditions', {}).get(condition, {}).get('source_records')
        require(selected is not None, 'Public TX answer lost its selected condition source index')
        records = document(Path(root) / folder, selected)
        candidates.extend(row.get('response') for row in records.get('records', [])
                          if row.get('case_id') == cid and row.get('response') is not None)
    component = record.get('theorem_extension_evidence')
    if component is not None:
        evidence = document(Path(root) / folder, component)
        candidates.extend(row.get('response') for row in evidence.get('records', [])
                          if row.get('case_id') == cid and row.get('response') is not None)
    for field in ('claim_review', 'public_claim_review'):
        if record.get(field) is None:
            continue
        archive = document(Path(root) / folder, record[field])
        cases = archive.get('conditions', {}).get(condition, {}).get('cases', [])
        for case in cases:
            if case.get('case_id') != cid:
                continue
            for source in case.get('sources', []):
                if source.get('sha256') == response_sha256:
                    require(source.get('archive', 'public') == 'public',
                            'A public TX review attempted to open private answer evidence')
                    candidates.append({k: source[k] for k in ('path', 'bytes', 'sha256')})
    for item in candidates:
        if item.get('sha256') == response_sha256:
            return read(Path(root) / folder, item)
    raise ValueError('Public TX review lacks its selected original answer bytes')


def project_score(score):
    """Delegate observation metadata to its original projection owner."""
    if score.get('record_kind') == 'native_harness':
        from .native_observations import project_score as project
    elif score.get('record_kind') == 'paper_observation':
        from .paper_observations import project_score as project
    else:
        from .records import project_assessment_score as project
    return project(score)


def load_public(root, item, *, policy, effective_scores, source_record, public_case_ids=None):
    """Read aggregate-only current views; never open or infer private case data."""
    from .records import project_assessment_score
    data = document(root, item)
    fields = {'schema', 'version', 'benchmark_version', 'model_id', 'record_id', 'source_record',
        'policy', 'private_inputs_sha256', 'private_manifest_sha256', 'base_reports', 'base_public_tasks',
        'scores', 'public_tasks', 'public_reviews', 'human_review', 'formal_comparison_eligible',
        'new_candidate_calls', 'post_observation'}
    require(set(data) == fields and data['schema'] == PUBLIC_SCHEMA and data['version'] == VERSION
            and data['benchmark_version'] == TARGET and data['human_review'] == 'pending'
            and data['formal_comparison_eligible'] is False and data['new_candidate_calls'] == 0
            and data['post_observation'] is True and _hash(data['private_inputs_sha256'])
            and _hash(data['private_manifest_sha256']) and _complete_views(data['scores'])
            and _complete_views(data['base_reports']) and _complete_views(effective_scores)
            and set(data['public_reviews']) == set(CONDITIONS),
            'Invalid public TX calibration projection or privacy boundary')
    require(load_policy(root, data['policy']) == policy,
            'Public TX calibration binds another selected policy')
    original = document(root, data['source_record'])
    require(original == source_record or data['source_record'] == source_record,
            'Public TX calibration changed its original source record')
    folder = Path(data['source_record']['path']).parent
    require(folder.name == data['record_id'] and folder.parent.name == data['model_id'],
            'Public TX calibration selected another model/record')
    old_tasks = document(root, data['base_public_tasks'])
    public_ids = _public_case_ids(root, public_case_ids)
    _public_task_projection(old_tasks, public_ids=public_ids, scores=effective_scores,
                            benchmark_version=policy['source_benchmark_version'])
    scores = {}
    for mode in MODES:
        scores[mode] = {}
        for condition in CONDITIONS:
            base = document(root, data['base_reports'][mode][condition])
            require(base == effective_scores[mode][condition],
                    'Public TX calibration lost its fully selected effective base')
            score = document(root, data['scores'][mode][condition])
            require(project_assessment_score(score) == score and score.get('score_mode') == mode
                    and score.get('attempt_condition') == condition and score.get('benchmark_version') == TARGET
                    and score.get('source_benchmark_version') == original.get('benchmark_version')
                    and score.get('tx_calibration', {}).get('inputs_sha256') == data['private_inputs_sha256']
                    and score['tx_calibration'].get('policy_sha256') == data['policy']['sha256']
                    and score['tx_calibration'].get('base_report_sha256')
                        == base['source_bindings']['private_report_sha256'],
                    'Public TX calibrated score lost its source/private-scorer binding')
            tx = score['tx_calibration']
            require(set(tx) == {'version', 'benchmark_version', 'source_benchmark_version',
                    'source_score_benchmark_version', 'policy_sha256',
                    'inputs_sha256', 'base_report_sha256', 'reviewed_cases', 'reviewer_kind',
                    'human_review', 'post_observation'}
                    and tx['version'] == VERSION and tx['benchmark_version'] == TARGET
                    and tx['source_benchmark_version'] == original.get('benchmark_version')
                    and tx['source_score_benchmark_version'] == base['benchmark_version']
                    and tx['reviewed_cases'] == 6 and tx['reviewer_kind'] == 'ai'
                    and tx['human_review'] == 'pending' and tx['post_observation'] is True,
                    'Public TX calibration metadata crossed its aggregate-only boundary')
            changed = {'benchmark_version', 'source_benchmark_version', 'metrics', 'contributions',
                       'source_bindings', 'tx_calibration', 'whole_task_counts'}
            require(all(score.get(key) == value for key, value in base.items() if key not in changed),
                    'Public TX calibration changed unrelated source metadata')
            for field in ('metrics', 'contributions'):
                require(set(score[field]) == set(base[field]) and all(score[field][key] == base[field][key]
                    for key in base[field] if key not in {'theorem-extension', 'research', 'earned', 'overall'}),
                    'Public TX calibration changed an unrelated score category')
            added = {'private_report_sha256', 'theorem_extension_calibration_inputs_sha256',
                     'theorem_extension_calibration_policy_sha256', 'theorem_extension_calibration_base_report_sha256'}
            require({k: v for k, v in score['source_bindings'].items() if k not in added}
                    == {k: v for k, v in base['source_bindings'].items() if k != 'private_report_sha256'}
                    and score['source_bindings']['theorem_extension_calibration_inputs_sha256'] == data['private_inputs_sha256']
                    and score['source_bindings']['theorem_extension_calibration_policy_sha256'] == data['policy']['sha256']
                    and score['source_bindings']['theorem_extension_calibration_base_report_sha256']
                        == base['source_bindings']['private_report_sha256'],
                    'Public TX calibration replaced an original source binding')
            scores[mode][condition] = score
            old_view = old_tasks.get('views', {}).get(mode, {}).get(condition, {})
            require(old_view.get('source_report_sha256') == base['source_bindings']['private_report_sha256']
                    and [r.get('case_id') for r in old_view.get('tasks', [])] == sorted(public_ids),
                    'Public TX task baseline is not the effective source report projection')
    projected = _public_task_projection(document(root, data['public_tasks']), public_ids=public_ids, scores=scores)
    require(projected['model_label'] == old_tasks['model_label'], 'Public TX task projection changed its model')
    reviews = {}
    for condition in CONDITIONS:
        refs = data['public_reviews'][condition]
        require(isinstance(refs, list) and [r.get('case_id') for r in refs] == list(PUBLIC_CASES)
                and all(set(r) == {'case_id', 'review'} for r in refs),
                'Public TX calibration can expose only the two public new reviews')
        reviews[condition] = {}
        for ref in refs:
            review = document(root, ref['review'])
            old_task = next(row for row in old_tasks['views']['partial'][condition]['tasks']
                            if row['case_id'] == ref['case_id'])
            source = dict(case_id=ref['case_id'],
                response=(None if old_task['response_sha256'] is None else
                          {'sha256': old_task['response_sha256']}),
                source_review=(None if old_task['review_sha256'] is None else
                               {'sha256': old_task['review_sha256']}),
                baseline_B=review.get('baseline_B'), old_R=review.get('old_R'), new_R=review.get('new_R'))
            answer = _public_answer(root, folder, original, cid=ref['case_id'], condition=condition,
                                    response_sha256=old_task['response_sha256'])
            validate_review(review, row=source, policy_sha256=data['policy']['sha256'],
                            standard_sha256=policy['standards']['sha256'], answer=answer)
            reviews[condition][ref['case_id']] = review
        for mode in MODES:
            old = {r['case_id']: r for r in old_tasks['views'][mode][condition]['tasks']}
            new = {r['case_id']: r for r in projected['views'][mode][condition]['tasks']}
            for cid in public_ids:
                if cid not in PUBLIC_CASES:
                    require(new[cid] == old[cid], 'Public TX calibration changed another task judgment')
                else:
                    require(new[cid]['response_sha256'] == old[cid]['response_sha256'],
                            'Public TX calibration replaced an original answer')
                    review = reviews[condition][cid]
                    require(review.get('answer_sha256') == old[cid]['response_sha256']
                            and review.get('source_review_sha256') == old[cid]['review_sha256'],
                            'Public TX review is detached from the selected original judgment')
                    expected_review = (next(r['review']['sha256'] for r in refs if r['case_id'] == cid)
                                       if new[cid]['response_sha256'] is not None else old[cid]['review_sha256'])
                    require(new[cid]['review_sha256'] == expected_review,
                            'Public TX task did not select its actual new review')
    return dict(data, _scores=scores, _public_tasks=projected, _reviews=reviews)


def verify_pair(public_root, private_root, public_item, private_item, *, policy, assessment_policy,
                public_effective_scores, private_effective_scores, source_record, public_case_ids=None):
    """Close the aggregate boundary against the recomputed private full reports."""
    from .records import project_public_task_view
    private = load_private(private_root, private_item, public_root=public_root, policy=policy,
        effective_scores=private_effective_scores, assessment_policy=assessment_policy)
    public = load_public(public_root, public_item, policy=policy,
        effective_scores=public_effective_scores, source_record=source_record,
        public_case_ids=public_case_ids)
    require(public['private_manifest_sha256'] == private_item['sha256']
            and public['private_inputs_sha256'] == private['inputs']['sha256']
            and public['model_id'] == private['model_id'] and public['record_id'] == private['record_id'],
            'Public TX reassessment is not paired with this exact private source manifest')
    ids = public['_public_tasks']['public_case_ids']
    for mode in MODES:
        for condition in CONDITIONS:
            full = private['_scores'][mode][condition]
            report_sha = private['scores'][mode][condition]['sha256']
            expected = project_score(full)
            expected['source_bindings']['private_report_sha256'] = report_sha
            require(public['_scores'][mode][condition] == expected,
                    'Public TX aggregate differs from the private shared-scorer report')
            require(public['_public_tasks']['views'][mode][condition]
                    == project_public_task_view(full, ids, report_sha),
                    'Public TX task judgments differ from the private shared-scorer report')
    inputs = document(private_root, private['inputs'])
    for condition in CONDITIONS:
        rows = {row['case_id']: row for row in inputs['conditions'][condition]}
        for cid in PUBLIC_CASES:
            require(public['_reviews'][condition][cid] == document(private_root, rows[cid]['new_review']),
                    'Public TX review is not the exact paired private new judgment')
    return dict(public=public, private=private)
