"""Source-bound manuscript reviews and descriptive unrequested-result observations.

This module validates mathematical judgments; scoring.py owns all arithmetic.
It never changes an original answer, a primary review or a candidate invocation.
"""
import copy
import hashlib
import json
from pathlib import Path

from .records import evidence_bytes

POLICY_SCHEMA = 'math-gauge.manuscript-surplus-policy/v1'
REVIEW_SCHEMA = 'math-gauge.manuscript-surplus-review/v1'
RESULT_SCHEMA = 'math-gauge.manuscript-observation/v1'
OBSERVATION_POLICY_SCHEMA = 'math-gauge.manuscript-observation-policy/v1'
REUSE_SCHEMA = 'math-gauge.manuscript-observation-reuse/v1'
ROOT_PATH = Path('results/manuscript-observations/v0.1.0')
REVIEW_ROOT_PATH = Path('results/manuscript-surplus/v0.1.0')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def descriptor(path, root):
    path, root = Path(path), Path(root)
    raw = path.read_bytes()
    return {'path': path.relative_to(root).as_posix(), 'bytes': len(raw),
            'sha256': hashlib.sha256(raw).hexdigest()}


def read_source(root, item):
    return json.loads(evidence_bytes(root, item))


def validate_policy(policy):
    """Validate the immutable source-review contract, not its retired score view."""
    require(policy.get('schema') == POLICY_SCHEMA and policy.get('version') == '0.1.0',
            'Unsupported manuscript-surplus reference policy')
    require(policy.get('scope') == {'component': 'manuscript-completion', 'families': 5,
            'public_families': 1, 'private_families': 4, 'public_case_ids': ['MG-MCP003']},
            'Surplus reference scope must remain the five manuscript families')
    require(policy.get('selection') == {'attempt': 'A1', 'condition': 'nonlogical_retry_3',
            'research_invitation': False, 'new_candidate_calls': 0}, 'Surplus must use selected A1 without new calls')
    require(policy.get('main_scores_modified') is False and policy.get('original_completion_gate') is False,
            'Surplus cannot change or replace original task completion')
    require(policy.get('accepted_gates') == {'correctness': 'proved', 'scope': 'beyond_required',
            'nontrivial': True, 'value': 'high', 'independent_of_errors': True},
            'Surplus acceptance gates changed')
    return policy


def validate_observation_policy(policy):
    require(policy.get('schema') == OBSERVATION_POLICY_SCHEMA and policy.get('version') == '0.1.0',
            'Unsupported manuscript observation policy')
    require(policy.get('scope') == {'component': 'manuscript-completion', 'families': 5,
            'public_families': 1, 'private_families': 4, 'public_case_ids': ['MG-MCP003']},
            'Observation scope must retain the five manuscript families')
    require(policy.get('selection') == {'attempt': 'A1', 'condition': 'nonlogical_retry_3',
            'research_invitation': False, 'new_candidate_calls': 0}, 'Observations require uninvited selected A1')
    require(policy.get('accepted_gates') == {'correctness': 'proved', 'scope': 'beyond_required',
            'nontrivial': True, 'independent_of_errors': True}, 'Observation gates changed')
    require(policy.get('kind') == 'descriptive-observation' and policy.get('unit') == 'result_groups'
            and policy.get('is_score') is False and policy.get('higher_is_better', 'missing') is None
            and policy.get('ceiling', 'missing') is None and policy.get('capability_inference') is False
            and policy.get('main_scores_modified') is False, 'Observations cannot imply a capability score or ceiling')
    return policy


def accepted(candidate):
    return all(candidate.get(key) == value for key, value in {
        'correctness': 'proved', 'scope': 'beyond_required', 'nontrivial': True,
        'value': 'high', 'independent_of_errors': True}.items())


def observed_result(candidate):
    """Neutral observation ignores the source review's contextual value label."""
    return all(candidate.get(key) == value for key, value in {
        'correctness': 'proved', 'scope': 'beyond_required', 'nontrivial': True,
        'independent_of_errors': True}.items())


def observation_note(candidate):
    if observed_result(candidate):
        return '原任务未要求；原文已交付正确、非简单重复的独立数学成果。同组论证与推论合并计数，价值另按研究情境判断。'
    if candidate['scope'] != 'beyond_required':
        return '属于正常必需交付、辅助步骤、直接推论、等价改写或无关内容，不计为额外独立成果。'
    if candidate['correctness'] != 'proved':
        return '现有核验尚未确认闭合且正确的数学成果，不计入已核实额外成果组。'
    if not candidate['nontrivial']:
        return '现有核验未确认区别于直接应用、代入或等价表达的实质独立内容，不另计一组。'
    return '尚未确认能够独立于错误前提成立，不计入已核实额外成果组。'


def validate_review(review, policy):
    """Pure mathematical contract, usable by the shared scorer and fixtures."""
    validate_policy(policy)
    require(review.get('schema') == REVIEW_SCHEMA and review.get('version') == '0.1.0',
            'Unsupported manuscript-surplus review')
    require(review.get('reviewer_kind') == 'ai' and review.get('human_review') == 'pending'
            and review.get('post_observation') is True and review.get('new_candidate_calls') == 0
            and review.get('main_scores_modified') is False, 'Surplus must preserve review and execution provenance')
    cases = review.get('cases', [])
    require(len(cases) == 5 and len({row['case_id'] for row in cases}) == 5
            and len({row['family_id'] for row in cases}) == 5, 'Surplus needs five independent fixed families')
    for row in cases:
        require(row.get('phase') == 'A1' and row.get('condition') == 'nonlogical_retry_3',
                'Only the retained rule-selected A1 can supply surplus')
        require(row.get('status') in policy['statuses'], 'Unknown surplus review status')
        require(isinstance(row.get('scope_audit'), str) and bool(row['scope_audit'].strip()),
                'Each family needs its scope/coverage review')
        candidates = row.get('candidates', [])
        require(isinstance(candidates, list) and len({c['id'] for c in candidates}) == len(candidates),
                'Surplus candidate identities must be unique within a family')
        for candidate in candidates:
            require(candidate.get('scope') in {'beyond_required', *policy['excluded_scope']}, 'Unknown surplus scope judgment')
            require(candidate.get('correctness') in {'proved', 'incorrect', 'unsupported', 'conjecture', 'unresolved', 'not_reassessed'},
                    'Unknown surplus correctness judgment')
            require(type(candidate.get('nontrivial')) is bool and type(candidate.get('independent_of_errors')) is bool
                    and candidate.get('value') in {'high', 'moderate', 'limited', 'none'}, 'Surplus needs explicit nontriviality/value judgments')
            for key in ('group_id', 'title', 'statement', 'scope_delta', 'proof_review', 'nontrivial_step', 'value_rationale', 'reason'):
                require(isinstance(candidate.get(key), str) and bool(candidate[key].strip()), f'Surplus candidate needs {key}')
            require(bool(candidate.get('citations')), 'Surplus judgment must cite original candidate text')
            expected = 'accepted' if accepted(candidate) else 'pending' if candidate['correctness'] == 'unresolved' else 'rejected'
            require(candidate.get('decision') == expected, 'Surplus decision contradicts its mathematical gates')
        if row['status'] in {'not_run', 'delivery_failed'}:
            require(not candidates, 'Unrun/failed delivery cannot create a mathematical surplus judgment')
        if row['status'] == 'reviewed':
            require(all(c['decision'] != 'pending' for c in candidates), 'Unresolved candidate must keep its family unresolved')
    return review


def source_context(public_root, private_root, model_id, record_id, *, include_judgments=False):
    """Resolve selected manuscripts across CLI, returned-paper and native archives."""
    public_root, private_root = Path(public_root), Path(private_root)
    relative = Path('results/v0.6.0') / model_id / record_id
    P, D = public_root / relative, private_root / relative
    name = 'record.json' if (D / 'record.json').is_file() else 'native-observation.json'
    record = json.loads((D / name).read_bytes())
    input_item = record.get('manuscript_completion_inputs', record.get('mathematical_inputs'))
    if record.get('attempt_condition_sources') is not None:
        from .attempt_conditions import load_sources
        selected = load_sources(D, record, 'nonlogical_retry_3', public_root=P)
        input_item = selected['bindings']['manuscript_completion_inputs']
    require(input_item is not None, 'Selected archive has no manuscript input source')
    source_inputs = read_source(D, input_item)
    input_rows = source_inputs.get('slots', source_inputs.get('tasks', []))
    report_path = record.get('assessment_results', {}).get('nonlogical_retry_3', {}).get('path', 'partial-retry-result.json')
    report = json.loads((D / report_path).read_bytes())
    rows = {}
    for score in report['tasks']:
        if score['subcategory'] != 'manuscript-completion':
            continue
        original = next(r for r in input_rows if r['case_id'] == score['case_id'])
        response = original.get('response')
        require((response or {}).get('sha256') == score.get('response_sha256'), 'Surplus source belongs to a different selected answer')
        documents = []
        for role in ('response', 'manuscript'):
            if original.get(role):
                item = original[role]
                evidence_bytes(D, item)
                documents.append({'role': role, **descriptor(D / item['path'], private_root)})
        status = original.get('status', 'reviewed')
        disposition = 'not_run' if status == 'not_run' else 'delivery_failed' if status == 'delivery_failed' else 'reviewed' if response else 'unresolved'
        rows[score['case_id']] = {'documents': documents, 'response_sha256': score.get('response_sha256'),
            'source_status': disposition, 'original_task': {'strict_pass': score.get('strict_pass'),
            'completion': score.get('completion'), 'family_id': score['family_id']}}
        if include_judgments:
            item = original.get('review')
            require(isinstance(item, dict) and {'path', 'bytes', 'sha256'} <= set(item)
                    and item['sha256'] == score.get('review_sha256'),
                    'Observation reuse needs the original mathematical review')
            evidence_bytes(D, item)
            # Bind the actual judgment, not merely an equal resulting score.
            judgment_keys = ('points', 'maximum', 'complete', 'fidelity', 'fidelity_case',
                             'strict_completion_case', 'strict_completion_review')
            rows[score['case_id']]['judgments'] = {
                'review': descriptor(D / item['path'], private_root),
                'input': {key: copy.deepcopy(original[key]) for key in judgment_keys if key in original},
                'claims': copy.deepcopy(next((row for row in source_inputs.get('claim_review', {}).get('cases', [])
                                               if row['case_id'] == score['case_id']), None)),
                'score': copy.deepcopy(score)}
    require(len(rows) == 5, 'Selected archive lacks the five manuscript families')
    return {'cases': rows, 'record': descriptor(D / name, private_root),
            'public_record': descriptor(P / name, public_root),
            'score': descriptor(D / report_path, private_root),
            'inputs': descriptor(D / input_item['path'], private_root)}


def validate_sources(review, root, context, baseline, policy):
    validate_context_rebinding(review, root)
    validate_review(review, policy)
    for key, expected in (('source_record', context['record']), ('source_score', context['score']), ('source_inputs', context['inputs'])):
        require(review.get(key) == expected, 'Surplus binds another selected record/score/input')
        evidence_bytes(root, expected)
    require(read_source(root, review['policy']) == policy, 'Surplus binds another reference policy')
    require(read_source(root, review['baseline']) == baseline, 'Surplus binds another common task boundary')
    index = {row['case_id']: row for row in baseline['cases']}
    require(set(index) == set(context['cases']) == {row['case_id'] for row in review['cases']},
            'Surplus review changed its common case inventory')
    for base in index.values():
        for item in base['materials'].values():
            evidence_bytes(root, item)
    for row in review['cases']:
        original = context['cases'][row['case_id']]
        require(row.get('response_sha256') == original['response_sha256']
                and row.get('documents') == original['documents']
                and row.get('original_task') == original['original_task'], 'Surplus changed original delivery or completion evidence')
        if original['source_status'] in {'not_run', 'delivery_failed', 'unresolved'}:
            require(row['status'] == original['source_status'], 'Surplus cannot turn an unavailable answer into a reviewed result')
        require(row['family_id'] == index[row['case_id']]['family_id'], 'Surplus changed family identity')
        available = {(d['path'], d['sha256']) for d in row['documents']}
        for candidate in row['candidates']:
            for citation in candidate['citations']:
                item = citation['source']
                require((item['path'], item['sha256']) in available, 'Surplus citation is not from the selected delivered manuscript')
                raw = evidence_bytes(root, item)
                start, end = citation['start_byte'], citation['end_byte']
                require(type(start) is int and type(end) is int and 0 <= start < end <= len(raw), 'Surplus citation bytes are invalid')
                require(raw[start:end].decode('utf-8') == citation['quote'], 'Surplus quote differs from original answer bytes')
    return review


def validate_context_rebinding(review, root):
    """A current metadata copy must retain every original mathematical judgment."""
    binding = review.get('metadata_rebind')
    if binding is None:
        return
    require(binding.get('schema') == 'math-gauge.manuscript-observation-context/v1'
            and binding.get('new_candidate_calls') == 0
            and binding.get('mathematical_judgments_changed') is False,
            'Invalid observation context rebinding')
    original = read_source(root, binding['original_review'])
    require('metadata_rebind' not in original, 'Observation context rebinding cannot chain')
    for name in ('source_record', 'source_score', 'source_inputs'):
        retained = binding['retained_original_context'][name]
        require(retained['sha256'] == original[name]['sha256']
                and retained['bytes'] == original[name]['bytes'],
                'Observation context lost its original source bytes')
        evidence_bytes(root, retained)
    identity_fields = {'record_id', 'source_record', 'source_score', 'source_inputs', 'metadata_rebind'}
    content = lambda value: _content_identity({k:v for k,v in value.items() if k not in identity_fields})
    require(content(review) == content(original),
            'Observation context rebinding changed mathematical review content')


def _content_identity(value):
    """Descriptors may relocate; every other judgment and role stays exact."""
    if isinstance(value, dict):
        if {'path', 'sha256'} <= set(value):
            return {key: _content_identity(item) for key, item in value.items() if key != 'path'}
        return {key: _content_identity(item) for key, item in value.items()}
    if isinstance(value, list):
        return [_content_identity(item) for item in value]
    return value


def _same_manuscripts(old, new):
    require(set(old['cases']) == set(new['cases']) and len(old['cases']) == 5,
            'Observation reuse changed the five manuscript families')
    for cid, original in old['cases'].items():
        current = new['cases'][cid]
        for row in (original, current):
            roles = [item.get('role') for item in row['documents']]
            require(len(roles) == len(set(roles)) and set(roles) <= {'response', 'manuscript'},
                    'Observation reuse has duplicate or unknown document roles')
        documents = lambda row: {item['role']: _content_identity(item) for item in row['documents']}
        require(original['response_sha256'] == current['response_sha256']
                and original['source_status'] == current['source_status']
                and original['original_task'] == current['original_task']
                and documents(original) == documents(current),
                'Observation reuse changed an answer, document role or original completion')
        require('judgments' in original and 'judgments' in current
                and _content_identity(original['judgments']) == _content_identity(current['judgments']),
                'Observation reuse changed an original mathematical judgment')


def prepare_reuse_binding(public_root, private_root, model_id, source_record_id, record_id):
    """Freeze two contexts only after proving unchanged answers and judgments."""
    require(all(isinstance(value, str) and value not in {'', '.', '..'}
                and '/' not in value and '\\' not in value
                for value in (model_id, source_record_id, record_id)),
            'Observation reuse needs safe model and record identities')
    require(source_record_id != record_id, 'Observation reuse needs distinct source and target records')
    public_root, private_root = Path(public_root).resolve(), Path(private_root).resolve()
    path = private_root / REVIEW_ROOT_PATH / model_id / source_record_id / 'review.json'
    review = json.loads(path.read_bytes())
    require(review['model_id'] == model_id and review['record_id'] == source_record_id,
            'Observation reuse source review identity differs')
    old = source_context(public_root, private_root, model_id, source_record_id, include_judgments=True)
    new = source_context(public_root, private_root, model_id, record_id, include_judgments=True)
    validate_sources(review, private_root, old, read_source(private_root, review['baseline']),
                     read_source(private_root, review['policy']))
    _same_manuscripts(old, new)
    return {'schema': REUSE_SCHEMA, 'version': '0.1.0', 'model_id': model_id,
            'source_review_record_id': source_record_id, 'record_id': record_id,
            'source_review': descriptor(path, private_root), 'source_context': old, 'target_context': new,
            'same_answer_only': True, 'new_candidate_calls': 0, 'main_scores_modified': False,
            'runtime_evidence_inference': False, 'reviewer_kind': 'ai', 'human_review': 'pending',
            'formal_comparison_eligible': False}


def validate_reuse_binding(binding, public_root, private_root):
    require(binding.get('schema') == REUSE_SCHEMA and binding.get('version') == '0.1.0',
            'Unsupported manuscript observation reuse binding')
    expected = prepare_reuse_binding(public_root, private_root, binding['model_id'],
                                    binding['source_review_record_id'], binding['record_id'])
    require(binding == expected, 'Observation reuse binding differs from its retained contexts')
    return binding


def observation_result(result, binding=None, binding_source=None):
    """Change observation identity without rewriting its frozen source review."""
    if binding is None:
        return result
    require(binding_source is not None, 'Observation reuse needs private source evidence')
    return {**result, 'record_id': binding['record_id'],
            'source_review_record_id': binding['source_review_record_id'], 'reuse_binding': binding_source,
            'source_record': binding['target_context']['record'],
            'source_score': binding['target_context']['score'],
            'source_inputs': binding['target_context']['inputs']}


def public_projection(review, result, policy, *, public_record, policy_source, private_review_sha256, private_baseline_sha256):
    """Only public-case evidence and anonymous combined descriptive counts escape."""
    validate_observation_policy(policy)
    cases = []
    for original in review['cases']:
        if original['case_id'] not in policy['scope']['public_case_ids']:
            continue
        row = {k: copy.deepcopy(original[k]) for k in ('case_id', 'family_id', 'phase', 'condition', 'status',
               'response_sha256', 'original_task', 'scope_audit')}
        row['candidates'] = []
        for source in original['candidates']:
            candidate = {k: copy.deepcopy(source[k]) for k in ('id', 'group_id', 'title', 'statement',
                'scope', 'correctness', 'nontrivial', 'value', 'independent_of_errors', 'scope_delta',
                'proof_review', 'nontrivial_step', 'value_rationale', 'reason', 'decision')}
            candidate['citations'] = [{'source_sha256': c['source']['sha256'],
                'start_byte': c['start_byte'], 'end_byte': c['end_byte'], 'quote': c['quote']} for c in source['citations']]
            candidate['observation_included'] = observed_result(source)
            candidate['observation_note'] = observation_note(source)
            row['candidates'].append(candidate)
        cases.append(row)
    public = {'schema': RESULT_SCHEMA, 'version': '0.1.0', 'visibility': 'public-projection',
            'observation_id': policy['observation_id'], 'base_benchmark_version': '0.6.0',
            'kind': 'descriptive-observation', 'is_score': False, 'higher_is_better': None,
            'capability_inference': False,
            'model_id': review['model_id'], 'record_id': result['record_id'],
            'source_record': public_record, 'policy': policy_source,
            'source_bindings': {'private_review_sha256': private_review_sha256, 'private_baseline_sha256': private_baseline_sha256,
                                'source_review_policy_sha256': review.get('policy', {}).get('sha256')},
            'counts': copy.deepcopy(result['counts']), 'coverage': copy.deepcopy(result['coverage']),
            'public_cases': cases,
            'reviewer_kind': 'ai', 'human_review': 'pending', 'post_observation': True,
            'formal_comparison_eligible': False, 'new_candidate_calls': 0, 'main_scores_modified': False,
            'novelty_scope': policy['novelty_scope']}
    if result.get('reuse_binding') is not None:
        public['source_review_record_id'] = result['source_review_record_id']
        public['source_bindings']['reuse_binding_sha256'] = result['reuse_binding']['sha256']
    return public


def load_public(folder, public_root):
    folder, public_root = Path(folder), Path(public_root)
    result = json.loads((folder / 'observation.json').read_bytes())
    require(result.get('schema') == RESULT_SCHEMA and result.get('visibility') == 'public-projection',
            'Invalid public manuscript observation')
    policy = validate_observation_policy(read_source(public_root, result['policy']))
    require(result['new_candidate_calls'] == 0 and result['main_scores_modified'] is False
            and result['formal_comparison_eligible'] is False, 'Reference result cannot change primary eligibility')
    evidence_bytes(public_root, result['source_record'])
    counts = result['counts']
    require(counts.get('unit') == 'result_groups' and type(counts.get('confirmed_groups')) is int
            and counts['confirmed_groups'] >= 0 and counts.get('total_groups') in (None, counts['confirmed_groups'])
            and result.get('is_score') is False and result.get('higher_is_better', 'missing') is None
            and result.get('capability_inference') is False and 'metrics' not in result,
            'Observation must retain descriptive counts without a score')
    require({r['case_id'] for r in result['public_cases']} == set(policy['scope']['public_case_ids']),
            'Public surplus projection changed its public-only case inventory')
    return result


def check_pair(public_root, private_root, model_id, record_id):
    from .scoring import summarize_manuscript_observations
    public_root, private_root = Path(public_root), Path(private_root)
    relative = ROOT_PATH / model_id / record_id
    D, P = private_root / relative, public_root / relative
    stored = json.loads((D / 'observation.json').read_bytes())
    review = read_source(private_root, stored['source_review'])
    source_policy = validate_policy(read_source(private_root, review['policy']))
    policy = validate_observation_policy(read_source(private_root, stored['policy']))
    public_policy = descriptor(public_root / 'protocol/manuscript-observations-policy.json', public_root)
    require(read_source(public_root, public_policy) == policy, 'Public/private observation policies differ')
    baseline = read_source(private_root, review['baseline'])
    binding = None
    if stored.get('reuse_binding') is not None:
        binding = validate_reuse_binding(read_source(private_root, stored['reuse_binding']), public_root, private_root)
        require(binding['model_id'] == model_id and binding['record_id'] == record_id
                and binding['source_review'] == stored['source_review'],
                'Observation reuse differs from its source review or target identity')
        context = binding['target_context']
    else:
        require(review['model_id'] == model_id and review['record_id'] == record_id,
                'Observation review belongs to another record without a reuse binding')
        context = source_context(public_root, private_root, model_id, record_id)
        validate_sources(review, private_root, context, baseline, source_policy)
    result = summarize_manuscript_observations(review, source_policy, policy)
    result = observation_result(result, binding, stored.get('reuse_binding'))
    require({**result, 'source_review': stored['source_review'], 'policy': stored['policy']} == stored,
            'Observation counts differ from their retained review')
    public = public_projection(review, result, policy, public_record=context['public_record'], policy_source=public_policy,
        private_review_sha256=stored['source_review']['sha256'],
        private_baseline_sha256=review['baseline']['sha256'])
    require(public == json.loads((P / 'observation.json').read_bytes()), 'Public observation differs from private evidence')
    return public
