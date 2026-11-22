"""Source-bound, whole-cohort adoption of independently reviewed research runs.

Execution and mathematical review remain separate owners. This module verifies
their original evidence and projects aggregate fields; scoring.py owns arithmetic.
"""
from copy import deepcopy
import hashlib
import json
from pathlib import Path

from . import independent_research_review as trajectory_review
from . import taste_v130 as flow


SCHEMA = 'math-gauge.independent-research-adoption/v2'
SELECTION = 'math-gauge.independent-research-review-selection/v2'
PUBLIC_PATH = 'protocol/mathematical-taste/v1.3.0/settled-results.json'


def _need(value, message):
    if not value:
        raise ValueError(message)


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, allow_nan=False, indent=2) + '\n').encode()


def _hash(raw):
    return hashlib.sha256(raw).hexdigest()


def _external(base, ref):
    _need(isinstance(ref, dict) and set(ref) == {'path', 'bytes', 'sha256'}, 'Exact original-file binding required')
    name = Path(ref['path'])
    path = flow._safe_absolute(name if name.is_absolute() else flow._contained(base, ref['path']))
    _need(path.is_file(), 'Missing original adoption source')
    raw = path.read_bytes()
    _need(type(ref['bytes']) is int and ref['bytes'] == len(raw) and ref['sha256'] == _hash(raw),
          'Adoption source bytes changed')
    return path, raw


def _reviewer(base, ref, review_path, review):
    path, raw = _external(base, ref)
    source = json.loads(raw)
    _need(source.get('schema') == 'math-gauge.independent-research-reviewer-observation/v1'
          and source.get('requested_model') == 'gpt-6.1-sol'
          and source.get('requested_effort') == 'max'
          and source.get('reviewer_kind') == 'ai' and source.get('human_review') == 'pending'
          and source.get('reviewer_context_id') == review['reviewer_context_id']
          and source.get('reviewer_id') == review['reviewer_id']
          and source.get('backend_identity_independently_verified') is False,
          'Adoption requires the specified independent Sol 6.1 Max AI reviewer')
    _, request = _external(path.parent, source['original_request'])
    _, response = _external(path.parent, source['original_response'])
    _need(request.strip() and response == review_path.read_bytes(), 'Reviewer original response differs from selected review')
    return _hash(raw)


def prepare(selection_path, public_root):
    """Return one public aggregate only after every frozen configuration settles.

    This does not start candidates, perform mathematical judgments, copy private
    manuscripts, or write the public index. The reviewer observation remains an
    operator source record, not an independently authenticated backend receipt.
    """
    from .independent_research_execution import NATIVE_ORIGIN, load_plan, validate_execution

    selection_path = flow._safe_absolute(selection_path)
    selection_raw = selection_path.read_bytes()
    source = json.loads(selection_raw)
    _need(set(source) == {'schema', 'plan', 'run_root', 'models', 'review_policy'} and source['schema'] == SELECTION,
          'Expected a complete whole-trajectory research review selection v2')
    plan_path, plan_raw = _external(selection_path.parent, source['plan'])
    public_root = flow._safe_absolute(public_root)
    plan, registration = load_plan(plan_path, public_root)
    review_policy, policy_raw = _external(selection_path.parent, source['review_policy'])
    review_policy_hash = trajectory_review.policy_sha256(registration, review_policy)
    _need(review_policy_hash == _hash(policy_raw), 'Selected trajectory policy changed during validation')
    run_root = flow._safe_absolute(source['run_root'])
    _need((run_root / 'control/plan.json').read_bytes() == plan_raw, 'Execution and review selected different frozen plans')
    expected = [row['id'] for row in plan['cohort']]
    rows = source['models']
    _need(isinstance(rows, list) and len(rows) == len(expected)
          and len({row['id'] for row in rows}) == len(rows)
          and {row['id'] for row in rows} == set(expected), 'Partial or changed cohorts cannot be adopted')
    selected, contexts, dispatches = {}, set(), 0
    for row in rows:
        _need(set(row) == {'id', 'execution', 'review', 'reviewer_source'}, 'Unexpected private adoption selection fields')
        execution = validate_execution(run_root, row['execution'], plan)
        _need(execution['origin'] == NATIVE_ORIGIN and execution['model_id'] == row['id']
              and execution['outcome'] in {'normal-finals', 'delivery-failed'},
              'A failed or unresolved trajectory needs its separate operational adjudication; no inferred zero')
        state = flow._contained(run_root, execution['state'])
        review_path, review_raw = _external(selection_path.parent, row['review'])
        review = json.loads(review_raw)
        _need(review['reviewer_kind'] == 'ai' and review['human_review'] == 'pending',
              'Fixtures and invented human approval cannot enter a real cohort')
        if execution['outcome'] == 'normal-finals':
            axes = trajectory_review.validate_review(registration, state, review_path, review_policy)
            status = 'reviewed'
        else:
            _need(set(review) == {'schema', 'execution_sha256', 'reviewer_kind', 'human_review',
                'reviewer_id', 'reviewer_context_id', 'conclusion', 'reason', 'evidence'}
                and review['schema'] == 'math-gauge.independent-research-operational-review/v1'
                and review['execution_sha256'] == row['execution']['sha256']
                and review['conclusion'] == 'confirmed-delivery-failed'
                and isinstance(review['reason'], str) and review['reason'].strip()
                and review['reviewer_context_id'] != execution['context_id'],
                'Failed trajectory needs its separate operational adjudication; no inferred zero')
            native = [r['wire_events'] for r in execution['rounds']]
            _need(review['evidence'] and all(ref in native for ref in review['evidence']),
                  'Operational judgment must bind the original native events')
            for ref in review['evidence']:
                flow._read(run_root, ref)
            axes = {axis: dict(score=None, strict=None) for axis in flow.AXES}
            status = 'delivery-failed'
        _need(review_path.read_bytes() == review_raw, 'Selected review changed during validation')
        _need(review['reviewer_context_id'] not in contexts
              and review['reviewer_context_id'] != execution['native_context_id'],
              'Each candidate needs an independent review context')
        contexts.add(review['reviewer_context_id'])
        reviewer_hash = _reviewer(selection_path.parent, row['reviewer_source'], review_path, review)
        selected[row['id']] = dict(status=status, axes={axis: {k: axes[axis][k] for k in ('score', 'strict')}
            for axis in flow.AXES}, normal_rounds=sum(r['delivery'] == 'normal-final' for r in execution['rounds']),
            round_dispatches=len(execution['rounds']), source_sha256=_hash(encoded({
                'execution': row['execution']['sha256'], 'review': _hash(review_raw), 'reviewer': reviewer_hash})))
        dispatches += len(execution['rounds'])
    result = dict(schema=SCHEMA, edition=flow.EDITION, kind='settled-selected-cohort',
        source_binding=deepcopy(plan['baseline']), policy_sha256=_hash(flow.POLICY_FILE.read_bytes()),
        review_policy_sha256=review_policy_hash,
        batch_sha256=_hash(plan_raw), cohort=expected, models={key: selected[key] for key in expected},
        reviewer=dict(requested_model='gpt-6.1-sol', requested_effort='max', reviewer_kind='ai',
                      human_review='pending', backend_identity_independently_verified=False),
        native_round_dispatches=dispatches, candidate_calls_by_adoption=0)
    _need(selection_path.read_bytes() == selection_raw and plan_path.read_bytes() == plan_raw,
          'Selection or plan changed during validation')
    _need(trajectory_review.policy_sha256(registration, review_policy) == review_policy_hash,
          'Selected trajectory policy changed during validation')
    return validate_public(result)


def validate_public(value):
    """Reject private additions, unknown/zero conflation and partial batch writes."""
    _need(set(value) == {'schema', 'edition', 'kind', 'source_binding', 'policy_sha256', 'review_policy_sha256', 'batch_sha256',
        'cohort', 'models', 'reviewer', 'native_round_dispatches', 'candidate_calls_by_adoption'}
        and value['schema'] == SCHEMA and value['edition'] == flow.EDITION
        and value['kind'] == 'settled-selected-cohort' and value['candidate_calls_by_adoption'] == 0,
        'Expected the whole-trajectory public adoption projection v2')
    baseline = value['source_binding']
    _need(set(baseline) == {'edition', 'path', 'sha256'} and baseline['edition'] == '1.2.0'
          and baseline['path'] == 'site/data.json', 'Adoption needs the fixed common 1.2 baseline')
    for h in (baseline['sha256'], value['policy_sha256'], value['review_policy_sha256'], value['batch_sha256']):
        _need(isinstance(h, str) and len(h) == 64 and all(c in '0123456789abcdef' for c in h), 'Opaque SHA256 required')
    cohort = value['cohort']
    _need(isinstance(cohort, list) and cohort and len(set(cohort)) == len(cohort)
          and set(cohort) == set(value['models'])
          and value['native_round_dispatches'] == sum(row['round_dispatches'] for row in value['models'].values()),
          'Public adoption must represent the whole selected cohort')
    _need(value['reviewer'] == dict(requested_model='gpt-6.1-sol', requested_effort='max', reviewer_kind='ai',
        human_review='pending', backend_identity_independently_verified=False), 'Unexpected reviewer projection')
    for row in value['models'].values():
        _need(set(row) == {'status', 'axes', 'normal_rounds', 'round_dispatches', 'source_sha256'}
              and row['status'] in {'reviewed', 'delivery-failed'} and set(row['axes']) == set(flow.AXES)
              and type(row['normal_rounds']) is int and type(row['round_dispatches']) is int
              and ((row['status'] == 'reviewed' and row['normal_rounds'] == row['round_dispatches'] == 3)
                   or (row['status'] == 'delivery-failed' and 0 <= row['normal_rounds'] < 3
                       and row['round_dispatches'] == row['normal_rounds'] + 1)), 'Unexpected public model projection')
        _need(isinstance(row['source_sha256'], str) and len(row['source_sha256']) == 64
              and all(c in '0123456789abcdef' for c in row['source_sha256']), 'Opaque review source binding required')
        for grade in row['axes'].values():
            _need(set(grade) == {'score', 'strict'} and (grade['score'] is None or
                type(grade['score']) in (int, float) and 0 <= grade['score'] <= 100)
                and (grade['strict'] is None or type(grade['strict']) is bool), 'Unknowns must remain distinct from zero')
            if row['status'] == 'delivery-failed':
                _need(grade == dict(score=None, strict=None), 'An operational loss is not a mathematical-axis judgment')
    return value
