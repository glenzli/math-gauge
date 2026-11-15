"""Bind a first current assessment to an actually frozen older task edition.

This validates source identity and the existing metadata-only method transition.
It neither creates historical scores nor grades answers or changes arithmetic.
"""
import copy
import hashlib
import json
from datetime import datetime


def _require(value, message):
    if not value:
        raise ValueError(message)


def validate(root, record, current):
    from .records import evidence_bytes
    from .benchmarks import validate_assessment_policy
    from .agy_evidence import validate_delivery, validate_failure

    _require(record.get('benchmark_version') == '0.6.0'
        and record.get('score_history') is None
        and record.get('first_assessment_source') is None
        and record.get('retention', {}).get('user_requested') is True,
        'Retained-source first assessment must preserve its actual edition and selection')
    validate_assessment_policy(current)
    proof = json.loads(evidence_bytes(root, record['source_assessment_admission']))
    _require(proof.get('schema') == 'math-gauge.source-assessment-admission/v1'
        and proof.get('version') == '0.1.0'
        and proof.get('model_id') == record.get('model_id')
        and proof.get('source_benchmark_version') == '0.6.0'
        and proof.get('assessment_method_version') == '0.9.0'
        and proof.get('post_observation') is True
        and proof.get('new_candidate_calls') == 0
        and proof.get('prior_score_views_existed') is False
        and proof.get('source_raw_bytes_rewritten') is False,
        'First source assessment cannot invent migration history or execution identity')
    freeze_raw = evidence_bytes(root, proof['source_freeze'])
    freeze = json.loads(freeze_raw)
    profile_raw = evidence_bytes(root, proof['source_benchmark_profile'])
    profile = json.loads(profile_raw)
    first = json.loads(evidence_bytes(root, proof['first_dispatch']))
    authority = json.loads(evidence_bytes(root, proof['user_adoption']))
    order = freeze.get('initial_order')
    _require(freeze.get('benchmark_version') == profile.get('version') == '0.6.0'
        and freeze.get('profile_sha256') == hashlib.sha256(profile_raw).hexdigest()
        and freeze.get('all_initials_fresh') is True
        and freeze.get('historical_answers_reused') == 0
        and freeze.get('mathematical_requests') == 0
        and first.get('freeze_sha256') == hashlib.sha256(freeze_raw).hexdigest()
        and first.get('physical_request_number') == 1
        and isinstance(order, list) and bool(order) and first.get('case_id') == order[0]
        and datetime.fromisoformat(freeze['utc'].replace('Z', '+00:00'))
            < datetime.fromisoformat(first['utc'].replace('Z', '+00:00')),
        'First assessment lost the actual pre-call older profile or first dispatch')
    _require(authority.get('post_observation') is True and bool(authority.get('user_quote'))
        and authority.get('source_benchmark_version') == '0.6.0'
        and authority.get('original_physical_effective_ordinals_preserved') is True,
        'Retained-source assessment needs the actual post-observation selection')
    original = validate_assessment_policy(copy.deepcopy(profile['assessment_policy']))
    expected = dict(original, version='0.9.0', capability_policy_version='0.3.0',
                    submission_policy_version='0.1.0')
    _require(original.get('version') == '0.8.0' and current == expected,
        'First source assessment changed frozen mathematical weights or contracts')
    native = json.loads(evidence_bytes(root, proof['first_native_admission']))
    _require(native.get('case_id') == first.get('case_id') and native.get('phase') == 'A1'
        and native.get('dispatch', {}).get('sha256') == proof['first_dispatch']['sha256'],
        'First source assessment borrowed another native dispatch')
    row = dict(case_id=first['case_id'], slot_id=first['case_id']+':A1',
        agy_native_evidence=proof['first_native_admission'], response=native.get('response'),
        original_input=native['candidate_input'], execution=native['native_execution'])
    if row['response'] is None:
        # The source edition starts at its actual first dispatch even when that
        # request failed. Keep the original ERROR/deadline proof; do not select
        # a later success or turn nonfinal mathematical work into a final.
        row.update(review=None, evaluation=dict(
            completion=dict(lower=0, upper=0, exact=0), strict_pass=False))
        validate_failure(root, row, evidence_bytes)
    else:
        validate_delivery(root, row, evidence_bytes)
    execution = json.loads(evidence_bytes(root, native['native_execution']))
    _require(execution.get('requested_model') == freeze.get('requested_model')
        and execution.get('requested_effort') == freeze.get('requested_effort'),
        'First source assessment changed the actual requested model or effort')
    return original
