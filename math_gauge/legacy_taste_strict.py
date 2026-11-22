"""Source-bound strict taste amendments; original RMC reviews stay immutable."""

import json
from pathlib import Path

from . import legacy_taste as legacy
from .mathematical_profile import _hash, _require, _text
from .open_research import encoded


VERSION = '0.2.0'
REVIEW_SCHEMA = 'math-gauge.legacy-taste-strict-review/v1'
PUBLIC_SCHEMA = 'math-gauge.legacy-taste-strict-profile-source/v1'
POLICY_SCHEMA = 'math-gauge.legacy-taste-strict-policy/v1'
POLICY_PATH = legacy.DIRECTORY / 'legacy-taste-strict-policy.json'
POLICY_FILE = Path(__file__).resolve().parents[1] / POLICY_PATH
PUBLIC_PATH = legacy.DIRECTORY / 'legacy-taste-strict-results.json'
DIMENSIONS = dict(value=40, conditions=30, support=30)
CHECKS = ('credited_work_closed', 'scope_faithful', 'no_silent_repair')
UNKNOWN_REASONS = ('source_missing', 'verification_unresolved')


def load_policy(path=POLICY_FILE):
    raw = Path(path).read_bytes()
    policy = json.loads(raw)
    fixed = dict(schema=POLICY_SCHEMA, version=VERSION, edition=legacy.EDITION,
                 condition=legacy.CONDITION, dimensions=DIMENSIONS,
                 strict_checks=list(CHECKS), unknown_reasons=list(UNKNOWN_REASONS),
                 review_mode='SMC-level-reviewed-0-to-100',
                 affects='mathematical_taste_profile_only', candidate_calls=0)
    _require(set(policy) == set(fixed) | {'base_scope_policy_sha256', 'private_standard_sha256'}
             and all(type(policy.get(k)) is type(v) and policy[k] == v for k, v in fixed.items())
             and all(_hash(policy[k]) for k in ('base_scope_policy_sha256', 'private_standard_sha256')),
             'Invalid strict taste policy or proof-level review contract')
    return policy, legacy.sha256(raw)


def _key(row):
    return row['model_id'], row['stage'], row['case_id']


def _normalized_review(review, previous, previous_raw, catalog, catalog_sha, roots, policy, policy_sha):
    fixed = dict(schema=REVIEW_SCHEMA, version=VERSION, edition=legacy.EDITION,
                 condition=legacy.CONDITION, source_catalog_sha256=catalog_sha,
                 policy_sha256=policy_sha, previous_review_sha256=legacy.sha256(previous_raw),
                 **legacy.REVIEWER)
    _require(set(review) == set(fixed) | {'reviewer_id', 'actual_context', 'judgments'}
             and all(type(review.get(k)) is type(v) and review[k] == v for k, v in fixed.items())
             and _text(review['reviewer_id']) and _text(review['actual_context'])
             and isinstance(review['judgments'], list) and review['judgments'],
             'Strict taste review lost its actual reviewer, standard, or prior-review binding')
    originals = {_key(row): row for row in previous['judgments']}
    selected = {}
    rows = []
    counts = dict(planned=len(originals), assessed=0, scored=0, source_missing=0,
                  verification_unresolved=0)
    for row in review['judgments']:
        key = _key(row)
        _require(key in originals and key not in selected,
                 'Strict taste review contains a duplicate or different original answer')
        original = originals[key]
        _require(set(row) == set(original) | {'criteria', 'strict_checks', 'unresolved_kind'}
                 and all(row[k] == original[k] for k in ('model_id', 'stage', 'case_id', 'response_sha256')),
                 'Strict taste amendment changed its original answer identity')
        mid, stage, cid = key
        material = catalog['models'][mid][stage][cid]
        base = {name: row[name] for name in original}
        legacy._review_grade(base, material, roots)
        checks, criteria = row['strict_checks'], row['criteria']
        _require(isinstance(checks, dict) and set(checks) == set(CHECKS)
                 and isinstance(criteria, dict) and set(criteria) == set(DIMENSIONS),
                 'Strict taste needs each proof/scope check and each fixed dimension')
        scored = row['score'] is not None
        if scored:
            _require(row['unresolved_kind'] is None and all(type(v) is bool for v in checks.values())
                     and checks['no_silent_repair'] is True,
                     'A scored strict taste judgment cannot be unresolved or rely on repairs')
        else:
            _require(row['unresolved_kind'] in UNKNOWN_REASONS
                     and all(v is None or type(v) is bool for v in checks.values())
                     and any(checks[k] is None for k in CHECKS[:2]),
                     'Unknown strict taste needs a specific missing source or unresolved mathematics')
        total = 0
        for name, maximum in DIMENSIONS.items():
            part = criteria[name]
            _require(isinstance(part, dict) and set(part) == {'points', 'reason', 'evidence'}
                     and _text(part['reason']), 'A strict taste dimension needs its own mathematical reason')
            points = part['points']
            _require((type(points) is int and 0 <= points <= maximum) if scored else points is None,
                     'Strict taste dimension changed its fixed point budget or unknown state')
            legacy._review_grade(dict(base, evidence=part['evidence']), material, roots)
            if scored:
                total += points
        if scored:
            _require(total == row['score'], 'Strict taste score must equal its three dimension contributions')
            _require(row['score'] != 100 or all(checks.values()),
                     'Full strict credit requires closed work, faithful scope, and no repair')
            _require(criteria['support']['points'] != 30 or checks['credited_work_closed'],
                     'Full strict credit for support requires complete credited work')
            # A false formula can invalidate the claimed scope while the actual
            # hypotheses are appropriate. Its loss belongs to the evidenced
            # dimension; the same cause is not charged to conditions again.
        counts['assessed'] += 1
        counts['scored' if scored else row['unresolved_kind']] += 1
        rows.append(base)
        selected[key] = True
    _require(set(selected) == set(originals), 'Strict review must assess every answer in its prior review group')
    normalized = {k: review[k] for k in ('edition', 'condition', 'source_catalog_sha256',
                  *legacy.REVIEWER, 'reviewer_id', 'actual_context')}
    normalized.update(schema=legacy.REVIEW_SCHEMA, version=legacy.VERSION, judgments=rows)
    return normalized, counts


def prepare_public(roots, catalog_raw, review_bytes, previous_bytes, policy, policy_sha,
                   base_policy, base_policy_sha):
    """Re-use the retained six-family arithmetic after independently checking strict reviews."""
    _require(policy['base_scope_policy_sha256'] == base_policy_sha
             and len(review_bytes) == len(previous_bytes) > 0,
             'Strict taste must preserve its frozen scope policy and exact prior groups')
    catalog = json.loads(catalog_raw)
    catalog_sha = legacy.sha256(catalog_raw)
    previous = [json.loads(raw) for raw in previous_bytes]
    # The previous judgments are original immutable inputs, not inherited new scores.
    original_scores = legacy._judgments(roots, catalog, catalog_sha, previous)
    expected = {(mid, stage, cid) for mid, model in catalog['models'].items()
                for stage in ('first', 'revision') for cid, source in (model[stage] or {}).items()
                if source['status'] == 'normal_final'}
    _require(set(original_scores) == expected,
             'Strict taste requires a retained prior assessment for every normal delivery')
    normalized, all_counts = [], []
    for raw, old, old_raw in zip(review_bytes, previous, previous_bytes):
        prepared, counts = _normalized_review(json.loads(raw), old, old_raw, catalog, catalog_sha,
                                              roots, policy, policy_sha)
        normalized.append(encoded(prepared))
        all_counts.append(counts)
    report = legacy.prepare_public(roots, catalog_raw, normalized, base_policy, base_policy_sha)
    report.update(schema=PUBLIC_SCHEMA, version=VERSION, policy_sha256=policy_sha,
                  base_scope_policy_sha256=base_policy_sha,
                  review_sha256=[legacy.sha256(raw) for raw in review_bytes],
                  previous_review_sha256=[legacy.sha256(raw) for raw in previous_bytes],
                  review_coverage={key: sum(row[key] for row in all_counts) for key in all_counts[0]})
    return report


def validate_public(report, policy_sha, baseline, baseline_sha, *, policy=None):
    """Only cohort-wide aggregates and opaque strict-review bindings may be published."""
    if policy is None:
        policy, actual_sha = load_policy()
        _require(actual_sha == policy_sha, 'Strict taste policy does not match its loaded bytes')
    additions = {'base_scope_policy_sha256', 'previous_review_sha256', 'review_coverage'}
    fields = {'schema', 'version', 'edition', 'condition', 'source_binding', 'policy_sha256',
              'source_catalog_sha256', 'review_sha256', 'reviewer_kind', 'human_review',
              'post_observation', 'models'}
    _require(set(report) == fields | additions and report['schema'] == PUBLIC_SCHEMA
             and report['version'] == VERSION and report['policy_sha256'] == policy_sha
             and report['base_scope_policy_sha256'] == policy['base_scope_policy_sha256']
             and isinstance(report['previous_review_sha256'], list)
             and len(report['review_sha256']) == len(report['previous_review_sha256']) > 0
             and all(_hash(value) for value in report['previous_review_sha256']),
             'Strict taste projection lost its policy or original review binding')
    counts = report['review_coverage']
    _require(isinstance(counts, dict)
             and set(counts) == {'planned', 'assessed', 'scored', *UNKNOWN_REASONS}
             and all(type(v) is int and v >= 0 for v in counts.values())
             and counts['planned'] == counts['assessed'] > 0
             and counts['assessed'] == counts['scored'] + sum(counts[k] for k in UNKNOWN_REASONS),
             'Strict taste cannot present a pending review as completed or unknown as zero')
    original_shape = {key: report[key] for key in fields}
    original_shape.update(schema=legacy.PUBLIC_SCHEMA, version=legacy.VERSION,
                          policy_sha256=report['base_scope_policy_sha256'])
    legacy.validate_public(original_shape, report['base_scope_policy_sha256'], baseline, baseline_sha)
    return report
