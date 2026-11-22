"""Versioned 1.3 profile composition from public grade and profile evidence."""

import hashlib
import json
from pathlib import Path

from .independent_research_score_modes import REQUIRED_CRITERIA
from .legacy_taste import FAMILIES as LEGACY_FAMILIES, UNIT as LEGACY_UNIT
from .scoring import _average, _bound, _interval, _percent


POLICY_PATH = Path('protocol/mathematical-taste/v1.3.0/profile-policy.json')
POLICY_FILE = Path(__file__).resolve().parents[1] / POLICY_PATH
SCHEMA = 'math-gauge.independent-research-abilities/v4'
STAGES = dict(first='first-answer', revision='revision-inclusive')
_FIELDS = ('lower', 'upper', 'exact')
_TASTE_CHECKS = REQUIRED_CRITERIA['taste']
_TASTE_SOURCES = dict(independent_mode='SMC', legacy_component_version='0.2.0')
_ROUTES = {
    'initiative_v130': ('initiative', {'autonomy'}),
    'depth_v130': ('depth', {'capacity'}),
    'open_research_v130': ('open_research', {'autonomy', 'capacity'}),
    'discernment_v130': ('discernment', {'taste'}),
}


def load_policy(path):
    raw = Path(path).read_bytes()
    policy = json.loads(raw)
    if (set(policy) != {'schema', 'edition', 'base_edition', 'routes', 'mathematical_taste'}
            or policy['schema'] != 'math-gauge.independent-research-profile-policy/v3'
            or policy['edition'] != '1.3.0' or policy['base_edition'] != '1.2.0'
            or set(policy['routes']) != set(_ROUTES)):
        raise ValueError('Invalid independent research profile policy')
    taste = policy['mathematical_taste']
    if (set(taste) != {'legacy_percent', *_TASTE_SOURCES}
            or any(taste[key] != value for key, value in _TASTE_SOURCES.items())
            or type(taste['legacy_percent']) is not int or not 0 < taste['legacy_percent'] < 100):
        raise ValueError('Invalid fixed mathematical taste profile blend')
    for axis, route in policy['routes'].items():
        base_axis, components = _ROUTES[axis]
        if (set(route) != {'base_axis', 'item_percent', 'component_weights'}
                or route['base_axis'] != base_axis or type(route['item_percent']) is not int
                or not 0 < route['item_percent'] < 100
                or set(route['component_weights']) != components
                or any(type(weight) is not int or weight <= 0 for weight in route['component_weights'].values())):
            raise ValueError('Invalid fixed independent research profile route: ' + axis)
    return policy, hashlib.sha256(raw).hexdigest()


def _indexed_profiles(data, field, schema, edition='1.2.0'):
    profile = data.get(field) or {}
    if profile.get('schema') != 'math-gauge.' + schema + '/v1' or profile.get('benchmark_version') != edition:
        return {}
    return {row['id']: row for row in profile.get('models', [])}


def _source_interval(metric):
    if metric is None:
        return _interval(None)
    for key in _FIELDS:
        value = metric[key]
        if not (key == 'exact' and value is None) and type(value) not in (int, float):
            raise ValueError('Expected public percentage score bounds')
    return _interval({key: None if metric[key] is None else metric[key] / 100 for key in _FIELDS})


def _score_interval(score):
    return _source_interval(dict.fromkeys(_FIELDS, score) if score is not None else None)


def _published_metric(interval, confirmed):
    low, high, value = interval
    exact = _percent(value)
    return dict(lower=exact if exact is not None else _bound(low, lower=True),
                upper=exact if exact is not None else _bound(high, lower=False),
                exact=exact, confirmed=_percent(confirmed))


def _base_coverage(metric, axis):
    unit, fixed = ('open_research_family', 5) if axis == 'open_research' else ('mathematical_family', 35)
    source = (metric or {}).get('coverage') or {}
    reviewed = source.get('reviewed')
    if source.get('unit') == unit and source.get('planned') == fixed and type(reviewed) is int and 0 <= reviewed <= fixed:
        return dict(unit=unit, planned=fixed, reviewed=reviewed)
    return None


def _blend_axis(base, grades, route):
    parts = route['component_weights']
    base_interval = _source_interval(base)
    base_confirmed = _score_interval(base['confirmed'])[2] if base is not None and 'confirmed' in base else base_interval[0]
    if base_confirmed is None or not base_interval[0] <= base_confirmed <= base_interval[1]:
        raise ValueError('Confirmed profile value lies outside its source bounds')
    item_interval = _average([_score_interval(grades.get(axis)) for axis in parts], list(parts.values()))
    weights = (100 - route['item_percent'], route['item_percent'])
    measured_parts = sum(grades.get(axis) is not None for axis in parts)
    combined = _average([base_interval, item_interval], weights)
    confirmed = _average([(base_confirmed,) * 3, (item_interval[0],) * 3], weights)[2]
    base_metric = None if base is None else dict(
        {key: base[key] for key in _FIELDS}, confirmed=base.get('confirmed', base['lower']))
    return dict(_published_metric(combined, confirmed), base_axis=route['base_axis'],
        base_metric=base_metric, base_coverage=_base_coverage(base, route['base_axis']),
        task_metric=_published_metric(item_interval, item_interval[0]),
        task_coverage=dict(unit='independent_open_research_task', planned=1,
            reviewed=int(measured_parts == len(parts)), components_planned=len(parts), components_reviewed=measured_parts),
        base_weight=weights[0] / 100, item_weight=weights[1] / 100, component_weights=dict(parts))


def _independent_taste_smc(report):
    missing_state = 'not-tested' if report is None else 'unavailable'
    report = report or {}
    metric = report.get('score_modes', {}).get('SMC', {}).get('components', {}).get('taste')
    counts = report.get('criteria', {}).get('taste')
    coverage = dict(unit='taste_checkpoint', planned=_TASTE_CHECKS, reviewed=0)
    if metric is None and counts is None:
        return dict(lower=0, upper=100, exact=None, confirmed=0, state=missing_state, coverage=coverage)
    if (metric is None or counts is None or counts['planned'] != _TASTE_CHECKS
            or type(counts['unknown']) is not int or not 0 <= counts['unknown'] <= _TASTE_CHECKS
            or (metric['exact'] is None) != (counts['unknown'] > 0)):
        raise ValueError('Mathematical taste SMC must retain its settled checkpoint coverage')
    coverage['reviewed'] = _TASTE_CHECKS - counts['unknown']
    return dict({key: metric[key] for key in (*_FIELDS, 'confirmed', 'state')}, coverage=coverage)


def _blend_taste(independent, legacy, *, legacy_percent):
    legacy_available = legacy is not None
    if legacy is None:
        legacy = dict(lower=0, upper=100, exact=None, confirmed=0,
                      coverage=dict(unit=LEGACY_UNIT, planned=LEGACY_FAMILIES, reviewed=0, observed=0))
    weights = [100 - legacy_percent, legacy_percent]
    interval = _average([_source_interval(metric) for metric in (independent, legacy)], weights)
    confirmed = _average([(_score_interval(metric['confirmed'])[2],) * 3 for metric in (independent, legacy)],
                         weights)[2]
    return dict(_published_metric(interval, confirmed),
                independent_metric={key: independent[key] for key in (*_FIELDS, 'confirmed', 'state')},
                independent_coverage=independent['coverage'], legacy_metric=legacy,
                legacy_review_available=legacy_available,
                independent_weight=weights[0] / 100, legacy_weight=weights[1] / 100)


def project_models(data, reports, policy, denominators, *, legacy_taste_strict=None):
    """Share the independent taste SMC across stages with their own strict legacy evidence."""
    legacy_taste_strict = legacy_taste_strict or {}
    if data.get('mathematical_profile_baseline') is not None:
        first = _indexed_profiles(data, 'mathematical_profile_baseline', 'mathematical-profile-baseline')
    else:
        first = _indexed_profiles(data, 'mathematical_profile', 'mathematical-profile', '1.1.0')
    revision = _indexed_profiles(data, 'mathematical_profile_revision', 'mathematical-profile-revision')
    open_research = _indexed_profiles(data, 'open_research', 'open-research')
    ids = dict.fromkeys(reports)
    if data.get('profile_models'):
        ids.update(dict.fromkeys(row['id'] for row in data['profile_models']
                                if row.get('presentation_eligibility', {}).get('ranked') is not False))
    projected = {}
    for identifier in ids:
        report = reports.get(identifier)
        grades = report['subscores'] if report is not None else {}
        row = {}
        for component, axis, denominator in [('autonomy', 'open_research_autonomy', 'open_research_autonomy'),
                                             ('taste', 'independent_taste', 'mathematical_taste')]:
            value = grades.get(component)
            planned = denominators[denominator]['planned']
            row[axis] = dict(lower=0 if value is None else value, upper=100 if value is None else value, exact=value,
                comparable=value is not None, observed=planned if value is not None else 0,
                denominator={key: denominators[denominator][key] for key in ('unit', 'planned', 'rounds')})
        row['independent_taste_smc'] = _independent_taste_smc(report)
        row['completion_v130'] = dict(report['strict_overall'] if report is not None else dict(lower=0, upper=100, exact=None),
            confirmed=report['strict_confirmed'] if report is not None else 0, coverage=None,
            source='same-v130-strict-overall', additional_projection_weight=0)
        row['stages'] = {}
        for stage, profiles in [('first', first), ('revision', revision)]:
            baselines = (profiles.get(identifier, {}).get('metrics') or {}).copy()
            baselines['open_research'] = open_research.get(identifier, {}).get(stage)
            row['stages'][stage] = {axis: _blend_axis(baselines.get(route['base_axis']), grades, route)
                                    for axis, route in policy['routes'].items()}
            row['stages'][stage]['mathematical_taste'] = _blend_taste(
                row['independent_taste_smc'], legacy_taste_strict.get(identifier, {}).get(stage),
                legacy_percent=policy['mathematical_taste']['legacy_percent'])
        projected[identifier] = row
    return projected
