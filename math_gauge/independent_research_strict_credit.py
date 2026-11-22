"""Project strict credit from the retained net credit of passed research checks."""

from fractions import Fraction
from pathlib import Path, PurePosixPath

from . import independent_research_adoption as adoption
from . import independent_research_score_modes as modes
from . import independent_research_value as value
from . import taste_v130 as flow
from .scoring import _average


VERSION = '0.1.0'
POLICY = 'math-gauge.independent-research-strict-credit-policy/v1'
REVIEW = 'math-gauge.independent-research-strict-credit-review/v1'
PUBLIC = 'math-gauge.independent-research-strict-credit-results/v1'
PATH = value.POLICY_PATH.with_name('strict-credit-policy.json')
FILE = value.POLICY_FILE.with_name(PATH.name)
PUBLIC_PATH = PATH.with_name('strict-credit-results.json')
_fields, _hash, _need, _json = value._fields, value._hash, value._need, value._json
_BOUNDS = ('lower', 'upper', 'exact')


def load_policy(path=FILE):
    raw = Path(path).read_bytes()
    policy = _json(raw)
    fixed = dict(schema=POLICY, version=VERSION, edition=flow.EDITION,
                 status='local-user-selected-strict-credit', method='retained-net-credit-of-passed-checkpoints',
                 taste_credit_limits=dict(value=60, structure=20, selection=20),
                 capacity_credit_limits=dict(planned=5, max_per_criterion=20))
    bindings = ('value_policy_sha256', 'value_results_sha256', 'score_modes_results_sha256')
    _need(_fields(policy, (*fixed, *bindings)) and all(policy[key] == expected for key, expected in fixed.items())
          and all(adoption._is_hash(policy[key]) for key in bindings)
          and all(type(n) is int for field in ('taste_credit_limits', 'capacity_credit_limits')
                  for n in policy[field].values()), 'Invalid independent-research strict-credit policy')
    return policy, _hash(raw)


def bind_policy(policy, value_policy, *, value_policy_sha256, value_results_sha256, score_modes_results_sha256):
    _need(policy['value_policy_sha256'] == value_policy_sha256
          and policy['value_results_sha256'] == value_results_sha256
          and policy['score_modes_results_sha256'] == score_modes_results_sha256 == value_policy['base_results_sha256']
          and policy['taste_credit_limits'] == value_policy['taste_dimensions']
          and policy['capacity_credit_limits']['planned'] == value_policy['strict_criteria']['capacity'],
          'Strict credit requires the exact retained value policy and score-mode indexes')


def load_sources(public_root, policy):
    value_policy, value_hash = value.load_policy(flow._contained(public_root, value.POLICY_PATH.as_posix()))
    raw = flow._contained(public_root, value.PUBLIC_PATH.as_posix()).read_bytes()
    bind_policy(policy, value_policy, value_policy_sha256=value_hash, value_results_sha256=_hash(raw),
                score_modes_results_sha256=value_policy['base_results_sha256'])
    adopted, retained, _ = value.load_retained(public_root, value_policy)
    values = value.validate_public(_json(raw), adopted, retained, value_policy, value_hash)
    return retained, values, raw


def _bounds(interval):
    published = modes._published(interval, interval[0])
    return {key: published[key] for key in _BOUNDS}


def _direct(rmc, count):
    """All passes preserve net RMC; no passing or unresolved checks leave zero credit."""
    if count['passed'] + count['unknown'] == 0 or rmc == 0:
        return modes._from_scalar(0)
    if count['passed'] == count['planned']:
        return modes._from_scalar(rmc)
    return None


def _unallocated(rmc, count):
    direct = _direct(rmc, count)
    if direct is not None:
        return direct
    upper = Fraction(1) if rmc is None else Fraction(str(rmc)) / 100
    return Fraction(), upper, None


def _counts(verdicts):
    _need(all(v is None or type(v) is bool for v in verdicts.values()), 'Invalid retained strict verdict')
    return dict(planned=len(verdicts), passed=sum(v is True for v in verdicts.values()),
                unknown=sum(v is None for v in verdicts.values()))


def _number(n, maximum):
    return type(n) in (int, float) and 0 <= n <= maximum


def _judgment(row, key, finals):
    _need(_fields(row, (key, 'reason', 'evidence')) and modes._text(row['reason']),
          'Each private credit allocation needs a reason and original evidence')
    value._evidence(row['evidence'], finals, flow.ROUNDS)


def _net_credit(points, deductions, original_roots, verdicts, grade, finals):
    _need(_fields(deductions, original_roots), 'Allocate each previously accounted error root exactly once')
    net = {name: Fraction(str(credit)) for name, credit in points.items()}
    _need(sum(net.values()) == Fraction(str(grade['mc'])), 'Allocated positive credit must equal retained MC')
    for root, row in deductions.items():
        _judgment(row, 'criterion', finals)
        criterion = row['criterion']
        _need(isinstance(criterion, str) and criterion in net, 'Each original root must charge one scored criterion')
        net[criterion] -= Fraction(str(original_roots[root]))
    _need(all(v >= 0 for v in net.values()) and sum(net.values()) == Fraction(str(grade['rmc'])),
          'Nonnegative net criterion credit must add up to retained RMC')
    lower = sum((net[key] for key, flag in verdicts.items() if flag is True), Fraction()) / 100
    upper = lower + sum((net[key] for key, flag in verdicts.items() if flag is None), Fraction()) / 100
    return lower, upper, lower if lower == upper else None


def _mixed(grade, count):
    return grade['rmc'] is not None and _direct(grade['rmc'], count) is None


def validate_allocation(review, *, model_id, policy, grade, verdicts, effective_sha256, mc_sha256,
                        taste_sha256, seals, finals, taste_source, mc_source):
    """Check allocation of previously retained credit; no new mathematics or flags enter."""
    expected = dict(schema=REVIEW, version=VERSION, edition=flow.EDITION, model_id=model_id,
                    reviewer_kind='ai', human_review='pending', source_review_sha256=effective_sha256,
                    source_mc_review_sha256=mc_sha256, source_value_review_sha256=taste_sha256,
                    sealed_finals=seals)
    _need(_fields(review, (*expected, 'reviewer_id', 'reviewer_context_id', *value.AXES))
          and all(review[k] == v for k, v in expected.items())
          and all(modes._text(review[k]) for k in ('reviewer_id', 'reviewer_context_id')),
          'Strict allocation must bind all selected review bytes, seals and AI attribution')
    intervals = {}
    for axis in value.AXES:
        count = _counts(verdicts[axis])
        entry = review[axis]
        if not _mixed(grade[axis], count):
            _need(entry is None, 'Direct or unreviewed credit needs no new allocation')
            intervals[axis] = _unallocated(grade[axis]['rmc'], count)
            continue
        if axis == 'capacity':
            _need(_fields(entry, ('directions', 'deductions')) and _fields(entry['directions'], verdicts[axis]),
                  'Allocate retained capacity credit over the five required directions only')
            points = {}
            for name, row in entry['directions'].items():
                _judgment(row, 'mc_points', finals)
                _need(_number(row['mc_points'], policy['capacity_credit_limits']['max_per_criterion']),
                      'Capacity credit exceeds its fixed direction budget')
                points[name] = row['mc_points']
            roots = {row['id']: row['points'] for row in mc_source['error_deductions'] if row['axis'] == axis}
        else:
            _need(_fields(entry, ('deductions',)), 'Retain established taste credit and allocate only original roots')
            points = {key: record['mc_points'] for key, record in taste_source['aspects'].items()}
            roots = {row['id']: row['points'] for row in taste_source['error_deductions']}
        intervals[axis] = _net_credit(points, entry['deductions'], roots, verdicts[axis], grade[axis], finals)
    return intervals


def _source_rows(retained, revised, identifier):
    old = retained['models'][identifier]
    current = revised['models'][identifier]
    return (dict(taste=current['taste'], capacity=old['axes']['capacity']),
            dict(taste=current['criteria'], capacity=old['criteria']['capacity']))


def _read_bounds(metric):
    _need(_fields(metric, _BOUNDS) and all(_number(metric[k], 100) for k in ('lower', 'upper'))
          and (metric['exact'] is None or _number(metric['exact'], 100)), 'Invalid strict-credit bounds')
    lower, upper, exact = (None if metric[k] is None else Fraction(str(metric[k])) / 100 for k in _BOUNDS)
    _need(lower <= upper and (exact is None or lower == upper == exact), 'Contradictory strict-credit bounds')
    return lower, upper, exact


def validate_public(result, retained, revised, policy, policy_hash):
    fixed = dict(schema=PUBLIC, version=VERSION, edition=flow.EDITION, policy_sha256=policy_hash,
                 value_results_sha256=policy['value_results_sha256'], candidate_calls_by_adoption=0)
    _need(_fields(result, (*fixed, 'cohort', 'models')) and all(result[k] == v for k, v in fixed.items())
          and type(result['candidate_calls_by_adoption']) is int and adoption._is_hash(policy_hash)
          and result['cohort'] == revised['cohort'] and _fields(result['models'], revised['cohort']),
          'Unexpected strict-credit result or unbound adopted cohort')
    for identifier, row in result['models'].items():
        _need(_fields(row, (*value.AXES, 'source_sha256')) and adoption._is_hash(row['source_sha256']),
              'Strict results expose only numeric bounds and an opaque source hash')
        grades, counts = _source_rows(retained, revised, identifier)
        for axis in value.AXES:
            metric = row[axis]
            _read_bounds(metric)
            rmc, count = grades[axis]['rmc'], counts[axis]
            direct = _direct(rmc, count)
            if direct is not None or rmc is None:
                _need(metric == _bounds(_unallocated(rmc, count)), 'Direct strict credit differs from the retained flags and RMC')
            else:
                _need(metric['upper'] <= rmc and (metric['exact'] is not None or count['unknown'] > 0)
                      and (metric['exact'] is None or metric['lower'] == metric['upper'] == metric['exact']),
                      'Allocated strict credit must preserve the retained RMC limit and unresolved flags')
    return result


def _frozen_contract(replay, selection, original_batch):
    plan_raw = flow._read(replay, dict(selection['plan'], path='control/plan.json'))
    _need(_hash(plan_raw) == original_batch, 'Archived plan differs from the adopted original batch')
    plan = _json(plan_raw)
    registration_raw = flow._contained(replay, 'control/registration.json').read_bytes()
    registration_hash = _hash(registration_raw)
    _need(registration_hash == plan['registration']['sha256'], 'Archived registration differs from the original plan')
    contract = _json(flow._read(replay / 'control/review-material', _json(registration_raw)['review_contract']))
    gates = contract['gates']['capacity']
    _need(all(type(gate['required']) is bool for gate in gates)
          and len({gate['id'] for gate in gates}) == len(gates)
          and sum(gate['required'] for gate in gates) == 5, 'Invalid original capacity gate contract')
    return registration_hash, gates


def prepare(replay_root, value_reviews_root, allocations_root, public_root):
    """Rebuild from the archived originals and a separate private allocation only."""
    replay, reviews, allocations, public = map(flow._safe_absolute, (replay_root, value_reviews_root,
                                                                    allocations_root, public_root))
    policy_path = flow._contained(public, PATH.as_posix())
    policy, digest = load_policy(policy_path)
    retained, revised, revised_raw = load_sources(public, policy)
    selection_path = flow._contained(replay, value.SELECTION_PATH)
    selection_raw = selection_path.read_bytes()
    selection = _json(selection_raw)
    base = _json(flow._contained(public, adoption.PUBLIC_PATH).read_bytes())
    # The existing owner verifies the original execution, reviews, all seals and
    # the exact v0.2 supplemental judgment before any credit is reallocated.
    _need(adoption.encoded(value.prepare(replay, reviews, public)) == revised_raw,
          'Private originals do not reproduce the retained value results')
    registration, gates = _frozen_contract(replay, selection, base['batch_sha256'])
    old_root = PurePosixPath(selection['run_root'])
    selection_dir = str(PurePosixPath(value.SELECTION_PATH).parent)
    _need(allocations.is_dir() and not allocations.is_relative_to(public), 'Allocations require a separate private directory')
    submitted = {path.name for path in allocations.iterdir()}
    required, historical_contexts, new_contexts, models = set(), set(), set(), {}
    for selected in selection['models']:
        identifier = selected['id']
        if identifier not in revised['models']:
            continue
        source = {key: value._archived(replay, old_root, selected[key], relative_to=selection_dir)
                  for key in ('effective_review', 'mc_review')}
        effective, mc_review = (_json(source[key]) for key in ('effective_review', 'mc_review'))
        _need(effective['registration_sha256'] == registration
              and _fields(effective['gates']['capacity'], (row['id'] for row in gates)), 'Wrong original capacity checks')
        review_raw = flow._contained(reviews, f'{identifier}/review.json').read_bytes()
        notes_raw = flow._contained(reviews, f'{identifier}/notes.md').read_bytes()
        source_hash = _hash(adoption.encoded(dict(review=_hash(review_raw), notes=_hash(notes_raw))))
        _need(source_hash == revised['models'][identifier]['source_sha256'], 'Retained value review bytes differ')
        original_taste = _json(review_raw)
        verdicts = dict(taste={name: row['verdict'] for name, row in original_taste['taste']['gates'].items()},
                        capacity={row['id']: effective['gates']['capacity'][row['id']]['verdict']
                                  for row in gates if row['required']})
        grade, count = _source_rows(retained, revised, identifier)
        _need(all(_counts(verdicts[axis]) == count[axis] for axis in value.AXES),
              'Retained checkpoint coverage differs from the original judgments')
        intervals = {axis: _unallocated(grade[axis]['rmc'], count[axis]) for axis in value.AXES}
        allocation_hash = None
        if any(_mixed(grade[axis], count[axis]) for axis in value.AXES):
            required.add(identifier)
            _need(identifier in submitted, 'Missing private allocation for a mixed strict outcome')
            allocation_raw = flow._contained(allocations, f'{identifier}/allocation.json').read_bytes()
            effective_hash, mc_hash, seals, finals, old_contexts = value._selected_originals(
                replay, old_root, selected, retained['models'][identifier])
            review = _json(allocation_raw)
            intervals = validate_allocation(review, model_id=identifier, policy=policy, grade=grade, verdicts=verdicts,
                effective_sha256=effective_hash, mc_sha256=mc_hash, taste_sha256=_hash(review_raw), seals=seals,
                finals=finals, taste_source=original_taste['taste'], mc_source=mc_review)
            historical_contexts.update(old_contexts)
            new_contexts.add(review['reviewer_context_id'])
            allocation_hash = _hash(allocation_raw)
        # A value reviewer can also allocate its retained T credit in this additive review.
        models[identifier] = dict({axis: _bounds(part) for axis, part in intervals.items()},
            source_sha256=_hash(adoption.encoded(dict(effective=_hash(source['effective_review']),
                positive_credit=_hash(source['mc_review']), value=source_hash,
                seals=effective['sealed_finals'], allocation=allocation_hash))))
    _need(submitted == required and not new_contexts & historical_contexts,
          'Strict allocation must use independent review contexts and only mixed outcomes')
    _need(selection_path.read_bytes() == selection_raw and _hash(policy_path.read_bytes()) == digest,
          'Strict-credit sources changed during verification')
    result = dict(schema=PUBLIC, version=VERSION, edition=flow.EDITION, policy_sha256=digest,
                  value_results_sha256=policy['value_results_sha256'], candidate_calls_by_adoption=0,
                  cohort=revised['cohort'], models=models)
    return validate_public(result, retained, revised, policy, digest)


def project_scores(original, base_strict, policy, *, row=None):
    """Replace SMC with retained strict credit while preserving the other score and diagnostic objects."""
    status = 'not-tested' if original['status'] == 'not-run' else original['status']
    reliable = original['score_modes']['RMC']['components']
    parts = {axis: _read_bounds(row[axis]) if row is not None else _unallocated(reliable[axis]['exact'],
             original['criteria'][axis]) for axis in value.AXES}
    item = _average(list(parts.values()), [policy['item_weights'][axis] for axis in parts])
    zero = modes._point(Fraction())
    if status == 'delivery-failed':
        item = zero
    strict_metrics = dict(components={axis: modes._published(interval, interval[0],
        state=modes._criterion_state(interval, status=status, pending=row is None)) for axis, interval in parts.items()},
        item=modes._published(item, item[0], state=modes._criterion_state(item, status=status, pending=row is None)))

    weights = policy['group_weights']
    groups = {key: modes._source_group(base_strict['metrics'].get(key), signed=False) for key in modes.BASE_GROUPS}
    groups[modes.ITEM] = item, item[0]
    total = _average([groups[key][0] for key in groups], [weights[key] for key in groups])
    confirmed = _average([modes._point(groups[key][1]) for key in groups], [weights[key] for key in groups])[2]
    item_points = modes._published(_average([item, zero], [weights[modes.ITEM], 100 - weights[modes.ITEM]]),
        item[0] * weights[modes.ITEM] / 100)
    bounds = _bounds(total)
    confirmed = modes._published(total, confirmed)['confirmed']
    return dict(original, strict_credit=True, strict_overall=bounds, strict_confirmed=confirmed,
        composite_by_base=dict(original['composite_by_base'], SMC=bounds),
        confirmed_by_base=dict(original['confirmed_by_base'], SMC=confirmed),
        score_modes=dict(original['score_modes'], SMC=strict_metrics),
        category_points=dict(original['category_points'], SMC=dict(original['category_points']['SMC'], **{modes.ITEM: item_points})))
