"""Bind 1.3 independent-research score modes to original, reviewed deliveries."""

from fractions import Fraction
import json
from pathlib import Path

from . import independent_research_adoption as baseline
from . import independent_research_review as trajectory_review
from . import taste_v130 as flow
from .scoring import _average, _boolean, _bound, _interval, _percent


EDITION = flow.EDITION
AXES = flow.AXES
MODES = ('MC', 'RMC', 'SMC')
BASE_GROUPS = ('written', 'lean', 'research')
ITEM = 'independent_open_research'
SCHEMA = 'math-gauge.independent-research-score-modes/v1'
SELECTION = 'math-gauge.independent-research-score-modes-selection/v1'
MC_REVIEW = 'math-gauge.independent-research-mc-review/v1'
MC_PURPOSE = 'post-observation-mc-calibration'
RECHECK = 'math-gauge.independent-research-recheck-selection/v1'
POLICY = 'math-gauge.independent-research-score-modes-policy/v1'
POLICY_PATH = Path('protocol/mathematical-taste/v1.3.0/score-modes-policy.json')
POLICY_FILE = Path(__file__).resolve().parents[1] / POLICY_PATH
PUBLIC_PATH = POLICY_PATH.with_name('score-modes-results.json')
REQUIRED_CRITERIA = dict(autonomy=2, taste=3, capacity=5)
_FIELDS = ('lower', 'upper', 'exact')
_need = flow._need
_hash = flow._sha


def load_policy(path=POLICY_FILE):
    raw = Path(path).read_bytes()
    policy = json.loads(raw)
    _need(isinstance(policy, dict) and set(policy) == {'schema', 'edition', 'version', 'status',
          'item_weights', 'group_weights', 'strict_criteria'}
          and policy['schema'] == POLICY and policy['edition'] == EDITION and policy['version'] == '0.1.0'
          and policy['status'] == 'local-preview-weights-not-ratified'
          and policy['strict_criteria'] == REQUIRED_CRITERIA
          and all(type(n) is int for n in policy['strict_criteria'].values()), 'Invalid score-modes policy')
    for field, keys in [('item_weights', AXES), ('group_weights', (*BASE_GROUPS, ITEM))]:
        weights = policy[field]
        _need(isinstance(weights, dict) and set(weights) == set(keys)
              and all(type(w) is int and 0 < w < 100 for w in weights.values())
              and sum(weights.values()) == 100, 'Score modes need fixed weights totaling 100')
    return policy, _hash(raw)


def _score(value):
    return type(value) in (int, float) and 0 <= value <= 100


def _text(value):
    return isinstance(value, str) and bool(value.strip())


def criteria_from_review(contract, review, policy):
    """Count only the private contract's required gates, exposing no gate identifiers."""
    criteria = {}
    for axis in AXES:
        required = [spec['id'] for spec in contract['gates'][axis] if spec['required']]
        _need(len(required) == policy['strict_criteria'][axis], 'Required gate count differs from score-modes policy')
        verdicts = [review['gates'][axis][key]['verdict'] for key in required]
        _need(all(v is None or type(v) is bool for v in verdicts), 'Required gate must be true, false or unresolved')
        criteria[axis] = dict(planned=len(required), passed=verdicts.count(True), unknown=verdicts.count(None))
    return criteria


def validate_mc_review(review, source_review, source_raw, state):
    """Check a positive-credit supplement against the exact reliable review and three seals."""
    _need(isinstance(review, dict) and set(review) == {'schema', 'reviewer_id', 'reviewer_context_id',
          'reviewer_kind', 'human_review', 'source_review_sha256', 'registration_sha256', 'sealed_finals',
          'axes', 'error_deductions', 'no_mathematical_errors'}
          and review['schema'] == MC_REVIEW and review['reviewer_kind'] == 'ai' and review['human_review'] == 'pending'
          and _text(review['reviewer_id']) and _text(review['reviewer_context_id'])
          and review['source_review_sha256'] == _hash(source_raw)
          and review['registration_sha256'] == source_review['registration_sha256']
          and review['sealed_finals'] == source_review['sealed_finals']
          and type(review['no_mathematical_errors']) is bool
          and isinstance(review['axes'], dict) and set(review['axes']) == set(AXES),
          'MC supplement must bind the selected review, registration and original seals')
    seals = flow._seals(state, review['registration_sha256'])
    _need(tuple(seals) == flow.ROUNDS and all(seals[r]['delivery'] == 'normal-final'
          and review['sealed_finals'][r] == _hash((state / f'{r}.seal.json').read_bytes()) for r in flow.ROUNDS),
          'MC supplement requires original normal finals')
    rounds = set(seals)
    scores, differences = {}, {}
    for axis, row in review['axes'].items():
        _need(isinstance(row, dict) and set(row) == {'mc_score', 'rmc_score', 'reason', 'evidence'}
              and _text(row['reason']), 'Invalid positive-credit axis judgment')
        mc, rmc = row['mc_score'], row['rmc_score']
        _need(rmc == source_review['axes'][axis]['score'] and (rmc is None or _score(rmc)),
              'Supplement RMC must equal the selected ordinary review')
        if rmc is None:
            _need(mc is None and row['evidence'] == [], 'Unadjudicated axis must remain unknown')
        else:
            _need(_score(mc) and rmc <= mc, 'MC must be independently assessed and at least RMC')
            flow._evidence(row['evidence'], state, seals, rounds)
        scores[axis] = mc
        differences[axis] = Fraction(str(mc)) - Fraction(str(rmc)) if mc is not None else Fraction()
    deductions = review['error_deductions']
    _need(isinstance(deductions, list) and (not review['no_mathematical_errors'] or not deductions),
          'A no-error judgment cannot list mathematical deductions')
    roots, totals = set(), dict.fromkeys(AXES, Fraction())
    for row in deductions:
        _need(isinstance(row, dict) and set(row) == {'id', 'axis', 'points', 'reason', 'evidence'}
              and _text(row['id']) and row['id'] not in roots and _text(row['reason'])
              and row['axis'] in AXES and scores[row['axis']] is not None and _score(row['points']),
              'A mathematical-error root must have one unique ID and one reviewed axis')
        flow._evidence(row['evidence'], state, seals, rounds)
        roots.add(row['id'])
        totals[row['axis']] += Fraction(str(row['points']))
    _need(totals == differences, 'Source-bound error deductions must reconcile MC minus RMC on each axis')
    return scores


def _authorize_recheck(base, ref, execution, original, effective):
    path, raw = baseline._external(base, ref)
    value = json.loads(raw)
    expected = dict(schema=RECHECK, decision='user-requested-recheck', execution_sha256=execution,
                    original_review_sha256=_hash(original), effective_review_sha256=_hash(effective))
    _need(isinstance(value, dict) and set(value) == set(expected) | {'reason', 'authorization'}
          and all(value[k] == v for k, v in expected.items()) and _text(value['reason']),
          'Recheck needs an explicit decision binding both reviews and the same execution')
    _, authorization = baseline._external(path.parent, value['authorization'])
    _need(authorization.strip(), 'Recheck decision needs the retained user request')
    return _hash(raw)


def _ordinary_review(base, review_ref, reviewer_ref, execution, run_root, registration, state, review_policy):
    review_path, raw = baseline._external(base, review_ref)
    review = json.loads(raw)
    _need(review.get('reviewer_kind') == 'ai' and review.get('human_review') == 'pending'
          and _text(review.get('reviewer_id')) and _text(review.get('reviewer_context_id'))
          and review.get('reviewer_context_id') not in {execution['context_id'], execution['native_context_id']},
          'Only an independent AI judgment with human review pending may be adopted')
    if execution['outcome'] == 'normal-finals':
        trajectory_review.validate_review(registration, state, review_path, review_policy)
    else:
        _need(set(review) == {'schema', 'execution_sha256', 'reviewer_kind', 'human_review',
              'reviewer_id', 'reviewer_context_id', 'conclusion', 'reason', 'evidence'}
              and review['schema'] == 'math-gauge.independent-research-operational-review/v1'
              and review['execution_sha256'] == execution['execution_sha256']
              and review['conclusion'] == 'confirmed-delivery-failed' and _text(review['reason']),
              'A delivery failure needs the original operational review')
        native = [r['wire_events'] for r in execution['rounds']]
        _need(review['evidence'] and all(ref in native for ref in review['evidence']),
              'Operational review must bind the original native events')
        for ref in review['evidence']:
            flow._read(run_root, ref)
    reviewer_hash = baseline._reviewer(base, reviewer_ref, review_path, review)
    _need(review_path.read_bytes() == raw, 'Selected review changed during verification')
    source = dict(execution=execution['execution_sha256'], review=_hash(raw), reviewer=reviewer_hash)
    return review, raw, _hash(baseline.encoded(source))


def _mc_supplement(base, row, effective, effective_raw, state, execution):
    ref, reviewer_ref = row['mc_review'], row['mc_reviewer_source']
    _need((ref is None) == (reviewer_ref is None), 'MC review and reviewer observation must be selected together')
    if ref is None:
        return dict.fromkeys(AXES), None, None
    _need(execution['outcome'] == 'normal-finals', 'MC supplement on failure needs separately admitted cutoff evidence')
    path, raw = baseline._external(base, ref)
    review = json.loads(raw)
    scores = validate_mc_review(review, effective, effective_raw, state)
    _, reviewer_raw = baseline._external(base, reviewer_ref)
    _need(json.loads(reviewer_raw).get('purpose') == MC_PURPOSE
          and review['reviewer_context_id'] not in {execution['context_id'], execution['native_context_id']},
          'MC reviewer needs the explicit post-observation calibration purpose and a separate context')
    reviewer_hash = baseline._reviewer(base, reviewer_ref, path, review)
    _need(path.read_bytes() == raw, 'MC supplement changed during verification')
    return scores, _hash(baseline.encoded(dict(review=_hash(raw), reviewer=reviewer_hash))), review['reviewer_context_id']


def prepare(selection_path, public_root):
    """Rebuild the public overlay from original private evidence, without writing it."""
    from .independent_research_execution import NATIVE_ORIGIN, load_plan, validate_execution

    public_root = flow._safe_absolute(public_root)
    selection_path = flow._safe_absolute(selection_path)
    raw = selection_path.read_bytes()
    source = json.loads(raw)
    _need(isinstance(source, dict) and set(source) == {'schema', 'plan', 'run_root', 'review_policy',
          'base_adoption', 'models'} and source['schema'] == SELECTION, 'Expected a score-modes selection')
    base = selection_path.parent
    base_path, base_raw = baseline._external(base, source['base_adoption'])
    _need(base_path == flow._contained(public_root, baseline.PUBLIC_PATH),
          'Selection must bind the installed original public index')
    adopted = baseline.validate_public(json.loads(base_raw))
    policy_path = flow._contained(public_root, POLICY_PATH.as_posix())
    policy, policy_hash = load_policy(policy_path)
    plan_path, plan_raw = baseline._external(base, source['plan'])
    plan, registration = load_plan(plan_path, public_root)
    run_root = flow._safe_absolute(source['run_root'])
    review_policy, review_policy_raw = baseline._external(base, source['review_policy'])
    _need(plan['baseline'] == adopted['source_binding'] and _hash(plan_raw) == adopted['batch_sha256']
          and [row['id'] for row in plan['cohort']] == adopted['planned_cohort']
          and (run_root / 'control/plan.json').read_bytes() == plan_raw
          and _hash(review_policy_raw) == adopted['review_policy_sha256']
          and trajectory_review.policy_sha256(registration, review_policy) == adopted['review_policy_sha256'],
          'Score modes must bind the original batch, execution and trajectory-review policy')
    case_path, case_root, case = flow.load_case(registration)
    contract = json.loads(flow._read(case_root, case['review_contract']))
    rows = source['models']
    _need(isinstance(rows, list) and rows and all(isinstance(row, dict) and set(row) == {'id', 'execution',
          'original_review', 'original_reviewer_source', 'effective_review', 'effective_reviewer_source',
          'recheck', 'mc_review', 'mc_reviewer_source'} and isinstance(row['id'], str) for row in rows),
          'Expected nonempty source-bound score-modes rows')
    ids = {row['id'] for row in rows}
    _need(len(ids) == len(rows) and ids <= set(adopted['cohort']),
          'Score modes require unique configurations already selected in the original index')

    selected, ordinary_contexts, mc_contexts, candidate_contexts = {}, set(), set(), set()
    for row in rows:
        identifier = row['id']
        old = adopted['models'][identifier]
        execution = validate_execution(run_root, row['execution'], plan)
        normal = execution['outcome'] == 'normal-finals'
        _need(execution['origin'] == NATIVE_ORIGIN and execution['model_id'] == identifier
              and execution['outcome'] in {'normal-finals', 'delivery-failed'}
              and old['status'] == ('reviewed' if normal else 'delivery-failed')
              and old['round_dispatches'] == len(execution['rounds'])
              and old['normal_rounds'] == sum(r['delivery'] == 'normal-final' for r in execution['rounds']),
              'Execution differs from the original adopted trajectory')
        execution = dict(execution, execution_sha256=row['execution']['sha256'])
        candidate_contexts.update((execution['context_id'], execution['native_context_id']))
        state = flow._contained(run_root, execution['state'])
        original, original_raw, original_hash = _ordinary_review(base, row['original_review'],
            row['original_reviewer_source'], execution, run_root, registration, state, review_policy)
        _need(original_hash == old['source_sha256']
              and (not normal or all(old['axes'][axis] == {k: original['axes'][axis][k] for k in ('score', 'strict')}
                                     for axis in AXES)), 'Original review differs from the selected v3 source')
        context = original['reviewer_context_id']
        _need(context not in ordinary_contexts, 'Ordinary reviews require independent contexts')
        ordinary_contexts.add(context)
        effective, effective_raw, effective_hash = original, original_raw, original_hash
        recheck = None
        if row['recheck'] is None:
            _need(row['effective_review'] == row['original_review']
                  and row['effective_reviewer_source'] == row['original_reviewer_source'],
                  'A different effective review requires explicit user recheck provenance')
        else:
            _need(normal, 'Reviewed score changes require three normal finals')
            effective, effective_raw, effective_hash = _ordinary_review(base, row['effective_review'],
                row['effective_reviewer_source'], execution, run_root, registration, state, review_policy)
            context = effective['reviewer_context_id']
            _need(effective_raw != original_raw and context not in ordinary_contexts,
                  'A recheck needs a distinct, independently reviewed source')
            ordinary_contexts.add(context)
            recheck = _authorize_recheck(base, row['recheck'], execution['execution_sha256'], original_raw, effective_raw)
        mc, mc_source, mc_context = _mc_supplement(base, row, effective, effective_raw, state, execution)
        if mc_context is not None:
            mc_contexts.add(mc_context)
        axes = effective['axes'] if normal else old['axes']
        selected[identifier] = dict(
            axes={axis: dict(mc=mc[axis], rmc=axes[axis]['score'], strict=axes[axis]['strict']) for axis in AXES},
            criteria=criteria_from_review(contract, effective, policy) if normal else _unknown_criteria(policy),
            original_source_sha256=original_hash, effective_source_sha256=effective_hash,
            recheck_sha256=recheck, mc_source_sha256=mc_source)
    _need(not (ordinary_contexts | mc_contexts) & candidate_contexts,
          'Candidate contexts cannot be reused for independent review')
    _need(selection_path.read_bytes() == raw and plan_path.read_bytes() == plan_raw
          and base_path.read_bytes() == base_raw and _hash(policy_path.read_bytes()) == policy_hash
          and _hash(case_path.read_bytes()) == plan['registration']['sha256']
          and review_policy.read_bytes() == review_policy_raw,
          'Score-mode sources changed during verification')
    cohort = [identifier for identifier in adopted['cohort'] if identifier in selected]
    value = dict(schema=SCHEMA, edition=EDITION, base_index_sha256=_hash(base_raw), policy_sha256=policy_hash,
                 cohort=cohort, models={identifier: selected[identifier] for identifier in cohort},
                 candidate_calls_by_adoption=0)
    return validate_public(value, adopted, _hash(base_raw), policy, policy_hash)


def _unknown_criteria(policy):
    return {axis: dict(planned=n, passed=0, unknown=n) for axis, n in policy['strict_criteria'].items()}


def _criteria_flag(row):
    if row['passed'] == row['planned']:
        return True
    if row['passed'] + row['unknown'] < row['planned']:
        return False
    return None


def validate_public(value, adopted, base_hash, policy, policy_hash):
    """Enforce the aggregate allowlist and bind it to the immutable v3 adoption."""
    is_hash = baseline._is_hash
    _need(isinstance(value, dict) and set(value) == {'schema', 'edition', 'base_index_sha256', 'policy_sha256',
          'cohort', 'models', 'candidate_calls_by_adoption'}
          and value['schema'] == SCHEMA and value['edition'] == EDITION
          and is_hash(base_hash) and value['base_index_sha256'] == base_hash
          and is_hash(policy_hash) and value['policy_sha256'] == policy_hash
          and type(value['candidate_calls_by_adoption']) is int and value['candidate_calls_by_adoption'] == 0,
          'Score modes overlay must bind the original index and its own policy')
    rows = value['models']
    _need(isinstance(rows, dict) and rows and set(rows) <= set(adopted['cohort'])
          and value['cohort'] == [identifier for identifier in adopted['cohort'] if identifier in rows],
          'Score modes must follow the selected original cohort')
    for identifier, row in rows.items():
        old = adopted['models'][identifier]
        _need(isinstance(row, dict) and set(row) == {'axes', 'criteria', 'original_source_sha256',
              'effective_source_sha256', 'recheck_sha256', 'mc_source_sha256'}
              and row['original_source_sha256'] == old['source_sha256'] and is_hash(row['effective_source_sha256'])
              and (row['recheck_sha256'] is None or is_hash(row['recheck_sha256']))
              and (row['mc_source_sha256'] is None or is_hash(row['mc_source_sha256']))
              and (row['recheck_sha256'] is None) == (row['original_source_sha256'] == row['effective_source_sha256'])
              and all(isinstance(row[k], dict) and set(row[k]) == set(AXES) for k in ('axes', 'criteria')),
              'Unexpected or unbound public score-mode row')
        failed = old['status'] == 'delivery-failed'
        if failed:
            _need(row['recheck_sha256'] is None and row['mc_source_sha256'] is None
                  and row['criteria'] == _unknown_criteria(policy), 'A delivery loss does not adjudicate mathematics')
        for axis in AXES:
            grade, criteria = row['axes'][axis], row['criteria'][axis]
            _need(isinstance(criteria, dict) and set(criteria) == {'planned', 'passed', 'unknown'}
                  and all(type(n) is int and n >= 0 for n in criteria.values())
                  and criteria['planned'] == policy['strict_criteria'][axis]
                  and criteria['passed'] + criteria['unknown'] <= criteria['planned'],
                  'Invalid fixed checkpoint coverage')
            _need(isinstance(grade, dict) and set(grade) == {'mc', 'rmc', 'strict'}
                  and (grade['rmc'] is None or _score(grade['rmc']))
                  and (grade['mc'] is None or (_score(grade['mc']) and grade['rmc'] is not None
                       and grade['mc'] >= grade['rmc'] and row['mc_source_sha256'] is not None))
                  and (row['mc_source_sha256'] is None or (grade['mc'] is None) == (grade['rmc'] is None))
                  and grade['strict'] is _criteria_flag(criteria), 'Invalid public score or strict flag')
            if row['recheck_sha256'] is None:
                _need(dict(score=grade['rmc'], strict=grade['strict']) == old['axes'][axis],
                      'Publish a revised ordinary grade only with a bound recheck')
    return value


def _point(value):
    return (value, value, value)


def _from_scalar(value):
    return _interval(None) if value is None else _point(Fraction(str(value)) / 100)


def _source_group(metric, *, signed):
    """Retain exact source values, signed RMC bounds and observed credit."""
    if metric is None:
        return _interval(None), Fraction()
    exact = metric['exact']
    keys = ('exact',) if exact is not None else ('lower', 'upper')
    lower_limit = -100 if signed else 0
    _need(all(type(metric[k]) in (int, float) and lower_limit <= metric[k] <= 100 for k in keys),
          'Invalid source category score bounds')
    if exact is not None:
        interval = _from_scalar(exact)
    elif signed:
        low, high = (Fraction(str(metric[k])) / 100 for k in ('lower', 'upper'))
        _need(low <= high, 'Source category bounds are reversed')
        interval = (low, high, None)
    else:
        interval = _interval({k: None if metric[k] is None else metric[k] / 100 for k in _FIELDS})
    known = metric.get('confirmed', 0) if exact is None else exact
    _need(type(known) in (int, float) and lower_limit <= known <= 100, 'Invalid confirmed category contribution')
    return interval, Fraction(str(known)) / 100


def _published(interval, confirmed, *, state=None):
    low, high, value = interval
    exact = _percent(value)
    result = dict(lower=exact if exact is not None else _bound(low, lower=True),
                  upper=exact if exact is not None else _bound(high, lower=False),
                  exact=exact, confirmed=_percent(confirmed))
    if state is not None:
        result['state'] = state
    return result


def _strict_interval(counts):
    passed, unknown = counts['passed'], counts['unknown']
    failed = counts['planned'] - passed - unknown
    return _average([_boolean(True)] * passed + [_boolean(False)] * failed + [_boolean(None)] * unknown)


def _criterion_state(interval, *, status, pending=False):
    if status != 'reviewed':
        return status
    if interval[2] is not None:
        return 'reviewed'
    return 'review-pending' if pending else 'insufficient-evidence'


def project_scores(base_reports, policy, *, adopted=None, overlay=None):
    """Aggregate one fixed task and every mode's own three retained baseline categories."""
    old_status = adopted['status'] if adopted is not None else 'not-run'
    status = 'not-tested' if old_status == 'not-run' else old_status
    raw_axes = adopted['axes'] if adopted is not None else {
        axis: dict(score=None, strict=None) for axis in AXES}
    axes = overlay['axes'] if overlay is not None else {
        axis: dict(mc=None, rmc=row['score'], strict=row['strict']) for axis, row in raw_axes.items()}
    criteria = overlay['criteria'] if overlay is not None else _unknown_criteria(policy)
    mode_parts = dict(MC={axis: _from_scalar(axes[axis]['mc']) for axis in AXES},
                      RMC={axis: _from_scalar(axes[axis]['rmc']) for axis in AXES},
                      SMC={axis: _strict_interval(criteria[axis]) for axis in AXES})
    weights = policy['group_weights']
    item_weights = [policy['item_weights'][axis] for axis in AXES]
    mode_metrics, overall, contributions = {}, {}, {}
    for mode, parts in mode_parts.items():
        pending = ((mode == 'MC' and (overlay is None or overlay['mc_source_sha256'] is None))
                   or (mode == 'SMC' and overlay is None))
        item = _average(list(parts.values()), item_weights)
        if status == 'delivery-failed' and mode != 'MC':
            item = _point(Fraction())
        metrics = {axis: _published(part, part[0], state=_criterion_state(part, status=status,
                   pending=pending and (mode != 'MC' or axes[axis]['rmc'] is not None)))
                   for axis, part in parts.items()}
        mode_metrics[mode] = dict(components=metrics,
            item=_published(item, item[0], state=_criterion_state(item, status=status, pending=pending)))
        groups = {key: _source_group(base_reports[mode]['metrics'].get(key), signed=mode == 'RMC')
                  for key in BASE_GROUPS}
        groups[ITEM] = item, item[0]
        total = _average([v[0] for v in groups.values()], [weights[key] for key in groups])
        known = _average([_point(v[1]) for v in groups.values()], [weights[key] for key in groups])[2]
        overall[mode] = _published(tuple(None if v is None else max(Fraction(), v) for v in total),
                                   max(Fraction(), known))
        contributions[mode] = {key: _published(
            _average([interval, _point(Fraction())], [weights[key], 100 - weights[key]]),
            _average([_point(confirmed), _point(Fraction())], [weights[key], 100 - weights[key]])[2])
            for key, (interval, confirmed) in groups.items()}

    stricts = {axis: grade['strict'] for axis, grade in axes.items()}
    strict_flag = False if status == 'delivery-failed' else flow._gate(list(stricts.values()))
    reviewed = sum(row['rmc'] is not None for row in axes.values())
    legacy = {mode: report['metrics']['overall'] for mode, report in base_reports.items()}
    return dict(status=old_status, legacy_scores={mode: score['exact'] if score['exact'] is not None
                else {k: score[k] for k in _FIELDS} for mode, score in legacy.items()},
        subscores={axis: grade['rmc'] for axis, grade in axes.items()}, strict_verdicts=stricts,
        item_strict=None if strict_flag is None else 100 * int(strict_flag),
        item_composite={k: mode_metrics['RMC']['item'][k] for k in _FIELDS},
        strict_overall={k: overall['SMC'][k] for k in _FIELDS}, strict_confirmed=overall['SMC']['confirmed'],
        composite_by_base={mode: {k: overall[mode][k] for k in _FIELDS} for mode in MODES},
        confirmed_by_base={mode: overall[mode]['confirmed'] for mode in MODES},
        score_modes=mode_metrics, criteria=criteria, category_points=contributions,
        coverage=dict(planned=1, reviewed=int(reviewed == len(AXES)), components_planned=len(AXES),
                      components_reviewed=reviewed))
