"""Bind the 1.3 value revision to the already-selected three-round evidence."""

from fractions import Fraction
import json
from pathlib import Path, PurePosixPath

from . import independent_research_adoption as adoption
from . import independent_research_score_modes as modes
from . import taste_v130 as flow
from .scoring import _average


VERSION = '0.2.0'
POLICY = 'math-gauge.independent-research-value-policy/v1'
REVIEW = 'math-gauge.independent-research-value-review/v1'
PUBLIC = 'math-gauge.independent-research-value-results/v1'
POLICY_PATH = modes.POLICY_PATH.with_name('value-policy.json')
POLICY_FILE = modes.POLICY_FILE.with_name(POLICY_PATH.name)
PUBLIC_PATH = POLICY_PATH.with_name('value-results.json')
SELECTION_PATH = 'control/score-mode-selections/modes-002.json'
AXES = ('taste', 'capacity')
DIMENSIONS = ('value', 'structure', 'selection')
EXTENSION = dict(E0=0, E1=0.25, E2=0.5, E3=1)
_need, _hash = flow._need, flow._sha


def _json(raw):
    def unique(pairs):
        result = dict(pairs)
        _need(len(pairs) == len(result), 'Duplicate JSON field in value review or source')
        return result

    return json.loads(raw, object_pairs_hook=unique)


def _fields(value, names):
    return isinstance(value, dict) and set(value) == set(names)


def load_policy(path=POLICY_FILE):
    raw = Path(path).read_bytes()
    policy = _json(raw)
    _need(_fields(policy, ('schema', 'version', 'edition', 'status', 'score_axes', 'item_weights',
          'group_weights', 'strict_criteria', 'taste_dimensions', 'extension_fractions',
          'extension_scope', 'capacity_source', 'base_results_sha256'))
          and policy['schema'] == POLICY and policy['version'] == VERSION and policy['edition'] == flow.EDITION
          and policy['status'] == 'local-user-selected-review-revision'
          and policy['score_axes'] == list(AXES) and policy['strict_criteria'] == dict(taste=3, capacity=5)
          and all(type(n) is int for n in policy['strict_criteria'].values())
          and _fields(policy['extension_fractions'], EXTENSION)
          and all(type(policy['extension_fractions'][k]) in (int, float) and policy['extension_fractions'][k] == v
                  for k, v in EXTENSION.items())
          and policy['extension_scope'] == 'profile-initiative-only'
          and policy['capacity_source'] == 'unchanged-selected-score-modes-v0.1.0'
          and adoption._is_hash(policy['base_results_sha256']), 'Invalid independent research value policy')
    for field, keys in [('item_weights', AXES), ('group_weights', (*modes.BASE_GROUPS, modes.ITEM)),
                        ('taste_dimensions', DIMENSIONS)]:
        weights = policy[field]
        _need(_fields(weights, keys) and all(type(w) is int and w > 0 for w in weights.values())
              and (field == 'item_weights' or sum(weights.values()) == 100), 'Invalid fixed value-policy weights')
    return policy, _hash(raw)


def _evidence(refs, finals, permitted):
    _need(isinstance(refs, list) and bool(refs), 'Expected evidence from the original sealed manuscripts')
    for ref in refs:
        _need(_fields(ref, ('round', 'file', 'start', 'end', 'quote')) and ref['round'] in permitted
              and ref['file'] == ref['round'] + '.md', 'Evidence must name the original round manuscript')
        raw = finals[ref['round']]
        start, end = ref['start'], ref['end']
        _need(type(start) is int and type(end) is int and 0 <= start < end <= len(raw),
              'Evidence must use a valid UTF-8 byte range')
        quote = raw[start:end].decode()
        _need(quote.strip() and quote == ref['quote'], 'Evidence must match the original manuscript bytes')


def validate_review(review, *, model_id, policy, policy_hash, effective_sha256, mc_sha256,
                    sealed_finals, finals):
    """Validate the frozen private review contract and return its allowlisted aggregates."""
    expected = dict(schema=REVIEW, version=VERSION, edition=flow.EDITION, model_id=model_id,
                    policy_sha256=policy_hash, source_review_sha256=effective_sha256,
                    source_mc_review_sha256=mc_sha256, sealed_finals=sealed_finals,
                    reviewer_kind='ai', human_review='pending')
    _need(_fields(review, (*expected, 'reviewer_id', 'reviewer_context_id', 'taste', 'extension'))
          and all(review[k] == v for k, v in expected.items())
          and all(adoption._is_hash(h) for h in (policy_hash, effective_sha256, mc_sha256, *sealed_finals.values()))
          and _fields(sealed_finals, flow.ROUNDS) and _fields(finals, flow.ROUNDS)
          and all(modes._text(review[k]) for k in ('reviewer_id', 'reviewer_context_id')),
          'Value review must bind the selected reviews, exact original seals and independent AI attribution')
    taste = review['taste']
    _need(_fields(taste, ('mc_score', 'rmc_score', 'aspects', 'gates', 'rounds', 'sufficient_choices',
                         'error_deductions'))
          and all(_fields(taste[k], DIMENSIONS) for k in ('aspects', 'gates'))
          and _fields(taste['rounds'], flow.ROUNDS), 'Expected only the defined taste judgments')

    def judgment(row, *fields, permitted=flow.ROUNDS):
        _need(_fields(row, ('reason', 'evidence', *fields)) and modes._text(row['reason']),
              'Each judgment needs its specified fields and a substantive reason')
        _evidence(row['evidence'], finals, permitted)

    for round_id, row in taste['rounds'].items():
        judgment(row, permitted=(round_id,))

    choice = taste['sufficient_choices']
    judgment(choice, 'verdict')
    _need(choice['verdict'] is None or type(choice['verdict']) is bool, 'Invalid choice-evidence verdict')
    points, verdicts = [], {}
    for name in DIMENSIONS:
        aspect, gate = taste['aspects'][name], taste['gates'][name]
        judgment(aspect, 'mc_points')
        judgment(gate, 'verdict')
        point, verdict = aspect['mc_points'], gate['verdict']
        _need(point is None or type(point) is int and 0 <= point <= policy['taste_dimensions'][name],
              'Taste credit exceeds its fixed dimension or is not an integer')
        _need(verdict is None or type(verdict) is bool, 'Strict taste verdict must be boolean or unresolved')
        points.append(point)
        verdicts[name] = verdict
    _need(choice['verdict'] is True or verdicts['selection'] is None,
          'Insufficient choices leave the selection verdict unresolved')
    mc, rmc = taste['mc_score'], taste['rmc_score']
    deductions = taste['error_deductions']
    _need(isinstance(deductions, list), 'Expected an array of source error roots')
    if mc is None:
        _need(rmc is None and all(point is None for point in points) and not deductions,
              'Unresolved taste credit cannot have points or deductions')
    else:
        _need(type(mc) is int and all(point is not None for point in points) and mc == sum(points)
              and modes._score(rmc) and rmc <= mc and choice['verdict'] is True,
              'Taste MC/RMC must reconcile to the assessed dimensions and sufficient choices')
        roots, total = set(), Fraction()
        for row in deductions:
            judgment(row, 'id', 'points')
            _need(modes._text(row['id']) and row['id'] not in roots and modes._score(row['points'])
                  and row['points'] > 0, 'Each source error root needs one positive deduction and unique ID')
            roots.add(row['id'])
            total += Fraction(str(row['points']))
        _need(total == Fraction(mc) - Fraction(str(rmc)), 'Taste deductions must reconcile MC minus RMC')

    extension = review['extension']
    _need(_fields(extension, ('level', 'reason', 'independent_question', 'outside_core', 'result_and_scope',
                              'value', 'evidence', 'assessed_rounds'))
          and (extension['level'] is None or isinstance(extension['level'], str) and extension['level'] in EXTENSION)
          and extension['assessed_rounds'] == list(flow.ROUNDS)
          and all(modes._text(extension[key]) for key in ('reason', 'independent_question', 'outside_core',
                                                         'result_and_scope', 'value')),
          'Expected an independent extension assessment of all three rounds')
    _evidence(extension['evidence'], finals, flow.ROUNDS)
    criteria = dict(planned=len(DIMENSIONS), passed=sum(v is True for v in verdicts.values()),
                    unknown=sum(v is None for v in verdicts.values()))
    return dict(taste=dict(mc=mc, rmc=rmc, strict=modes._criteria_flag(criteria)),
                criteria=criteria, extension_level=extension['level'])


def validate_public(value, adopted, retained, policy, policy_hash):
    """Reject extra private data and bind each aggregate to a selected normal trajectory."""
    expected = dict(schema=PUBLIC, version=VERSION, edition=flow.EDITION, policy_sha256=policy_hash,
                    base_results_sha256=policy['base_results_sha256'], candidate_calls_by_adoption=0)
    _need(_fields(value, (*expected, 'cohort', 'models')) and all(value[k] == v for k, v in expected.items())
          and type(value['candidate_calls_by_adoption']) is int and adoption._is_hash(policy_hash),
          'Value aggregates must bind their versioned policy and the retained score modes')
    rows = value['models']
    _need(isinstance(rows, dict) and set(rows) <= set(retained['cohort'])
          and value['cohort'] == [key for key in retained['cohort'] if key in rows],
          'Value aggregates must follow the retained model cohort')
    for identifier, row in rows.items():
        _need(adopted['models'][identifier]['status'] == 'reviewed'
              and _fields(row, ('taste', 'criteria', 'extension_level', 'source_sha256'))
              and adoption._is_hash(row['source_sha256'])
              and (row['extension_level'] is None or isinstance(row['extension_level'], str)
                   and row['extension_level'] in EXTENSION), 'Unexpected or unbound public value row')
        count, taste = row['criteria'], row['taste']
        _need(_fields(count, ('planned', 'passed', 'unknown'))
              and all(type(v) is int and v >= 0 for v in count.values()) and count['planned'] == len(DIMENSIONS)
              and count['passed'] + count['unknown'] <= count['planned'], 'Invalid public taste coverage')
        _need(_fields(taste, ('mc', 'rmc', 'strict')) and taste['strict'] is modes._criteria_flag(count)
              and (taste['mc'] is None and taste['rmc'] is None or type(taste['mc']) is int
                   and modes._score(taste['mc']) and modes._score(taste['rmc']) and taste['rmc'] <= taste['mc']),
              'Invalid public taste grades or strict flag')
    return value


def load_retained(public_root, policy):
    base_raw = flow._contained(public_root, adoption.PUBLIC_PATH).read_bytes()
    retained_raw = flow._contained(public_root, modes.PUBLIC_PATH.as_posix()).read_bytes()
    _need(_hash(retained_raw) == policy['base_results_sha256'], 'Retained score modes differ from the value-policy source')
    original = adoption.validate_public(_json(base_raw))
    old_policy, old_hash = modes.load_policy(flow._contained(public_root, modes.POLICY_PATH.as_posix()))
    retained = modes.validate_public(_json(retained_raw), original, _hash(base_raw), old_policy, old_hash)
    return original, retained, base_raw


def _source_descriptor(ref):
    _need(_fields(ref, ('path', 'bytes', 'sha256')) and isinstance(ref['path'], str)
          and type(ref['bytes']) is int and adoption._is_hash(ref['sha256']), 'Expected an exact archive descriptor')


def _archived(replay, old_root, ref, *, relative_to=''):
    """Use the archived bytes only, with exact lexical rebasing of absolute old-run paths."""
    _source_descriptor(ref)
    name = PurePosixPath(ref['path'])
    _need(name.as_posix() == ref['path'], 'Noncanonical original archive path')
    if name.is_absolute():
        _need(name.is_relative_to(old_root), 'An original path is outside the selected old run')
        relative = name.relative_to(old_root)
    else:
        relative = PurePosixPath(relative_to) / name
    return flow._read(replay, dict(ref, path=relative.as_posix()))


def _selected_originals(replay, old_root, row, retained):
    # The old public source hashes include execution, ordinary review and reviewer
    # observation bytes. Read those originals and the relevant seals only.
    selection_dir = str(PurePosixPath(SELECTION_PATH).parent)
    executive = _archived(replay, old_root, row['execution'])
    originals = {key: _archived(replay, old_root, row[key], relative_to=selection_dir) for key in
                 ('effective_review', 'effective_reviewer_source', 'mc_review', 'mc_reviewer_source')}
    execution, effective, mc = map(_json, (executive, originals['effective_review'], originals['mc_review']))
    hashes = {key: _hash(raw) for key, raw in originals.items()}
    effective_binding = adoption.encoded(dict(execution=_hash(executive), review=hashes['effective_review'],
                                              reviewer=hashes['effective_reviewer_source']))
    mc_binding = adoption.encoded(dict(review=hashes['mc_review'], reviewer=hashes['mc_reviewer_source']))
    registration = execution['registration_sha256']
    seals = effective['sealed_finals']
    capacity = retained['axes']['capacity']
    _need(_hash(effective_binding) == retained['effective_source_sha256']
          and _hash(mc_binding) == retained['mc_source_sha256']
          and execution['model_id'] == row['id'] and execution['outcome'] == 'normal-finals'
          and _fields(seals, flow.ROUNDS) and all(adoption._is_hash(value) for value in seals.values())
          and effective['registration_sha256'] == mc['registration_sha256'] == registration
          and mc['source_review_sha256'] == hashes['effective_review'] and mc['sealed_finals'] == seals
          and effective['axes']['capacity']['score'] == mc['axes']['capacity']['rmc_score'] == capacity['rmc']
          and effective['axes']['capacity']['strict'] is capacity['strict']
          and mc['axes']['capacity']['mc_score'] == capacity['mc'], 'Selected execution, original reviews or retained C differ')
    state = flow._contained(replay, execution['state'])
    finals, previous = {}, None
    _need([part['round'] for part in execution['rounds']] == list(flow.ROUNDS), 'Expected the selected three-round execution')
    for part in execution['rounds']:
        round_id, descriptor = part['round'], part['seal']
        _need(descriptor['path'] == f'{execution["state"]}/{round_id}.seal.json', 'Seal must belong to its selected round state')
        raw = _archived(replay, old_root, descriptor)
        seal = _json(raw)
        _need(_hash(raw) == seals[round_id] and seal['round'] == round_id and seal['previous'] == previous
              and seal['registration_sha256'] == registration and seal['delivery'] == part['delivery'] == 'normal-final'
              and seal['raw']['path'] == f'{round_id}.md', 'Original normal-final seal or its chain differs')
        finals[round_id] = flow._read(state, seal['raw'])
        _need(finals[round_id].decode().strip(), 'Original sealed final is empty')
        previous = seals[round_id]
    contexts = {execution['context_id'], execution['native_context_id'], effective['reviewer_context_id'],
                mc['reviewer_context_id']}
    return hashes['effective_review'], hashes['mc_review'], seals, finals, contexts


def prepare(replay_root, reviews_root, public_root):
    """Recompute the source-bound supplement using the retained local replay."""
    replay, reviews, public = map(flow._safe_absolute, (replay_root, reviews_root, public_root))
    policy_path = flow._contained(public, POLICY_PATH.as_posix())
    policy, policy_hash = load_policy(policy_path)
    adopted, retained, base_raw = load_retained(public, policy)
    selection_path = flow._contained(replay, SELECTION_PATH)
    selection_raw = selection_path.read_bytes()
    selection = _json(selection_raw)
    _need(_fields(selection, ('schema', 'plan', 'run_root', 'review_policy', 'base_adoption', 'models'))
          and selection['schema'] == modes.SELECTION and isinstance(selection['models'], list),
          'Expected the archived modes-002 selection')
    _source_descriptor(selection['base_adoption'])
    _need(selection['base_adoption']['sha256'] == _hash(base_raw)
          and selection['base_adoption']['bytes'] == len(base_raw), 'Selection differs from the original adoption index')
    old_root = PurePosixPath(selection['run_root'])
    _need(old_root.is_absolute() and old_root.as_posix() == selection['run_root'] and '..' not in old_root.parts,
          'Invalid archived run root')
    rows = selection['models']
    _need(all(_fields(row, ('id', 'execution', 'original_review', 'original_reviewer_source',
                           'effective_review', 'effective_reviewer_source', 'recheck', 'mc_review', 'mc_reviewer_source'))
              for row in rows) and [row['id'] for row in rows] == retained['cohort'],
          'Archived selection must match the score-mode cohort exactly')
    _need(reviews.is_dir() and not reviews.is_relative_to(public), 'Value reviews require a separate private directory')
    submitted = {path.name for path in reviews.iterdir()}
    _need(submitted <= set(retained['cohort']), 'Unexpected configuration in the private value review directory')
    projected, contexts, historical = {}, set(), set()
    for row in rows:
        identifier = row['id']
        if identifier not in submitted:
            continue
        _need(adopted['models'][identifier]['status'] == 'reviewed', 'A value review requires normal finals')
        effective, mc, seals, finals, old_contexts = _selected_originals(replay, old_root, row, retained['models'][identifier])
        review_path = flow._contained(reviews, f'{identifier}/review.json')
        notes_path = flow._contained(reviews, f'{identifier}/notes.md')
        review_raw, notes = review_path.read_bytes(), notes_path.read_bytes()
        _need(notes.decode().strip(), 'A separate readable explanation is required for each value review')
        review = _json(review_raw)
        grade = validate_review(review, model_id=identifier, policy=policy, policy_hash=policy_hash,
            effective_sha256=effective, mc_sha256=mc, sealed_finals=seals, finals=finals)
        context = review['reviewer_context_id']
        # One independent context may review a batch of models.
        contexts.add(context)
        historical.update(old_contexts)
        source_sha256 = _hash(adoption.encoded(dict(review=_hash(review_raw), notes=_hash(notes))))
        projected[identifier] = dict(grade, source_sha256=source_sha256)
    _need(not contexts & historical, 'Value review cannot reuse a selected candidate or earlier review context')
    _need(selection_path.read_bytes() == selection_raw and _hash(policy_path.read_bytes()) == policy_hash,
          'Value review sources changed during verification')
    value = dict(schema=PUBLIC, version=VERSION, edition=flow.EDITION, policy_sha256=policy_hash,
                 base_results_sha256=policy['base_results_sha256'], candidate_calls_by_adoption=0,
                 cohort=list(projected), models=projected)
    return validate_public(value, adopted, retained, policy, policy_hash)


def project_scores(base_reports, policy, *, adopted=None, retained=None, review=None):
    """Compose fixed-denominator T/C scores with the retained 1.2 groups."""
    old_status = adopted['status'] if adopted is not None else 'not-run'
    status = 'not-tested' if old_status == 'not-run' else old_status
    unknown = modes._unknown_criteria(policy)
    axes = dict(taste=(review or {}).get('taste', dict.fromkeys(('mc', 'rmc', 'strict'))),
                capacity=(retained or {}).get('axes', {}).get('capacity', dict.fromkeys(('mc', 'rmc', 'strict'))))
    criteria = dict(taste=(review or {}).get('criteria', unknown['taste']),
                    capacity=(retained or {}).get('criteria', {}).get('capacity', unknown['capacity']))
    parts = {mode: {axis: modes._from_scalar(axes[axis][key]) for axis in AXES}
             for mode, key in [('MC', 'mc'), ('RMC', 'rmc')]}
    parts['SMC'] = {axis: modes._strict_interval(criteria[axis]) for axis in AXES}
    weights = policy['group_weights']
    item_weights = [policy['item_weights'][axis] for axis in AXES]
    missing = {'taste': review is None, 'capacity': retained is None}
    metrics, overall, contributions = {}, {}, {}
    zero = modes._point(Fraction())
    for mode, components in parts.items():
        item = _average(list(components.values()), item_weights)
        if status == 'delivery-failed' and mode != 'MC':
            item = zero
        pending = dict(missing)
        if mode == 'MC' and retained is not None and retained['mc_source_sha256'] is None:
            pending['capacity'] = True
        metrics[mode] = dict(components={axis: modes._published(part, part[0], state=modes._criterion_state(
            part, status=status, pending=pending[axis])) for axis, part in components.items()},
            item=modes._published(item, item[0], state=modes._criterion_state(item, status=status,
                                                                              pending=any(pending.values()))))
        groups = {key: modes._source_group(base_reports[mode]['metrics'].get(key), signed=mode == 'RMC')
                  for key in modes.BASE_GROUPS}
        groups[modes.ITEM] = item, item[0]
        total = _average([v[0] for v in groups.values()], [weights[key] for key in groups])
        known = _average([modes._point(v[1]) for v in groups.values()], [weights[key] for key in groups])[2]
        overall[mode] = modes._published(tuple(None if v is None else max(Fraction(), v) for v in total),
                                         max(Fraction(), known))
        contributions[mode] = {key: modes._published(
            _average([interval, zero], [weights[key], 100 - weights[key]]),
            _average([modes._point(confirmed), zero], [weights[key], 100 - weights[key]])[2])
            for key, (interval, confirmed) in groups.items()}

    def bounds(metric):
        return {key: metric[key] for key in ('lower', 'upper', 'exact')}

    strict = {axis: grade['strict'] for axis, grade in axes.items()}
    strict_flag = False if status == 'delivery-failed' else flow._gate(list(strict.values()))
    reviewed = sum(grade['rmc'] is not None for grade in axes.values())
    legacy = {mode: report['metrics']['overall'] for mode, report in base_reports.items()}
    level = (review or {}).get('extension_level')
    return dict(status=old_status, legacy_scores={mode: score['exact'] if score['exact'] is not None else bounds(score)
                for mode, score in legacy.items()}, subscores={axis: grade['rmc'] for axis, grade in axes.items()},
        autonomous_extension=dict(level=level, fraction=policy['extension_fractions'].get(level)), strict_verdicts=strict,
        item_strict=None if strict_flag is None else 100 * int(strict_flag), item_composite=bounds(metrics['RMC']['item']),
        strict_overall=bounds(overall['SMC']), strict_confirmed=overall['SMC']['confirmed'],
        composite_by_base={mode: bounds(metric) for mode, metric in overall.items()},
        confirmed_by_base={mode: metric['confirmed'] for mode, metric in overall.items()},
        score_modes=metrics, criteria=criteria, category_points=contributions,
        coverage=dict(planned=1, reviewed=int(reviewed == len(AXES)), components_planned=len(AXES), components_reviewed=reviewed))
