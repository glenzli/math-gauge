"""Source-bound, evaluator-only mathematical traits for assessment edition1.1.

This owner validates independent judgments and publishes aggregate traits. The
shared scoring owner performs arithmetic; this module never runs a candidate or
changes a retained MC/RMC/SMC answer, judgment, selection or score.
"""
from copy import deepcopy
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path, PurePosixPath
import re

from .evidence_retention import read_bytes, is_file

VERSION = '0.3.0'
PREVIOUS_VERSION = '0.2.0'
LEGACY_VERSION = '0.1.0'
VERSIONS = (LEGACY_VERSION, PREVIOUS_VERSION, VERSION)
WHOLE_COMPLETION = 'all-visible-goals-per-task;whole-three-round-selfcheck;TX-baseline-only'
EDITION = '1.1.0'
CONDITION = 'nonlogical_retry_3'
AXES = ('proof', 'fidelity', 'completion', 'discernment', 'initiative', 'depth', 'closure')
BEHAVIOR = frozenset(AXES) - {'completion'}
FAMILIES = dict.fromkeys(AXES, 35)
LEGACY_FAMILIES = dict(zip(AXES, (20, 35, 35, 11, 6, 11, 11)))
POLICY_PATH = 'protocol/mathematical-profile.json'
INDEX_PATH = 'results/mathematical-profiles/v0.3.0/index.json'
_LEGACY_ANCHOR = ('protocol/mathematical-profile.md',
                  '98c40378e115a041649241a38cad3e4fa22a0b169fc21cf17683620badafdbb9')
_LEGACY_POLICY_SHA256 = 'de25ce588b61bf8e689f1f79202931b9467258df4c09ca4d13e4319bad0212a3'
_PREVIOUS_POLICY_SHA256 = 'b0ed9e2e9f50f248dcc0f060f12b1fcb513869c43d92bddb3936969574770158'
_PREVIOUS_ANCHOR = ('protocol/mathematical-profile.md',
                    'd19302d80c8ee2441f4f3f33f9e7089cc8d6f6c724a759170a9b693daf8e7268')
_HASH = re.compile(r'[0-9a-f]{64}\Z')


def _require(value, message):
    if not value:
        raise ValueError(message)


def _hash(value):
    return isinstance(value, str) and bool(_HASH.fullmatch(value))


def _text(value):
    return isinstance(value, str) and bool(value.strip()) and '\0' not in value


def index_path(version=VERSION):
    _require(version in VERSIONS, 'Unsupported mathematical-profile version')
    return 'results/mathematical-profiles/v' + version + '/index.json'


def _families(policy):
    return LEGACY_FAMILIES if policy['version'] == LEGACY_VERSION else FAMILIES


def _behavior(policy):
    return BEHAVIOR - {'closure'} if policy.get('version') == LEGACY_VERSION else BEHAVIOR


def _relative(value):
    _require(isinstance(value, str) and value and '\\' not in value
             and not any(ord(c) < 32 for c in value), 'Unsafe mathematical-profile source path')
    path = PurePosixPath(value)
    _require(not path.is_absolute() and str(path) == value
             and all(p not in {'', '.', '..', '.git'} and ':' not in p for p in value.split('/')),
             'Mathematical-profile sources require canonical relative paths')
    return value


def source_bytes(root, source):
    _require(isinstance(source, dict) and _hash(source.get('sha256')),
             'Mathematical-profile source lacks its SHA256')
    raw = read_bytes(Path(root) / _relative(source.get('path')))
    _require(hashlib.sha256(raw).hexdigest() == source['sha256'],
             'Mathematical-profile source bytes changed')
    if 'bytes' in source:
        _require(type(source['bytes']) is int and len(raw) == source['bytes'],
                 'Mathematical-profile source size changed')
    return raw


def validate_policy(policy):
    _require(isinstance(policy, dict) and policy.get('schema') == 'math-gauge.mathematical-profile-policy/v1',
             'Unsupported mathematical-profile policy')
    _require(policy.get('version') in VERSIONS, 'Unsupported mathematical-profile version')
    for key, value in (('benchmark_version', EDITION), ('condition', CONDITION),
                       ('reviewer_kind', 'ai'), ('human_review', 'pending')):
        _require(policy.get(key) == value, 'Unsupported mathematical-profile ' + key)
    _require(policy.get('new_candidate_calls') == 0 and policy.get('main_scores_modified') is False
             and policy.get('legacy_edition_profile') is False
             and policy.get('formal_comparison_eligible') is False,
             'Profiles cannot change candidate calls, main scores, eligibility or edition1.0')
    _require([a.get('id') for a in policy.get('axes', [])] == list(AXES)
             and policy.get('planned_families') == _families(policy)
             and _hash(policy.get('private_contract_sha256')), 'Profile axes or fixed families differ')
    for axis in policy['axes']:
        for field in ('label', 'description'):
            _require(set(axis.get(field, {})) == {'zh', 'en'}
                     and all(_text(v) for v in axis[field].values()), 'Profile axis needs bilingual copy')
    if policy['version'] == PREVIOUS_VERSION:
        previous = policy.get('previous_component', {})
        _require(previous.get('version') == LEGACY_VERSION
                 and previous.get('policy') == dict(path='protocol/mathematical-profile-v0.1.0.json',
                                                    sha256=_LEGACY_POLICY_SHA256)
                 and previous.get('anchors') == dict(path='protocol/mathematical-profile-v0.1.0.md',
                                                     sha256=_LEGACY_ANCHOR[1]),
                 'v0.2 must bind the exact immutable v0.1 policy and anchors')
    if policy['version'] == VERSION:
        previous = policy.get('previous_component', {})
        _require(previous == dict(version=PREVIOUS_VERSION,
                    policy=dict(path='protocol/mathematical-profile-v0.2.0.json',
                                sha256=_PREVIOUS_POLICY_SHA256),
                    anchors=dict(path='protocol/mathematical-profile-v0.2.0.md',
                                 sha256=_PREVIOUS_ANCHOR[1])),
                 'v0.3 must bind the exact immutable v0.2 policy and anchors')
        _require(policy.get('completion') == WHOLE_COMPLETION,
                 'v0.3 requires whole-task and whole-trajectory completion')
        _require(policy.get('fidelity_core_gate')
                 == 'any-required-core-scope-drift-without-delivered-bridge-caps-grade-at2',
                 'v0.3 must retain its source-reviewed fidelity core gate')
    return policy


def load_policy(root, *, version=None):
    path = POLICY_PATH
    if version in {LEGACY_VERSION, PREVIOUS_VERSION}:
        legacy = 'protocol/mathematical-profile-v' + version + '.json'
        if is_file(Path(root) / legacy):
            path = legacy
    elif version is not None:
        _require(version == VERSION, 'Unsupported mathematical-profile version')
    raw = read_bytes(Path(root) / path)
    policy = validate_policy(json.loads(raw))
    _require(version is None or policy['version'] == version, 'Profile policy version differs')
    anchor = policy['anchors']
    # The immutable v0.1 policy names the original current document. Resolve
    # that one exact old digest to its byte-identical frozen alias; never use an
    # alias for arbitrary policies or conceal a damaged source with a fallback.
    legacy_anchor = 'protocol/mathematical-profile-v' + policy['version'] + '.md'
    old_anchor = {LEGACY_VERSION:_LEGACY_ANCHOR, PREVIOUS_VERSION:_PREVIOUS_ANCHOR}.get(policy['version'])
    if (old_anchor is not None
            and (anchor.get('path'), anchor.get('sha256')) == old_anchor
            and is_file(Path(root) / legacy_anchor)):
        anchor = dict(anchor, path=legacy_anchor)
    source_bytes(root, anchor)
    if policy['version'] != LEGACY_VERSION:
        previous = policy['previous_component']
        predecessor = source_bytes(root, previous['policy'])
        _, predecessor_sha = load_policy(root, version=previous['version'])
        _require(hashlib.sha256(predecessor).hexdigest() == predecessor_sha,
                 'Profile predecessor differs from its frozen component')
        source_bytes(root, previous['anchors'])
    return policy, hashlib.sha256(raw).hexdigest()


def validate_contracts(contracts, policy):
    validate_policy(policy)
    _require(contracts.get('schema') == 'math-gauge.mathematical-profile-contracts/v1'
             and contracts.get('version') == policy['version'] and contracts.get('benchmark_version') == EDITION
             and contracts.get('condition') == CONDITION, 'Unsupported private profile contracts')
    _require(contracts.get('planned_families') == policy['planned_families'],
             'Private profile family plan differs')
    rows = contracts.get('tasks', [])
    _require(len(rows) == 42 and len({r['id'] for r in rows}) == 42
             and len({r['case_id'] for r in rows}) == 39
             and len({r['family_id'] for r in rows}) == 35, 'Profile task/family denominator differs')
    _require(sum(r['kind'] == 'initial' for r in rows) == 39
             and sum(r['kind'] == 'selfcheck' for r in rows) == 3, 'Profile trajectory denominator differs')
    for axis in AXES:
        relevant = [r for r in rows if axis in r['axis_weights']]
        _require(sum((Fraction(r['axis_weights'][axis]) for r in relevant), Fraction()) == 1
                 and all(Fraction(r['axis_weights'][axis]) > 0 for r in relevant)
                 and len({r['family_id'] for r in relevant}) == _families(policy)[axis],
                 'Profile weights or family count differ for ' + axis)
    for row in rows:
        _require(set(row['axis_weights']) <= set(AXES), 'Unknown profile axis')
        goals = row['goals']
        _require(goals and len({g['id'] for g in goals}) == len(goals)
                 and all(type(g['weight']) in (int, float) and g['weight'] > 0 for g in goals),
                 'Profile goals need fixed positive independent weights')
    if policy['version'] != LEGACY_VERSION:
        by_family = {}
        for row in rows:
            _require(set(row['axis_weights']) == set(AXES),
                     'Every v0.2 task must contribute to all seven axes')
            by_family.setdefault(row['family_id'], []).append(row)
        for variants in by_family.values():
            initial = [r for r in variants if r['kind'] == 'initial']
            rounds = [r for r in variants if r['kind'] == 'selfcheck']
            if rounds:
                _require(len(initial) == 1 and initial[0]['id'] == 'MG-C003:A1'
                         and {r['id'] for r in rounds} == {'MG-C003:R1', 'MG-C003:R2', 'MG-C003:R3'},
                         'Only the C003 family contains the fixed selfcheck trajectory')
            for row in variants:
                if rounds:
                    expected = Fraction(1, 70) if row['kind'] == 'initial' else Fraction(1, 210)
                else:
                    expected = Fraction(1, 35 * len(variants))
                _require(all(Fraction(value) == expected for value in row['axis_weights'].values()),
                         'v0.2 axes must preserve equal fixed family mass and C003 nesting')
    if policy['version'] == VERSION:
        _require(contracts.get('completion_rule') == WHOLE_COMPLETION,
                 'Private contracts must freeze whole-task and whole-trajectory acceptance')
    public = {r['id']: r for r in policy['public_task_contracts']}
    _require(len(public) == 28 and set(public) == {r['id'] for r in rows if r['public']},
             'Public profile contract projection differs')
    for row in rows:
        if not row['public']:
            continue
        projected = deepcopy(row)
        for goal in projected['goals']:
            goal['definition_evidence'] = [d for d in goal.get('definition_evidence', [])
                                           if d.get('repository') == 'public']
        _require(projected == public[row['id']], 'Public and private profile goals differ')
    return contracts


def _pointer(value, pointer):
    _require(isinstance(pointer, str) and (not pointer or pointer.startswith('/')),
             'Profile evidence needs a JSON pointer')
    for part in pointer.split('/')[1:] if pointer else []:
        part = part.replace('~1', '/').replace('~0', '~')
        try:
            if isinstance(value, list):
                _require(bool(re.fullmatch(r'0|[1-9][0-9]*', part)), 'Invalid profile array pointer')
                value = value[int(part)]
            else:
                value = value[part]
        except (KeyError, IndexError, TypeError, ValueError) as error:
            raise ValueError('Profile evidence pointer is missing') from error
    return value


def _delivery(material):
    state = material['selected_state']
    return (state.get('submission_assessment') or {}).get('classification',
                state.get('submission_classification'))


def manuscript_delivery_sources(public_root, private_root, model_id, record_id):
    """Expose exact selected manuscript deliveries, including bound companions.

    The manuscript source owner resolves the original inputs and archived bytes.
    This inventories evidence only; no observation count or judgment is imported.
    """
    from .manuscript_surplus import source_context, delivery_context
    context = delivery_context(private_root,
        source_context(public_root, private_root, model_id, record_id),
        'all_bound_additional_deliveries')
    return {'manuscript:' + cid + ':A1:' + doc['role']:
                dict(repository='private', **{k:doc[k] for k in ('path', 'bytes', 'sha256')})
            for cid, row in context['cases'].items() if row['source_status'] == 'reviewed'
            for doc in row['documents']}


class ProfileInputs:
    """Validated source-bound inputs for the shared scoring owner."""
    def __init__(self, review, policy, contracts, materials, *, roots, policy_sha256):
        contract_source = materials['sources']['contracts']
        _require(contract_source['sha256'] == policy['private_contract_sha256']
                 and json.loads(source_bytes(roots['private'], contract_source)) == contracts,
                 'Profile private contracts differ from the frozen bytes')
        validate_contracts(contracts, policy)
        validate_review(review, policy, contracts, materials,
                        roots=roots, policy_sha256=policy_sha256)
        self.review, self.policy, self.contracts, self.materials = (
            deepcopy(review), deepcopy(policy), deepcopy(contracts), deepcopy(materials))


def validate_review(review, policy, contracts, materials, *, roots, policy_sha256):
    _require(review.get('schema') == 'math-gauge.mathematical-profile-review/v1',
             'Unsupported mathematical-profile review')
    version = policy.get('version', review.get('version'))
    _require(version in VERSIONS, 'Unsupported mathematical-profile review version')
    for key, value in (('version', version), ('benchmark_version', EDITION), ('condition', CONDITION),
                       ('policy_sha256', policy_sha256), ('private_contract_sha256', policy['private_contract_sha256']),
                       ('reviewer_kind', 'ai'), ('human_review', 'pending')):
        _require(review.get(key) == value, 'Profile review differs in ' + key)
    _require(review.get('new_candidate_calls') == 0 and review.get('formal_comparison_eligible') is False
             and _text(review.get('reviewer_id')), 'Profile review cannot invent calls or human approval')
    _require(review.get('model_id') == materials.get('model_id')
             and materials.get('condition') == CONDITION
             and materials.get('policy_sha256') == policy_sha256
             and materials.get('private_contract_sha256') == policy['private_contract_sha256'],
             'Profile review does not match its selected source materials')
    if version != LEGACY_VERSION:
        _require(materials.get('version') == version and materials.get('new_candidate_calls') == 0,
                 'Profile materials differ in version or candidate calls')
        _validate_prior_profile(review, materials, roots, contracts=contracts)
    contracts_by_id = {r['id']: r for r in contracts['tasks']}
    originals = {r['id']: r for r in materials['tasks']}
    rows = review.get('tasks', [])
    _require(len(rows) == len(contracts_by_id) and {r['id'] for r in rows} == set(contracts_by_id)
             and set(originals) == set(contracts_by_id), 'Profile review has missing or duplicate slots')
    sources = materials['sources']
    raw_cache, json_cache = {}, {}

    def original(ident):
        if ident not in raw_cache:
            source = sources[ident]
            _require(source.get('repository') in roots, 'Unknown profile source repository')
            raw_cache[ident] = source_bytes(roots[source['repository']], source)
        return raw_cache[ident]

    def original_json(ident):
        if ident not in json_cache:
            json_cache[ident] = json.loads(original(ident))
        return json_cache[ident]

    # Bind all convenient indices and aliases back to the real selected chain.
    # A correct top-level record hash cannot authenticate a substituted task,
    # another model's score report or a different attempt hidden behind an alias.
    from .current_results import selected_current_record_paths, load_source_assessment
    from .editions import load_assessment_transition
    mid, public_root, private_root = review['model_id'], roots['public'], roots['private']
    selected_path = selected_current_record_paths(public_root).get(mid)
    _require(sources['public_source_record']['path'] == selected_path,
             'Profile source record is not selected for this model')
    original('public_source_record')
    from .current_assessment_admissions import selections, validate_private
    initial_ref = selections(public_root).get(mid)
    initial = initial_ref is not None
    binding_key = 'initial_assessment' if initial else 'calibration'
    inputs_key = 'initial_assessment_inputs' if initial else 'calibration_inputs'
    if initial:
        selected_binding = initial_ref
    else:
        selected_binding = load_assessment_transition(public_root)['calibrations'][mid]
    _require(all(sources[binding_key][k] == selected_binding[k] for k in ('path', 'sha256')),
             'Profile assessment is not selected for this model')
    public_binding = original_json(binding_key)
    if initial:
        private_ref = sources['private_initial_assessment']
        private_manifest, assessment_inputs = validate_private(public_root, private_root, mid,
            {k:private_ref[k] for k in ('path', 'bytes', 'sha256')})
    else:
        private_transition = json.loads(read_bytes(Path(private_root) / 'results/edition-reassessments/v1.1.0/transition.json'))
        private_manifest_raw = source_bytes(private_root, private_transition['calibrations'][mid])
        _require(hashlib.sha256(private_manifest_raw).hexdigest() == public_binding['private_manifest_sha256'],
                 'Profile private calibration differs from its public source binding')
        private_manifest = json.loads(private_manifest_raw)
    selected_report_ref = private_manifest['scores']['partial'][CONDITION]
    _require(all(sources['selected_report'][k] == selected_report_ref[k] for k in ('path', 'sha256'))
             and all(sources[inputs_key][k] == private_manifest['inputs'][k] for k in ('path', 'sha256')),
             'Profile report or inputs are not the condition-selected source')
    inputs_raw = original(inputs_key)
    _require(hashlib.sha256(inputs_raw).hexdigest() == public_binding['private_inputs_sha256'],
             'Profile private inputs differ from the public source binding')
    calibration_inputs = json.loads(inputs_raw)
    _require(calibration_inputs['model_id'] == mid, 'Profile inputs belong to another model')
    _, _, current_rates, _, _ = load_source_assessment(public_root, mid, selected_path)
    content_raw, goal_raw = original('content_review'), original('goal_review')
    _require(hashlib.sha256(content_raw).hexdigest() == current_rates['private_review_sha256']
             and hashlib.sha256(goal_raw).hexdigest() == current_rates['private_goal_review_sha256'],
             'Profile micro reviews are not the actual selected corrected trajectory')
    content_source, goal_source = original_json('content_review'), original_json('goal_review')
    selected_source = original_json('selected_report')
    selected_tasks = {t['case_id']:(i,t) for i,t in enumerate(selected_source['tasks'])}
    tx_inputs = {t['case_id']:t for t in calibration_inputs['conditions'][CONDITION]}
    allowed_report_prefixes = {}
    for slot, contract in contracts_by_id.items():
        material = originals[slot]
        ci, gi = material['content_index'], material['goal_index']
        _require(type(ci) is int and 0 <= ci < len(content_source['tasks'])
                 and content_source['tasks'][ci]['id'] == slot
                 and type(gi) is int and 0 <= gi < len(goal_source['tasks'])
                 and goal_source['tasks'][gi]['id'] == slot,
                 'Profile micro-review index belongs to another task')
        if contract['kind'] == 'selfcheck':
            number = int(slot.rsplit(':R', 1)[1])
            expected_state = next(r for r in selected_source['alignment_selfcheck']['rounds']
                                  if r['round'] == number)
            position = selected_source['alignment_selfcheck']['rounds'].index(expected_state)
            prefix = '/alignment_selfcheck/rounds/' + str(position)
        else:
            position, expected_state = selected_tasks[contract['case_id']]
            prefix = '/tasks/' + str(position)
        allowed_report_prefixes[slot] = prefix
        _require(material['selected_state'] == expected_state,
                 'Profile task state is not the actual condition-selected delivery')
        response_sha = expected_state.get('response_sha256')
        if contract['subcategory'] == 'theorem-extension':
            tx_source = tx_inputs[contract['case_id']]
            if tx_source.get('response'):
                response_sha = tx_source['response']['sha256']
            expected_tx = tx_source['review' if initial else 'new_review']
            alias = sources.get('tx-review:' + slot, {})
            _require(all(alias.get(k) == expected_tx[k] for k in ('path', 'sha256')),
                     'Profile TX evidence is another answer or attempt')
        _require(material['response_sha256'] == response_sha,
                 'Profile mathematical answer SHA differs from the selected task')
        answer = sources.get('answer:' + slot)
        _require((answer is None) == (material['raw_answer'] is None), 'Profile answer alias is unbound')
        if answer is not None:
            _require(answer == material['raw_answer'] and answer['sha256'] == response_sha,
                     'Profile answer alias is not the selected original answer')

    manuscript_aliases = {name for name in sources if name.startswith('manuscript:')}
    if manuscript_aliases:
        _require(version != LEGACY_VERSION, 'Bound manuscript companions require a modern profile component')
        record_id = Path(sources['public_source_record']['path']).parent.name
        delivered = manuscript_delivery_sources(public_root, private_root, mid, record_id)
        for name in manuscript_aliases:
            _require(name in delivered and sources[name] == delivered[name],
                     'Profile manuscript evidence is not an exact selected delivery')

    def evidence(entries, slot):
        _require(isinstance(entries, list) and entries, 'Every profile judgment needs source evidence')
        original_task = originals[slot]
        for entry in entries:
            _require(set(entry) == {'source_id', 'pointer', 'quote'}
                     and entry['source_id'] in sources and _text(entry['quote']),
                     'Unsupported or empty profile evidence')
            ident, pointer = entry['source_id'], entry['pointer']
            _require(ident in {'content_review', 'goal_review', 'selected_report'}
                     or ident in {'answer:' + slot, 'tx-review:' + slot}
                     or ident in manuscript_aliases and ident.startswith('manuscript:' + slot + ':'),
                     'Profile judgments require the selected task mathematical evidence')
            if ident in {'content_review', 'goal_review'}:
                index = original_task['content_index' if ident == 'content_review' else 'goal_index']
                prefix = '/tasks/' + str(index)
                _require(pointer == prefix or pointer.startswith(prefix + '/'),
                         'Profile evidence belongs to another task')
            if ident == 'selected_report':
                prefix = allowed_report_prefixes[slot]
                _require(pointer == prefix or pointer.startswith(prefix + '/'),
                         'Profile score-report evidence belongs to another task')
            if ident.startswith(('answer:', 'tx-review:')):
                _require(ident.split(':', 1)[1] == slot, 'Profile evidence uses another answer')
            raw = original(ident)
            if sources[ident]['path'].endswith('.json'):
                value = _pointer(original_json(ident), pointer)
                text = value if isinstance(value, str) else json.dumps(value, ensure_ascii=False)
            else:
                _require(pointer == '', 'Raw profile evidence cannot have a JSON pointer')
                text = raw.decode('utf-8')
            _require(entry['quote'] in text, 'Profile evidence quote does not match original bytes')

    for row in rows:
        contract = contracts_by_id[row['id']]
        expected = set(contract['axis_weights']) & _behavior({'version':version})
        _require(set(row.get('axes', {})) == expected, 'Profile behavior axes differ from task contract')
        if version == VERSION:
            _validate_fidelity_core(row['axes']['fidelity'])
        for judgment in row['axes'].values():
            grade = judgment.get('grade')
            _require(grade is None or type(grade) is int and 0 <= grade <= 4,
                     'Profile behavior grade must be integer0to4 or unknown')
            _require(_text(judgment.get('reason')), 'Profile judgment needs its mathematical reason')
            evidence(judgment.get('evidence'), row['id'])
            if version != LEGACY_VERSION:
                _validate_assessment_status(judgment, grade, originals[row['id']], goal=False)
        goals = row.get('goals', [])
        _require(len(goals) == len(contract['goals'])
                 and {g['id'] for g in goals} == {g['id'] for g in contract['goals']},
                 'Profile visible-goal contract differs')
        delivery = _delivery(originals[row['id']])
        for goal in goals:
            _require(goal.get('passed') is None or type(goal.get('passed')) is bool,
                     'Profile goal must be accepted, failed or unknown')
            if delivery in {'blank', 'forced_content'}:
                _require(goal['passed'] is False, 'An undelivered goal cannot earn completion')
            if delivery == 'not_run':
                _require(goal['passed'] is None, 'Unrun profile goals must remain unknown')
            _require(_text(goal.get('reason')), 'Profile goal needs its acceptance reason')
            evidence(goal.get('evidence'), row['id'])
            if version != LEGACY_VERSION:
                _validate_assessment_status(goal, goal['passed'], originals[row['id']], goal=True)
        research = row.get('research')
        if version != LEGACY_VERSION and research is None:
            continue
        if version == LEGACY_VERSION and contract['subcategory'] not in {'theorem-extension', 'manuscript-completion'}:
            _require(research is None, 'Research opportunity was not frozen for this task')
            continue
        _require(isinstance(research, dict) and (research.get('complete') is None
                 or type(research.get('complete')) is bool) and _text(research.get('reason')),
                 'Profile research needs its actual result register')
        _require(isinstance(research.get('results'), list)
                 and isinstance(research.get('unfinished_claims'), list)
                 and all(_text(v) for v in research['unfinished_claims']), 'Invalid research result register')
        evidence(research.get('evidence'), row['id'])
        for result in research['results']:
            _require(_text(result.get('statement')) and _text(result.get('scope'))
                     and type(result.get('substantive')) is bool
                     and (result.get('complete') is None or type(result.get('complete')) is bool),
                     'Research results need their actual scope and completion')
            evidence(result.get('evidence'), row['id'])
        if version == LEGACY_VERSION and contract['subcategory'] == 'theorem-extension' and research['complete'] is True:
            _require(delivery == 'active_final' and any(r['substantive'] and r['complete'] is True
                                                       for r in research['results']),
                     'TX completion needs an actually delivered substantive independent result')
        if delivery in {'blank', 'forced_content'}:
            _require(research['complete'] is False, 'Undelivered research cannot be completed')
        if delivery == 'not_run':
            _require(research['complete'] is None, 'Unrun research must remain unknown')
    return review


def _validate_fidelity_core(judgment):
    grade, failed = judgment.get('grade'), judgment.get('core_scope_failure')
    _require(failed is None if grade is None else type(failed) is bool,
             'v0.3 fidelity requires an explicit core-scope judgment; only unknown evidence stays unknown')
    _require(failed is not True or grade is not None and grade <= 2,
             'Unbridged drift of any required core scope cannot receive fidelity grade3or4')


def _validate_assessment_status(judgment, value, material, *, goal):
    status = judgment.get('assessment_status')
    _require(status in {'reviewed', 'operational_zero', 'not_run', 'source_unresolved'},
             'v0.2 profile judgments need a typed assessment status')
    _require((value is None) == (status in {'not_run', 'source_unresolved'}),
             'Only unrun or missing-source evidence may remain unknown')
    delivery = _delivery(material)
    if delivery == 'blank':
        _require(status == 'operational_zero' and value == (False if goal else 0),
                 'Settled blank deliveries must be assessed as operational zero')
    elif delivery == 'not_run':
        _require(status == 'not_run' and value is None,
                 'Unrun profile slots must remain unknown')
    else:
        _require(status != 'not_run', 'A delivered profile slot is not unrun')
    if status == 'operational_zero':
        _require(value == (False if goal else 0) and delivery in {'blank', 'forced_content'},
                 'Operational zero requires a settled nondelivery')
    if status == 'source_unresolved':
        _require(_text(judgment.get('missing_evidence')),
                 'Missing-source unknowns must identify the unavailable evidence')


def _validate_prior_profile(review, materials, roots, *, contracts=None):
    """Bind revisions to v0.1; permit an explicit first profile without one."""
    if review.get('version', materials.get('version')) == VERSION:
        return _validate_recent_profile(review, materials, roots, contracts=contracts)
    mid = review['model_id']
    legacy_policy, legacy_digest = load_policy(roots['public'], version=LEGACY_VERSION)
    legacy_index = Path(roots['public']) / index_path(LEGACY_VERSION)
    index = json.loads(read_bytes(legacy_index)) if is_file(legacy_index) else None
    if index is not None:
        _require(index.get('version') == LEGACY_VERSION and index.get('policy_sha256') == legacy_digest,
                 'Prior profile index differs from its immutable policy')
    sources = materials['sources']
    if index is None or mid not in index['models']:
        prefix = 'results/mathematical-profiles/v0.1.0/' + mid + '/'
        retained = any(is_file(Path(roots[repository]) / (prefix + name))
                       for repository,name in (('public','profile.json'),
                                               ('private','review.json'),
                                               ('private','source-bindings.json')))
        private_index = Path(roots['private']) / index_path(LEGACY_VERSION)
        if is_file(private_index):
            private = json.loads(read_bytes(private_index))
            _require(private.get('version') == LEGACY_VERSION
                     and private.get('policy_sha256') == legacy_digest,
                     'Private prior profile index differs from its immutable policy')
            retained = retained or mid in private['models']
        _require(not retained, 'A retained or incomplete v0.1 profile cannot use the initial-profile path')
        _require(review.get('review_origin') == 'initial_profile'
                 and not {'prior_profile_review','prior_profile_materials'} & set(sources),
                 'A first v0.2 profile needs explicit initial_profile origin and no invented predecessor')
        if contracts is not None:
            old_contracts = json.loads(source_bytes(roots['private'], dict(
                path='protocol/mathematical-profile/v0.1.0/contracts.json',
                sha256=legacy_policy['private_contract_sha256'])))
            _validate_unchanged_profile_contracts(contracts, old_contracts)
        return
    _require(review.get('review_origin', 'bound_revision') == 'bound_revision',
             'An existing v0.1 profile requires the bound-revision path')
    old_public = validate_public(json.loads(source_bytes(roots['public'], index['models'][mid])),
                                 legacy_policy, policy_sha256=legacy_digest)
    prior = {}
    for key, filename, digest_key in (
            ('prior_profile_review', 'review.json', 'private_review_sha256'),
            ('prior_profile_materials', 'source-bindings.json', 'private_materials_sha256')):
        source = sources.get(key, {})
        expected = 'results/mathematical-profiles/v0.1.0/' + mid + '/' + filename
        _require(source.get('repository') == 'private' and source.get('path') == expected
                 and source.get('sha256') == old_public[digest_key],
                 'v0.2 supplements require the exact retained v0.1 profile source')
        prior[key] = json.loads(source_bytes(roots['private'], source))
    old_review, old_materials = prior['prior_profile_review'], prior['prior_profile_materials']
    _require(all(value.get('model_id') == mid and value.get('version') == LEGACY_VERSION
                 and value.get('policy_sha256') == legacy_digest
                 and value.get('condition') == CONDITION for value in (old_review, old_materials)),
             'Prior profile evidence belongs to another model, policy or condition')
    _require(old_public['model_id'] == mid
             and old_public['source_record'] == {k:sources['public_source_record'][k] for k in ('path','sha256')},
             'Profile supplements cannot replace the original selected record')
    old_sources = old_materials['sources']
    _require(all(sources.get(key) == value for key,value in old_sources.items() if key != 'contracts'),
             'Profile supplements cannot replace retained source evidence aliases')
    _require({row['id']:row for row in materials['tasks']}
             == {row['id']:row for row in old_materials['tasks']},
             'Profile supplements cannot replace the original selected task states or answers')
    if contracts is not None:
        old_contracts = json.loads(source_bytes(roots['private'], old_sources['contracts']))
        _validate_unchanged_profile_contracts(contracts, old_contracts)


def _validate_recent_profile(review, materials, roots, *, contracts=None):
    """Bind v0.3 to the selected v0.2 review without changing old aliases."""
    mid, sources = review['model_id'], materials['sources']
    policy, digest = load_policy(roots['public'], version=PREVIOUS_VERSION)
    public_path = Path(roots['public']) / index_path(PREVIOUS_VERSION)
    private_path = Path(roots['private']) / index_path(PREVIOUS_VERSION)
    index = json.loads(read_bytes(public_path)) if is_file(public_path) else None
    private = json.loads(read_bytes(private_path)) if is_file(private_path) else None
    for value in (index, private):
        if value is not None:
            _require(value.get('version') == PREVIOUS_VERSION and value.get('policy_sha256') == digest,
                     'Prior v0.2 profile index differs from its immutable policy')
    keys = {'prior_component_review', 'prior_component_materials'}
    if index is None or mid not in index['models']:
        prefix = 'results/mathematical-profiles/v0.2.0/' + mid + '/'
        retained = any(is_file(Path(roots[repo]) / (prefix + name))
            for repo, name in (('public','profile.json'), ('private','review.json'),
                               ('private','source-bindings.json')))
        _require(not retained and (private is None or mid not in private['models']),
                 'A retained or incomplete v0.2 profile cannot be bypassed')
        _require(review.get('review_origin') == 'initial_profile' and not keys & set(sources),
                 'A first v0.3 profile needs explicit initial origin without an invented predecessor')
        old_contracts = json.loads(source_bytes(roots['private'], dict(
            path='protocol/mathematical-profile/v0.2.0/contracts.json',
            sha256=policy['private_contract_sha256'])))
    else:
        _require(private is not None and mid in private['models']
                 and review.get('review_origin', 'bound_revision') == 'bound_revision',
                 'An existing v0.2 profile requires its bound private predecessor')
        old_public = validate_public(json.loads(source_bytes(roots['public'], index['models'][mid])),
                                     policy, policy_sha256=digest)
        prior = {}
        for alias, key, digest_key in (
            ('prior_component_review','review','private_review_sha256'),
            ('prior_component_materials','source-bindings','private_materials_sha256')):
            source, expected = sources.get(alias, {}), private['models'][mid][key]
            _require(source == dict(repository='private', **expected)
                     and source.get('sha256') == old_public[digest_key],
                     'v0.3 requires the exact selected retained v0.2 profile source')
            prior[key] = json.loads(source_bytes(roots['private'], source))
        old_review, old_materials = prior['review'], prior['source-bindings']
        _require(all(value.get('model_id') == mid and value.get('version') == PREVIOUS_VERSION
                     and value.get('policy_sha256') == digest and value.get('condition') == CONDITION
                     for value in (old_review, old_materials)),
                 'Prior v0.2 evidence belongs to another model, policy or condition')
        _require(old_public['model_id'] == mid
                 and old_public['source_record'] == {k:sources['public_source_record'][k] for k in ('path','sha256')},
                 'Profile revisions cannot replace the selected original record')
        _require(all(sources.get(key) == value for key, value in old_materials['sources'].items()
                     if key != 'contracts') and materials['tasks'] == old_materials['tasks'],
                 'Profile revisions cannot replace retained source aliases, task states or answers')
        old_contracts = json.loads(source_bytes(roots['private'], old_materials['sources']['contracts']))
    if contracts is not None:
        _validate_unchanged_profile_contracts(contracts, old_contracts)


def _validate_unchanged_profile_contracts(contracts, old_contracts):
    unchanged = lambda rows: {row['id']:{k:v for k,v in row.items() if k != 'axis_weights'}
                              for row in rows}
    _require(unchanged(contracts['tasks']) == unchanged(old_contracts['tasks'])
             and contracts.get('source_goal_definition_sha256')
                 == old_contracts.get('source_goal_definition_sha256'),
             'v0.2 cannot replace visible goals, task scopes or mathematical family ownership')


_METRIC_KEYS = frozenset({'exact', 'confirmed', 'lower', 'upper', 'unknown_weight',
                          'reviewed_families', 'planned_families'})
_PUBLIC_KEYS = frozenset({'schema', 'version', 'benchmark_version', 'condition', 'model_id',
    'policy_sha256', 'private_review_sha256', 'private_materials_sha256', 'source_record',
    'source_calibration', 'metrics', 'groups', 'reviewer_kind', 'human_review',
    'formal_comparison_eligible', 'new_candidate_calls', 'main_scores_modified'})


def validate_public(report, policy, *, policy_sha256):
    validate_policy(policy)
    version, families = policy['version'], _families(policy)
    binding_key = 'source_initial_assessment' if 'source_initial_assessment' in report else 'source_calibration'
    expected_keys = (_PUBLIC_KEYS - {'source_calibration'}) | {binding_key}
    _require(set(report) == expected_keys
             and report['schema'] == 'math-gauge.mathematical-profile-model/v1'
             and report['version'] == version and report['benchmark_version'] == EDITION
             and report['condition'] == CONDITION and report['policy_sha256'] == policy_sha256,
             'Unsupported public mathematical profile')
    _require(report['reviewer_kind'] == 'ai' and report['human_review'] == 'pending'
             and report['formal_comparison_eligible'] is False and report['new_candidate_calls'] == 0
             and report['main_scores_modified'] is False
             and _hash(report['private_review_sha256']) and _hash(report['private_materials_sha256']),
             'Public profile must retain its AI review and source boundaries')
    for key in ('source_record', binding_key):
        source = report[key]
        _require(isinstance(source, dict) and set(source) == {'path', 'sha256'}
                 and _hash(source['sha256']), 'Public profile source contains unsupported fields')
        _relative(source['path'])
    _require(set(report['metrics']) == set(AXES), 'Public profile axes differ')
    for axis, metric in report['metrics'].items():
        _require(set(metric) == _METRIC_KEYS and metric['planned_families'] == families[axis]
                 and type(metric['reviewed_families']) is int
                 and 0 <= metric['reviewed_families'] <= families[axis],
                 'Public profile family coverage differs')
        for key in ('confirmed', 'lower', 'upper', 'unknown_weight'):
            value = metric[key]
            _require(type(value) in (int, float) and math.isfinite(value) and 0 <= value <= 100,
                     'Invalid public profile interval')
        exact = metric['exact']
        _require(exact is None or type(exact) in (int, float) and math.isfinite(exact)
                 and metric['lower'] == exact == metric['upper'], 'Invalid exact profile value')
        _require(metric['confirmed'] == metric['lower']
                 and metric['lower'] <= metric['upper']
                 and abs(metric['upper'] - metric['lower'] - metric['unknown_weight']) < 1e-8
                 and (exact is None) == (metric['unknown_weight'] > 0),
                 'Profile unknowns cannot be rescaled away')
    # Group scores are aggregate numbers only, never private task/family rows.
    if version != LEGACY_VERSION:
        _require(report['groups'] == {}, 'v0.2 profiles have no separately weighted research layers')
        return report
    _require(set(report['groups']) == {'depth', 'closure'}, 'Profile research layers differ')
    for groups in report['groups'].values():
        _require(set(groups) == {'theorem-extension', 'manuscript-completion'},
                 'Unsupported public research layer')
        for group, metric in groups.items():
            _require(set(metric) == {'exact', 'confirmed', 'lower', 'upper', 'planned_families', 'reviewed_families'}
                     and metric['planned_families'] == (6 if group == 'theorem-extension' else 5)
                     and type(metric['reviewed_families']) is int
                     and 0 <= metric['reviewed_families'] <= metric['planned_families'],
                     'Private research rows cannot enter the public profile')
            for key in ('confirmed', 'lower', 'upper'):
                value = metric[key]
                _require(type(value) in (int, float) and math.isfinite(value) and 0 <= value <= 100,
                         'Public research layers require finite aggregate numbers')
            _require(metric['confirmed'] == metric['lower'] <= metric['upper']
                     and (metric['exact'] is None and metric['lower'] != metric['upper']
                          or type(metric['exact']) in (int, float)
                          and metric['lower'] == metric['exact'] == metric['upper']),
                     'Public research layer interval is inconsistent')
    return report


def project_public(score, *, policy, policy_sha256, private_review_sha256,
                   private_materials_sha256, source_record, source_calibration=None, source_initial_assessment=None):
    """Explicit allowlist: no private ids, reasons, quotes, raw paths or judgments."""
    _require(score.get('version') == policy['version'], 'Profile score and policy versions differ')
    report = dict(schema='math-gauge.mathematical-profile-model/v1', version=policy['version'],
        benchmark_version=EDITION, condition=CONDITION, model_id=score['model_id'],
        policy_sha256=policy_sha256, private_review_sha256=private_review_sha256,
        private_materials_sha256=private_materials_sha256,
        source_record={k:source_record[k] for k in ('path', 'sha256')},
        **({'source_calibration':{k:source_calibration[k] for k in ('path', 'sha256')}}
           if source_calibration is not None else {}),
        metrics=deepcopy(score['metrics']), groups=deepcopy(score['groups']),
        reviewer_kind='ai', human_review='pending', formal_comparison_eligible=False,
        new_candidate_calls=0, main_scores_modified=False)
    _require((source_calibration is None) != (source_initial_assessment is None),
             'Profile requires exactly one assessment provenance kind')
    key = 'source_initial_assessment' if source_initial_assessment is not None else 'source_calibration'
    source = source_initial_assessment if source_initial_assessment is not None else source_calibration
    report[key] = {k:source[k] for k in ('path', 'sha256')}
    return validate_public(report, policy, policy_sha256=policy_sha256)


def load_public_profiles(root, models, *, benchmark_version, component_version=None):
    """Load the independently reviewed1.1 layer; edition1.0 never inherits it."""
    if benchmark_version != EDITION:
        return None
    if (not is_file(Path(root) / POLICY_PATH)
            and not (component_version == LEGACY_VERSION
                     and is_file(Path(root) / 'protocol/mathematical-profile-v0.1.0.json'))):
        return None
    policy, digest = load_policy(root, version=component_version)
    version, families = policy['version'], _families(policy)
    path = index_path(version)
    if not is_file(Path(root) / path):
        return None
    index = json.loads(read_bytes(Path(root) / path))
    _require(index.get('schema') == 'math-gauge.mathematical-profile-index/v1'
             and index.get('version') == version and index.get('benchmark_version') == EDITION
             and index.get('policy_sha256') == digest, 'Mathematical-profile index differs')
    from .current_results import selected_current_record_paths
    from .editions import load_assessment_transition
    selected = selected_current_record_paths(root)
    transition = load_assessment_transition(root)
    from .current_assessment_admissions import selections
    initial_selections = selections(root)
    values = []
    for model in models:
        mid = model['id']
        ref = index['models'].get(mid)
        if ref is None:
            metrics = {a:dict(exact=None, confirmed=0, lower=0, upper=100, unknown_weight=100,
                              reviewed_families=0, planned_families=families[a]) for a in AXES}
            values.append(dict(id=mid, metrics=metrics, groups={}, review_status='unreviewed'))
            continue
        report = validate_public(json.loads(source_bytes(root, ref)), policy, policy_sha256=digest)
        binding_key = 'source_initial_assessment' if mid in initial_selections else 'source_calibration'
        expected_binding = initial_selections[mid] if mid in initial_selections else transition['calibrations'][mid]
        _require(report['model_id'] == mid and report['source_record']['path'] == selected[mid]
                 and report.get(binding_key) == {k:expected_binding[k] for k in ('path', 'sha256')},
                 'Profile sources are not the selected answers for this model')
        source_bytes(root, report['source_record'])
        source_bytes(root, report[binding_key])
        values.append(dict(id=mid, metrics=report['metrics'], groups=report['groups'],
                           review_status='ai-reviewed', source=ref))
    return dict(schema='math-gauge.mathematical-profile/v1', version=version,
        benchmark_version=EDITION, axes=deepcopy(policy['axes']), models=values,
        reviewer_kind='ai', human_review='pending', new_candidate_calls=0,
        main_scores_modified=False, method='../../protocol/mathematical-profile'
            + ('' if version == VERSION else '-v' + version) + '.md')
