"""Source-bound admission of externally collected independent-research handoffs.

The operator format is retained as such. It is never converted into a native
execution receipt or inserted into the original GPT execution plan. Mathematical
judgments and explicitly delivered attachments are verified separately, then the
existing value and strict-credit projectors perform all score composition.
"""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import re
import shutil
import struct
import tempfile

from . import independent_research_handoff as handoff
from . import independent_research_review as trajectory_review
from . import independent_research_score_modes as modes
from . import independent_research_strict_credit as credit
from . import independent_research_value as value
from . import taste_v130 as flow

VERSION = '0.1.0'
SCHEMA = 'math-gauge.independent-research-external-results/v1'
REVIEW = 'math-gauge.independent-research-external-review/v1'
SELECTION = 'math-gauge.independent-research-external-selection/v1'
REAUDIT = 'math-gauge.independent-research-reaudit/v1'
AMENDMENT = 'math-gauge.external-research-review-amendment/v1'
PUBLIC_PATH = Path('protocol/mathematical-taste/v1.3.0/external-results.json')
POLICY_PATHS = {
    'value': value.POLICY_PATH,
    'strict_credit': credit.PATH,
    'item_weight': Path('protocol/mathematical-taste/v1.3.0/item-weight-policy.json'),
}
_need, _fields = flow._need, value._fields
ROUNDS = flow.ROUNDS
AXES = value.AXES
# These are observed request labels, not independently authenticated backend SKUs.
CONFIGURATIONS = {
    'claude-opus-5.5-max': ('claude-opus-5-5[1m]', 'max'),
    'claude-opus-5.5-xhigh': ('claude-opus-5-5[1m]', 'xhigh'),
    'claude-sonnet-5.5-max': ('claude-sonnet-5-5[1m]', 'max'),
    'kimi-3.1-pro-max': ('claude-kimi-k3.1-pro[1m]', 'max'),
    'deepseek-v4.1-flash-1017': ('ttsw-codex-deepseek-v4.1-flash', 'max'),
}


def encoded(data):
    return (json.dumps(data, ensure_ascii=False, indent=2, allow_nan=False) + '\n').encode()


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def descriptor(path, root):
    path, root = Path(path), Path(root)
    raw = path.read_bytes()
    return dict(path=path.relative_to(root).as_posix(), bytes=len(raw), sha256=digest(raw))


def _text(text):
    return isinstance(text, str) and bool(text.strip())


def _number(number, maximum=100):
    return type(number) in (int, float) and 0 <= number <= maximum


def _hash(number):
    return isinstance(number, str) and re.fullmatch(r'[0-9a-f]{64}', number) is not None


def policy_bindings(root):
    root = Path(root)
    return {key: digest((root / path).read_bytes()) for key, path in POLICY_PATHS.items()}


def _metadata_sidecar(path):
    if not path.name.startswith('._'):
        return False
    raw = path.read_bytes()
    if len(raw) < 26:
        return False
    magic, version, _, entries = struct.unpack('>II16sH', raw[:26])
    end = 26 + 12 * entries
    if magic != 0x00051607 or version not in (0x00010000, 0x00020000) or not entries or end > len(raw):
        return False
    regions, ids = [], set()
    for offset in range(26, end, 12):
        identifier, start, length = struct.unpack('>III', raw[offset:offset + 12])
        if identifier in ids or start < end or start + length > len(raw):
            return False
        ids.add(identifier)
        if length:
            regions.append((start, start + length))
    regions.sort()
    return all(left[1] <= right[0] for left, right in zip(regions, regions[1:]))


def validate_state(state, bundle):
    """Verify the unchanged handoff, ignoring only authenticated AppleDouble noise.

    The complete original container remains in the private archive. A temporary
    materialization omits transport sidecars only; no seal or response is edited.
    Unexpected mathematical/runtime files still fail the original strict reader.
    """
    state, bundle = map(flow._safe_absolute, (state, bundle))
    ignored, captured = [], {}
    with tempfile.TemporaryDirectory(prefix='mg-external-handoff-', dir=Path(tempfile.gettempdir()).resolve()) as directory:
        mirror = Path(directory) / 'state'
        mirror.mkdir()
        for source in state.rglob('*'):
            _need(not source.is_symlink(), 'External handoff contains a symbolic link')
            target = mirror / source.relative_to(state)
            if source.is_dir():
                target.mkdir(exist_ok=True, parents=True)
            elif source.is_file():
                if _metadata_sidecar(source):
                    ignored.append(descriptor(source, state))
                else:
                    target.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(source, target)
                    captured[source.relative_to(state).as_posix()] = digest(target.read_bytes())
            else:
                raise ValueError('External handoff contains a nonregular file')
        checked = handoff.check(bundle, mirror)
        _need(checked['kind'] == 'operator-attestation'
              and checked['sealed'] == dict.fromkeys(ROUNDS, 'normal-final')
              and checked['open_round'] is None and checked['next_round'] is None,
              'Only three fully sealed original normal finals can be adopted')
        session = value._json((mirror / 'session.json').read_bytes())
        metadata = (value._json(handoff._read_ref(mirror, session['metadata']))
                    if session['metadata'] is not None else None)
        files, seals, observations = {}, {}, {}
        previous_time = None
        for rid in ROUNDS:
            seal_raw = handoff.read_file(mirror, rid + '/seal.json')
            seal = value._json(seal_raw)
            obs = value._json(handoff._read_ref(mirror, seal['observation']))
            dispatched = handoff._stamp(obs['dispatched_at'])
            _need(previous_time is None or dispatched >= previous_time,
                  'A later round was dispatched before its parent was sealed')
            previous_time = handoff._stamp(seal['sealed_at'])
            for ref in [seal['final'], *seal['attachments']]:
                files[ref['path']] = handoff._read_ref(mirror, ref)
            seals[rid] = digest(seal_raw)
            observations[rid] = obs
        _need(all(digest(handoff.read_file(state, name)) == expected for name, expected in captured.items()),
              'External source changed during snapshot validation')
    return dict(session=session, checked=checked, files=files, seals=seals,
                metadata=metadata, observations=observations, ignored_transport_sidecars=ignored,
                session_sha256=captured['session.json'], snapshot_sha256=digest(encoded(captured)))


def validate_configuration(model_id, metadata):
    _need(model_id in CONFIGURATIONS and isinstance(metadata, dict), 'Missing external requested configuration')
    declaration = metadata.get('model')
    if isinstance(declaration, dict):
        observed = declaration.get('requested'), declaration.get('reasoning_effort')
    else:
        observed = metadata.get('model_requested'), metadata.get('effort')
    _need(observed == CONFIGURATIONS[model_id], 'External source model or effort differs from its selected label')


def validate_normalization(original, normalized):
    """Formatting adaptation cannot change the actual Sol 6.1 mathematical grades."""
    if original.get('schema') == REAUDIT:
        reviewer = original['reviewer']
        _need(original['candidate'] == normalized['model_id'] and original['edition'] == flow.EDITION
              and reviewer['kind'] == 'ai' and reviewer['human_review'] == 'pending'
              and reviewer['requested_model'] == normalized['reviewer']['requested_model'] == 'gpt-6.1-sol'
              and reviewer['requested_effort'] == normalized['reviewer']['requested_effort'] == 'max'
              and reviewer['context'] == normalized['reviewer']['reviewer_context_id']
              and reviewer['backend_identity_independently_verified'] is False
              and isinstance(original['source_bindings'], list) and original['source_bindings']
              and isinstance(original['evidence'], dict) and original['evidence']
              and {ref['round'] for ref in original['evidence'].values()} == set(ROUNDS),
              'Re-audit normalization changed its actual reviewer or candidate')
        for axis in AXES:
            source, target = original[axis], normalized[axis]
            rows = source['dimensions']
            _need(len({row['id'] for row in rows}) == len(rows)
                  and {row['id'] for row in rows} == set(target['directions'])
                  and source['MC'] == target['mc_score'] and source['RMC'] == target['rmc_score']
                  and not target['deductions']
                  and all(row['deductions'] == 0 and row['net'] == row['mc']
                          and row['mc'] == target['directions'][row['id']]['mc_points']
                          and row['strict_pass'] is target['directions'][row['id']]['verdict'] for row in rows)
                  and source['MC'] == sum(row['mc'] for row in rows)
                  and source['SMC_retained_net_credit'] == sum(row['net'] for row in rows if row['strict_pass'])
                  and source['all_gates_pass'] is all(row['strict_pass'] for row in rows),
                  'Re-audit normalization changed credit, deductions or a checkpoint')
        return
    identifier = normalized['model_id']
    aliases = {identifier}
    if identifier == 'deepseek-v4.1-flash-1017':
        aliases.add('deepseek-v4.1-flash-max')
    _need(original['model_id'] in aliases, 'Normalization borrowed a different model review')
    old_reviewer = original.get('reviewer', original)
    _need(old_reviewer['reviewer_context_id'] == normalized['reviewer']['reviewer_context_id']
          and old_reviewer['reviewer_kind'] == 'ai' and old_reviewer['human_review'] == 'pending',
          'Normalization changed the original review context or approval status')
    for axis in AXES:
        before, after = original[axis], normalized[axis]
        _need(all(before[key] == after[key] for key in ('mc_score', 'rmc_score')),
              'Normalization changed a mathematical score')
        if axis == 'taste':
            _need(before['sufficient_choices']['verdict'] == after['sufficient_choices']['verdict'],
                  'Normalization changed selection sufficiency')
            _need(set(before['aspects']) == set(after['directions']), 'Normalization changed taste coverage')
            for key, row in after['directions'].items():
                _need(row['mc_points'] == before['aspects'][key]['mc_points']
                      and row['verdict'] is before['gates'][key]['verdict'],
                      'Normalization changed a taste dimension or verdict')
        else:
            _need(set(before['directions']) == set(after['directions']), 'Normalization changed capacity coverage')
            for key, row in after['directions'].items():
                _need(all(row[k] == before['directions'][key][k] for k in ('mc_points', 'verdict')),
                      'Normalization changed capacity credit or a checkpoint')
        expected = {row['id']: (row.get('criterion', row.get('dimension')), row['points'])
                    for row in before['error_deductions']}
        actual = {row['id']: (row['criterion'], row['points']) for row in after['deductions']}
        _need(len(expected) == len(before['error_deductions']) and expected == actual,
              'Normalization changed or duplicated an original error deduction')
    _need(original['autonomy']['score'] == normalized['autonomy']['score']
          and {k: v['verdict'] for k, v in original['autonomy']['gates'].items()} ==
              {k: v['verdict'] for k, v in normalized['autonomy']['gates'].items()}
          and original['extension']['level'] == normalized['extension']['level'],
          'Normalization changed autonomy or the outside-core extension grade')


def check_evidence(refs, files, *, permitted=ROUNDS):
    _need(isinstance(refs, list) and refs, 'A judgment requires original delivered evidence')
    for ref in refs:
        _need(_fields(ref, ('round', 'file', 'sha256', 'start', 'end', 'quote'))
              and ref['round'] in permitted and ref['file'] in files
              and ref['file'].startswith(ref['round'] + '/'),
              'Evidence must name a delivered file in its actual round')
        raw = files[ref['file']]
        start, end = ref['start'], ref['end']
        _need(digest(raw) == ref['sha256'] and type(start) is int and type(end) is int
              and 0 <= start < end <= len(raw) and _text(ref['quote'])
              and raw[start:end] == ref['quote'].encode('utf-8'),
              'External review quote differs from the original UTF-8 bytes')


def _judgment(row, files, *, fields, permitted=ROUNDS):
    _need(_fields(row, (*fields, 'reason', 'evidence')) and _text(row['reason']),
          'Each judgment needs its defined fields, reason and original evidence')
    check_evidence(row['evidence'], files, permitted=permitted)


def _axis(row, files, keys, limits):
    _need(_fields(row, ('mc_score', 'rmc_score', 'directions', 'deductions'))
          and _fields(row['directions'], keys) and isinstance(row['deductions'], list),
          'An axis needs the complete fixed credit allocation')
    points, verdicts = {}, {}
    for key, detail in row['directions'].items():
        _judgment(detail, files, fields=('mc_points', 'verdict'))
        _need((detail['mc_points'] is None or _number(detail['mc_points'], limits[key]))
              and (detail['verdict'] is None or type(detail['verdict']) is bool),
              'Invalid credit or checkpoint verdict')
        points[key], verdicts[key] = detail['mc_points'], detail['verdict']
    counts = credit._counts(verdicts)
    mc, rmc = row['mc_score'], row['rmc_score']
    if mc is None:
        _need(rmc is None and all(p is None for p in points.values()) and not row['deductions'],
              'An unassessed axis cannot invent positive credit or deductions')
        interval = credit._unallocated(None, counts)
    else:
        _need(_number(mc) and _number(rmc) and rmc <= mc
              and all(p is not None for p in points.values()),
              'MC and RMC must be complete, ordered scores')
        roots, allocations = {}, {}
        for error in row['deductions']:
            _judgment(error, files, fields=('id', 'criterion', 'points'))
            _need(_text(error['id']) and error['id'] not in roots
                  and error['criterion'] in keys and _number(error['points']) and error['points'] > 0,
                  'A mathematical error root must be charged once per axis')
            roots[error['id']] = error['points']
            allocations[error['id']] = {key: error[key] for key in ('criterion', 'reason', 'evidence')}
        interval = credit._net_credit(points, allocations, roots, verdicts, dict(mc=mc, rmc=rmc), None,
            evidence_check=lambda refs: check_evidence(refs, files))
    return (dict(mc=mc, rmc=rmc, strict=modes._criteria_flag(counts)), counts,
            credit._bounds(interval))


def validate_review(review, state, *, model_id, policies, capacity_keys, autonomy_keys):
    """Validate independent AI judgments without creating a candidate receipt."""
    _need(_fields(review, ('schema', 'edition', 'model_id', 'reviewer', 'sealed_finals',
                          'policy_bindings', 'rounds', 'taste', 'capacity', 'autonomy',
                          'extension', 'error_roots'))
          and review['schema'] == REVIEW and review['edition'] == flow.EDITION
          and review['model_id'] == model_id and review['sealed_finals'] == state['seals']
          and review['policy_bindings'] == policies, 'External review source or policy changed')
    reviewer = review['reviewer']
    _need(_fields(reviewer, ('requested_model', 'requested_effort', 'reviewer_id', 'reviewer_context_id',
                            'reviewer_kind', 'human_review', 'backend_identity_independently_verified'))
          and reviewer['requested_model'] == 'gpt-6.1-sol' and reviewer['requested_effort'] == 'max'
          and reviewer['reviewer_kind'] == 'ai' and reviewer['human_review'] == 'pending'
          and reviewer['backend_identity_independently_verified'] is False
          and all(_text(reviewer[key]) for key in ('reviewer_id', 'reviewer_context_id'))
          and reviewer['reviewer_context_id'] != state['session']['session_id'],
          'A fresh Sol 6.1 Max AI review is required without invented backend or human approval')
    files = state['files']
    _need(_fields(review['rounds'], ROUNDS), 'All three manuscripts need an explicit review')
    for rid, row in review['rounds'].items():
        _judgment(row, files, fields=(), permitted=(rid,))
    taste = review['taste']
    _need(_fields(taste, ('mc_score', 'rmc_score', 'directions', 'deductions', 'sufficient_choices')),
          'Taste must explicitly assess the available selection')
    choice = taste['sufficient_choices']
    _judgment(choice, files, fields=('verdict',))
    _need(choice['verdict'] is None or type(choice['verdict']) is bool, 'Invalid selection-coverage judgment')
    _need(choice['verdict'] is True or taste['mc_score'] is None,
          'Insufficient choices cannot earn a high score for empty selection')
    _need(choice['verdict'] is True or taste['directions']['selection']['verdict'] is None,
          'Insufficient choices require an unresolved selection verdict')
    taste_part = {key: taste[key] for key in ('mc_score', 'rmc_score', 'directions', 'deductions')}
    t_grade, t_count, t_credit = _axis(taste_part, files, value.DIMENSIONS,
                                     dict(value=60, structure=20, selection=20))
    _need(len(capacity_keys) == 5 and len(set(capacity_keys)) == 5,
          'The original five distinct capacity directions are required')
    c_grade, c_count, c_credit = _axis(review['capacity'], files, capacity_keys,
                                     dict.fromkeys(capacity_keys, 20))
    autonomy = review['autonomy']
    _need(_fields(autonomy, ('score', 'gates')) and _number(autonomy['score'])
          and _fields(autonomy['gates'], autonomy_keys) and len(autonomy_keys) == 2,
          'Autonomy retains its original two-round judgment')
    for index, (rid, key) in enumerate(zip(ROUNDS[:2], autonomy_keys)):
        row = autonomy['gates'][key]
        # R2 may cite its parent to demonstrate an increment, but needs actual
        # R2 evidence and cannot borrow a future correction from R3.
        _judgment(row, files, fields=('verdict',), permitted=ROUNDS[:index + 1])
        _need(any(ref['round'] == rid for ref in row['evidence']), 'Autonomy needs progress in its own round')
        _need(row['verdict'] is None or type(row['verdict']) is bool, 'Invalid autonomy judgment')
    extension = review['extension']
    _need(_fields(extension, ('level', 'assessed_rounds', 'independent_question', 'outside_core',
                            'result_and_scope', 'value', 'reason', 'evidence'))
          and extension['level'] in (None, *value.EXTENSION)
          and extension['assessed_rounds'] == list(ROUNDS)
          and all(_text(extension[key]) for key in ('independent_question', 'outside_core',
                                                  'result_and_scope', 'value', 'reason')),
          'Extension is a separately reviewed outside-core opportunity')
    check_evidence(extension['evidence'], files)
    errors = review['error_roots']
    _need(isinstance(errors, list) and all(isinstance(r, dict) for r in errors)
          and len({r.get('id') for r in errors}) == len(errors), 'Duplicate global error root')
    by_root = {}
    for error in errors:
        _judgment(error, files, fields=('id', 'effects'))
        _need(_text(error['id']) and isinstance(error['effects'], dict)
              and set(error['effects']) <= set(AXES) and error['effects']
              and all(_text(reason) for reason in error['effects'].values()),
              'A shared error needs separate explanations of its affected abilities')
        by_root[error['id']] = error
    for axis in AXES:
        for charged in review[axis]['deductions']:
            _need(charged['id'] in by_root and axis in by_root[charged['id']]['effects'],
                  'A deduction must reference the single documented mathematical root')
    return dict(axes=dict(taste=t_grade, capacity=c_grade),
                criteria=dict(taste=t_count, capacity=c_count),
                strict_credit=dict(taste=t_credit, capacity=c_credit),
                extension_level=extension['level'])


def validate_public(index, *, policies=None, baseline_hash=None, model_ids=None):
    _need(_fields(index, ('schema', 'version', 'edition', 'source_kind', 'source_binding',
                         'policy_bindings', 'cohort', 'models', 'reviewer_kind', 'human_review',
                         'candidate_calls_by_adoption'))
          and index['schema'] == SCHEMA and index['version'] == VERSION and index['edition'] == flow.EDITION
          and index['source_kind'] == 'external-handoff-operator-attestation'
          and index['reviewer_kind'] == 'ai' and index['human_review'] == 'pending'
          and type(index['candidate_calls_by_adoption']) is int and index['candidate_calls_by_adoption'] == 0,
          'Invalid external public aggregate or extra private fields')
    _need(_fields(index['source_binding'], ('base_edition', 'baseline_sha256', 'adoption_sha256'))
          and index['source_binding']['base_edition'] == '1.2.0'
          and all(_hash(index['source_binding'][key]) for key in ('baseline_sha256', 'adoption_sha256'))
          and (baseline_hash is None or index['source_binding']['baseline_sha256'] == baseline_hash)
          and _fields(index['policy_bindings'], POLICY_PATHS)
          and all(_hash(v) for v in index['policy_bindings'].values())
          and (policies is None or index['policy_bindings'] == policies), 'External source or policy binding differs')
    _need(isinstance(index['models'], dict) and index['cohort'] == list(index['models'])
          and len(set(index['cohort'])) == len(index['cohort'])
          and set(index['cohort']) <= set(CONFIGURATIONS)
          and (model_ids is None or set(index['cohort']) <= set(model_ids)), 'Unexpected external model cohort')
    for mid, row in index['models'].items():
        _need(_text(mid) and _fields(row, ('status', 'axes', 'criteria', 'strict_credit', 'extension_level',
                                         'normal_rounds', 'round_dispatches', 'source_sha256'))
              and row['status'] == 'reviewed' and row['normal_rounds'] == row['round_dispatches'] == 3
              and _hash(row['source_sha256']) and row['extension_level'] in (None, *value.EXTENSION)
              and all(_fields(row[key], AXES) for key in ('axes', 'criteria', 'strict_credit')),
              'Invalid external result or leaked private inventory')
        for axis in AXES:
            grade, counts, bound = row['axes'][axis], row['criteria'][axis], row['strict_credit'][axis]
            _need(_fields(grade, ('mc', 'rmc', 'strict')) and _fields(counts, ('planned', 'passed', 'unknown'))
                  and all(type(v) is int and v >= 0 for v in counts.values())
                  and counts['planned'] == (3 if axis == 'taste' else 5)
                  and counts['passed'] + counts['unknown'] <= counts['planned']
                  and grade['strict'] is modes._criteria_flag(counts)
                  and (grade['mc'] is None and grade['rmc'] is None or _number(grade['mc'])
                       and _number(grade['rmc']) and grade['rmc'] <= grade['mc']), 'Invalid external axis aggregate')
            _need(_fields(bound, ('lower', 'upper', 'exact'))
                  and _number(bound['lower']) and _number(bound['upper'])
                  and bound['lower'] <= bound['upper']
                  and (bound['exact'] is None or bound['lower'] == bound['upper'] == bound['exact'])
                  and (grade['rmc'] is None or bound['upper'] <= grade['rmc']), 'Invalid strict net-credit bounds')
            direct = credit._direct(grade['rmc'], counts)
            if direct is not None:
                _need(bound == credit._bounds(direct), 'Direct strict credit must preserve its actual net RMC')
    return index


def load_public(public_root):
    root = Path(public_root)
    path = root / PUBLIC_PATH
    if not path.exists():
        return None
    baseline_raw = (root / 'site/data.json').read_bytes()
    baseline = value._json(baseline_raw)
    _need(baseline['benchmark_version'] == '1.2.0', 'External adoption requires the exact retained 1.2 baseline')
    return validate_public(value._json(path.read_bytes()), policies=policy_bindings(root),
                           baseline_hash=digest(baseline_raw), model_ids=[m['id'] for m in baseline['models']])


def project_model(base_reports, policy, public_row):
    """Use the existing shared T/C, strict-credit and overall projection, unchanged."""
    _need(policy['item_weights'] == dict(taste=2, capacity=1)
          and policy['group_weights'] == dict(written=30, lean=30, research=30, independent_open_research=10),
          'External projection requires the selected shared 2:1 item and 30/30/30/10 weights')
    retained = dict(axes=public_row['axes'], criteria=public_row['criteria'],
                    mc_source_sha256=public_row['source_sha256'])
    reviewed = dict(taste=public_row['axes']['taste'], criteria=public_row['criteria']['taste'],
                    extension_level=public_row['extension_level'])
    result = value.project_scores(base_reports, policy, adopted=dict(status=public_row['status']),
                                  retained=retained, review=reviewed)
    result = credit.project_scores(result, base_reports['SMC'], policy, row=public_row['strict_credit'])
    result['external_source_sha256'] = public_row['source_sha256']
    return result


def _absolute_ref(ref):
    _need(_fields(ref, ('path', 'bytes', 'sha256')) and type(ref['bytes']) is int
          and ref['bytes'] >= 0 and _hash(ref['sha256']), 'Invalid amendment source descriptor')
    path = flow._safe_absolute(ref['path'])
    raw = path.read_bytes()
    _need(len(raw) == ref['bytes'] and digest(raw) == ref['sha256'], 'Amendment source bytes changed')
    return raw


def amendment_parent(selection_path, proposal, public_root, *, _ancestors=()):
    """Verify the named correction and its fully replayable prior selection."""
    selection_path = flow._safe_absolute(selection_path)
    selected_raw = selection_path.read_bytes()
    selection = value._json(selected_raw)
    _need(digest(selected_raw) == proposal['source_binding']['adoption_sha256']
          and 'review_amendment' in selection, 'Correction must bind the actual selected proposal')
    amendment = value._json(_absolute_ref(selection['review_amendment']))
    _need(_fields(amendment, ('schema', 'edition', 'model_id', 'before_index', 'before_selection',
          'before_review', 'after_review', 'reevaluation', 'normalization_receipt', 'review_sources',
          'retained_fields', 'user_selection')) and amendment['schema'] == AMENDMENT
          and amendment['edition'] == flow.EDITION
          and amendment['retained_fields'] == ['rounds', 'autonomy', 'extension'],
          'Invalid named external review correction')
    authorization = amendment['user_selection']
    _need(_fields(authorization, ('source_kind', 'text', 'date', 'scope', 'human_mathematical_approval'))
          and authorization['source_kind'] == 'direct-user-message' and _text(authorization['text'])
          and authorization['scope'] == 'full-independent-reaudit'
          and authorization['human_mathematical_approval'] is False,
          'A review correction needs its explicit selection without invented human approval')
    before_raw = _absolute_ref(amendment['before_index'])
    _absolute_ref(amendment['before_selection'])
    prior = prepare(amendment['before_selection']['path'], public_root,
                    _ancestors=(*_ancestors, str(selection_path)))
    _need(encoded(prior) == before_raw, 'The archived parent index does not replay from its selected evidence')
    mid = amendment['model_id']
    _need(mid in prior['models'] and prior['cohort'] == proposal['cohort']
          and prior['policy_bindings'] == proposal['policy_bindings']
          and all(prior['source_binding'][key] == proposal['source_binding'][key]
                  for key in ('base_edition', 'baseline_sha256'))
          and {key for key in prior['models'] if prior['models'][key] != proposal['models'][key]} == {mid},
          'A correction must change only its named model, under the same cohort and policy')
    for key in ('status', 'extension_level', 'normal_rounds', 'round_dispatches'):
        _need(prior['models'][mid][key] == proposal['models'][mid][key],
              'A mathematical correction cannot rewrite execution or extension evidence')
    before = value._json(_absolute_ref(amendment['before_review']))
    after = value._json(_absolute_ref(amendment['after_review']))
    original = value._json(_absolute_ref(amendment['reevaluation']))
    _absolute_ref(amendment['normalization_receipt'])
    row = next(item for item in selection['models'] if item['id'] == mid)
    _need(row['review'] == amendment['after_review']['path']
          and row['original_review'] == amendment['reevaluation']['path']
          and before['model_id'] == after['model_id'] == original['candidate'] == mid
          and original['calibration']['old_review_read_only_after_blind_freeze']['sha256']
              == amendment['before_review']['sha256']
          and all(before[key] == after[key] for key in (*amendment['retained_fields'],
                                                       'sealed_finals', 'policy_bindings')),
          'The new review must preserve its original answers and explicitly retained judgments')
    parent_selection = value._json(_absolute_ref(amendment['before_selection']))
    parent_row = next(item for item in parent_selection['models'] if item['id'] == mid)
    _need(parent_row['review'] == amendment['before_review']['path'], 'Correction borrowed a different old review')
    snapshots = amendment['review_sources']
    _need(isinstance(snapshots, list) and len(snapshots) == len(original['source_bindings'])
          and len({item['original_path'] for item in snapshots}) == len(snapshots),
          'Review provenance needs its frozen source snapshots')
    retained = {item['original_path']: item['retained'] for item in snapshots}
    for ref in original['source_bindings']:
        frozen = retained.get(ref['path'])
        _need(frozen is not None and frozen['sha256'] == ref['sha256'] and frozen['bytes'] == ref['bytes'],
              'Re-audit provenance differs from its frozen original')
        _absolute_ref(frozen)
    validate_normalization(original, after)
    return before_raw


def prepare(selection_path, public_root, *, _ancestors=()):
    """Reproduce aggregate admission from private original handoffs and AI reviews."""
    selection_path, public_root = map(flow._safe_absolute, (selection_path, public_root))
    _need(str(selection_path) not in _ancestors and len(_ancestors) < 16, 'Cyclic or excessive amendment lineage')
    raw = selection_path.read_bytes()
    selection = value._json(raw)
    fields = ('schema', 'registration', 'review_policy', 'bundle', 'source_evidence', 'models')
    _need(_fields(selection, (*fields, 'review_amendment') if 'review_amendment' in selection else fields)
          and selection['schema'] == SELECTION and isinstance(selection['models'], list)
          and selection['models'], 'Expected a fixed external admission selection')
    registration = Path(selection['registration'])
    _, case, registered = flow.load_case(registration)
    trajectory_hash = trajectory_review.policy_sha256(registration, selection['review_policy'])
    evidence = selection['source_evidence']
    _need(isinstance(evidence, list) and evidence, 'Original containers and operational decisions are required')
    decisions, evidence_hashes = [], []
    for ref in evidence:
        _need(_fields(ref, ('path', 'bytes', 'sha256')) and type(ref['bytes']) is int
              and ref['bytes'] >= 0 and _hash(ref['sha256']), 'Invalid private source descriptor')
        source = flow._safe_absolute(ref['path'])
        _need(source.is_relative_to(selection_path.parent), 'Archive source must remain with its private selection')
        original = source.read_bytes()
        _need(len(original) == ref['bytes'] and digest(original) == ref['sha256'],
              'An original container or operational decision changed')
        evidence_hashes.append(ref['sha256'])
        if source.suffix == '.json':
            item = value._json(original)
            if isinstance(item, dict) and item.get('schema') == 'math-gauge.external-operational-user-confirmation/v1':
                decisions.append(item)
    if any(row.get('id') == 'deepseek-v4.1-flash-1017' for row in selection['models']):
        _need(len(decisions) == 1 and decisions[0]['model_id'] == 'deepseek-v4.1-flash-1017'
              and decisions[0]['source_kind'] == 'direct-user-message'
              and len(decisions[0]['decisions']) == 2
              and all(row['classification'] == 'user-confirmed-invalid-system-run'
                      for row in decisions[0]['decisions'])
              and set(decisions[0]['excluded_from']) == {'effective_model_attempts', 'mathematical_score',
                   'adopted_usage', 'adopted_cost', 'adopted_timing'}
              and decisions[0]['human_mathematical_approval'] is False,
              'DeepSeek system exclusions require the retained direct user confirmation')
    contract = value._json(flow._read(case, registered['review_contract']))
    bundle = Path(selection['bundle'])
    manifest, original_inputs = handoff.bundle_files(bundle)
    expected_inputs = {f'control-inputs/{rid}.md': flow._read(case, registered['rounds'][rid]) for rid in ROUNDS}
    expected_inputs['control-inputs/rules.md'] = flow._read(case, registered['rules'])
    expected_inputs.update({f'control-inputs/{ref["path"]}': flow._read(case, ref) for ref in registered['packet']})
    _need(all(original_inputs.get(key) == content for key, content in expected_inputs.items()),
          'External inputs differ from the registered task, body, rules or figures')
    policies = policy_bindings(public_root)
    models, sessions = {}, set()
    capacity_keys = [r['id'] for r in contract['gates']['capacity'] if r['required']]
    autonomy_keys = [r['id'] for r in contract['gates']['autonomy'] if r['required']]
    for selected in selection['models']:
        _need(_fields(selected, ('id', 'state', 'review', 'reviewer_observation', 'original_review'))
              and selected['id'] not in models, 'Duplicate or invalid external selection')
        state_root = Path(selected['state'])
        checked = validate_state(state_root, bundle)
        validate_configuration(selected['id'], checked['metadata'])
        _need(checked['session']['session_id'] not in sessions, 'Candidates cannot share a solver session')
        sessions.add(checked['session']['session_id'])
        review_path, observation_path = map(Path, (selected['review'], selected['reviewer_observation']))
        review_raw, observation_raw = review_path.read_bytes(), observation_path.read_bytes()
        review, observation = map(value._json, (review_raw, observation_raw))
        original_raw = Path(selected['original_review']).read_bytes()
        original = value._json(original_raw)
        validate_normalization(original, review)
        if original.get('schema') == REAUDIT:
            _need('review_amendment' in selection, 'A settled re-audit requires a source-bound amendment')
            for ref in original['evidence'].values():
                name = flow._safe_absolute(ref['file']).relative_to(state_root).as_posix()
                check_evidence([dict(round=ref['round'], file=name,
                    **{key: ref[key] for key in ('sha256', 'start', 'end', 'quote')})], checked['files'])
        _need(_fields(observation, ('schema', 'requested_model', 'requested_effort', 'reviewer_context_id',
                                   'reviewer_kind', 'human_review', 'backend_identity_independently_verified',
                                   'review_sha256', 'original_review_sha256'))
              and observation['schema'] == 'math-gauge.external-reviewer-observation/v1'
              and observation['requested_model'] == 'gpt-6.1-sol' and observation['requested_effort'] == 'max'
              and observation['reviewer_context_id'] == review['reviewer']['reviewer_context_id']
              and observation['reviewer_kind'] == 'ai' and observation['human_review'] == 'pending'
              and observation['backend_identity_independently_verified'] is False
              and observation['review_sha256'] == digest(review_raw)
              and observation['original_review_sha256'] == digest(original_raw),
              'External reviewer observation is unbound')
        grade = validate_review(review, checked, model_id=selected['id'], policies=policies,
                                capacity_keys=capacity_keys, autonomy_keys=autonomy_keys)
        source = digest(encoded(dict(review=digest(review_raw), reviewer=digest(observation_raw),
                                     session=checked['session_sha256'], seals=checked['seals'],
                                     snapshot=checked['snapshot_sha256'], trajectory_policy=trajectory_hash,
                                     operational_sources=evidence_hashes)))
        models[selected['id']] = dict(status='reviewed', **grade, normal_rounds=3, round_dispatches=3,
                                     source_sha256=source)
    baseline_raw = (public_root/'site/data.json').read_bytes()
    baseline = value._json(baseline_raw)
    order = [m['id'] for m in baseline['models'] if m['id'] in models]
    _need(set(order) == set(models), 'External selection includes a withdrawn or absent model')
    result = dict(schema=SCHEMA, version=VERSION, edition=flow.EDITION,
                  source_kind='external-handoff-operator-attestation',
                  source_binding=dict(base_edition='1.2.0', baseline_sha256=digest(baseline_raw),
                                      adoption_sha256=digest(raw)), policy_bindings=policies,
                  cohort=order, models={mid: models[mid] for mid in order}, reviewer_kind='ai',
                  human_review='pending', candidate_calls_by_adoption=0)
    _need(selection_path.read_bytes() == raw, 'External selection changed during admission')
    if 'review_amendment' in selection:
        amendment_parent(selection_path, result, public_root, _ancestors=_ancestors)
    return validate_public(result, policies=policies, baseline_hash=digest(baseline_raw), model_ids=order)
