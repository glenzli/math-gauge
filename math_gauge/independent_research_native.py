"""Admit separately collected native research without rewriting a frozen batch.

This owner binds the retained native conversation, original seals and independent
AI judgments. Existing trajectory, MC and net-credit validators remain canonical;
the existing projectors delegate every weight and calculation to scoring.py.
"""
from pathlib import Path
import shutil
import tempfile

from . import independent_research_adoption as adoption
from . import independent_research_external as external
from . import independent_research_review as trajectory
from . import independent_research_score_modes as modes
from . import independent_research_strict_credit as credit
from . import independent_research_value as value
from . import taste_v130 as flow

SCHEMA = 'math-gauge.independent-research-native-results/v1'
SELECTION = 'math-gauge.independent-research-native-selection/v1'
PUBLIC_PATH = Path('protocol/mathematical-taste/v1.3.0/native-results.json')
SOURCE_KIND = 'native-agy-same-conversation-sealed-finals'
CONFIGURATIONS = {'gemini-4-hydrogen-xhigh': ('gemini-4-hydrogen', 'xhigh'),
                  'gemini-4-neon-xhigh': ('gemini-4-neon', 'xhigh')}
encoded, digest = external.encoded, external.digest
_need, _fields = flow._need, value._fields


def _read(base, ref):
    return adoption._external(base, ref)


def _judgment(row, state, seals, fields=()):
    _need(_fields(row, (*fields, 'reason', 'evidence')) and modes._text(row['reason']),
          'Native review judgment requires its original reason and evidence')
    flow._evidence(row['evidence'], state, seals, set(flow.ROUNDS))


def validate_scores(recommendation, review, mc, review_raw, state, contract, policies, model_id):
    """Bind the existing reviewer's final allocation, without making new judgments."""
    r = recommendation
    expected = ('schema', 'edition', 'case_id', 'candidate_configuration', 'status', 'reviewer',
        'source_review_sha256', 'registration_sha256', 'sealed_finals', 'state', 'policy_bindings',
        'score_meaning', 'autonomy', 'taste', 'capacity', 'extension', 'item_weights',
        'assessment_method', 'deduplication', 'candidate_calls_by_review', 'canonical_writes',
        'git_or_index_changes', 'human_review', 'item_score', 'item_score_exact_fractions')
    _need(_fields(r, expected) and r['schema'] == 'math-gauge.independent-review-current-score-recommendation/v1'
          and r['edition'] == flow.EDITION and r['source_review_sha256'] == digest(review_raw)
          and r['case_id'] == review['case_id'] and r['sealed_finals'] == review['sealed_finals']
          and r['registration_sha256'] == review['registration_sha256']
          and r['policy_bindings'] == policies and r['human_review'] == 'pending'
          and r['candidate_calls_by_review'] == 0 and r['item_weights'] == dict(taste=2, capacity=1),
          'Native current-score recommendation changed its original source or policy')
    config, reviewer = r['candidate_configuration'], r['reviewer']
    _need(_fields(config, ('requested_model', 'requested_effort', 'harness', 'backend_identity_independently_verified'))
          and (config['requested_model'], config['requested_effort']) == CONFIGURATIONS[model_id]
          and config['backend_identity_independently_verified'] is False,
          'Native request labels must not invent an independently verified backend')
    _need(_fields(reviewer, ('requested_model', 'requested_effort', 'reviewer_id', 'reviewer_context_id',
                            'reviewer_kind', 'human_review', 'backend_identity_independently_verified'))
          and all(reviewer[k] == v for k, v in adoption.REVIEWER.items())
          and all(reviewer[k] == review[k] == mc[k] for k in ('reviewer_id', 'reviewer_context_id')),
          'Native adoption requires the original independent Sol 6.1 Max AI attribution')
    seals = flow._seals(state, r['registration_sha256'])
    capacity = [row['id'] for row in contract['gates']['capacity'] if row['required']]
    axes, criteria, strict = {}, {}, {}
    for axis, keys, limits in [('taste', value.DIMENSIONS, dict(value=60, structure=20, selection=20)),
                              ('capacity', capacity, dict.fromkeys(capacity, 20))]:
        row = r[axis]
        _need(_fields(row, ('mc_score', 'rmc_score', 'smc', 'all_required_checkpoints', 'directions', 'error_deductions'))
              and _fields(row['directions'], keys)
              and row['mc_score'] == mc['axes'][axis]['mc_score']
              and row['rmc_score'] == review['axes'][axis]['score'],
              'Native allocation cannot change original MC or RMC')
        points, verdicts = {}, {}
        for key, detail in row['directions'].items():
            _need(_fields(detail, ('mc_points', 'verdict', 'reason', 'evidence', 'net_rmc_points')),
                  'Native allocation needs all original credit fields')
            _judgment({k: detail[k] for k in ('mc_points', 'verdict', 'reason', 'evidence')}, state, seals,
                      ('mc_points', 'verdict'))
            _need(credit._number(detail['mc_points'], limits[key]) and type(detail['verdict']) is bool,
                  'Native allocation exceeds the fixed credit budget')
            if axis == 'capacity':
                _need(detail['verdict'] is review['gates'][axis][key]['verdict'],
                      'Native capacity checkpoint changed its original judgment')
            points[key], verdicts[key] = detail['mc_points'], detail['verdict']
        roots, allocations = {}, {}
        for error in row['error_deductions']:
            _judgment(error, state, seals, ('id', 'criterion', 'points'))
            _need(error['id'] not in roots and error['criterion'] in keys and error['points'] > 0,
                  'A native error root must have one allocation per affected axis')
            roots[error['id']] = error['points']
            allocations[error['id']] = {k: error[k] for k in ('criterion', 'reason', 'evidence')}
        original = {error['id'].removesuffix('/' + axis): error['points']
                    for error in mc['error_deductions'] if error['axis'] == axis}
        _need(roots == original and all(root in {e['id'] for e in review['error_roots']} for root in roots),
              'Native net credit must retain every original mathematical deduction')
        grade = dict(mc=row['mc_score'], rmc=row['rmc_score'])
        interval = credit._net_credit(points, allocations, roots, verdicts, grade, None,
            evidence_check=lambda refs: flow._evidence(refs, state, seals, set(flow.ROUNDS)))
        count = credit._counts(verdicts)
        _need(row['smc'] == credit._bounds(interval)
              and row['all_required_checkpoints'] is modes._criteria_flag(count),
              'Native SMC must be retained strict net credit, not a checkpoint percentage')
        axes[axis], criteria[axis], strict[axis] = dict(grade, strict=modes._criteria_flag(count)), count, row['smc']
    autonomy = r['autonomy']
    _need(autonomy == dict(score=review['axes']['autonomy']['score'],
                          strict=review['axes']['autonomy']['strict'], not_in_item_score=True),
          'Autonomy stays a separate original assessment')
    extension = r['extension']
    _need(_fields(extension, ('level', 'assessed_rounds', 'independent_question', 'outside_core',
                             'result_and_scope', 'value', 'reason', 'evidence'))
          and extension['level'] in value.EXTENSION and extension['assessed_rounds'] == list(flow.ROUNDS)
          and all(modes._text(extension[k]) for k in ('independent_question', 'outside_core', 'result_and_scope', 'value')),
          'Native extension requires the actual separate outside-core judgment')
    flow._evidence(extension['evidence'], state, seals, set(flow.ROUNDS))
    return dict(axes=axes, criteria=criteria, strict_credit=strict,
                extension_level=extension['level'], autonomy_score=autonomy['score'])


def _retained(base, ref, model_id):
    path, raw = _read(base, ref)
    retained = value._json(raw)
    _need(retained['schema'] == 'math-gauge.private-test-evidence-retention/v1'
          and retained['model'] == model_id and retained['authentication_state_excluded'] is True
          and retained['original_source_bytes_unchanged'] is True,
          'Native admission requires retained original evidence without authentication state')
    source = flow._contained(path.parent, retained['retained_source_root'])
    for item in retained['files']:
        flow._read(source, item)
    return source, retained, digest(raw)


def _validate_trajectory(registration, state, review, review_policy):
    # The retained archive is intentionally inside the private repository. The
    # shared reviewer requires a separate evaluator materialization. Copy exact
    # sealed bytes only, without changing any original path or receipt.
    with tempfile.TemporaryDirectory(prefix='mg-native-review-') as directory:
        mirror = Path(directory).resolve() / 'state'
        source_files = {p.relative_to(state): p.read_bytes() for p in state.rglob('*') if p.is_file()}
        _need(not any(p.is_symlink() for p in state.rglob('*')), 'Native state cannot contain symbolic links')
        shutil.copytree(state, mirror)
        _need(all((mirror / name).read_bytes() == raw for name, raw in source_files.items()),
              'Native materialization changed original sealed bytes')
        trajectory.validate_review(registration, mirror, review, review_policy)
        _need(all((state / name).read_bytes() == raw for name, raw in source_files.items()),
              'Native source changed during trajectory validation')


def _archived_native(source, retained, ref):
    original = Path(ref['path'])
    relative = original.relative_to(Path(retained['original_runtime_root']))
    return flow._read(source, dict(path=relative.as_posix(), bytes=ref['bytes'], sha256=ref['sha256']))


def _validate_execution(source, retained, state, registered, completion, history, history_path, mid):
    """Keep the two actual native collection formats; never synthesize receipts."""
    if completion['schema'] == 'math-gauge.independent-research-local-completion/v1':
        _need(mid == 'gemini-4-hydrogen-xhigh' and completion['model'] == mid
              and completion['effort'] == CONFIGURATIONS[mid][1]
              and completion['native_cli_version'] == '1.5.12' and completion['normal_finals'] == 3
              and completion['transport_recovery']['same_native_context'] is True
              and completion['transport_recovery']['mathematical_feedback'] is False
              and completion['transport_recovery']['print_errors_preserved'] is True,
              'Native recovery must preserve the actual conversation and old errors')
        conversation = completion['native_conversation_id']
        declarations = completion['seals']
        terminals = ('SUCCESS', 'end_turn', 'end_turn')
    else:
        _need(completion['schema'] == 'math-gauge.agy-fresh-three-round-execution/v1'
              and mid == 'gemini-4-neon-xhigh' and completion['model'] == CONFIGURATIONS[mid][0]
              and completion['effort'] == CONFIGURATIONS[mid][1]
              and completion['fresh_session_new'] is True and completion['same_native_conversation'] is True
              and completion['normal_finals'] == completion['native_prompt_requests'] == 3
              and completion['failure'] is None and len(completion['rounds']) == 3,
              'Fresh ACP admission requires the actual three completed native rounds')
        files = {ref['path']: ref for ref in retained['files']}
        config = value._json(flow._read(source, files['control/config.json']))
        identity = value._json(flow._read(source, files['control/identity.json']))
        exited = value._json(flow._read(source, files['formal/process-exit-startup-recovery.json']))
        _need(config['client'] == 'agy' and config['model'] == mid and config['effort'] == CONFIGURATIONS[mid][1]
              and identity['version'] == '1.5.12' and exited['returncode'] == 0
              and exited['pid'] == completion['parent_pid_proof']['pid'],
              'Fresh ACP native identity, selected request or actual process exit differs')
        conversation = completion['native_session_id']
        declarations = [row['seal'] for row in completion['rounds']]
        terminals = ('end_turn',) * 3
        for rid, row in zip(flow.ROUNDS, completion['rounds']):
            _need(row['round'] == rid and row['delivery'] == 'normal-final'
                  and row['native_terminal'] == row['native_reply']['result']['stopReason'] == 'end_turn'
                  and row['failure'] is None, 'Fresh ACP round did not normally terminate')
            wire = _archived_native(source, retained, row['raw_events'])
            _need(value._json(wire.splitlines()[-1]) == row['native_reply'],
                  'Fresh ACP terminal differs from the original native wire reply')
            final = _archived_native(source, retained, row['visible_agent_message'])
            _need(final == (state / (rid + '.md')).read_bytes(),
                  'Fresh ACP final differs from the original sealed manuscript')
            observation = value._json((state / (rid + '.observation.json')).read_bytes())
            _need(observation['boundary']['at'] == row['boundary_at']
                  and observation['delivered_files'] == row['explicit_delivered_files'],
                  'Fresh ACP boundary or attachments differ from the original observation')
    _need(history['schema'] == 'math-gauge.native-conversation-retention/v1'
          and history['native_conversation_id'] == conversation
          and history['authentication_files_copied'] is False
          and history['opaque_native_history_not_used_as_mathematical_submission'] is True,
          'Native history remains operational evidence, separate from mathematical delivery')
    seals = flow._seals(state, value._json((state / 'session.json').read_bytes())['registration_sha256'])
    _need(tuple(seals) == flow.ROUNDS and len(declarations) == 3, 'Native adoption requires all three prescribed seals')
    for rid, seal, declared, terminal in zip(flow.ROUNDS, seals.values(), declarations, terminals):
        observation = value._json(flow._read(state, seal['observation']))
        issued = value._json((state / (rid + '.issued.json')).read_bytes())
        _need(seal['delivery'] == 'normal-final' and observation['kind'] == 'operator-attestation'
              and observation['first_normal_final'] is True and observation['native_terminal'] == terminal
              and observation['request_id'].startswith(conversation + '/')
              and issued['prompt_sha256'] == registered['rounds'][rid]['sha256']
              and digest((state / (rid + '.seal.json')).read_bytes()) == declared['sha256']
              and (state / (rid + '.seal.json')).stat().st_size == declared['bytes'],
              'A stale running record or old ERROR is not a native normal final')


def prepare(selection_path, public_root):
    """Produce an aggregate proposal only; no model calls and no source writes."""
    selection_path, public_root = map(flow._safe_absolute, (selection_path, public_root))
    raw = selection_path.read_bytes()
    selection = value._json(raw)
    _need(_fields(selection, ('schema', 'registration', 'review_policy', 'models'))
          and selection['schema'] == SELECTION and isinstance(selection['models'], list) and selection['models'],
          'Expected the separately selected native trajectory source')
    registration, _ = _read(selection_path.parent, selection['registration'])
    review_policy, _ = _read(selection_path.parent, selection['review_policy'])
    _, case, registered = flow.load_case(registration)
    trajectory_hash = trajectory.policy_sha256(registration, review_policy)
    contract = value._json(flow._read(case, registered['review_contract']))
    policies, models = external.policy_bindings(public_root), {}
    for selected in selection['models']:
        _need(_fields(selected, ('id', 'retention', 'native_history', 'completion', 'review', 'mc_review',
                                'recommendation', 'reviewer_observation'))
              and selected['id'] in CONFIGURATIONS and selected['id'] not in models,
              'Unexpected or duplicate selected native configuration')
        mid = selected['id']
        source, retained, retention_hash = _retained(selection_path.parent, selected['retention'], mid)
        state = flow._contained(source, retained['selected_state_relative'])
        paths, originals = {}, {}
        for name in ('completion', 'review', 'mc_review', 'recommendation', 'reviewer_observation', 'native_history'):
            paths[name], originals[name] = _read(selection_path.parent, selected[name])
        records = {name: value._json(content) for name, content in originals.items()}
        review, mc, completion = (records[k] for k in ('review', 'mc_review', 'completion'))
        _validate_trajectory(registration, state, paths['review'], review_policy)
        modes.validate_mc_review(mc, review, originals['review'], state)
        _need(review['reviewer_kind'] == 'ai' and review['human_review'] == 'pending',
              'Native admission cannot invent human approval')
        reviewer = records['reviewer_observation']
        _need(reviewer['schema'] == 'math-gauge.independent-review-preparation/v1'
              and reviewer['requested_model'] == 'gpt-6.1-sol'
              and reviewer['requested_reasoning_effort'] == 'max'
              and reviewer['reviewer_context_id'] == review['reviewer_context_id']
              and reviewer['reviewer_id'] == review['reviewer_id']
              and reviewer['reviewer_kind'] == 'ai' and reviewer['human_review'] == 'pending'
              and reviewer['backend_identity_independently_verified'] is False,
              'Native reviewer request configuration differs from original observation')
        _validate_execution(source, retained, state, registered, completion, records['native_history'],
                            paths['native_history'], mid)
        history = flow._read(paths['native_history'].parent, dict(path=records['native_history']['retained_path'],
            bytes=records['native_history']['bytes'], sha256=records['native_history']['sha256']))
        grade = validate_scores(records['recommendation'], review, mc, originals['review'],
                                state, contract, policies, mid)
        binding = digest(encoded(dict(originals={k: digest(v) for k, v in originals.items()},
            retained=retention_hash, native_history=digest(history), trajectory_policy=trajectory_hash)))
        models[mid] = dict(status='reviewed', **grade, normal_rounds=3, round_dispatches=3, source_sha256=binding)
    baseline_raw = (public_root / 'site/data.json').read_bytes()
    baseline = value._json(baseline_raw)
    _need(baseline['benchmark_version'] == '1.2.0', 'Native supplement needs the exact retained 1.2 baseline')
    order = [m['id'] for m in baseline['models'] if m['id'] in models]
    _need(set(order) == set(models) and selection_path.read_bytes() == raw, 'Selected native sources changed or model is absent')
    result = dict(schema=SCHEMA, version='0.1.0', edition=flow.EDITION, source_kind=SOURCE_KIND,
        source_binding=dict(base_edition='1.2.0', baseline_sha256=digest(baseline_raw), adoption_sha256=digest(raw)),
        policy_bindings=policies, cohort=order, models={mid: models[mid] for mid in order},
        reviewer_kind='ai', human_review='pending', candidate_calls_by_adoption=0)
    return validate_public(result, policies=policies, baseline_hash=digest(baseline_raw), model_ids=order)


def validate_public(index, *, policies=None, baseline_hash=None, model_ids=None):
    """Allow only aggregate scores and opaque source bindings into public files."""
    _need(_fields(index, ('schema', 'version', 'edition', 'source_kind', 'source_binding', 'policy_bindings',
                         'cohort', 'models', 'reviewer_kind', 'human_review', 'candidate_calls_by_adoption'))
          and index['schema'] == SCHEMA and index['version'] == '0.1.0' and index['edition'] == flow.EDITION
          and index['source_kind'] == SOURCE_KIND and index['reviewer_kind'] == 'ai'
          and index['human_review'] == 'pending' and type(index['candidate_calls_by_adoption']) is int
          and index['candidate_calls_by_adoption'] == 0, 'Invalid public native aggregate or private fields')
    binding = index['source_binding']
    _need(_fields(binding, ('base_edition', 'baseline_sha256', 'adoption_sha256'))
          and binding['base_edition'] == '1.2.0' and all(adoption._is_hash(binding[k]) for k in ('baseline_sha256', 'adoption_sha256'))
          and (baseline_hash is None or binding['baseline_sha256'] == baseline_hash)
          and _fields(index['policy_bindings'], external.POLICY_PATHS)
          and all(adoption._is_hash(v) for v in index['policy_bindings'].values())
          and (policies is None or index['policy_bindings'] == policies), 'Native source or policy binding differs')
    _need(isinstance(index['models'], dict) and index['models'] and index['cohort'] == list(index['models'])
          and set(index['cohort']) <= set(CONFIGURATIONS)
          and (model_ids is None or set(index['cohort']) <= set(model_ids)), 'Unexpected native cohort')
    for row in index['models'].values():
        _need(_fields(row, ('status', 'axes', 'criteria', 'strict_credit', 'extension_level', 'autonomy_score',
                           'normal_rounds', 'round_dispatches', 'source_sha256'))
              and row['status'] == 'reviewed' and row['normal_rounds'] == row['round_dispatches'] == 3
              and adoption._is_hash(row['source_sha256']) and row['extension_level'] in value.EXTENSION
              and modes._score(row['autonomy_score'])
              and all(_fields(row[k], value.AXES) for k in ('axes', 'criteria', 'strict_credit')),
              'Invalid native aggregate or leaked private inventory')
        for axis in value.AXES:
            grade, count, bound = row['axes'][axis], row['criteria'][axis], row['strict_credit'][axis]
            _need(_fields(grade, ('mc', 'rmc', 'strict')) and modes._score(grade['mc'])
                  and modes._score(grade['rmc']) and grade['rmc'] <= grade['mc']
                  and _fields(count, ('planned', 'passed', 'unknown'))
                  and all(type(v) is int and v >= 0 for v in count.values())
                  and count['planned'] == (3 if axis == 'taste' else 5)
                  and count['passed'] + count['unknown'] <= count['planned']
                  and grade['strict'] is modes._criteria_flag(count), 'Invalid native axis score or coverage')
            _need(_fields(bound, ('lower', 'upper', 'exact'))
                  and all(modes._score(bound[k]) for k in ('lower', 'upper'))
                  and bound['lower'] <= bound['upper'] <= grade['rmc']
                  and (bound['exact'] is None or bound['lower'] == bound['upper'] == bound['exact']),
                  'Invalid native strict net-credit interval')
            direct = credit._direct(grade['rmc'], count)
            _need(direct is None or bound == credit._bounds(direct), 'Direct native strict credit must retain its RMC')
    return index


def load_public(root):
    root = Path(root)
    path = root / PUBLIC_PATH
    if not path.is_file():
        return None
    raw = (root / 'site/data.json').read_bytes()
    baseline = value._json(raw)
    _need(baseline['benchmark_version'] == '1.2.0', 'Native supplement requires retained 1.2 data')
    return validate_public(value._json(path.read_bytes()), policies=external.policy_bindings(root),
                           baseline_hash=digest(raw), model_ids=[m['id'] for m in baseline['models']])


def project_model(base_reports, policy, public_row):
    result = external.project_model(base_reports, policy, public_row)
    result['native_source_sha256'] = result.pop('external_source_sha256')
    return result
