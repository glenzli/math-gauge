"""Exact normal AGY DB replies and lossless native-input projections.

Only an already timely first native SUCCESS can enter this branch. The raw
transport aggregate, CLI cleanup, original request and sealed DB stay separate.
This reader executes no candidate code and decodes only user19.2/reply20.1.
"""
import hashlib
import json
import math
from pathlib import Path, PurePosixPath
import sqlite3
import tempfile
from datetime import datetime

SCHEMA = 'math-gauge.agy-native-evidence/v2'
INPUT_SCHEMA = 'math-gauge.agy-lossless-input-source/v1'


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def same(a, b):
    return isinstance(a, dict) and isinstance(b, dict) and all(a.get(k) == b.get(k) for k in ('bytes', 'sha256'))


def receipt(root, row, data, phase, evidence):
    require(data.get('schema') == SCHEMA and data.get('post_observation') is True
            and data.get('source_raw_bytes_rewritten') is False
            and data.get('case_id') == row.get('case_id') and data.get('phase') == phase
            and phase in {'A1', 'R1', 'R2', 'R3'}
            and data.get('outcome') == 'response_received',
            'Visible-final admission needs its original normal case/phase')
    source = row.get('source', {})
    pairs = [(row.get('execution'), data['native_execution']),
             (source.get('native_execution'), data['native_execution']),
             (row.get('original_input'), data['input_projection']['original_task']),
             (row.get('candidate_input'), data['candidate_input']),
             (source.get('candidate_input'), data['candidate_input'])]
    require(all(a is None or same(a, b) for a, b in pairs),
            'Visible-final source selection changed native or logical input')
    return data


def _projected_messages(root, projection, phase, evidence):
    index = json.loads(evidence(root, projection['attachment_index']))
    require(index.get('schema') == 'math-gauge.exact-own-visible-history-attachments/v1',
            'Unknown lossless attachment ordering')
    sources = projection.get('attachment_sources', [])
    require(len(sources) == len({x['name'] for x in sources}), 'Repeated attachment source')
    sources = {x['name']: x['evidence'] for x in sources}
    messages, used = [], set()
    for i, row in enumerate(index['messages']):
        require(row.get('message_index') == i and row.get('role') in {'user', 'assistant'},
                'Visible input roles or ordering changed')
        pieces = []
        for part in row['parts']:
            name = part['file']
            require(isinstance(name, str) and PurePosixPath(name).name == name
                    and name not in {'.', '..'} and name not in used
                    and name in sources and same(part, sources[name]),
                    'Input fragment is absent, repeated or changed')
            raw = evidence(root, sources[name]); raw.decode('utf-8')
            pieces.append(raw); used.add(name)
        raw = b''.join(pieces)
        require(len(raw) == row['utf8_bytes'] and sha(raw) == row['sha256'],
                'Complete visible message changed')
        messages.append(dict(role=row['role'], content=raw.decode('utf-8')))
    # This second complete copy was also candidate-readable. Its own hash is
    # insufficient: it must encode precisely the same reconstructed messages.
    full = index['full_serialized_history']
    require(full['file'] in sources and same(full, sources[full['file']]),
            'Lossless transport lost its full serialized original')
    serialized = json.dumps({'messages': messages}, ensure_ascii=False, indent=2)
    if phase != 'A1':
        require(phase in {'R1', 'R2', 'R3'}, 'Unknown own-history serialization phase')
        serialized = '请按以下完整消息的角色与顺序继续对话，回答最后一条用户消息。\n\n' + serialized
    require(evidence(root, sources[full['file']]) == serialized.encode('utf-8'),
            'Complete serialized visible history differs from its reconstructed fragments')
    used.add(full['file'])
    require(set(sources) == used, 'Unspecified files entered visible input projection')
    return messages


def validate_projection(root, data, evidence):
    from .catalog import candidate_message
    p = data['input_projection']
    require(p.get('schema') == INPUT_SCHEMA and p.get('reviewer_feedback_included') is False,
            'Native input needs its explicit feedback-free projection')
    original = evidence(root, p['original_task'])
    request = json.loads(evidence(root, p['logical_request']))
    require(request.get('case_id') == data['case_id'] and request.get('schema') == 'math-gauge.request/v1'
            and request.get('task', '').encode('utf-8') == original,
            'Logical request changed the original mathematical task')
    payload = candidate_message(request).encode('utf-8')
    require(evidence(root, p['candidate_message']) == payload,
            'Logical candidate message differs from its original supplied files')
    files = p.get('provided_files', [])
    require([x['name'] for x in files] == [x['name'] for x in request.get('files', [])],
            'The supplied file projection changed its complete inventory')
    for bound, supplied in zip(files, request.get('files', [])):
        require(evidence(root, bound['original']) == supplied['content'].encode('utf-8')
                == evidence(root, bound['sealed']), 'Supplied original file bytes changed')
    messages = _projected_messages(root, p, data['phase'], evidence)
    header = evidence(root, data['candidate_input'])
    require(same(p['native_header'], data['candidate_input'])
            and evidence(root, p['native_header']) == header, 'Native short header changed')
    if data['phase'] == 'A1':
        pre = json.loads(evidence(root, p['projection_preflight']))
        record = json.loads(evidence(root, p['operator_record']))
        manifest = json.loads(evidence(root, p['exact_input_manifest']))
        selected = manifest['cases'][data['case_id']]
        canonical_request = sha(json.dumps(request, ensure_ascii=False, sort_keys=True).encode())
        require(messages == [dict(role='user', content=payload.decode('utf-8'))]
                and pre.get('schema') == 'math-gauge.exact-original-A1-input-preflight/v1'
                and pre.get('case_id') == data['case_id']
                and pre.get('mathematical_input_bytes_unchanged') is True
                and pre.get('reviewer_feedback_included') is False and pre.get('candidate_calls') == 0
                and same(pre.get('original_payload'), p['candidate_message'])
                and same(pre.get('native_header'), p['native_header'])
                and same(pre.get('index'), p['attachment_index'])
                and same(pre.get('manifest'), p['exact_input_manifest'])
                and same(selected.get('original_payload'), p['candidate_message'])
                and same(selected.get('native_header'), p['native_header'])
                and selected.get('original_candidate_message_sha256') == sha(payload)
                and record.get('case_id') == data['case_id']
                and record.get('request_sha256') == canonical_request
                and record.get('candidate_message_sha256') == sha(payload),
                'Native A1 lost its actual exact-input/request bridge')
    else:
        from .agy_evidence import validate_delivery
        n = int(data['phase'][1:]); parent_ref = p['immediate_parent_native_evidence']
        parent = json.loads(evidence(root, parent_ref))
        phase = 'A1' if n == 1 else 'R' + str(n - 1)
        require(parent.get('case_id') == data['case_id'] and parent.get('phase') == phase,
                'Selfcheck input borrowed another parent or skipped a prescribed round')
        parent_row = dict(case_id=data['case_id'], id=data['case_id'] + ':' + phase,
                          agy_native_evidence=parent_ref, response=parent['response'])
        previous = validate_delivery(root, parent_row, evidence)
        neutral = evidence(root, p['neutral_invitation']).decode('utf-8')
        expected = previous['input_messages'] + [dict(role='assistant', content=previous['text']),
                                               dict(role='user', content=neutral)]
        projected = json.loads(evidence(root, p['projected_request']))
        pre = json.loads(evidence(root, p['projection_preflight']))
        frozen = json.loads(evidence(root, data['round_freeze']))
        plan = json.loads(evidence(root, data['selfcheck_plan']))
        index = json.loads(evidence(root, p['attachment_index']))
        parent_seal = json.loads(evidence(root, parent['native_terminal_seal']))
        inherited = {x['path']: x for x in parent_seal['work']}
        require(messages == expected == projected.get('messages')
                and projected.get('case_id') == data['case_id'] and projected.get('round') == n
                and projected.get('candidate_user_message', '').encode() == header
                and pre.get('round') == n and pre.get('parent_attempt') == parent['original_attempt']
                and same(pre.get('parent_seal'), parent['native_terminal_seal'])
                and pre.get('reviewer_feedback_included') is False
                and pre.get('artifact_checks_passed') is True
                and pre.get('frozen_inputs_unchanged') is True
                and pre.get('all_original_messages_reconstruct_exactly') is True
                and pre.get('round_freeze_sha256') == data['round_freeze']['sha256']
                and pre.get('plan_sha256') == data['selfcheck_plan']['sha256']
                and frozen.get('parent_attempt') == parent['original_attempt']
                and same(frozen.get('parent_seal'), parent['native_terminal_seal'])
                and frozen.get('projected_request_sha256') == sha(json.dumps(projected, ensure_ascii=False, sort_keys=True).encode())
                and frozen.get('candidate_message_sha256') == sha(header)
                and frozen.get('full_serialized_history_sha256') == index['full_serialized_history']['sha256']
                and frozen.get('reviewer_feedback_included') is False
                and plan.get('neutral_prompt_sha256') == p['neutral_invitation']['sha256']
                and all(x == inherited.get(x['path']) for x in pre['carried_files']),
                'Selfcheck lost the immediate actual engineering/truefinal parent chain')
    return messages


def validate_db_final(root, data, evidence, header, aggregate, seal):
    from .result_corrections import _field
    f = data['normal_final_source']
    witness = json.loads(evidence(root, f['extraction']))
    inventory = json.loads(evidence(root, f['step_inventory']))
    snapshot = json.loads(evidence(root, f['database_snapshot']))
    conversation = witness.get('conversation_id')
    require(witness.get('schema') == 'math-gauge.normal-native-final-body-extraction/v1'
            and witness.get('source_raw_bytes_rewritten') is False
            and witness.get('original_attempt') == data['original_attempt']
            and witness.get('phase') == data['phase'] and witness.get('native_terminal_status') == 'SUCCESS'
            and witness.get('selection') == 'highest_completed_agent_response_index'
            and witness.get('protobuf_field') == '20.1' and witness.get('hidden_reasoning_decoded') is False
            and witness.get('legacy_v0_1_0_admission_compatible') is True
            and witness.get('WAL_dependent_formal_admission_requires_explicit_adapter') is False
            and witness.get('source_origin') == 'same_physical_attempt_stable_sealed_DB_WAL_SHM'
            and witness.get('live_native_database_read') is False
            and witness.get('other_conversations_read') is False
            and inventory.get('schema') == 'math-gauge.native-sqlite-step-inventory/v1'
            and inventory.get('complete_conversation_export') is True
            and inventory.get('source_database_requires_WAL') is False
            and inventory.get('conversation_id') == conversation
            and same(witness['native_step_inventory'], f['step_inventory'])
            and same(witness['selected_step_payload'], f['selected_payload'])
            and same(witness['native_database_snapshot'], f['database_snapshot'])
            and same(witness['final_body'], data['response'])
            and witness['native_final_sha256'] == data['response']['sha256']
            and witness['native_final_bytes'] == data['response']['bytes']
            and witness['raw_result_response_sha256'] == sha(aggregate)
            and witness['raw_result_response_bytes'] == len(aggregate),
            'Normal final lacks its exact same-physical immutable-main extraction witness')
    require(isinstance(conversation, str) and conversation and len(conversation) <= 255
            and all(c.isalnum() or c in '-_' for c in conversation)
            and snapshot.get('schema') == 'math-gauge.stopped-native-database-snapshot/v1'
            and snapshot.get('stable_before_after_copy') is True
            and snapshot.get('source_files_unchanged') is True
            and seal.get('native_database_snapshot_sha256') == f['database_snapshot']['sha256'],
            'Normal DB was not the stable own cutoff snapshot')
    originals, files = {}, {}
    for item in snapshot['files']:
        copied, source = item['sealed_copy'], item['source']
        name = PurePosixPath(copied['path']).name
        require(name in {conversation + '.db', conversation + '.db-wal', conversation + '.db-shm'}
                and copied['path'] == data['original_attempt'] + '/sealed/native-state/conversations/' + name
                and source['path'] == data['original_attempt'] + '/session/state/antigravity-cli/conversations/' + name
                and same(copied, source) and name not in originals,
                'Database snapshot contains a foreign physical source')
        originals[name] = copied
    for bound in f['database_files']:
        name = bound['name']; require(name in originals and name not in files
            and same(bound['evidence'], originals[name]), 'Archived DB family changed')
        files[name] = evidence(root, bound['evidence'])
    require(set(files) == set(originals) and conversation + '.db' in files
            and same(inventory['source_database'], originals[conversation + '.db'])
            and {(x['bytes'], x['sha256']) for x in inventory['source_evidence']}
                == {(x['bytes'], x['sha256']) for x in originals.values()},
            'Archived DB/WAL/SHM family is incomplete')
    # Immutable-main only: the preserved WAL/SHM are hashed, never replayed into
    # an original DB. A future WAL-dependent format needs its own explicit gate.
    with tempfile.TemporaryDirectory(prefix='agy-admission-db-') as temporary:
        db = Path(temporary) / (conversation + '.db'); db.write_bytes(files[db.name])
        connection = sqlite3.connect(db.as_uri() + '?mode=ro&immutable=1', uri=True)
        try:
            connection.execute('PRAGMA query_only=ON')
            identities = connection.execute('SELECT trajectory_id,cascade_id FROM trajectory_meta').fetchall()
            rows = connection.execute('SELECT idx,step_type,status,has_subtrajectory,step_payload,step_format FROM steps ORDER BY idx').fetchall()
        finally:
            connection.close()
    require(len(identities) == 1 and conversation in identities[0] and rows
            and all(x[5] == 0 for x in rows), 'Unknown or foreign native DB encoding')
    opaque_rows = [dict(idx=i, step_type=t, native_status_code=s,
        native_status='completed' if s == 3 else 'other', has_subtrajectory=bool(h),
        step_format=fmt, payload_sha256=sha(raw or b'')) for i,t,s,h,raw,fmt in rows]
    require(opaque_rows == inventory['rows'], 'Logical extraction and immutable-main inventory differ')
    users = [x for x in rows if x[1] == 14]
    completed = [x for x in rows if x[1] == 15 and x[2] == 3]
    require(len(users) == 1 and users[0][2] == 3 and completed,
            'Normal DB lacks its single actual completed user turn')
    selected = max(completed, key=lambda x: x[0])
    require(users[0][0] < selected[0]
            and _field(_field(users[0][4], 19), 2) == header,
            'Native DB user19.2 differs from this physical request')
    payload = evidence(root, f['selected_payload'])
    require(selected[0] == witness['selected_step_index'] and selected[4] == payload,
            'Selected visible final is not the highest completed native reply')
    final = _field(_field(payload, 20), 1)
    require(isinstance(final, bytes) and final.strip() and final == evidence(root, data['response'])
            and aggregate.find(final) == witness['exact_native_final_is_substring_at'] >= 0
            and witness.get('aggregate_response_equal_final_body') is (aggregate == final),
            'Reply20.1 changed or is absent from its same native aggregate')
    final.decode('utf-8')
    return final, conversation


def validate_delivery(root, row, data, execution, events, dispatch, evidence):
    from .agy_control_evidence import validate_local_tools
    seal = json.loads(evidence(root, data['native_terminal_seal']))
    result = json.loads(evidence(root, data['execution_result']))
    terminal = json.loads(evidence(root, data['native_terminal_event']))
    freeze = json.loads(evidence(root, data['acquisition_freeze']))
    native = terminal.get('result', {})
    limit, elapsed = dispatch.get('outer_budget_seconds'), seal.get('elapsed_seconds')
    require(isinstance(data.get('original_attempt'), str) and data['original_attempt'].startswith('/')
            and type(data.get('physical_request')) is int and data['physical_request'] >= 1
            and [e for e in events if e.get('event') == 'result'] == [terminal]
            and native.get('status') == seal.get('native_status') == 'SUCCESS'
            and seal.get('trigger') == 'first-native-terminal'
            and type(limit) in (int,float) and type(elapsed) in (int,float)
            and math.isfinite(limit) and math.isfinite(elapsed) and 0 <= elapsed < limit
            and seal.get('deadline_seconds') == limit
            and seal.get('normal_complete_delivery') is True
            and result.get('normal_complete_delivery') is True and result.get('artifact_checks_passed') is True
            and not result.get('tool_mismatch') and result.get('native_terminal') == seal
            and result.get('case_id') == dispatch.get('case_id') == data['case_id']
            and result.get('physical_request_number') == dispatch.get('physical_request_number') == data['physical_request']
            and result.get('freeze_sha256') == dispatch.get('freeze_sha256') == data['acquisition_freeze']['sha256']
            and freeze.get('benchmark_version') == '1.0.0'
            and seal.get('raw_terminal_sha256') == data['native_terminal_event']['sha256'],
            'Visible-final admission needs its original timely first native SUCCESS')
    plan = json.loads(evidence(root, data['native_plan']))
    require(plan.get('run_dir') == data['original_attempt'] + '/session'
            and plan.get('cwd') == data['original_attempt'] + '/session/work'
            and plan.get('stdin_file') == data['original_attempt'] + '/session/runtime/request.ndjson',
            'Native plan belongs to another physical session')
    frozen = datetime.fromisoformat(freeze['utc'].replace('Z', '+00:00'))
    dispatched = datetime.fromisoformat(dispatch['utc'].replace('Z', '+00:00'))
    require(frozen.tzinfo is not None and dispatched.tzinfo is not None and frozen < dispatched,
            'Native acquisition freeze was not retained before this actual dispatch')
    control = json.loads(evidence(root, data['local_tools']['native_control']))
    require(freeze.get('native_binary_sha256') == execution.get('parent_identity', {}).get('executable_sha256')
            and freeze.get('requested_model') == execution.get('requested_model')
            and freeze.get('requested_effort') == execution.get('requested_effort')
            and result.get('requested_model') == execution.get('requested_model')
            and result.get('requested_effort') == execution.get('requested_effort')
            and any(same(x, control['original_validation']) for x in freeze.get('source_bindings', []))
            and any(same(x, data['input_projection']['exact_input_manifest'])
                    for x in freeze.get('source_bindings', [])),
            'Native binary, controls or exact input changed from the actual acquisition freeze')
    if data['phase'] != 'A1':
        n = int(data['phase'][1:])
        round_freeze = json.loads(evidence(root, data['round_freeze']))
        evidence(root, data['selfcheck_plan'])
        require(dispatch.get('phase') == data['phase'] and dispatch.get('round') == n
                and dispatch.get('round_freeze_sha256') == data['round_freeze']['sha256']
                and dispatch.get('selfcheck_plan_sha256') == data['selfcheck_plan']['sha256']
                and round_freeze.get('round') == n, 'Prescribed round freeze changed')
    aggregate = native.get('response')
    require(isinstance(aggregate, str) and aggregate.strip(), 'Native SUCCESS has no complete aggregate')
    aggregate = aggregate.encode('utf-8')
    require(seal.get('answer_sha256') == seal.get('native_return_sha256') == sha(aggregate)
            and evidence(root, data['aggregate_response']) == aggregate
            and same(data['response'], row['response']), 'Raw native aggregate or selected final changed')
    header = evidence(root, data['candidate_input'])
    final, conversation = validate_db_final(root, data, evidence, header, aggregate, seal)
    require(conversation == native.get('conversation_id'), 'Terminal and DB conversation differ')
    messages = validate_projection(root, data, evidence)
    validate_local_tools(root, data, execution, evidence)
    return dict(delivered=True, native_status='SUCCESS', text=final.decode('utf-8'),
                cli_status=execution.get('status'), cli_exit_code=execution.get('exit_code'),
                selected_visible_final_sha256=sha(final), aggregate_response_sha256=sha(aggregate),
                native_terminal_seal=seal, logical_input_verified=True, input_messages=messages)
