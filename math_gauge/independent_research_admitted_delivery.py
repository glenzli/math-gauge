"""Carbon-only, post-observation selection of actual native cutoff manuscripts.

This evaluator adapter never changes a native delivery state or manufactures a
normal seal. The normal-only owners remain unchanged. All original sources are
read from an explicitly closed archive; mathematical credit is independently
reviewed and delegated to the existing strict-credit and scoring owners.
"""
from contextlib import closing
from dataclasses import dataclass
from fractions import Fraction
import json
import math
from pathlib import Path, PurePosixPath
import sqlite3
import tempfile
from types import ModuleType

from . import independent_research_adoption as adoption
from . import independent_research_external as external
from . import independent_research_review as trajectory
from . import independent_research_score_modes as modes
from . import independent_research_strict_credit as credit
from . import independent_research_value as value
from . import taste_v130 as flow

MODEL = 'gemini-4-carbon-medium'
SCHEMA = 'math-gauge.independent-research-admitted-results/v1'
SELECTION = 'math-gauge.independent-research-admitted-selection/v1'
FROZEN_SELECTION = 'math-gauge.independent-research-admitted-selection/v2'
FROZEN_RUNNER = 'math-gauge.independent-research-frozen-runner/v1'
ADMISSION = 'math-gauge.carbon-research-admitted-deliveries/v1'
ARCHIVE = 'math-gauge.carbon-research-closed-source-archive/v1'
HISTORY = 'math-gauge.carbon-research-closed-native-history/v1'
CUTOFF = 'math-gauge.carbon-research-cutoff-inventory/v1'
REVIEW = 'math-gauge.carbon-research-admitted-review/v1'
SOURCE_KIND = 'user-selected-native-cutoff-deliveries'
PUBLIC_PATH = Path('protocol/mathematical-taste/v1.3.0/native-additions/gemini-4-carbon-medium.json')
R1_CONTINUATION = '请继续先前正在进行的同一任务，沿用本会话原始材料、已有完整历史和当前工程。本次沿同一R1追加最多5分钟，请在这段时间内交付当前可交付的最终稿；不另起独立作答。这里没有评审反馈；不要引入其他会话或外部材料。完成后请给出最终答复，并明确链接或列出实际交付的附件。\n'
AUTHORIZATION_SHA256 = 'ae1c0fb63edcb2effaa8a93047994704cfa6142088da0819b3205bd499fba05a'
encoded, digest = external.encoded, external.digest
_need, _fields = flow._need, value._fields


def _positive(n):
    return type(n) in (int, float) and math.isfinite(n) and n >= 0


def _absolute_ref(ref):
    _need(_fields(ref, ('path', 'bytes', 'sha256')) and type(ref['bytes']) is int
          and ref['bytes'] >= 0 and adoption._is_hash(ref['sha256']), 'Invalid original source descriptor')
    p = PurePosixPath(ref['path'])
    _need(p.is_absolute() and p.as_posix() == ref['path'] and '..' not in p.parts,
          'Original source identity must be an exact absolute path')


def _relative_original(parent, ref):
    _need(_fields(ref, ('path', 'bytes', 'sha256')), 'Invalid original sealed source')
    name = PurePosixPath(ref['path'])
    _need(not name.is_absolute() and name.as_posix() == ref['path'] and '..' not in name.parts,
          'Unsafe sealed original path')
    return dict(ref, path=str(PurePosixPath(parent['path']).parent / name))


class ClosedArchive:
    """Resolve old absolute identities only to their exact retained regular bytes."""
    def __init__(self, base, ref):
        self.root = flow._contained(base, ref['path']).parent
        self.raw = flow._read(base, ref)
        archive = value._json(self.raw)
        _need(_fields(archive, ('schema', 'closed', 'all_processes_exited',
              'authentication_state_excluded', 'original_source_bytes_unchanged', 'files'))
              and archive['schema'] == ARCHIVE
              and all(archive[k] is True for k in ('closed', 'all_processes_exited',
                  'authentication_state_excluded', 'original_source_bytes_unchanged'))
              and isinstance(archive['files'], list) and archive['files'],
              'Adoption requires an explicitly closed, authentication-free original archive')
        self.files, self.raws = {}, {}
        retained_paths = set()
        for row in archive['files']:
            _need(_fields(row, ('original_path', 'path', 'bytes', 'sha256')),
                  'Unexpected closed archive inventory fields')
            original = dict(path=row['original_path'], bytes=row['bytes'], sha256=row['sha256'])
            _absolute_ref(original)
            key = (original['path'], original['bytes'], original['sha256'])
            _need(key not in self.files, 'Duplicate exact original source in archive')
            relative = {k: row[k] for k in ('path', 'bytes', 'sha256')}
            raw = flow._read(self.root, relative)
            self.files[key] = relative
            self.raws[row['path']] = raw
            retained_paths.add(row['path'])

    def read(self, ref):
        _absolute_ref(ref)
        retained = self.files.get((ref['path'], ref['bytes'], ref['sha256']))
        _need(retained is not None and all(retained[k] == ref[k] for k in ('bytes', 'sha256')),
              'Original source is absent or differs from the closed archive')
        return flow._read(self.root, retained)

    def json(self, ref):
        return value._json(self.read(ref))

    def descriptor(self, ref):
        self.read(ref)
        return dict(self.files[(ref['path'], ref['bytes'], ref['sha256'])])

    def unchanged(self):
        _need(all(flow._contained(self.root, name).read_bytes() == raw for name, raw in self.raws.items()),
              'Closed source archive changed during verification')


def _authorization(archive, ref, registration, native_session):
    raw = archive.read(ref)
    auth = value._json(raw)
    _need(digest(raw) == AUTHORIZATION_SHA256
          and auth['schema'] == 'math-gauge.carbon-open-research-forced-submission-authorization/v1'
          and auth['model_configuration'] == MODEL and auth['native_session_id'] == native_session
          and auth['registration']['sha256'] == registration and auth['selected_rounds'] == list(flow.ROUNDS)
          and auth['adopted_after_observation'] is True and auth['benchmark_adoption_authorized'] is True
          and all(auth[k] is False for k in ('fourth_round_allowed', 'fresh_math_attempt_allowed',
              'math_feedback_allowed', 'native_status_rewrite_allowed', 'normal_final_synthesized',
              'force_content_direct_math_zero', 'normal_only_validator_rewrite_allowed',
              'human_mathematical_approval', 'commit_authorized', 'push_authorized', 'deployment_authorized'))
          and auth['R2_seconds'] == auth['R3_seconds'] == 2700,
          'Not the exact user-selected Carbon-only force admission authorization')
    archive.read(auth['prior_R1_forced_admission'])
    for source in auth['source_receipts']:
        archive.read(source)
    return auth


def _history(archive, ref, conversation):
    history = archive.json(ref)
    _need(_fields(history, ('schema', 'native_session_id', 'complete_own_history', 'all_processes_exited',
          'hidden_history_used_as_mathematical_submission', 'authentication_state_excluded',
          'snapshots', 'process_exits', 'continuity_proofs'))
          and history['schema'] == HISTORY and history['native_session_id'] == conversation
          and history['complete_own_history'] is history['all_processes_exited'] is True
          and history['authentication_state_excluded'] is True
          and history['hidden_history_used_as_mathematical_submission'] is False
          and history['snapshots'] and history['process_exits'] and history['continuity_proofs'],
          'Need complete, closed own-history evidence; opaque history is never mathematics')
    ids = set()
    for row in history['snapshots']:
        _need(_fields(row, ('id', 'source_files', 'complete')) and row['complete'] is True
              and modes._text(row['id']) and row['id'] not in ids
              and isinstance(row['source_files'], list) and 1 <= len(row['source_files']) <= 3,
              'Incomplete or repeated native history snapshot')
        ids.add(row['id'])
        sources = {Path(r['path']).name: r for r in row['source_files']}
        mains = [name for name in sources if not name.endswith(('-wal', '-shm'))]
        _need(len(sources) == len(row['source_files']) and len(mains) == 1
              and set(sources) <= {mains[0], mains[0] + '-wal', mains[0] + '-shm'},
              'A native snapshot must retain its exact main DB and available WAL/SHM companions')
        original_main = next(r['path'] for r in row['source_files'] if Path(r['path']).name == mains[0])
        available = {original_main + suffix for suffix in ('', '-wal', '-shm')} & {key[0] for key in archive.files}
        _need({r['path'] for r in row['source_files']} == available,
              'Do not omit an archived WAL/SHM companion from the native history snapshot')
        # SQLite may create/read coordination files. Inspect an exact disposable
        # copy so the archived DB/WAL/SHM bytes cannot be altered by validation.
        with tempfile.TemporaryDirectory(prefix='mg-carbon-closed-db-') as tmp:
            for name, source in sources.items():
                (Path(tmp) / name).write_bytes(archive.read(source))
            try:
                with closing(sqlite3.connect('file:' + str(Path(tmp)/mains[0]) + '?mode=ro', uri=True)) as db:
                    _need(db.execute('PRAGMA quick_check').fetchall() == [('ok',)],
                          'Closed native SQLite history is damaged')
            except sqlite3.DatabaseError as error:
                raise ValueError('Unreadable closed native history') from error
    pids = set()
    for ref in history['process_exits']:
        exited = archive.json(ref)
        _need(type(exited.get('returncode')) is int and type(exited.get('pid')) is int
              and exited['pid'] not in pids, 'Native cleanup needs distinct original process-exit receipts')
        pids.add(exited['pid'])
    for ref in history['continuity_proofs']:
        proof = archive.json(ref)
        if proof.get('transport') == 'native-print-conversation-stream-json':
            _need(proof.get('passed') is True and proof.get('native_session_id') == conversation
                  and proof.get('session_new_calls') == proof.get('candidate_prompts') == 0,
                  'Actual print recovery did not retain the same native own-history')
            before, after = proof['history_before'], proof['history_after']
            _need(all(adoption._is_hash(v['core_history_sha256']) for v in (before, after))
                  and before['trajectory_metadata'] == after['trajectory_metadata'],
                  'Native print context identity changed')
            if before['core_history_sha256'] != after['core_history_sha256']:
                change = proof['exact_preinput_history_migration_proof']
                _need(change['passed'] is True and change['mode'] == 'exact-observed-native-preinput-step45-status8-to6'
                      and change['before_core_sha256'] == before['core_history_sha256']
                      and change['after_core_sha256'] == after['core_history_sha256']
                      and change['all_tables_and_rows_compared_exactly'] is True
                      and change['generic_status_migration_allowed'] is False
                      and change['database_modified_by_controller'] is False
                      and change['new_mathematical_input_before_check'] is False,
                      'A changed history needs its exact observed native pending-state proof')
                archive.read(change['root_user_authorization'])
                matches = [key for key in archive.files if key[0] == change['source_record']]
                _need(len(matches) == 1, 'Need the exact original pending-state comparison record')
                source = archive.json(dict(zip(('path', 'bytes', 'sha256'), matches[0])))
                _need(source['schema'] == 'math-gauge.carbon-forced-parent-exact-expected-preinput-history/v1'
                      and source['root_user_authorization'] == change['root_user_authorization']
                      and source['last_pending_row'] == 45 and source['rows'] == 46
                      and source['only_changed_columns'] == ['status', 'step_payload']
                      and source['only_expected_payload_change'] == 'offset3 8to6; SQLitestatus8to6; everyothercellidentical'
                      and source['expected_is_derived_not_observed'] is True
                      and source['real_or_source_DB_modified'] is False,
                      'Do not generalize or rewrite the retained native pending-state change')
                archive.read(source['source_execution']); archive.read(source['source_result'])
            archive.read(proof['accept_edits_settings_source'])
        else:
            _need(proof.get('schema') == 'math-gauge.carbon-native-history-continuity/v1'
                  and proof.get('native_session_id') == conversation and proof.get('passed') is True
                  and proof.get('complete_own_history') is True and proof.get('new_independent_context') is False
                  and adoption._is_hash(proof.get('history_before_sha256'))
                  and proof['history_before_sha256'] == proof.get('history_after_sha256')
                  and proof.get('source_receipts'), 'History continuity needs its exact, complete same-context proof')
            for source in proof['source_receipts']:
                archive.read(source)
    return history


def _budget(archive, row, result):
    segments = row['budget_segments']
    _need(isinstance(segments, list) and segments, 'Missing actual round budget provenance')
    expected = [2700, 600, 300] if row['round'] == 'R1' else [2700]
    _need([segment.get('seconds') for segment in segments] == expected,
          'Retain R1 original2700+authorized600+300; R2/R3 each2700, without a fresh R1')
    for index, segment in enumerate(segments):
        _need(_fields(segment, ('seconds', 'kind', 'authorization'))
              and type(segment['seconds']) is int and segment['kind'] == ('original-limit' if index == 0 else 'user-extension')
              and (segment['authorization'] is None) == (index == 0), 'Invalid controller-limit segment')
        if index:
            _need(archive.read(segment['authorization']).strip(), 'Extra time needs its actual explicit authorization')
    elapsed, prefix = result['elapsed_seconds'], result['original_prefix_seconds']
    _need(_positive(elapsed) and _positive(prefix)
          and result['total_round_math_elapsed_seconds'] == prefix + elapsed
          and result['budget_seconds_this_dispatch'] == (300 if row['round'] == 'R1' else 2700)
          and (row['round'] == 'R1' or prefix == 0)
          and prefix + elapsed <= sum(expected) + 5,
          'Actual observed time or selected controller limits changed')
    if row['selected_delivery'] == 'normal-final':
        _need(elapsed <= result['budget_seconds_this_dispatch'], 'First normal final arrived after its actual deadline')
    else:
        _need(result['budget_seconds_this_dispatch'] <= elapsed <= result['budget_seconds_this_dispatch'] + 5,
              'Forced content needs the actual fixed deadline boundary')
    for source in result.get('all_original_results', []):
        archive.read(source)
    for source in result.get('budget_decision', {}).get('source_receipts', []):
        archive.read(source)


def _round(archive, row, registered, conversation, context, prior, original_r1, prompts, previous_original_seal):
    _need(_fields(row, ('round', 'selected_delivery', 'original_result', 'original_boundary', 'original_seal',
          'original_observation', 'cutoff_inventory', 'documents', 'parent_sha256', 'budget_segments'))
          and row['round'] in flow.ROUNDS and row['parent_sha256'] == prior
          and row['selected_delivery'] in ('normal-final', 'forced-content')
          and isinstance(row['documents'], list) and row['documents'], 'Broken selected-delivery chain')
    rid = row['round']
    result, boundary, seal, observation = [archive.json(row[key]) for key in
        ('original_result', 'original_boundary', 'original_seal', 'original_observation')]
    _need(result['schema'] == 'math-gauge.carbon-account-r1-round/v1'
          and boundary['schema'] == 'math-gauge.carbon-open-research-native-boundary/v1'
          and observation['schema'] == 'math-gauge.research-round-observation/v1'
          and observation['kind'] == 'operator-attestation'
          and result['round'] == boundary['round'] == seal['round'] == observation['round'] == rid
          and result['native_session_id'] == boundary['native_session_id'] == conversation
          and result['model'] == 'gemini-4-carbon' and result['effort'] == 'medium'
          and result['native_transport'] == 'print-stream-json' and result['no_synthetic_acp_receipts'] is True
          and result['new_independent_opportunity'] is False
          and result['old_results_classifications_seals_native_db_rewritten'] is False
          and result['agent_thought_used_for_submission'] is boundary['agent_thought_used_as_submission'] is False
          and result['elapsed_seconds'] == boundary['elapsed_seconds']
          and result['began'] == boundary['began']
          and seal['registration_sha256'] == registered and observation['context_id'] == context
          and seal['prompt_sha256'] == prompts[rid]['sha256']
          and (rid == 'R1' or seal['previous'] == previous_original_seal)
          and seal['delivery'] == observation['delivery'] == result['delivery']
          and row['original_seal'] == result['seal']
          and digest(archive.read(row['original_observation'])) == seal['observation']['sha256'],
          'Selected round differs from its original native receipts or unchanged delivery state')
    _budget(archive, row, result)
    request = archive.json(result['native_prompt_request'])
    _need(_fields(request, ('event', 'message')) and request['event'] == 'user'
          and _fields(request['message'], ('content',)) and modes._text(request['message']['content']),
          'Need the original actual native print user request')
    if rid != 'R1':
        prompt = request['message']['content'].encode()
        _need(len(prompt) == prompts[rid]['bytes'] and digest(prompt) == prompts[rid]['sha256'],
              'Later round prompt differs from the original frozen task')
    else:
        _need(request['message']['content'] == R1_CONTINUATION,
              'Changed the actual neutral same-R1 extra-five-minute continuation')
    raw_wire = archive.read(result['raw_events'])
    wire = [value._json(line) for line in raw_wire.splitlines() if line.strip()]
    documents = []
    for index, document in enumerate(row['documents']):
        _need(_fields(document, ('source', 'role'))
              and document['role'] == ('manuscript' if index == 0 else 'explicit-attachment'),
              'Selected mathematical sources require one manuscript and explicit attached files')
        ref = archive.descriptor(document['source'])
        _need(archive.read(document['source']).decode('utf-8').strip(), 'Empty selected manuscript or attachment')
        documents.append(ref)
    _need(len({ref['path'] for ref in documents}) == len(documents), 'Duplicate selected mathematical source')
    normal = row['selected_delivery'] == 'normal-final'
    if normal:
        _need(result['delivery'] == 'normal-final' and result['status'] == 'normal_final'
              and result['first_normal_final'] is True and observation['first_normal_final'] is True
              and result['native_terminal'] == 'SUCCESS' and result['failure'] is None
              and result['native_result']['result']['status'] == 'SUCCESS'
              and row['cutoff_inventory'] is None and seal['raw'] is not None,
              'A forced/failed/native ERROR round cannot become a normal final')
        raw = archive.read(result['visible_agent_message'])
        _need(raw == result['native_result']['result']['response'].encode()
              and result['native_result']['result']['conversation_id'] == conversation
              and [event for event in wire if event.get('event') == 'result'] == [result['native_result']]
              and wire[-1] == result['native_result']
              and raw == archive.read(row['documents'][0]['source']), 'Normal final differs from first original native terminal')
        sources = [_relative_original(row['original_seal'], ref) for ref in [seal['raw'], *seal['files']]]
        _need([d['source'] for d in row['documents']] == sources,
              'Normal evidence must be the actual sealed final and all explicit delivered files')
        _need([(r['bytes'], r['sha256']) for r in seal['files']] ==
              [(r['bytes'], r['sha256']) for r in result['explicit_delivered_files']],
              'Normal attachments differ from the actual explicit delivery')
    else:
        _need(result['delivery'] == 'delivery-failed' and result['status'] == 'cutoff_without_final'
              and result['first_normal_final'] is False and observation['first_normal_final'] is None
              and observation['boundary']['kind'] == 'deadline'
              and result['native_terminal'] is result['native_result'] is None
              and seal['raw'] is None and seal['files'] == [] and observation['raw'] is None
              and not result['explicit_delivered_files'] and row['cutoff_inventory'] is not None
              and not any(event.get('event') == 'result' and event.get('result', {}).get('status') == 'SUCCESS' for event in wire),
              'Forced selection must retain the original failed, no-final deadline receipts')
        cutoff = archive.json(row['cutoff_inventory'])
        _need(_fields(cutoff, ('schema', 'round', 'native_session_id', 'boundary_source',
              'candidate_writes_stopped', 'operator_repaired', 'hidden_thought_used', 'files'))
              and cutoff['schema'] == CUTOFF and cutoff['round'] == rid
              and cutoff['native_session_id'] == conversation and cutoff['boundary_source'] == row['original_boundary']
              and cutoff['candidate_writes_stopped'] is True
              and cutoff['operator_repaired'] is cutoff['hidden_thought_used'] is False
              and [d['source'] for d in row['documents']] == cutoff['files'],
              'Forced mathematics must be the exact stopped, unrepaired cutoff inventory')
        if rid == 'R1':
            _need(row['documents'][0]['source'] == original_r1['forced_parent_manuscript']
                  and original_r1['R1_original_normal_final'] is False
                  and original_r1['R1_original_delivery_state_preserved'] == 'delivery-failed',
                  'R1 changed the actual user-selected forced parent')
    return dict(delivery=row['selected_delivery'], raw=documents[0], files=documents[1:],
                observation=archive.descriptor(row['original_observation']))


@dataclass(frozen=True)
class AdmittedEvidence:
    archive: ClosedArchive
    records: dict
    row_hashes: dict
    admission_sha256: str
    registration_sha256: str
    candidate_context_id: str
    native_session_id: str
    original: dict


def load_admission(path, registration_sha256, *, round_prompts):
    path = flow._safe_absolute(path)
    raw = path.read_bytes()
    document = value._json(raw)
    _need(_fields(document, ('schema', 'edition', 'model_id', 'native_session_id', 'candidate_context_id',
          'registration_sha256', 'authorization', 'prior_R1_admission', 'archive', 'history',
          'rounds', 'conditions', 'human_review'))
          and document['schema'] == ADMISSION and document['edition'] == flow.EDITION
          and document['model_id'] == MODEL and document['registration_sha256'] == registration_sha256
          and document['human_review'] == 'pending' and modes._text(document['candidate_context_id'])
          and modes._text(document['native_session_id']) and isinstance(document['rounds'], list)
          and [r.get('round') for r in document['rounds']] == list(flow.ROUNDS),
          'Need the complete selected Carbon three-round admission; no provisional score')
    archive = ClosedArchive(path.parent, document['archive'])
    auth = _authorization(archive, document['authorization'], registration_sha256, document['native_session_id'])
    _need(document['prior_R1_admission'] == auth['prior_R1_forced_admission'], 'Changed earlier R1 selection')
    r1 = archive.json(document['prior_R1_admission'])
    _need(r1['native_session_id'] == document['native_session_id']
          and r1['chain_context_id'] == document['candidate_context_id']
          and r1['registration']['sha256'] == registration_sha256, 'Changed original R1 context or source')
    _history(archive, document['history'], document['native_session_id'])
    expected = dict(original_round_limit_seconds=2700, R1_extension_seconds=900,
        R1_extension_timing='post-cutoff-user-authorized', network_tools_used=False,
        external_retrieval_used=False, source_materials_unchanged=True,
        account_condition_change_preserved=True, system_retry_exclusion_inferred=False)
    _need(document['conditions'] == expected, 'Actual time/account conditions must be retained without inferred exclusions')
    records, hashes, prior, previous_original_seal = {}, {}, None, None
    for row in document['rounds']:
        records[row['round']] = _round(archive, row, registration_sha256, document['native_session_id'],
                                     document['candidate_context_id'], prior, r1, round_prompts, previous_original_seal)
        prior = digest(encoded(row))
        hashes[row['round']] = prior
        previous_original_seal = row['original_seal']['sha256']
    archive.unchanged()
    _need(path.read_bytes() == raw, 'Admission changed during verification')
    return AdmittedEvidence(archive, records, hashes, digest(raw), registration_sha256,
                            document['candidate_context_id'], document['native_session_id'], document)


def _judgment(row, evidence, allowed, fields):
    if fields:
        return trajectory._judgment(row, evidence.archive.root, evidence.records, set(allowed), fields)
    _need(_fields(row, ('reason', 'evidence')) and modes._text(row['reason']),
          'Need the original reason and exact selected-delivery evidence')
    flow._evidence(row['evidence'], evidence.archive.root, evidence.records, set(allowed))
    return {ref['round'] for ref in row['evidence']}


def _original_review_sources(review, evidence):
    sources = review.get('review_sources')
    if sources is None:
        return
    _need(_fields(sources, ('calibration', 'quote_dictionary', 'root_adjudication', 'normalization_receipt')),
          'Need the exact source reviews and explicit post-observation normalization record')
    for ref in sources.values(): evidence.archive.read(ref)
    _need(sources['calibration']['sha256'] == '4ff4283f3fcc82146da23bd1d03ab51cdb7fe8e839750cead50421a4a41ae50e'
          and sources['quote_dictionary']['sha256'] == '0a88642fde57511c87b57bd888091182dc54bf6110bee10aa03d23ef7ebb4286'
          and sources['root_adjudication']['sha256'] == 'b9d5f2bb46f0f55b59d374ae5807a59918bb7425224266ca88aa328de9b92b29',
          'Changed the actual final Carbon mathematical calibration or Root decision')
    calibration = evidence.archive.json(sources['calibration'])
    selected = evidence.archive.json(sources['root_adjudication'])
    _need(calibration['mathematical_method_changed'] is False
          and calibration['delivery_admission_only_changes_operational_source_gate'] is True
          and selected['human_mathematical_approval'] is False
          and selected['admitted_delivery_sequence'] == [evidence.records[r]['delivery'] for r in flow.ROUNDS],
          'Normalization cannot invent human approval or change the admitted trajectory')
    for axis, key in (('taste', 'T'), ('capacity', 'C')):
        row = review['axes'][axis]
        original = calibration['axes_recommendation'][axis]
        root = selected[key]
        _need(all(row[k] == original[k] for k in ('mc_score', 'rmc_score', 'smc', 'all_required_checkpoints'))
              and (row['mc_score'], row['rmc_score'], row['smc']['exact']) == (root['mc'], root['rmc'], root['smc'])
              and [r['mc_points'] for r in row['directions'].values()] == root['positive_points']
              and [r['net_rmc_points'] for r in row['directions'].values()] == root['net_points']
              and [r['verdict'] for r in row['directions'].values()] == root['strict_gates']
              and [{k:r[k] for k in ('id','criterion','points','reason')} for r in row['error_deductions']] ==
                  [{k:r[k] for k in ('id','criterion','points','reason')} for r in original['error_deductions']],
              'Source-only normalization changed the actual Root-adopted mathematical judgment')


def validate_review(review, evidence, contract, *, case_id, review_policy_sha256):
    """Validate independent new judgments without entering a normal-final validator."""
    expected = dict(schema=REVIEW, edition=flow.EDITION, case_id=case_id,
        registration_sha256=evidence.registration_sha256, admission_sha256=evidence.admission_sha256,
        review_policy_sha256=review_policy_sha256, delivery_records=evidence.row_hashes)
    qualitative = 'round_diagnostics' in review
    diagnostics = 'round_diagnostics' if qualitative else 'round_reviews'
    extra = ('review_sources',) if 'review_sources' in review else ()
    _need(_fields(review, (*expected, 'reviewer', 'axes', 'gates', diagnostics,
          'selection_audit', 'error_roots', 'extension', *extra))
          and all(review[k] == v for k, v in expected.items()), 'Admitted review changed its exact selected source')
    reviewer = review['reviewer']
    _need(_fields(reviewer, ('requested_model', 'requested_effort', 'reviewer_id', 'reviewer_context_id',
          'reviewer_kind', 'human_review', 'backend_identity_independently_verified'))
          and all(reviewer[k] == v for k, v in adoption.REVIEWER.items())
          and all(modes._text(reviewer[k]) for k in ('reviewer_id', 'reviewer_context_id'))
          and reviewer['reviewer_context_id'] not in (evidence.candidate_context_id, evidence.native_session_id),
          'Need the actual independent Sol6.1 Max AI review, human pending')
    _need(all(_fields(review[key], flow.AXES) for key in ('axes', 'gates')), 'Missing original review axes')
    if qualitative:
        _need(_fields(review['round_diagnostics'], flow.ROUNDS), 'Need all three actually reviewed manuscripts')
        for rid, row in review['round_diagnostics'].items():
            _need(_fields(row, ('assessment', 'diagnostic_score', 'reason', 'evidence'))
                  and row['assessment'] == 'reviewed' and row['diagnostic_score'] is None,
                  'Qualitative review is reviewed mathematics, without an invented diagnostic number')
            _judgment({k: row[k] for k in ('reason', 'evidence')}, evidence, (rid,), ())
    else:
        _need(_fields(review['round_reviews'], flow.AXES), 'Missing original per-axis round diagnostics')
    _original_review_sources(review, evidence)
    roots = review['error_roots']
    _need(isinstance(roots, list) and len({r['id'] for r in roots}) == len(roots), 'Duplicate mathematical error root')
    for root in roots:
        _need(_fields(root, ('id', 'effects', 'reason', 'evidence')) and modes._text(root['id'])
              and root['effects'] and set(root['effects']) <= set(flow.AXES)
              and all(modes._text(v) for v in root['effects'].values()), 'Explain each genuine distinct axis effect')
        _judgment({k: root[k] for k in ('reason', 'evidence')}, evidence, flow.ROUNDS, ())
    axes, criteria, strict_credit = {}, {}, {}
    for axis in flow.AXES:
        by_round = None if qualitative else review['round_reviews'][axis]
        if by_round is not None:
            _need(_fields(by_round, contract['round_coverage'][axis]), 'Missing prescribed per-manuscript assessment')
            for rid, judgment in by_round.items():
                _judgment(judgment, evidence, (rid,), ('score', 'strict'))
        specs, gates = contract['gates'][axis], review['gates'][axis]
        _need(_fields(gates, [s['id'] for s in specs]), 'Wrong private review gate inventory')
        for spec in specs:
            permitted = flow.ROUNDS if axis == 'capacity' else spec['rounds']
            cited = _judgment(gates[spec['id']], evidence, permitted, ('verdict',))
            if axis != 'capacity' and gates[spec['id']]['verdict'] is True:
                _need(set(permitted) <= cited, 'Strict gate needs every prescribed manuscript')
        row = review['axes'][axis]
        verdicts = {s['id']: gates[s['id']]['verdict'] for s in specs if s['required']}
        if axis == 'autonomy':
            _judgment(row, evidence, flow.ROUNDS, ('score', 'strict'))
            _need(row['strict'] is flow._gate(list(verdicts.values())), 'Autonomy must retain its original required gates')
            autonomy = row['score']
            continue
        _need(_fields(row, ('mc_score', 'rmc_score', 'smc', 'all_required_checkpoints', 'reason', 'evidence',
                          'directions', 'error_deductions')) and modes._text(row['reason'])
              and ((row['mc_score'] is row['rmc_score'] is None) or
                   modes._score(row['mc_score']) and modes._score(row['rmc_score'])
                   and row['rmc_score'] <= row['mc_score']),
              'Admitted mathematical axes need independently reviewed positive and reliable credit')
        if row['rmc_score'] is None:
            count = credit._counts(verdicts)
            unknown = credit._bounds(credit._unallocated(None, count))
            _need(row['directions'] is None and row['error_deductions'] == [] and row['evidence'] == []
                  and row['smc'] == unknown and row['all_required_checkpoints'] is modes._criteria_flag(count)
                  and not any(axis in root['effects'] for root in roots),
                  'Unadjudicated aggregate stays unknown without invented allocations')
            axes[axis] = dict(mc=None, rmc=None, strict=modes._criteria_flag(count))
            criteria[axis], strict_credit[axis] = count, unknown
            continue
        cited = _judgment({k: row[k] for k in ('reason', 'evidence')}, evidence, flow.ROUNDS, ())
        _need(axis != 'capacity' or cited == set(flow.ROUNDS), 'Capacity must assess the actual complete trajectory')
        _need(qualitative or all(j['score'] is not None for j in by_round.values()), 'Need every manuscript assessment')
        limits = dict(value=60, structure=20, selection=20) if axis == 'taste' else dict.fromkeys(verdicts, 20)
        _need(_fields(row['directions'], limits), 'Retain the frozen60/20/20 or five20-point credit budgets')
        points, flags = {}, {}
        for key, detail in row['directions'].items():
            _need(_fields(detail, ('mc_points', 'net_rmc_points', 'verdict', 'reason', 'evidence'))
                  and credit._number(detail['mc_points'], limits[key])
                  and credit._number(detail['net_rmc_points'], limits[key])
                  and (detail['verdict'] is None or type(detail['verdict']) is bool), 'Invalid credit allocation')
            _judgment({k: detail[k] for k in ('reason', 'evidence')}, evidence, flow.ROUNDS, ())
            _need(axis != 'capacity' or detail['verdict'] is verdicts[key], 'Changed capacity gate in credit allocation')
            points[key], flags[key] = detail['mc_points'], detail['verdict']
        deductions, original = {}, {}
        for error in row['error_deductions']:
            _need(_fields(error, ('id', 'criterion', 'points', 'reason', 'evidence'))
                  and error['id'] not in original and error['criterion'] in limits
                  and credit._number(error['points'], 100) and error['points'] > 0
                  and error['id'] in {root['id'] for root in roots if axis in root['effects']},
                  'Each actual error root needs one source-bound allocation per affected axis')
            original[error['id']] = error['points']
            deductions[error['id']] = {k: error[k] for k in ('criterion', 'reason', 'evidence')}
        _need(set(original) == {root['id'] for root in roots if axis in root['effects']},
              'Do not omit an established error root from the admitted axis')
        grade = dict(mc=row['mc_score'], rmc=row['rmc_score'])
        interval = credit._net_credit(points, deductions, original, flags, grade, None,
            evidence_check=lambda refs: flow._evidence(refs, evidence.archive.root, evidence.records, set(flow.ROUNDS)))
        # Net allocations are explanatory source data, checked exactly, never a
        # separately computed display score or another mathematical judgment.
        for key, detail in row['directions'].items():
            net = Fraction(str(points[key])) - sum((Fraction(str(original[root])) for root, allocation in
                deductions.items() if allocation['criterion'] == key), Fraction())
            _need(Fraction(str(detail['net_rmc_points'])) == net, 'Declared net credit differs from its retained error roots')
        count = credit._counts(flags)
        _need(count['planned'] == (3 if axis == 'taste' else 5)
              and row['smc'] == credit._bounds(interval)
              and row['all_required_checkpoints'] is modes._criteria_flag(count)
              and modes._criteria_flag(count) is flow._gate(list(verdicts.values())),
              'Strict credit, frozen gate verdicts or unknown denominator changed')
        axes[axis] = dict(grade, strict=modes._criteria_flag(count))
        criteria[axis], strict_credit[axis] = count, row['smc']
    selection = review['selection_audit']
    _need(_fields(selection, ('sufficient_choices', 'reason', 'kept', 'removed'))
          and (selection['sufficient_choices'] is None or type(selection['sufficient_choices']) is bool)
          and modes._text(selection['reason']), 'Invalid actual selection audit')
    for key, rounds in (('kept', ('R3',)), ('removed', ('R1', 'R2'))):
        if selection[key]:
            flow._evidence(selection[key], evidence.archive.root, evidence.records, set(rounds))
    _need((selection['sufficient_choices'] is True or axes['taste']['mc'] is axes['taste']['rmc'] is None)
          and (axes['taste']['strict'] is not True or selection['sufficient_choices'] is True and bool(selection['kept'])),
          'Insufficient selectable mathematics must not gain a known taste score')
    extension = review['extension']
    _need(_fields(extension, ('level', 'assessed_rounds', 'independent_question', 'outside_core',
          'result_and_scope', 'value', 'reason', 'evidence')) and extension['level'] in value.EXTENSION
          and extension['assessed_rounds'] == list(flow.ROUNDS)
          and all(modes._text(extension[k]) for k in ('independent_question', 'outside_core', 'result_and_scope', 'value')),
          'Need the separate actual extension judgment; no E-to-initiative conversion')
    _judgment({k: extension[k] for k in ('reason', 'evidence')}, evidence, flow.ROUNDS, ())
    return dict(axes=axes, criteria=criteria, strict_credit=strict_credit,
                extension_level=extension['level'], autonomy_score=autonomy)


def baseline(root, ref):
    _need(_fields(ref, ('path', 'bytes', 'sha256')) and adoption._is_hash(ref['sha256'])
          and ref['path'] == f'results/independent-research-baselines/v0.1.0/{ref["sha256"]}/data.json',
          'Admitted source requires its own immutable complete1.2 parent')
    raw = flow._read(Path(root), ref)
    data = value._json(raw)
    _need(data.get('benchmark_version') == '1.2.0' and isinstance(data.get('models'), list)
          and len({m['id'] for m in data['models']}) == len(data['models']), 'Invalid unique-model1.2 parent')
    return raw, data


def retained_case_reader(registration, manifest_path, public_root):
    """Replay only the original source validator; current scoring stays current.

    The three trusted public files must match both the original registration
    descriptors and their regular blobs in an explicit complete local commit.
    No fallback, source edit, global module replacement or old-score execution.
    """
    from .evidence_retention import _git
    path = flow._safe_absolute(manifest_path)
    raw = path.read_bytes()
    manifest = value._json(raw)
    registered = value._json(Path(registration).read_bytes())
    _need(_fields(manifest, ('schema', 'source_commit', 'registration_sha256', 'root', 'files',
          'reader_use', 'final_scoring_owner', 'network_fetch'))
          and manifest['schema'] == FROZEN_RUNNER and manifest['root'] == 'frozen-runner'
          and isinstance(manifest['source_commit'], str) and len(manifest['source_commit']) == 40
          and all(c in '0123456789abcdef' for c in manifest['source_commit'])
          and manifest['registration_sha256'] == digest(Path(registration).read_bytes())
          and manifest['files'] == registered['runner']['files']
          and manifest['reader_use'] == 'original-load-case-only'
          and manifest['final_scoring_owner'] == 'current-shared-scoring'
          and manifest['network_fetch'] is False, 'Invalid explicit frozen-runner source binding')
    frozen_root = flow._contained(path.parent, manifest['root'])
    _need(_git(public_root, 'cat-file', '-t', manifest['source_commit']).strip() == b'commit',
          'Frozen runner needs its complete local source commit; never fetch')
    files = {}
    for ref in manifest['files']:
        payload = flow._read(frozen_root, ref)
        entry = _git(public_root, 'ls-tree', manifest['source_commit'], '--', ref['path']).decode().strip()
        head, name = entry.split('\t')
        mode, kind, blob = head.split()
        _need(name == ref['path'] and mode == '100644' and kind == 'blob'
              and _git(public_root, 'cat-file', 'blob', blob) == payload,
              'Frozen runner differs from the original regular local Git blob')
        files[ref['path']] = payload
    _need(set(files) == {'math_gauge/taste_v130.py','math_gauge/scoring.py',
                        'protocol/mathematical-taste/v1.3.0/policy.json'},
          'Frozen source reader can load only the original three runner files')
    module = ModuleType('math_gauge._retained_admitted_case_reader')
    module.__file__ = str(frozen_root/'math_gauge/taste_v130.py')
    # Execute verified original public reader bytes without a loader/pycache.
    exec(compile(files['math_gauge/taste_v130.py'], module.__file__, 'exec'), module.__dict__)
    result = module.load_case(registration)
    _need(path.read_bytes() == raw, 'Frozen runner selection changed during verification')
    return result


def prepare(selection_path, public_root):
    """Offline source/review validation only; incomplete trajectories cannot emit a score."""
    selection_path, public_root = map(flow._safe_absolute, (selection_path, public_root))
    raw = selection_path.read_bytes()
    selection = value._json(raw)
    frozen = selection.get('schema') == FROZEN_SELECTION
    _need(_fields(selection, ('schema', 'baseline', 'registration', 'review_policy', 'admission', 'review',
                             *(['frozen_runner'] if frozen else [])))
          and selection['schema'] in (SELECTION,FROZEN_SELECTION), 'Expected a separate Carbon admitted-delivery selection')
    sources = {name: adoption._external(selection_path.parent, selection[name]) for name in
               ('registration', 'review_policy', 'admission', 'review')}
    if frozen:
        runner_path, runner_raw = adoption._external(selection_path.parent, selection['frozen_runner'])
        registration, case, registered = retained_case_reader(sources['registration'][0], runner_path, public_root)
        sources['frozen_runner'] = (runner_path, runner_raw)
    else:
        registration, case, registered = flow.load_case(sources['registration'][0])
    trajectory_hash = trajectory._policy_binding(registration,case,registered,sources['review_policy'][0])
    evidence = load_admission(sources['admission'][0], digest(sources['registration'][1]), round_prompts=registered['rounds'])
    contract = value._json(flow._read(case, registered['review_contract']))
    grade = validate_review(value._json(sources['review'][1]), evidence, contract,
                            case_id=registered['case_id'], review_policy_sha256=trajectory_hash)
    parent_raw, parent = baseline(public_root, selection['baseline'])
    _need(MODEL in [m['id'] for m in parent['models']], 'Admitted model is absent from its own actual1.2 parent')
    deliveries = [evidence.records[r]['delivery'] for r in flow.ROUNDS]
    binding = digest(encoded(dict(admission=evidence.admission_sha256, review=digest(sources['review'][1]),
        archive=digest(evidence.archive.raw), history=evidence.original['history']['sha256'], trajectory_policy=trajectory_hash)))
    row = dict(status='reviewed', **grade, normal_rounds=deliveries.count('normal-final'),
               forced_rounds=deliveries.count('forced-content'), round_dispatches=3,
               delivery_kinds=deliveries, source_sha256=binding)
    result = dict(schema=SCHEMA, version='0.1.0', edition=flow.EDITION, source_kind=SOURCE_KIND,
        source_binding=dict(base_edition='1.2.0', baseline=selection['baseline'], adoption_sha256=digest(raw),
            admission_sha256=evidence.admission_sha256, review_sha256=digest(sources['review'][1]),
            authorization_sha256=evidence.original['authorization']['sha256']),
        policy_bindings=external.policy_bindings(public_root), cohort=[MODEL], models={MODEL: row},
        method=dict(selection='post-observation-user-selected-cutoff', native_status_preserved=True,
            forced_content_is_mathematically_reviewed=True, original_round_limit_seconds=2700,
            R1_user_extension_seconds=900, account_condition_changed=True,
            historical_results_unchanged=True, resource_usage_scope='unknown-until-independently-reconciled'),
        reviewer_kind='ai', human_review='pending', candidate_calls_by_adoption=0)
    if frozen:
        result['source_binding']['frozen_runner_sha256'] = digest(runner_raw)
    evidence.archive.unchanged()
    _need(selection_path.read_bytes() == raw and all(p.read_bytes() == b for p, b in sources.values()),
          'Selected source or review changed during verification')
    return validate_public(result, policies=external.policy_bindings(public_root),
                           baseline_hash=digest(parent_raw), model_ids=[MODEL])


def validate_public(index, *, policies=None, baseline_hash=None, model_ids=None):
    """Allowlist aggregate public fields; no private identifiers, paths or quotations."""
    _need(_fields(index, ('schema', 'version', 'edition', 'source_kind', 'source_binding', 'policy_bindings',
          'cohort', 'models', 'method', 'reviewer_kind', 'human_review', 'candidate_calls_by_adoption'))
          and index['schema'] == SCHEMA and index['version'] == '0.1.0' and index['edition'] == flow.EDITION
          and index['source_kind'] == SOURCE_KIND and index['cohort'] == [MODEL]
          and _fields(index['models'], (MODEL,)) and index['reviewer_kind'] == 'ai'
          and index['human_review'] == 'pending' and type(index['candidate_calls_by_adoption']) is int
          and index['candidate_calls_by_adoption'] == 0
          and (model_ids is None or MODEL in model_ids), 'Invalid admitted public aggregate or leaked private fields')
    binding = index['source_binding']
    extra = ('frozen_runner_sha256',) if 'frozen_runner_sha256' in binding else ()
    _need(_fields(binding, ('base_edition', 'baseline', 'adoption_sha256', 'admission_sha256',
          'review_sha256', 'authorization_sha256', *extra))
          and (not extra or adoption._is_hash(binding['frozen_runner_sha256'])) and binding['base_edition'] == '1.2.0'
          and all(adoption._is_hash(binding[k]) for k in ('adoption_sha256', 'admission_sha256',
              'review_sha256', 'authorization_sha256')) and binding['authorization_sha256'] == AUTHORIZATION_SHA256,
          'Lost exact independent admitted source selection')
    parent = binding['baseline']
    _need(_fields(parent, ('path', 'bytes', 'sha256')) and adoption._is_hash(parent['sha256'])
          and type(parent['bytes']) is int and parent['bytes'] >= 0
          and parent['path'] == f'results/independent-research-baselines/v0.1.0/{parent["sha256"]}/data.json'
          and (baseline_hash is None or parent['sha256'] == baseline_hash)
          and _fields(index['policy_bindings'], external.POLICY_PATHS)
          and all(adoption._is_hash(v) for v in index['policy_bindings'].values())
          and (policies is None or index['policy_bindings'] == policies), 'Invalid exact public parent or scoring policy')
    _need(index['method'] == dict(selection='post-observation-user-selected-cutoff', native_status_preserved=True,
          forced_content_is_mathematically_reviewed=True, original_round_limit_seconds=2700,
          R1_user_extension_seconds=900, account_condition_changed=True, historical_results_unchanged=True,
          resource_usage_scope='unknown-until-independently-reconciled'), 'Changed actual method or invented resource certainty')
    row = index['models'][MODEL]
    _need(_fields(row, ('status', 'axes', 'criteria', 'strict_credit', 'extension_level', 'autonomy_score',
          'normal_rounds', 'forced_rounds', 'round_dispatches', 'delivery_kinds', 'source_sha256'))
          and row['status'] == 'reviewed' and row['round_dispatches'] == 3
          and isinstance(row['delivery_kinds'], list) and len(row['delivery_kinds']) == 3
          and set(row['delivery_kinds']) <= {'normal-final', 'forced-content'}
          and row['delivery_kinds'][0] == 'forced-content'
          and type(row['normal_rounds']) is type(row['forced_rounds']) is int
          and row['normal_rounds'] == row['delivery_kinds'].count('normal-final')
          and row['forced_rounds'] == row['delivery_kinds'].count('forced-content')
          and row['normal_rounds'] + row['forced_rounds'] == 3
          and adoption._is_hash(row['source_sha256']) and row['extension_level'] in value.EXTENSION
          and (row['autonomy_score'] is None or modes._score(row['autonomy_score']))
          and all(_fields(row[k], value.AXES) for k in ('axes', 'criteria', 'strict_credit')),
          'Invalid admitted delivery counts or public score contract')
    for axis in value.AXES:
        grade, count, bound = row['axes'][axis], row['criteria'][axis], row['strict_credit'][axis]
        _need(_fields(grade, ('mc', 'rmc', 'strict'))
              and (grade['mc'] is grade['rmc'] is None or modes._score(grade['mc'])
                   and modes._score(grade['rmc']) and grade['rmc'] <= grade['mc'])
              and _fields(count, ('planned', 'passed', 'unknown'))
              and all(type(v) is int and v >= 0 for v in count.values())
              and count['planned'] == (3 if axis == 'taste' else 5)
              and count['passed'] + count['unknown'] <= count['planned']
              and grade['strict'] is modes._criteria_flag(count), 'Changed fixed mathematical denominator')
        _need(_fields(bound, ('lower', 'upper', 'exact'))
              and all(modes._score(bound[k]) for k in ('lower', 'upper'))
              and bound['lower'] <= bound['upper'] <= (100 if grade['rmc'] is None else grade['rmc'])
              and (bound['exact'] is None or bound['lower'] == bound['upper'] == bound['exact']),
              'Invalid retained strict-credit interval')
        direct = credit._direct(grade['rmc'], count)
        _need(direct is None or bound == credit._bounds(direct), 'Direct strict credit must retain its actual RMC')
    return index


def project_model(base_reports, policy, public_row):
    """All weights and score arithmetic remain in the existing scoring owner."""
    result = external.project_model(base_reports, policy, public_row)
    result['admitted_source_sha256'] = result.pop('external_source_sha256')
    return result
