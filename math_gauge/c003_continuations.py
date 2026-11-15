"""Evaluator-only source admission for the named C003 sealed continuation.

This owner reads retained evidence. It does not execute models, candidate code,
Lean, or score mathematics. The original A1 and submission observations are
never mutated. The first version admits the prospectively frozen Argon chain;
retained normal prefixes need their own explicit source-contract adapter.
"""
from dataclasses import dataclass
from pathlib import Path
import hashlib
import json
import math
import sqlite3
import tempfile

from . import agy_evidence
from .benchmarks import identity
from .catalog import validate_alignment_manifest

VERSION = '0.1.0'
COMPONENT = 'c003-sealed-continuation/' + VERSION
SCHEMA = 'math-gauge.c003-sealed-continuation/v1'
CONDITION = 'nonlogical_retry_3'
LEGACY_COMPONENT_VERSION = '0.2.0'
LEGACY_BASELINE_ADAPTER = 'retained-operational-workspace/0.1.0'


def require(value, message):
    if not value:
        raise ValueError(message)


def read(root, item):
    # Import at call time: records owns the canonical retained-byte reader.
    from .records import evidence_bytes
    return evidence_bytes(root, item)


def document(root, item):
    return json.loads(read(root, item))


def _safe_name(name):
    require(isinstance(name, str) and name and not Path(name).is_absolute()
            and all(p and p not in {'.', '..'} for p in name.split('/'))
            and '\\' not in name, 'Unsafe C003 workspace path')
    return name


def _inventory(root, node, seal):
    supplied = node.get('files')
    require(isinstance(supplied, list), 'C003 source needs its whole actual seal inventory')
    files = {}
    for entry in supplied:
        name = _safe_name(entry['name'])
        require(name not in files, 'Repeated C003 workspace file')
        require(entry.get('retained_kind') == 'regular', 'C003 source cannot follow links')
        raw = read(root, entry['evidence'])
        files[name] = (entry['evidence'], raw)
    original = seal.get('work')
    require(isinstance(original, list) and len(original) == len(files)
            and len({r['path'] for r in original}) == len(original)
            and not seal.get('symlinks_not_followed'),
            'C003 seal inventory is missing, ambiguous or unresolved')
    for entry in original:
        name = _safe_name(entry['path'])
        require(name in files and all(files[name][0][k] == entry[k] for k in ('bytes', 'sha256')),
                'C003 retained source differs from the actual seal')
    return files


def _semantic_inventory(files):
    # Transport attachments and regenerated tool configuration are not proofs.
    # Candidate Lean source, mapping and build/dependency contracts all count.
    names = {'alignment.json', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json'}
    return {name: (item['bytes'], item['sha256']) for name, (item, _) in files.items()
            if name.endswith('.lean') or name in names}


def _review(root, node, files, ids):
    review = document(root, node['math_review'])
    require(review.get('schema') == 'math-gauge.c003-sealed-source-review/v1'
            and review.get('version') == VERSION and review.get('case_id') == 'MG-C003'
            and review.get('case_version') == '0.1.1' and review.get('phase') == node['phase']
            and review.get('source_seal_sha256') == node['seal']['sha256']
            and review.get('reviewer_kind') == 'ai' and review.get('human_review') == 'pending'
            and review.get('source_repaired') is False,
            'C003 mathematical review lost its original sealed source')
    rows = review.get('obligations')
    require(isinstance(rows, list) and len(rows) == len(ids)
            and {r.get('id') for r in rows} == ids
            and all(r.get('complete') is None or type(r.get('complete')) is bool for r in rows),
            'C003 review must preserve the complete 92-ID inventory and unknowns')
    kernel = document(root, review['kernel_review'])
    require(kernel.get('schema') == 'math-gauge.c003-source-kernel-review/v1'
            and kernel.get('source_seal_sha256') == node['seal']['sha256']
            and kernel.get('source_repaired') is False and kernel.get('evidence')
            and kernel.get('files_sha256') == {n: d['sha256'] for n, (d, _) in files.items() if n.endswith('.lean')},
            'C003 kernel evidence belongs to other source bytes')
    for item in kernel['evidence']:
        read(root, item)
    audited = {(r['file'], r['name']) for r in kernel.get('audited_declarations', [])}
    for row in rows:
        if row['complete'] is True:
            require(kernel.get('status') == 'passed' and kernel.get('axioms_allowed') is True
                    and row.get('declarations') and all((d['file'], d['name']) in audited for d in row['declarations']),
                    'Verified C003 obligations need bound kernel and declaration evidence')
    return review


def _project_delivery(root, node, files, contract):
    # Completeness here is the actual delivered project structure, not 92/92.
    require({'Main.lean', 'alignment.json'} <= files.keys(), 'FULL/KEEP needs the actual complete project')
    mapping = validate_alignment_manifest(json.loads(files['alignment.json'][1]), contract)
    require(all(d['file'] in files for row in mapping['items'] for d in row['declarations']),
            'C003 alignment names a missing source file')
    structure = document(root, node['project_review'])
    require(structure.get('schema') == 'math-gauge.c003-project-delivery-review/v1'
            and structure.get('source_seal_sha256') == node['seal']['sha256']
            and structure.get('reviewer_kind') == 'ai'
            and structure.get('entry') == 'Main.lean'
            and structure.get('all_target_modules_in_main_import_closure') is True
            and set(structure.get('local_lean_files', [])) == {n for n in files if n.endswith('.lean')},
            'Complete engineering delivery needs its source-bound import-closure review')


def _native(root, node, *, failed, plan):
    row = node['native']
    require(row.get('case_id') == 'MG-C003' and row.get('id') == 'MG-C003:' + node['phase'],
            'C003 native receipt borrowed another phase')
    if failed:
        receipt = agy_evidence.validate_failure(root, row, read)
        execution = document(root, receipt['native_execution'])
        agy_evidence.validate_local_tools(root, row, execution, read)
    else:
        agy_evidence.validate_delivery(root, row, read)
        receipt = document(root, row['agy_native_evidence'])
        execution = document(root, receipt['native_execution'])
    require(receipt.get('native_terminal_seal') == node['seal'],
            'C003 engineering seal is not that native request seal')
    require(execution.get('requested_model') == plan['model']
            and execution.get('requested_effort') == plan['effort'], 'C003 model/runtime identity changed')
    if plan.get('_tool_binary_sha256') is not None:
        require(execution.get('parent_identity', {}).get('executable_sha256') == plan['_tool_binary_sha256'],
                'C003 observed executable differs from the frozen tool identity')
    auth = read(root, node['authentication_evidence'])
    require(b'authMethod=consumer, quotaProject=' in auth and b'authMethod=gcp' not in auth,
            'C003 supplement changed the frozen subscription execution condition')


def _native_database_inventory(root, inventory):
    """Hash every step, but decode no hidden payload or thought text.

    Raw native DBs use WAL header flags. sqlite.deserialize then querying an
    in-memory handle fails on these exact bytes. A private immutable file copy
    permits read-only queries without rewriting the source header or DB.
    """
    raw = read(root, inventory['source_database'])
    with tempfile.TemporaryDirectory(prefix='c003-native-read-') as temporary:
        path = Path(temporary) / 'native.db'
        path.write_bytes(raw)
        connection = sqlite3.connect(path.as_uri() + '?mode=ro&immutable=1', uri=True)
        try:
            connection.execute('PRAGMA query_only=ON')
            identities = connection.execute('SELECT trajectory_id,cascade_id FROM trajectory_meta').fetchall()
            require(any(inventory['conversation_id'] in row for row in identities),
                    'C003 native DB belongs to another conversation')
            rows = connection.execute('SELECT idx,step_type,status,step_payload FROM steps ORDER BY idx').fetchall()
        finally:
            connection.close()
    canonical = [dict(idx=idx, step_type=kind, native_status_code=status,
                      payload_sha256=hashlib.sha256(payload or b'').hexdigest())
                 for idx,kind,status,payload in rows]
    supplied = [{k:r[k] for k in ('idx','step_type','native_status_code','payload_sha256')}
                for r in inventory['rows']]
    require(canonical == supplied, 'C003 native inventory differs from the complete original DB')
    return {idx:payload for idx,kind,status,payload in rows if kind == 15 and status == 3}


def _final_body(root, node):
    """Read a native final body; never strip progress or search for a marker."""
    aggregate = read(root, node['native']['response'])
    if node.get('final_body_extraction') is None:
        require(node.get('final_body') is None,
                'A distinct native final body needs its original extraction witness')
        return aggregate
    from .result_corrections import _field
    extraction = document(root, node['final_body_extraction'])
    body = read(root, node['final_body'])
    inventory = document(root, extraction['native_step_inventory'])
    bodies = _native_database_inventory(root, inventory)
    completed = [r for r in inventory['rows']
                 if r.get('step_type') == 15 and r.get('native_status_code') == 3]
    require(completed and len({r['idx'] for r in inventory['rows']}) == len(inventory['rows']),
            'Native final extraction needs the complete ordered source step inventory')
    selected = max(completed, key=lambda row: row['idx'])
    payload = read(root, extraction['selected_step_payload'])
    require(extraction.get('schema') == 'math-gauge.normal-native-final-body-extraction/v1'
            and extraction.get('version') == VERSION and extraction.get('phase') == node['phase']
            and extraction.get('source_raw_bytes_rewritten') is False
            and extraction.get('native_terminal_status') == 'SUCCESS'
            and extraction.get('selection') == 'highest_completed_agent_response_index'
            and extraction.get('aggregate_response') == node['native']['response']
            and extraction.get('final_body') == node['final_body']
            and extraction.get('selected_step_index') == selected['idx']
            and selected.get('payload_sha256') == extraction['selected_step_payload']['sha256']
            and payload == bodies[selected['idx']]
            and _field(_field(payload, 20), 1) == body
            and body and body in aggregate,
            'Native final extraction changed original bytes or selected by content')
    # The DB closes inventory completeness and native status3. This remains
    # post-observation extraction, never a reconstructed native SUCCESS.
    require(inventory.get('conversation_id') == extraction.get('conversation_id')
            and inventory.get('complete_conversation_export') is True,
            'Native final extraction borrowed an incomplete or foreign conversation')
    for item in inventory.get('source_evidence', []):
        read(root, item)
    require(inventory.get('source_evidence'), 'Native step inventory needs its retained original export')
    return body


@dataclass(frozen=True)
class ContinuationInputs:
    """Immutable normalized review, created only after reading original sources."""
    _payload: bytes

    def for_score(self, inputs, *, condition):
        data = json.loads(self._payload)
        require(condition == data['condition'] and inputs.get('model_label') == data['model_label']
                and identity(inputs) == data['target_inputs_identity'],
                'C003 continuation cannot cross record, model or attempt condition')
        return data


def _legacy_file_inventory(root,node,manifest):
    """Retain original source while naming unavailable compiler caches."""
    omitted = node.get('omitted_non_source_cache', [])
    require(isinstance(omitted, list) and len(omitted) == len(set(omitted))
            and all(_safe_name(name).endswith('.olean') and name in manifest['files'] for name in omitted),
            'Only explicitly unavailable legacy compiler caches may be omitted')
    files = {}
    for entry in node['files']:
        name = _safe_name(entry['name'])
        require(name not in files and name in manifest['files']
                and entry.get('retained_kind') == 'regular', 'Invalid legacy regular-file inventory')
        raw = read(root, entry['evidence'])
        require(all(entry['evidence'][key] == manifest['files'][name][key] for key in ('bytes','sha256')),
                'Legacy C003 source bytes differ from the retained manifest')
        files[name] = (entry['evidence'], raw)
    require(set(files) == set(manifest['files']) - set(omitted),
            'Legacy C003 reconstruction dropped original source or invented cache recovery')
    return files


def _legacy_supplied_inputs(root,node,files,kernel,request):
    """Append exact frozen inputs without repairing candidate mathematics."""
    frozen_inputs = {row['name']:row['content'].encode() for row in request['files']}
    require(len(frozen_inputs) == len(request['files']), 'Original frozen request repeats an input name')
    supplied = node.get('runtime_supplied_inputs', [])
    supplied_names = set()
    for entry in supplied:
        name = _safe_name(entry['name']); raw = read(root, entry['evidence'])
        require(name not in supplied_names, 'Runtime supplied input names must be unique')
        supplied_names.add(name)
        read(root, entry['origin_evidence'])
        require(frozen_inputs.get(name) == raw, 'Runtime supplied bytes differ from the original frozen request')
        if name in files:
            require(files[name][1] == raw, 'Runtime supplied input overwrote an original legacy file')
        elif name.endswith('.lean'):
            require(kernel.get('input_files_sha256', {}).get(name) == entry['evidence']['sha256'],
                    'Runtime supplied Lean source is not an original frozen dependency')
        else:
            require(name.startswith('source/') or name in {'obligations.json','dependencies.md','ATTRIBUTION.md','LICENSE'},
                    'Runtime supplied input cannot repair candidate source, Main or alignment')
        files[name] = (entry['evidence'], raw)
    require(all(name in files and files[name][1] == raw for name,raw in frozen_inputs.items()),
            'Legacy reconstruction must retain every original frozen request input unchanged')
    return files


def _legacy_record_binding(root,data,record,inputs,selection):
    """Bind the old public workspace review to this unchanged private record."""
    public = document(root,data['public_base_record'])
    original = public.get('formalization_review', {})
    retained = data['baseline']['original_formalization_review']
    require(public.get('schema') == record.get('schema') == 'math-gauge.result-record/v1'
            and public.get('benchmark_version') == record.get('benchmark_version')
            and public.get('record_id') == record.get('record_id') == selection.get('record_id')
            and public.get('model', {}).get('requested_label')
                == record.get('model', {}).get('requested_label') == inputs.get('model_label')
            and public.get('model', {}).get('display') == selection.get('model_id')
            and original == record.get('formalization_review')
            and original.get('path') == 'reviews/formalization.json'
            and all(original.get(key) == retained.get(key) for key in ('bytes','sha256')),
            'Legacy C003 public baseline review belongs to another model or original record')
    read(root,retained)
    return public


def _legacy_baseline(root, node, snapshot, ids):
    """Admit an old selected workspace without inventing a native receipt.

    The retained manifest is an archival source anchor. It is deliberately
    distinct from both a native terminal seal and a newly reconstructed parent.
    """
    require(node.get('phase') == 'baseline' and node.get('source_origin') == 'legacy_archived_source'
            and node.get('adapter') == LEGACY_BASELINE_ADAPTER
            and all(node.get(key) is None for key in ('native','seal','final_body','final_body_extraction')),
            'A legacy C003 parent cannot manufacture a new native delivery')
    manifest = document(root, node['legacy_manifest'])
    require(manifest.get('tree_sha256') == node.get('source_tree_sha256')
            and isinstance(manifest.get('files'), dict), 'Legacy C003 manifest source changed')
    files = _legacy_file_inventory(root,node,manifest)
    original = document(root, node['original_formalization_review'])
    chapter = next((row for row in original.get('cases', []) if row.get('case_id') == 'MG-C003'), None)
    kernel = document(root, node['original_kernel_review'])
    require(chapter is not None and chapter.get('case_version') == '0.1.1'
            and chapter.get('source_sha256') == node['source_tree_sha256']
            and chapter.get('source_kind') == 'sealed_workspace'
            and kernel.get('schema') == 'math-gauge.candidate-lean/v1'
            and kernel.get('source_repaired') is False
            and kernel.get('reliability_binding', {}).get('sealed_tree_sha256') == node['source_tree_sha256'],
            'Legacy C003 review belongs to another archived workspace')
    for name, digest in chapter.get('compiled_sources', {}).items():
        require(name in files and files[name][0]['sha256'] == digest
                and kernel.get('files_sha256', {}).get(name) == digest,
                'Legacy C003 selected target source differs from the original kernel review')
    request = document(root, node['original_candidate_request'])
    require(request.get('schema') == 'math-gauge.request/v1' and request.get('case_id') == 'MG-C003'
            and request.get('case_version') == '0.1.1', 'Legacy supplied files need the original case request')
    files = _legacy_supplied_inputs(root,node,files,kernel,request)
    rows = chapter.get('obligations', [])
    require(len(rows) == 92 and {row.get('id') for row in rows} == ids
            and {row['id']: row.get('complete') for row in rows}
                == {row['id']: row.get('complete') for row in snapshot.get('obligations', [])}
            and snapshot.get('source_kind') == 'sealed_workspace'
            and snapshot.get('source_sha256') == node['source_tree_sha256']
            and snapshot.get('delivery_verified') is False
            and node['original_formalization_review']['sha256'] in snapshot['review_evidence_sha256'],
            'Legacy C003 baseline must preserve its original complete 92-ID judgments')
    require(not any(row.get('complete') is True for row in rows) or
            chapter.get('kernel_status') == kernel.get('status') == 'passed'
            and kernel.get('audit', {}).get('summary', {}).get('passed') is True,
            'Legacy completion needs its unchanged original kernel and axiom evidence')
    if node.get('independent_baseline_review') is not None:
        recheck=document(root,node['independent_baseline_review'])
        require(recheck.get('schema') == 'math-gauge.c003-independent-baseline-semantic-review/v1'
                and recheck.get('reviewer_kind') == 'ai' and recheck.get('human_approval') is False
                and recheck.get('baseline_binding', {}).get('historical_tree_sha256') == node['source_tree_sha256']
                and recheck['baseline_binding'].get('proof_main_alignment_modified') is False
                and {row['id']:row['complete']for row in recheck.get('per_obligation',[])}
                    == {row['id']:row['complete']for row in rows},
                'Independent legacy baseline review changed the selected original source judgments')
    reconstruction = document(root, node['reconstruction_manifest'])
    require(reconstruction.get('schema') == 'math-gauge.legacy-workspace-operator-reconstruction/v1'
            and reconstruction.get('is_historical_native_seal') is False
            and reconstruction.get('normal_final_invented') is False
            and reconstruction.get('candidate_source_modified') is False
            and reconstruction.get('Main_or_alignment_repaired') is False
            and reconstruction.get('missing_legacy_cache_reconstructed') is False
            and reconstruction.get('source_anchor_legacy_tree_sha256') == node['source_tree_sha256']
            and {r['path']:(r['bytes'],r['sha256']) for r in reconstruction['work']}
                == {name:(item['bytes'],item['sha256']) for name,(item,_) in files.items()},
            'Legacy runtime reconstruction changed source or claimed a historical native seal')
    history = document(root, node['own_history'])
    require(history.get('schema') == 'math-gauge.source-visible-history/v1'
            and history.get('evaluator_feedback_included') is False
            and history.get('old_selfcheck_rounds_included') is False,
            'Legacy C003 must preserve only its selected pre-R1 own visible history')
    original_sources = history.get('message_sources', [])
    retained_sources = node.get('history_sources', [])
    require(len(history.get('messages', [])) == len(original_sources) == len(retained_sources)
            and history.get('original_a1_visible_reply', {}).get('assistant_message_inserted') is False
            and history.get('extension_visible_reply', {}).get('normal_final_inferred') is False
            and history.get('extension_visible_reply', {}).get('native_assistant_turn_boundaries_reconstructed') is False,
            'Legacy history must preserve missing A1 text and original aggregate boundaries')
    messages = []
    for message, source, retained in zip(history['messages'], original_sources, retained_sources):
        raw = read(root, retained)
        require(message.get('role') in {'system','user','assistant'}
                and source['role'] == message['role']
                and all(source[key] == retained[key] for key in ('bytes','sha256'))
                and raw == message['content'].encode(), 'Legacy visible history bytes or roles changed')
        messages.append(dict(role=message['role'],content=raw.decode()))
    require(messages and any(m['role'] == 'user' for m in messages), 'Legacy C003 history is missing its original question')
    original_conversation = document(root, node['original_extension_conversation'])
    original_freeze = document(root, node['original_execution_freeze'])
    request_digest = hashlib.sha256(json.dumps(request, ensure_ascii=False, sort_keys=True).encode()).hexdigest()
    require(node['original_extension_conversation']['sha256'] in original_freeze.get('bindings', {}).values()
            and original_freeze.get('parent', {}).get('tree_sha256') == node['source_tree_sha256']
            and original_conversation.get('messages') == messages[:-1]
            and messages[-1]['role'] == 'assistant'
            and hashlib.sha256(messages[-1]['content'].encode()).hexdigest() == original_freeze['parent']['response_sha256']
            and history.get('original_candidate_request_sha256') == request_digest
            and history.get('original_candidate_request_canonical_identity') == identity(request),
            'Legacy C003 replay no longer matches its original frozen own conversation')
    return files, messages


def effective_base_reports(public_root, private_root, model, public, private):
    """Resolve immutable original reports, then any explicitly selected A1 erratum.

    This intentionally never resolves a C003 continuation: a continuation
    cannot become its own base or rewrite frozen reports during retention.
    """
    from . import result_corrections
    from .records import load_assessment_results, load_retry_inputs
    public_root, private_root, public, private = map(Path, (public_root,private_root,public,private))
    record, original = (json.loads((folder/'record.json').read_bytes()) for folder in (public,private))
    correction = result_corrections.load_selected(public_root, model, public, record=record)
    if correction is not None:
        private_scores = result_corrections.verify_private(private_root,public_root,model,private,correction)
        public_scores = correction['_scores']
        order = ['original_record','selected_hch02_correction','selected_c003_continuation']
    else:
        private_scores, public_scores = {}, {}
        for mode in ('capability','partial','strict'):
            private_scores[mode] = load_assessment_results(private,original,mode=mode,public_root=public)[CONDITION]
            public_scores[mode] = load_assessment_results(public,record,mode=mode)[CONDITION]
        order = ['original_record','selected_c003_continuation']
    require(all(score.get('c003_continuation') is None for score in private_scores.values()),
            'A C003 continuation cannot recursively replace its own base')
    if original.get('attempt_condition_sources') is not None:
        sources = document(private,original['attempt_condition_sources'])
        inputs = document(private,sources['conditions'][CONDITION]['scoring_inputs'])
    else:
        inputs = load_retry_inputs(private,original,public_root=public,validate_results=False)
        if inputs is None:
            from .evidence_retention import read_bytes
            raw = read_bytes(private/'scoring-inputs.json')
            require(all(score.get('source_bindings', {}).get('scoring_inputs_sha256') == hashlib.sha256(raw).hexdigest()
                        for score in private_scores.values()), 'Original C003 input bytes changed')
            inputs = json.loads(raw)
    return dict(private=private_scores,public=public_scores,inputs=inputs,order=order)


def _operational_exclusions(root, entries, rounds):
    """Retain the proved empty-SUCCESS environment fault without relabelling it.

    This is a named0.2 source adapter, not a relaxation of validate_failure and
    not a mathematical-quality retry. Original absolute labels are never read.
    """
    require(isinstance(entries,list), 'C003 operational exclusions need an explicit source list')
    seen=set()
    fields={'original_terminal','original_result','original_seal','original_response','native_events',
            'visible_command_evidence','supplied_lean_environment'}
    for entry in entries:
        receipt=document(root,entry['receipt'])
        key=(receipt.get('phase'),receipt.get('physical_request'))
        require(receipt.get('schema') == 'math-gauge.c003-operational-exclusion/v1'
                and receipt.get('version') == VERSION and key not in seen
                and key[0] in {'R1','R2','R3'} and type(key[1]) is int and key[1] > 0
                and receipt.get('category') == 'proven_system_configuration_failure'
                and all(receipt.get(field) is False for field in ('effective_attempt_consumed','workspace_used_as_parent',
                    'native_status_rewritten','normal_final_reconstructed','mathematical_quality_used_for_exclusion')),
                'C003 system exclusion changed its preserved source classification')
        retained=entry['retained']
        require(set(retained)==fields, 'C003 operational exclusion lost original evidence')
        for field,item in retained.items():
            read(root,item)
            require(all(item[k]==receipt[field][k]for k in ('bytes','sha256')),
                    'C003 system exclusion source bytes changed')
        terminal=document(root,retained['original_terminal'])
        result=document(root,retained['original_result'])
        seal=document(root,retained['original_seal'])
        events=[json.loads(line)for line in read(root,retained['native_events']).splitlines()]
        response=read(root,retained['original_response'])
        require(terminal.get('result', {}).get('status') == seal.get('native_status') == 'SUCCESS'
                and terminal['result'].get('response','').encode() == response == b''
                and terminal['result'].get('denied_actions')
                and result.get('normal_complete_delivery') is False
                and seal.get('normal_complete_delivery') is False
                and [event for event in events if event.get('event')=='result']==[terminal],
                'C003 system exclusion must preserve exact empty SUCCESS and denied-action evidence')
        for node in rounds:
            require(node.get('physical_request_global') is None
                    or node['physical_request_global'] != key[1],
                    'Excluded physical request cannot be the selected final')
            require(node.get('parent_source_anchor_sha256') != retained['original_seal']['sha256'],
                    'Excluded workspace cannot become a selected selfcheck parent')
        seen.add(key)
    return seen


def load(root, component, *, record, inputs, source_policy, condition, effective_scores):
    """Validate one independently adopted selfcheck source; never replace A1.

    root is the explicit private archive folder. Original absolute execution
    paths are historical labels only; every read uses a retained descriptor.
    """
    if component is None:
        return None
    require(condition == CONDITION, 'C003 supplement0.1.0 does not backfill single_attempt')
    data = document(root, component)
    component_version = data.get('version')
    legacy = component_version == LEGACY_COMPONENT_VERSION
    require(data.get('schema') == SCHEMA and component_version in {VERSION,LEGACY_COMPONENT_VERSION}
            and data.get('case_id') == 'MG-C003' and data.get('case_version') == '0.1.1'
            and data.get('attempt_condition') == condition
            and data.get('model_label') == inputs.get('model_label')
            and data.get('initial_answers_replaced') is False
            and data.get('source_benchmark') == '1.0.0'
            and data.get('round_origins') == ['new_execution'] * 3,
            'Unsupported named C003 sealed continuation')
    require(document(root, data['base_record']) == record
            and document(root, data['target_inputs']) == inputs
            and document(root, data['source_policy']) == source_policy
            and source_policy.get('version') == '0.4.0', 'C003 supplement lost its untouched original record')
    require(set(effective_scores) == {'capability', 'partial', 'strict'}
            and set(data['effective_base_scores']) == set(effective_scores),
            'C003 continuation needs the three current effective score sources')
    for mode, score in effective_scores.items():
        require(document(root, data['effective_base_scores'][mode]) == score
                and score.get('score_mode') == mode
                and score.get('attempt_condition') == condition,
                'C003 continuation cannot discard a selected A1 correction')
    contract = document(root, data['case_contract'])
    require(contract.get('id') == 'MG-C003' and contract.get('version') == '0.1.1'
            and data['case_contract']['sha256'] == source_policy['case_contract_sha256'],
            'C003 supplemental source changed the mathematical contract')
    plan = document(root, data['execution_plan'])
    require(plan.get('schema') == 'math-gauge.c003-sealed-engineering-supplement/v1'
            and plan.get('version') == VERSION and plan.get('rounds') == [1, 2, 3]
            and plan.get('seconds_per_round') == 10800 and plan.get('new_initial_calls') == 0
            and plan.get('normal_final_required_for_each_round') is True
            and plan.get('reviewer_feedback_included') is False
            and plan.get('authentication') == 'consumer_subscription'
            and data['operator']['sha256'] == plan.get('operator_sha256')
            and data['prompt']['sha256'] == plan.get('neutral_prompt_sha256'), 'C003 frozen execution condition changed')
    read(root, data['operator']); prompt = read(root, data['prompt'])
    original_sources = {r['path']: r for r in plan['source_bindings']}
    retained = data['retained_plan_sources']
    require(set(retained) == set(original_sources), 'C003 frozen source bindings are incomplete')
    tool_identity = document(root, data['tool_binary_identity'])
    require(tool_identity.get('schema') == 'math-gauge.cli-identity/v1'
            and tool_identity.get('client') == 'agy' and tool_identity.get('binary_unchanged') is True,
            'C003 native tool identity observation is missing')
    tool_observations = 0
    for label, item in retained.items():
        if item.get('kind') == 'tool_binary_identity_observation':
            require(label == tool_identity.get('selected_binary')
                    and item.get('identity') == data['tool_binary_identity']
                    and item.get('sha256') == tool_identity.get('sha256'),
                    'C003 binary observation differs from the frozen native tool identity')
            tool_observations += 1
        else:
            read(root, item)
        require(all(item[k] == original_sources[label][k] for k in ('bytes', 'sha256')),
                'C003 frozen execution source bytes changed')
    require(tool_observations == 1, 'C003 must identify its tool binary separately from distributable source')
    plan['_tool_binary_sha256'] = tool_identity['sha256']
    runtime = data['retained_runtime_sources']
    require(set(runtime) == set(plan['runtime_identity']), 'C003 frozen runtime sources are incomplete')
    for label, item in runtime.items():
        read(root, item)
        require(item['sha256'] == plan['runtime_identity'][label], 'C003 frozen runtime bytes changed')
    baseline, rounds = data['baseline'], data['rounds']
    if legacy:
        _operational_exclusions(root,data.get('operational_exclusions',[]),rounds)
    selection = document(root, data['baseline_selection'])
    if legacy:
        _legacy_record_binding(root,data,record,inputs,selection)
        legacy_selection=document(root,baseline['legacy_selection'])
        require(selection.get('schema') == 'math-gauge.explicit-user-c003-legacy-baseline-selection/v1'
                and selection.get('version') == LEGACY_COMPONENT_VERSION
                and selection['current_public_record']['sha256'] == data['public_base_record']['sha256']
                and selection['current_private_record']['sha256'] == data['base_record']['sha256']
                and selection.get('attempt_condition') == condition
                and selection['baseline_selection']['sha256'] == baseline['legacy_selection']['sha256']
                and selection['own_visible_history']['sha256'] == baseline['own_history']['sha256']
                and selection['supplement_plan']['sha256'] == data['execution_plan']['sha256']
                and selection.get('new_initial_calls') == 0 and selection.get('new_followup_slots') == [1,2,3]
                and legacy_selection.get('schema') == 'math-gauge.flash-c003-baseline-selection/v1'
                and legacy_selection.get('model_id') == selection.get('model_id')
                and legacy_selection.get('record_id') == selection.get('record_id')
                and legacy_selection.get('record_sha256') == data['public_base_record']['sha256']
                and legacy_selection.get('selected_tree_sha256') == baseline.get('source_tree_sha256')
                and legacy_selection.get('used_old_selfcheck_rounds') is False
                and legacy_selection.get('source_repaired') is False
                and legacy_selection.get('candidate_proof_main_alignment_repaired') is False
                and legacy_selection.get('runtime_reconstruction_is_separate') is True,
                'Legacy C003 baseline lost its explicit selected historical source')
        if selection.get('operational_exclusion') is not None:
            require(selection['operational_exclusion']['sha256'] in
                    {entry['receipt']['sha256'] for entry in data.get('operational_exclusions', [])},
                    'Legacy C003 selection lost its preserved operational exclusion')
    else:
        require(selection.get('schema') == 'math-gauge.explicit-user-c003-sealed-baseline-selection/v1'
            and data['base_record']['sha256'] in {selection['current_public_record']['sha256'],
                                                selection['current_private_record']['sha256']}
            and selection.get('target_condition') == condition
            and selection['failed_baseline_seal']['sha256'] == baseline['seal']['sha256']
            and selection['supplement_plan']['sha256'] == data['execution_plan']['sha256']
            and selection.get('scoring_scope') == 'Independent lean-selfcheck trajectory only; no silent replacement or promotion of old A1 source/submission status'
            and selection.get('new_initial_calls') == 0
            and selection.get('new_followup_slots') == [1, 2, 3],
                'Failed A1 needs its explicit selfcheck-only baseline selection')
    adoption = document(root, data['adoption'])
    require(adoption.get('explicit_user_selection') is True
            and adoption.get('component_execution_plan_sha256') == data['execution_plan']['sha256']
            and adoption.get('target_record_sha256') == data['base_record']['sha256']
            and adoption.get('attempt_condition') == condition,
            'C003 supplemental execution is not automatically an adopted score source')
    require(baseline.get('phase') == ('baseline' if legacy else 'A1') and len(rounds) == 3
            and [r.get('phase') for r in rounds] == ['R1', 'R2', 'R3'], 'C003 must retain its fixed adjacent three rounds')
    nodes = [baseline, *rounds]
    review = document(root, data['alignment_review'])
    require(review.get('primary_source_kind') == 'sealed_workspace'
            and review.get('model_label') == inputs['model_label']
            and review.get('policy_sha256') == data['source_policy']['sha256']
            and len(review.get('rounds', [])) == 3
            and [r.get('round') for r in review['rounds']] == [1, 2, 3],
            'C003 supplemental trajectory lost its policy, model or fixed rounds')
    snapshots = [review['baseline'], *(r.get('snapshot') for r in review['rounds'])]
    ids = set(source_policy['obligation_ids'])
    previous_files, answers = None, []
    submissions, held, prefix = [], False, None
    for index, (node, snapshot) in enumerate(zip(nodes, snapshots)):
        if index == 0 and legacy:
            previous_files, prefix = _legacy_baseline(root,node,snapshot,ids)
            continue
        if index and node.get('source_origin') == 'not_run':
            require(held and snapshot is None and review['rounds'][index - 1].get('diagnosis') is None
                    and node.get('native') is None and node.get('seal') is None,
                    'C003 unrun suffix needs the actual held parent, without invented source')
            read(root, node['blocking_receipt'])
            submissions.append(dict(round=index, classification='not_run'))
            continue
        require(not held, 'C003 frozen condition holds after a nonnormal round')
        require(node.get('source_origin') == 'new_execution', 'Retained prefixes need an explicit legacy source adapter')
        failed = index == 0 or node.get('delivery_status') == 'delivery_failed'
        _native(root, node, failed=failed, plan=plan)
        seal = document(root, node['seal'])
        files = _inventory(root, node, seal)
        math = _review(root, node, files, ids)
        require(snapshot.get('source_kind') == 'sealed_workspace'
                and snapshot.get('source_sha256') == node['seal']['sha256']
                and snapshot.get('delivery_verified') is (not failed)
                and {r['id']: r['complete'] for r in snapshot['obligations']}
                    == {r['id']: r['complete'] for r in math['obligations']}
                and node['math_review']['sha256'] in snapshot['review_evidence_sha256'],
                'C003 mathematical snapshot borrowed another sealed review')
        if index == 0:
            require(seal.get('native_status') == 'ERROR' and seal.get('normal_complete_delivery') is False,
                    'C003 failed baseline must retain its original native ERROR')
            visible = read(root, node['visible_text'])
            require(hashlib.sha256(visible).hexdigest() == seal.get('native_return_sha256'),
                    'C003 failed baseline visible text changed')
        else:
            if failed:
                answer = read(root, node['visible_text'])
                require(hashlib.sha256(answer).hexdigest() == seal.get('native_return_sha256'),
                        'C003 failed round visible text changed')
            else:
                answer = read(root, node['native']['response'])
                final_body = _final_body(root, node)
                marker = next((r.strip() for r in final_body.decode().splitlines() if r.strip()), '')
                require(marker in {'KEEP', 'FULL'}, 'C003 normal final needs its actual KEEP/FULL marker')
                diagnosis = review['rounds'][index - 1].get('diagnosis') or {}
                require(diagnosis.get('source_response_sha256') == hashlib.sha256(final_body).hexdigest(),
                        'C003 diagnosis must bind the actual native final, including any extraction')
                _project_delivery(root, node, files, contract)
                if marker == 'KEEP':
                    require(_semantic_inventory(files) == _semantic_inventory(previous_files), 'KEEP changed source or alignment bytes')
            freeze = document(root, node['round_freeze'])
            history = document(root, node['visible_history'])
            parent_anchor = (baseline['reconstruction_manifest']['sha256'] if legacy and index == 1
                             else nodes[index - 1]['seal']['sha256'])
            expected_history = ([{'role': 'user', 'content': read(root, data['original_user_message']).decode()},
                        *[m for j, text in enumerate(answers) for m in
                          ([{'role': 'assistant', 'content': text.decode()}] if j == 0 else
                           [{'role': 'user', 'content': prompt.decode()}, {'role': 'assistant', 'content': text.decode()}])],
                        {'role': 'user', 'content': prompt.decode()}] if not legacy else
                        [*prefix, *[m for text in answers for m in
                            [{'role':'user','content':prompt.decode()},{'role':'assistant','content':text.decode()}]],
                         {'role':'user','content':prompt.decode()}])
            parent_matches = ((freeze.get('parent_manifest', {}).get('sha256') == parent_anchor
                               and node.get('parent_source_anchor_sha256') == parent_anchor
                               and freeze.get('parent_is_historical_native_seal') is not True
                               and freeze.get('parent_is_new_actual_native_terminal_seal') is (index > 1))
                              if legacy else (freeze.get('parent_seal_sha256') == parent_anchor
                                              and node.get('parent_seal_sha256') == parent_anchor))
            require(freeze.get('round') == index and parent_matches
                    and freeze.get('reviewer_feedback_included') is False
                    and history.get('messages') == expected_history,
                    'C003 history or immediate parent source changed')
            # Native transport attachments are separately byte-bound by the
            # round transport audit, not inferred from this evaluator projection.
            transport = document(root, node['history_transport_review'])
            receipt = document(root, node['native']['agy_native_evidence'])
            require(transport.get('projected_request_sha256') == node['visible_history']['sha256']
                    and transport.get('native_candidate_input_sha256') == receipt['candidate_input']['sha256']
                    and transport.get('exact_own_messages_reconstructed') is True
                    and transport.get('reviewer_feedback_included') is False,
                    'C003 visible-history attachments lost their exact native transport binding')
            visible = answer
            submissions.append(dict(round=index, classification='forced_content' if failed else 'active_final',
                scored_math_is_delivered=not failed, reviewable_content_verified=failed,
                mathematical_source_sha256=node['seal']['sha256']))
            held = failed
        answers.append(visible)
        previous_files = files
    normalized = dict(model_label=inputs['model_label'], condition=condition,
        target_inputs_identity=identity(inputs), source_policy=source_policy,
        effective_base_identities={mode: identity(score) for mode, score in effective_scores.items()},
        effective_base_sha256={mode: item['sha256'] for mode, item in data['effective_base_scores'].items()},
        alignment_review=review, round_submissions=submissions,
        public_identity=dict(component='c003-sealed-continuation/'+component_version, version=component_version,
            source_component_sha256=component['sha256'], execution_plan_sha256=data['execution_plan']['sha256'],
            alignment_review_sha256=data['alignment_review']['sha256'],
            **(dict(baseline_source_kind='legacy_archived_source',baseline_manifest_sha256=baseline['legacy_manifest']['sha256'],
                    baseline_reconstruction_sha256=baseline['reconstruction_manifest']['sha256'],
                    baseline_tree_sha256=baseline['source_tree_sha256']) if legacy else
               dict(baseline_seal_sha256=baseline['seal']['sha256'])),
            initial_answers_replaced=False, adopted_conditions=[condition], scored_rounds=[1, 2, 3]))
    return ContinuationInputs(json.dumps(normalized, sort_keys=True, ensure_ascii=False).encode())


def load_selected_public(root, model_id, folder, *, effective_scores=None, record=None):
    """Resolve a public companion after the existing HCH02 correction layer.

    Absent selectors preserve the exact old path. This reader never opens a
    private archive, reconstructs a native receipt, or performs score arithmetic.
    """
    from .records import project_assessment_score
    root, folder = Path(root), Path(folder)
    edition = json.loads((root / 'benchmark.json').read_bytes())
    selected = edition.get('c003_continuations', {}).get(model_id)
    if selected is None:
        return None
    data = document(root, selected)
    required = {'schema','version','visibility','benchmark_version','model_id','record_id',
                'condition','base_record','private_component_sha256','effective_base_private_sha256',
                'scores','order','initial_answers_replaced','human_review','formal_comparison_eligible'}
    require(required <= set(data) and not set(data) - required - {'rates','delivery_evidence','cost_source','timing_source'}
            and data.get('schema') == 'math-gauge.c003-sealed-continuation-public/v1'
            and data.get('version') == VERSION and data.get('visibility') == 'public-projection'
            and data.get('benchmark_version') == edition['version']
            and data.get('model_id') == model_id and data.get('record_id') == folder.name
            and data.get('condition') == CONDITION and data.get('initial_answers_replaced') is False
            and data.get('human_review') == 'pending' and data.get('formal_comparison_eligible') is False
            and data.get('order') == (['original_record','selected_hch02_correction','selected_c003_continuation']
                if edition.get('result_corrections', {}).get(model_id) is not None else
                ['original_record','selected_c003_continuation']),
            'Invalid selected public C003 companion')
    original = document(folder, data['base_record'])
    require(record is None or original == record, 'C003 companion binds another original public record')
    modes = {'capability','partial','strict'}
    require(isinstance(effective_scores, dict) and set(effective_scores) == modes
            and set(data['scores']) == modes, 'C003 companion requires the current effective A1 views first')
    scores = {}
    changed = {'alignment_selfcheck','strict_alignment_selfcheck','metrics','contributions',
               'source_bindings','c003_continuation'}
    changed_metrics = {'lean-selfcheck','lean','earned','overall'}
    for mode in modes:
        base = effective_scores[mode]
        score = document(folder, data['scores'][mode])
        require(project_assessment_score(score) == score and score['score_mode'] == mode
                and score['attempt_condition'] == CONDITION
                and score['c003_continuation']['source_component_sha256'] == data['private_component_sha256']
                and data['effective_base_private_sha256'][mode] == base['source_bindings']['private_report_sha256']
                == score['source_bindings']['c003_effective_base_report_sha256'],
                'Public C003 companion lost its HCH-corrected base or private scorer binding')
        require(set(score) == set(base) | {'c003_continuation'}
                and all(score[key] == base[key] for key in base if key not in changed),
                'C003 companion changed unrelated public report metadata')
        for field in ('metrics','contributions'):
            require(set(score[field]) == set(base[field])
                    and all(score[field][key] == base[field][key] for key in base[field]
                            if key not in changed_metrics), 'C003 companion changed an unrelated score category')
        expected_binding = {key:value for key,value in score['source_bindings'].items()
                            if key not in {'c003_continuation_sha256','c003_effective_base_report_sha256','private_report_sha256'}}
        require(expected_binding == {key:value for key,value in base['source_bindings'].items()
                                    if key != 'private_report_sha256'},
                'C003 public companion replaced an original source or correction binding')
        scores[mode] = score
    data['_scores'], data['_selection'] = scores, selected
    if data.get('delivery_evidence') is not None:
        deliveries = data['delivery_evidence']
        require(isinstance(deliveries, list) and len(deliveries) == 3
                and [row.get('round') for row in deliveries] == [1,2,3],
                'C003 public deliveries must preserve all three actual rounds')
        loaded_rounds = []
        for row in deliveries:
            number = row['round']
            require(set(row) == {'round','phase','normal_final','source_seal_sha256','final_text','review','elapsed_seconds'}
                    and row['phase'] == 'R' + str(number) and row['normal_final'] is True
                    and type(row['elapsed_seconds']) in (int,float)
                    and math.isfinite(row['elapsed_seconds']) and row['elapsed_seconds'] >= 0,
                    'C003 public delivery lost its phase, normal-final status or timing')
            body = read(folder, row['final_text'])
            require(next((line.strip() for line in body.decode().splitlines() if line.strip()), '') in {'KEEP','FULL'},
                    'C003 public final is not its original KEEP/FULL body')
            summary = document(folder, row['review'])
            require(set(summary) == {'schema','version','phase','round','source_seal_sha256','final_text_sha256',
                                     'complete','not_complete','unknown','total','diagnosis','original_review_sha256'}
                    and summary['schema'] == 'math-gauge.c003-selfcheck-public-review/v1'
                    and summary['version'] == VERSION and summary['round'] == number
                    and summary['phase'] == row['phase']
                    and summary['source_seal_sha256'] == row['source_seal_sha256']
                    and summary['final_text_sha256'] == row['final_text']['sha256']
                    and summary['total'] == 92,
                    'C003 public diagnosis summary belongs to another delivered source')
            diagnosis = summary['diagnosis']
            require(set(diagnosis) == {'global_points','localization_points','accurate','claims_complete','major_false_complete'},
                    'C003 public diagnosis contains unsupported private fields')
            for mode in modes:
                scored = next(r for r in scores[mode]['alignment_selfcheck']['rounds'] if r['round'] == number)
                require(scored['source_sha256'] == row['source_seal_sha256']
                        and scored['delivery_verified'] is True
                        and scored['complete'] == summary['complete']
                        and scored['not_complete'] == summary['not_complete']
                        and scored['unknown_obligations'] == summary['unknown']
                        and scored['major_false_complete'] == diagnosis['major_false_complete']
                        and scored['diagnosis_points'] == diagnosis['global_points'] + diagnosis['localization_points'],
                        'C003 public final or diagnosis differs from its shared scorer source')
            loaded_rounds.append(dict(row, response_text=body.decode(), review_summary=summary))
        data['_rounds'] = loaded_rounds
    if data.get('rates') is not None:
        from .content_rates import validate_public_rates
        rates = validate_public_rates(document(folder, data['rates']))
        require(rates['source_bindings']['record_sha256'] == data['base_record']['sha256']
                and rates['source_bindings']['assessment_result_sha256'] == data['scores']['partial']['sha256'],
                'C003 rates bind another original record or selected partial score')
        data['_rates'] = rates
    for key in ('cost_source','timing_source'):
        if data.get(key) is not None:
            # Their respective owners validate arithmetic. Here only bind the
            # public retained bytes without introducing a cross-repository read.
            read(folder, data[key])
    return data
