"""Evaluator-only provenance gate for the 2026-11-25 native Dot acquisition.

Not a CLI receipt reader, mathematical adjudication, or public selection.
"""
import argparse
import hashlib
import json
from pathlib import Path

from .harness import _h_case_request, _h_message, inspect_release_dataset
from .native_observations import require
from .theorem_extension_calibration import read

SCHEMA = 'math-gauge.dot-native-rerun-sources/v1'
MODEL = 'dot-20261125'
DATASET = 'cd3660d73567c4393a64f9bd606a6e7387aae07c524a2e53142e9c40817ac94f'
DAMAGED_ARCHIVES = frozenset({'MG-GP001:A1', 'MG-GR005:A1', 'MG-GR021:A1'})
CAPTURE_LOSS = frozenset('MG-' + name + ':A1' for name in (
    'GP001', 'GP002', 'GR005', 'GR009', 'GR021', 'PS001'))
DELIVERY_RECOVERY = frozenset({'HCH02:A1', 'MG-C003:A1'})
REJECTION = 'MG-AR004:A1'
C003_PROMPT = 'a982ffe9187fb1a4412c7eb8b8b3e631c2a5c30b540aa1e36503603c50c7eb43'
C003_ROUNDS = tuple(f'MG-C003:R{i}' for i in range(1, 4))
CALL_FIELDS = {'request', 'context_id', 'observation', 'status', 'terminal', 'archive', 'designation'}


def _json(root, ref):
    return json.loads(read(root, ref))


def _assert_keys(row, keys, message):
    require(isinstance(row, dict) and set(row) == keys, message)


def _bind_review(root, ref, call, response):
    review = _json(root, ref)
    _assert_keys(review, {'source', 'observation_sha256', 'response_sha256', 'kind', 'human_review'},
                 'Review binding must distinguish source judgment from its wrapper')
    require(review['kind'] == 'ai' and review['human_review'] == 'pending'
            and review['observation_sha256'] == call['observation']['sha256']
            and review['response_sha256'] == (None if response is None else response['sha256']),
            'Mathematical judgment does not bind the selected evidence')
    require(bool(read(root, review['source'])), 'Missing original mathematical judgment')


def _call(root, call, seen, slot):
    _assert_keys(call, CALL_FIELDS, 'Every native call needs explicit terminal and archive states')
    cid = call['context_id']
    require(isinstance(cid, str) and bool(cid.strip()) and cid not in seen,
            'Physical native call contexts must be distinct')
    seen.add(cid)
    read(root, call['request'])
    obs = _json(root, call['observation'])
    _assert_keys(obs, {'slot', 'context_id', 'request_sha256', 'status', 'terminal_sha256',
                       'source', 'archive_sha256', 'designation_sha256'},
                 'Observation needs the original independently retained note or event')
    require(obs['slot'] == slot and obs['context_id'] == cid and obs['status'] == call['status']
            and obs['request_sha256'] == call['request']['sha256']
            and bool(read(root, obs['source'])), 'Observation lost its own request or physical identity')
    for key in ('terminal', 'archive', 'designation'):
        ref = call[key]
        if ref is not None:
            require(bool(read(root, ref)), 'Empty native evidence object')
        require(obs[key + '_sha256'] == (None if ref is None else ref['sha256']),
                'Native evidence binding differs from its observation')
    return call['status']


def _same_request(left, right):
    return left['request']['sha256'] == right['request']['sha256']


def _authorizes(root, reference, scope):
    data = _json(root, reference)
    require(data.get('scope') == scope and data.get('post_observation') is True
            and bool(read(root, data['source'])), 'Exception needs its retained post-observation authorization')


def _basis(root, slot, selection, call, authorization):
    status = call['status']
    terminal, archive, designation = (call[key] for key in ('terminal', 'archive', 'designation'))
    if selection == 'native_inline':
        require(status == 'native_final' and terminal is not None and designation is None,
                'Inline completion requires exact retained native final, not archive math alone')
        return terminal
    if selection == 'observed_inline_bound_authored_file':
        require(status == 'observed_native_final'
                and archive is not None and designation is not None,
                'Observed full inline completion must bind its independent candidate-authored file')
        data = _json(root, designation)
        require(data == dict(context_id=call['context_id'],answer=archive,
                             source=data.get('source'),comparison='observed_full_final_matches_authored_file')
                and bool(read(root,data['source'])),
                'A compared candidate archive is not an exact native transport receipt')
        return archive
    if selection == 'candidate_designated_file':
        require(slot in {'MG-C003:A1', *C003_ROUNDS} and status in {'native_final', 'partial_native_final', 'observed_file_final'}
                and (terminal is not None or status in {'partial_native_final','observed_file_final'})
                and archive is not None and designation is not None and authorization is not None,
                'C003 file delivery needs an explicitly designated full candidate-authored file')
        _authorizes(root, authorization, 'c003_designated_file')
        designation_data = _json(root, designation)
        require(designation_data == dict(context_id=call['context_id'], answer=archive,
                    source=designation_data.get('source'))
                and archive['sha256'].encode('ascii') in read(root, designation_data['source']),
                'Candidate designation does not bind this exact file and native context')
        return archive
    if selection == 'forced_content':
        require(status in {'partial_native_final', 'platform_rejected'} and archive is not None,
                'Forced content requires separate cutoff evidence from the same failed physical call')
        return archive
    require(selection == 'nondelivery' and status == 'platform_rejected',
            'Unresolved evidence cannot be marked as a settled normal final')
    return None


def validate(root, dataset_root, manifest, *, include_evaluator_bindings=False):
    """Read paired private proof; no archives are repaired, inferred, or included in output."""
    from .dot_rerun_evidence_replacement import SCHEMA as REPLACEMENT, validate as replace
    if isinstance(manifest,dict) and manifest.get('schema')==REPLACEMENT:
        return replace(root,dataset_root,manifest,include_evaluator_bindings=include_evaluator_bindings)
    _assert_keys(manifest, {'schema', 'model_id', 'dataset_sha256', 'source_benchmark_version',
        'model_override', 'effort_override', 'backend_sku', 'fork_turns', 'isolation', 'slots',
        'capture_recovery_authorization', 'delivery_recovery_authorization', 'c003_file_authorization',
        'c003_fixed_prompt', 'original_c003_rounds', 'rejection_retry_authorization', 'recapture_authorization',
        'additional_capture_authorizations'}, 'Unsupported private Dot rerun proof')
    expected = dict(schema=SCHEMA, model_id=MODEL, dataset_sha256=DATASET,
                    source_benchmark_version='1.0.0', model_override=None, effort_override=None,
                    backend_sku=None, fork_turns='none', isolation='instruction_only')
    require(all(manifest[key] == value for key, value in expected.items()), 'Changed native execution identity')
    dataset = inspect_release_dataset(dataset_root)
    require(dataset['release_version'] == '1.0.0' and dataset['dataset_sha256'] == DATASET,
            'Proof requires the actual frozen complete release, not the historical 0.6.0 archive')
    initial = set(dataset['selected_slot_ids'])
    require(len(initial) == 39 and all(slot.endswith(':A1') for slot in initial),
            'Proof needs the complete 39 first-answer population')
    fixed_prompt = read(root, manifest['c003_fixed_prompt'])
    require(fixed_prompt and manifest['c003_fixed_prompt']['sha256'] == C003_PROMPT,
            'Missing original prescribed C003 revision invitation')
    candidate_messages = {case['case_id'] + ':A1': _h_message(_h_case_request(dataset_root, case))
                          for case in dataset['cases']}
    require(set(candidate_messages) == initial, 'A1 proof needs every frozen candidate task')
    original = manifest['original_c003_rounds']
    _assert_keys(original, set(C003_ROUNDS), 'Retain the unselected original C003 trajectory separately')
    _authorizes(root, manifest['capture_recovery_authorization'], 'capture_recovery')
    _authorizes(root, manifest['delivery_recovery_authorization'], 'lean_delivery_recovery')
    _authorizes(root, manifest['recapture_authorization'], 'damaged_archive_exact_recapture')
    retry_authorized = manifest['rejection_retry_authorization'] is not None
    if retry_authorized:
        _authorizes(root, manifest['rejection_retry_authorization'], 'unchanged_guarded_platform_retry')
    additions = manifest['additional_capture_authorizations']
    require(isinstance(additions,dict) and set(additions) <= initial - CAPTURE_LOSS - DELIVERY_RECOVERY - {REJECTION}
            and all(slot.startswith('MG-') for slot in additions),
            'Additional evidence recaptures must have explicit eligible A1 slot scope')
    for slot, ref in additions.items():
        _authorizes(root,ref,'observed_damaged_archive_recapture:'+slot)
    slots, contexts, bindings, first = manifest['slots'], set(), {}, {}
    require(isinstance(slots, dict) and set(slots) == initial | set(C003_ROUNDS),
            'One selected logical slot needed for all 39 A1 and three fixed rounds')
    for slot in list(sorted(initial)) + list(C003_ROUNDS):
        row = slots[slot]
        _assert_keys(row, {'physical_calls', 'selection', 'review', 'replay'}, 'Unknown selected slot fields')
        calls = row['physical_calls']
        is_first = slot in initial
        needs_recovery = slot in CAPTURE_LOSS | DELIVERY_RECOVERY or slot in additions or (slot == REJECTION and retry_authorized)
        expected_calls = 3 if slot in DAMAGED_ARCHIVES else 2 if needs_recovery else 1
        require(isinstance(calls, list) and len(calls) == expected_calls,
                'Only the authorized replacement calls may add physical executions')
        statuses = [_call(root, call, contexts, slot) for call in calls]
        for call in calls:
            expected_message = candidate_messages[slot if is_first else 'MG-C003:A1']
            request = _json(root, call['request'])
            require(request == {'schema': 'math-gauge.conversation/v1',
                        'messages': [{'role': 'user', 'content': expected_message}],
                        'parameters': {'model': 'dot-native-default'}},
                    'Native call lost the exact release task or claimed unobserved request options')
        if needs_recovery:
            require(all(_same_request(calls[0], call) for call in calls[1:]), 'Technical replacement did not use the exact frozen request')
        if slot in CAPTURE_LOSS:
            require(statuses[0] == 'final_archive_lost'
                    and all(calls[0][k] is None for k in ('terminal','archive','designation'))
                    and ((statuses[-1], row['selection']) in {
                        ('native_final','native_inline'),
                        ('observed_native_final','observed_inline_bound_authored_file')}),
                    'Capture replacement must preserve lost original and use the intact authorized recapture')
            if slot in DAMAGED_ARCHIVES:
                require(statuses[1] == 'final_capture_damaged' and calls[1]['archive'] is not None
                        and calls[1]['terminal'] is None
                        and calls[1]['archive']['sha256'] != (
                            calls[-1]['archive'] or calls[-1]['terminal'])['sha256'],
                        'Keep the intermediate damaged archive, not a fictitious damaged model output')
        if slot in additions:
            damaged = calls[0]['archive']
            require(statuses[0]=='final_capture_damaged' and calls[0]['terminal'] is None
                    and damaged is not None and any(c < 32 and c not in (9,10,13)
                        for c in read(root,damaged))
                    and (statuses[-1],row['selection']) in {
                        ('native_final','native_inline'),
                        ('observed_native_final','observed_inline_bound_authored_file')}
                    and damaged['sha256'] != (calls[-1]['archive'] or calls[-1]['terminal'])['sha256'],
                    'Further physical calls require established actual archive corruption and exact recovery')
        if slot in DELIVERY_RECOVERY:
            require(statuses[0] == 'partial_native_final' and calls[0]['archive'] is not None,
                    'Lean delivery replacement must preserve original incomplete delivery and its artifact')
        if slot == REJECTION:
            require(statuses[0] == 'platform_rejected' and calls[0]['terminal'] is None
                    and calls[0]['designation'] is None,
                    'Preserve the unchanged first platform rejection')
            if retry_authorized:
                require((statuses[1],row['selection']) in {('native_final','native_inline'),
                        ('observed_native_final','observed_inline_bound_authored_file'),
                        ('platform_rejected','nondelivery'), ('platform_rejected','forced_content')},
                        'One unchanged guarded retry may qualify only through a normal native final')
            if statuses[-1] == 'platform_rejected':
                require(calls[-1]['terminal'] is None and calls[-1]['designation'] is None
                        and row['selection'] in {'forced_content', 'nondelivery'},
                        'A policy-rejected physical call is never a normal answer or continuation parent')
        selected = calls[-1]
        response = _basis(root, slot, row['selection'], selected, manifest['c003_file_authorization'])
        _bind_review(root, row['review'], selected, response)
        bindings[slot] = {'response': response, 'review': _json(root, row['review'])['source'],
                          'selection': row['selection']}
        before = calls[0]
        first[slot] = {'response': (response if not needs_recovery else
            before['terminal'] if before['status'] == 'native_final' else None if slot in additions or slot == REJECTION else before['archive']),
            'review': (_json(root,row['review'])['source'] if not needs_recovery else None),
            'selection': (row['selection'] if not needs_recovery else
                'unresolved_capture_loss' if slot in CAPTURE_LOSS or slot in additions else
                'forced_content' if before['archive'] is not None and slot != REJECTION else 'nondelivery')}

        if is_first:
            require(row['replay'] is None, 'First answers cannot inherit a reviewer or previous attempt')
        else:
            i = C003_ROUNDS.index(slot)
            parent = 'MG-C003:A1' if i == 0 else C003_ROUNDS[i-1]
            replay = row['replay']
            _assert_keys(replay, {'parent', 'parent_answer', 'invitation', 'dispatch'},
                         'Continuation requires its separately retained replay inputs')
            dispatch = _json(root, replay['dispatch'])
            require(slots[parent]['selection'] in {'native_inline', 'candidate_designated_file',
                                                    'observed_inline_bound_authored_file'}
                    and bindings[parent] is not None and replay['parent'] == parent
                    and read(root, replay['parent_answer']) == read(root, bindings[parent]['response'])
                    and read(root, replay['invitation']) == fixed_prompt
                    and dispatch == dict(context_id=selected['context_id'],
                        request_sha256=selected['request']['sha256'],
                        parent_answer_sha256=replay['parent_answer']['sha256'],
                        invitation_sha256=replay['invitation']['sha256'],
                        source=dispatch.get('source'))
                    and bool(read(root, dispatch['source'])),
                    'C003 rounds must bind the immediately preceding selected recovery answer')
            old = original[slot]
            require(_call(root, old, contexts, slot) in {
                        'native_final', 'partial_native_final'} and old['archive'] is not None,
                    'Keep old file-only C003 rounds without allowing cross-trajectory inheritance')
            first[slot] = {'response':old['archive'], 'selection':'forced_content'}
    require(any(row['selection'] == 'candidate_designated_file' for row in slots.values())
            or manifest['c003_file_authorization'] is None,
            'A file authorization must not masquerade as an effective selection')
    result = {'model_id': MODEL, 'source_benchmark_version': '1.0.0',
            'initial_slots': len(initial), 'c003_rounds': len(C003_ROUNDS),
            'physical_calls': len(contexts), 'native_exact_finals': sum(
                row['selection'] == 'native_inline' for row in slots.values()),
            'observed_inline_authored_file_deliveries': sum(
                row['selection'] == 'observed_inline_bound_authored_file' for row in slots.values()),
            'designated_file_deliveries': sum(row['selection'] == 'candidate_designated_file'
                                             for row in slots.values())}
    if include_evaluator_bindings:
        result.update(selected=bindings, first=first, effective_slots=slots)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--private-root', type=Path, required=True)
    parser.add_argument('--dataset', type=Path, required=True)
    parser.add_argument('manifest', type=Path)
    args = parser.parse_args()
    print(json.dumps(validate(args.private_root, args.dataset, json.loads(args.manifest.read_bytes()))))


if __name__ == '__main__':
    main()
