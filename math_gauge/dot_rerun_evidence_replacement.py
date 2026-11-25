"""A fixed, additive evidence-replacement selection for Dot (261125)."""
from copy import deepcopy
import re

from .theorem_extension_calibration import document, read, require

SCHEMA = 'math-gauge.dot-native-system-evidence-replacement/v1'
REPLACEMENT = 'evidence-replacement-v1'
PRIVATE_DIR = 'admission-build/' + REPLACEMENT + '/'
A1 = frozenset('MG-' + name + ':A1' for name in
    ('GP001','GR021','AR002','BC001','PS001','GR022','GR023'))
C003 = ('MG-C003:A1','MG-C003:R1','MG-C003:R2','MG-C003:R3')
SLOTS = A1 | set(C003)
RECOVERED = {'MG-GP001:A1','MG-BC001:A1'}
RECOVERY_SELECTION = 'observed_inline_bound_capture_projection'


def check_readable_capture(raw, projection):
    """Replay only the observed JS escapes as data; never evaluate the original script."""
    text=projection.decode('utf-8')
    escapes={'b':'\b','f':'\f','n':'\n','r':'\r','t':'\t','v':'\v','\n':''}
    require(text.strip() and not any(ord(c)<32 and c not in '\t\n' for c in text)
            and not re.search(r'\\[xu0-9]|\\$',text),
            'Unrecognized or damaged technical capture reconstruction')
    replay=re.sub(r'\\([\s\S])',lambda m:escapes.get(m[1],m[1]),text).encode()
    require(replay==raw and raw!=projection and any(c<32 and c not in (9,10,13) for c in raw),
            'Technical read projection does not reproduce the exact damaged timing-bound capture')



def validate(root, dataset, ledger, *, include_evaluator_bindings=False):
    from . import dot_rerun_sources as old
    old._assert_keys(ledger, {'schema','model_id','source_benchmark_version','base',
                             'authorization','replacement_slots'}, 'Invalid fixed Dot evidence replacement')
    require(ledger['schema']==SCHEMA and ledger['model_id']==old.MODEL
            and ledger['source_benchmark_version']=='1.0.0',
            'Replacement must keep the original Dot and benchmark identity')
    previous = document(root,ledger['base'])
    require(previous.get('schema') == old.SCHEMA, 'Replacement cannot discard or chain the original ledger')
    prior = old.validate(root,dataset,previous,include_evaluator_bindings=True)
    auth = document(root,ledger['authorization'])
    old._assert_keys(auth, {'scope','source','model_id','original_ledger_sha256',
        'classification','not_retry','best_of','preserve_original'}, 'Invalid held owner approval')
    source = document(root,auth['source'])
    require(auth['scope'] == 'exact_c003_and_seven_missing_a1_clocks'
            and auth['model_id'] == old.MODEL and auth['original_ledger_sha256']==ledger['base']['sha256']
            and auth['classification']=='user_adjudicated_system_evidence_failure'
            and auth['not_retry'] is True and auth['best_of'] is False
            and auth['preserve_original'] is True and source.get('exclude_other_models') is True
            and source.get('selected_new_c003_rounds') == ['A1','R1','R2','R3']
            and set(source.get('selected_new_a1',[])) == {s[3:-3] for s in A1}
            and len(source['selected_new_a1']) == len(A1)
            and isinstance(source.get('messages'),list) and len(source['messages']) >= 2
            and all(isinstance(x.get('id'),str) and x['id'] and isinstance(x.get('text'),str) and x['text']
                    for x in source['messages']),
            'Replacement must bind the exact selected system-evidence scope and actual authorization')
    updates = ledger['replacement_slots']
    old._assert_keys(updates,SLOTS,'Adopt exactly seven A1 calls and an entire C003 trajectory, or no changes')
    history = previous['slots']
    contexts = {c['context_id'] for row in history.values() for c in row['physical_calls']}
    contexts.update(c['context_id'] for c in previous['original_c003_rounds'].values())
    effective_slots = deepcopy(history)
    selected = deepcopy(prior['selected'])
    designated = 0
    for slot in sorted(A1)+list(C003):
        r = updates[slot]
        old._assert_keys(r, {'call','selection','review','replay','prior_answer_sha256','readable_capture'},
                         'Every replaced slot needs its own delivery and old source binding')
        archived = history[slot]['physical_calls'][-1]
        call = r['call']
        old._call(root,call,contexts,slot)
        require(r['prior_answer_sha256']==prior['selected'][slot]['response']['sha256']
                and read(root,call['request'])==read(root,archived['request']),
                'Selected physical replacement must keep the exact frozen request and prior incident')
        capture=r['readable_capture']
        if capture is not None:
            require(slot in RECOVERED and r['selection']==RECOVERY_SELECTION
                    and call['status']=='observed_native_final_with_damaged_archive'
                    and call['terminal'] is None and call['designation'] is None and call['archive'] is not None,
                    'Readable recovery is separate from exact authored or native transport bytes')
            old._assert_keys(capture,{'projection','same_call_note'},
                             'Keep both exact raw source and derived readable projection')
            response=call['archive']
            check_readable_capture(read(root,response),read(root,capture['projection']))
            require(bool(read(root,capture['same_call_note'])),'Missing actual same-call recovery observation')
            require(response['path']!=prior['selected'][slot]['response']['path'],
                    'Readable capture must belong to the new physical call')
        else:
            expected_selection=('candidate_designated_file' if slot in C003 else
                                 'observed_inline_bound_authored_file')
            require(r['selection']==expected_selection, 'Replacement must follow the observed delivery basis')
            response=old._basis(root,slot,r['selection'],call,previous['c003_file_authorization'])
            body=read(root,response)
            require(response['path'] != prior['selected'][slot]['response']['path'] and body.decode('utf-8').strip()
                    and not any(c < 32 and c not in (9,10,13) for c in body),
                    'Replacement must retain intact new source; never repair or reuse an earlier answer')
        old._bind_review(root,r['review'],call,response)
        selected[slot]=dict(response=response,review=document(root,r['review'])['source'],selection=r['selection'])
        effective_slots[slot]=dict(physical_calls=[*history[slot]['physical_calls'],call],
            selection=r['selection'],review=r['review'],replay=r['replay'])
        if slot in C003:
            designated += 1
        if slot in old.C003_ROUNDS:
            i=C003.index(slot)
            parent=C003[i-1]
            replay=r['replay']
            old._assert_keys(replay,{'parent','parent_answer','invitation','dispatch'},
                             'C003 engineering self-check must replay its immediate new parent')
            dispatch=document(root,replay['dispatch'])
            require(replay['parent']==parent and read(root,replay['parent_answer'])==read(root,selected[parent]['response'])
                    and read(root,replay['invitation'])==read(root,previous['c003_fixed_prompt'])
                    and dispatch == dict(context_id=call['context_id'],request_sha256=call['request']['sha256'],
                        parent_answer_sha256=replay['parent_answer']['sha256'],
                        invitation_sha256=replay['invitation']['sha256'],source=dispatch.get('source'))
                    and bool(read(root,dispatch['source'])),
                    'C003 replacement borrowed earlier trajectory, changed its prompt, or lacked its actual dispatch')
        else:
            require(r['replay'] is None, 'A1 must not include another candidate answer or grader feedback')
    out=dict(model_id=old.MODEL,source_benchmark_version='1.0.0',initial_slots=39,c003_rounds=3,
        physical_calls=prior['physical_calls']+len(SLOTS),replacement_physical_calls=len(SLOTS),
        selected_system_evidence_replacements=len(SLOTS),first_source_sha256=ledger['base']['sha256'],
        designated_file_deliveries=designated)
    if include_evaluator_bindings:
        effective_first=deepcopy(prior['first'])
        effective_first.update({slot:deepcopy(selected[slot]) for slot in SLOTS})
        out.update(first=effective_first,archived_first=prior['first'],selected=selected,effective_slots=effective_slots)
    return out
