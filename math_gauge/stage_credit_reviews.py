"""Replay explicitly source-bound continuous credit on unchanged written stages.

This owns the exceptional review schema, not native execution or score policy.
The original progressive contract and every imported/native byte stay unchanged.
records.py supplies safe retained-byte reads; existing review arithmetic produces
the diagnostic and scoring.py still owns category/family/overall aggregation.
"""
import copy
import hashlib
import json

REVIEW_SCHEMA = 'math-gauge.source-stage-credit-review/v1'
SOURCE_SCHEMA = 'math-gauge.carbon-medium-original-byte-ai-review/v1'


def _require(value, message):
    if not value:
        raise ValueError(message)


def build_review(original, *, original_review, contract_sha256, binding=None,
                 logical_model_label=None):
    """Convert existing judgments; caller retains the original and binds import."""
    return {'schema': REVIEW_SCHEMA, 'version': '0.1.0',
        'source_benchmark_version': '0.6.0',
        'source_model_label': original['model_label'],
        'logical_model_label': logical_model_label or original['model_label'],
        'logical_alias_post_observation': True, 'backend_identity_inferred': False,
        'case_id': original['case_id'], 'slot_id': original['case_id'] + ':A1',
        'binding': copy.deepcopy(binding), 'reviewer_kind': 'ai',
        'reviewer': 'Source-bound replay of the original AI stage-credit review',
        'human_review': 'pending', 'formal_comparison_eligible': False,
        'new_candidate_calls': 0, 'post_observation': True,
        'group_contract_sha256': contract_sha256,
        'source_adjudication': copy.deepcopy(original_review),
        'source_answer_sha256': original['original_source']['sha256'],
        'credit_units': copy.deepcopy(original['credit_units']),
        'complete': original['complete'], 'findings': copy.deepcopy(original['findings']),
        'original_quotes': copy.deepcopy(original.get('original_quotes', [])),
        'notes': original.get('notes') or 'Original unit credit and strict judgment retained without regrading.'}


def evaluate_credit(contract, review):
    """Use the existing continuous-criterion arithmetic on the same unit weights.

    The temporary list below is an arithmetic view only. It is never exported as
    a replacement task, contract, import plan, candidate request or model input.
    """
    from .review import _validate_written_proof_review
    units = review['credit_units']
    complete = review['complete']
    arithmetic_contract = {'criteria': [{'id': s['id'], 'points': s['points']}
                                       for s in contract['stages']]}
    arithmetic_review = {
        'criteria': [{'criterion_id': u['id'], 'score': u['earned'], 'notes': u['reason']}
                     for u in units],
        'decision': 'pass' if complete else 'fail',
        'assumption_fidelity': 'clean' if complete else 'unknown',
        'proof_validity': 'valid' if complete else 'unknown',
        'scope_accuracy': 'correct' if complete else 'unknown',
        'unnecessary_restriction': False}
    diagnostic = _validate_written_proof_review(arithmetic_contract, arithmetic_review,
                                               {'status': 'ok'})
    _require(diagnostic['strict_pass'] is complete,
             'Original strict judgment is not representable by the retained unit credit')
    diagnostic.update(kind='source_bound_stage_credit',
        original_contract_kind=contract['kind'], review_schema=REVIEW_SCHEMA)
    reasons = ([] if complete else ['mathematical_error'] if review['findings']
               else ['candidate_incomplete'])
    axis = {'state': 'C' if complete else 'I', 'adjudicated': True, 'reasons': reasons}
    return {'completion': diagnostic['completion'], 'strict_pass': complete,
        'whole_math': dict(axis), 'whole_strict': dict(axis),
        'focus_math': {'state': 'U', 'adjudicated': False, 'reasons': ['not_selected']},
        'group_diagnostic': diagnostic, 'problem_defect': False,
        'lean_evidence_verified': False}


def validate_entry(root, meta, records, entry, *, source_row, evidence_reader):
    """Verify a normal A1 and unchanged original judgments before replaying credit."""
    from .agy_evidence import validate_delivery
    from .reliability_review import review_binding
    _require(entry.get('schema') == REVIEW_SCHEMA and entry.get('version') == '0.1.0',
             'Unsupported source stage-credit review')
    _require(entry.get('reviewer_kind') == 'ai' and entry.get('human_review') == 'pending'
        and entry.get('formal_comparison_eligible') is False
        and entry.get('new_candidate_calls') == 0 and entry.get('post_observation') is True
        and entry.get('source_benchmark_version') == '0.6.0',
        'Stage-credit replay cannot upgrade source identity or human approval')
    sid = entry.get('slot_id')
    _require(sid in records, 'Stage-credit review needs an actual imported slot')
    record = records[sid]
    case = next(c for c in meta['plan']['case_index'] if c['case_id'] == record['case_id'])
    planned = next(s for s in meta['plan']['slots'] if s['slot_id'] == sid)
    _require(entry.get('case_id') == record['case_id'] and sid == record['case_id'] + ':A1'
        and planned.get('kind') == 'independent' and planned.get('attempt_label') == 'A1'
        and planned.get('parent_slot') is None
        and case.get('component') in {'proofs', 'exploration'}
        and case.get('source_suite', {}).get('version') == '0.6.0'
        and entry.get('binding') == review_binding(meta, record),
        'Stage-credit replay changed its independent A1/import/material binding')
    _require(not any(c.get('case_id') == case['case_id']
        for c in meta['plan'].get('reliability', {}).get('selection', {}).get('cases', [])),
        'Stage-credit replay does not replace an active focus or trajectory judgment')
    _require(record.get('material', {}).get('status') == 'resolved'
        and record['material'].get('mode') in {None, 'INITIAL', 'FULL'},
        'Stage-credit replay needs this actual resolved full answer')
    contract_raw = evidence_reader(root, source_row['source']['case_contract'])
    contract = json.loads(contract_raw)
    contract_hash = hashlib.sha256(contract_raw).hexdigest()
    _require(contract.get('kind') == 'progressive'
        and contract.get('id') == case['case_id']
        and all(s.get('lean_required') is False for s in contract.get('stages', []))
        and contract_hash == entry.get('group_contract_sha256') == case['group_contract_sha256'],
        'Stage-credit replay cannot replace the original progressive written contract')
    original_raw = evidence_reader(root, entry['source_adjudication'])
    original = json.loads(original_raw)
    answer = evidence_reader(root, source_row['response'])
    answer_hash = hashlib.sha256(answer).hexdigest()
    _require(original.get('schema') == SOURCE_SCHEMA
        and original.get('reviewer_kind') == 'ai' and original.get('human_review') == 'pending'
        and original.get('formal_comparison_eligible') is False
        and original.get('source_kind') == 'first_normal_native_final'
        and original.get('case_id') == case['case_id']
        and original.get('model_label') == entry.get('source_model_label')
        and entry.get('logical_model_label') == meta['plan']['model_label']
        and entry.get('logical_alias_post_observation') is True
        and entry.get('backend_identity_inferred') is False
        and original.get('original_case_version') == case['version']
        and original.get('frozen_case_contract_sha256') == contract_hash
        and original.get('original_source', {}).get('sha256') == answer_hash
        and original['original_source'].get('bytes') == len(answer)
        and source_row['response']['sha256'] == record['response_sha256'] == answer_hash
        and entry.get('source_answer_sha256') == answer_hash,
        'Stage-credit replay lost its exact original answer/review/contract identity')
    _require(type(original.get('complete')) is bool
        and entry.get('complete') is original['complete']
        and entry.get('credit_units') == original.get('credit_units')
        and entry.get('findings') == original.get('findings')
        and entry.get('original_quotes') == original.get('original_quotes', []),
        'Stage-credit replay cannot rewrite original unit credit, false claims or Strict')
    units = entry['credit_units']
    stages = contract['stages']
    _require([u.get('id') for u in units] == [s['id'] for s in stages]
        and all(u.get('maximum') == s['points'] for u, s in zip(units, stages)),
        'Stage-credit replay changed original stage ids/order/maxima')
    fractional = any(u['earned'] not in {0, u['maximum']} for u in units)
    whole_blocker = (all(u['earned'] == u['maximum'] for u in units)
                     and original['complete'] is False and bool(original['findings']))
    _require(fractional or whole_blocker,
        'Ordinary binary stage reviews must use the existing reliability contract')
    for quote in entry['original_quotes']:
        text = quote if isinstance(quote, str) else quote.get('quote')
        _require(isinstance(text, str) and bool(text) and text.encode() in answer,
                 'Stage-credit original quotation differs from the original final')
    native = validate_delivery(root, source_row, evidence_reader)
    _require(native.get('delivered') is True,
             'Stage-credit positive work requires the original normal native final')
    admission = json.loads(evidence_reader(root, source_row['agy_native_evidence']))
    for source_field, native_field in [('original_execution', 'native_execution'),
            ('terminal_seal', 'native_terminal_seal'), ('native_terminal', 'native_terminal_event')]:
        source_hash = original.get(source_field, {}).get('sha256')
        _require(isinstance(source_hash, str) and len(source_hash) == 64
            and source_hash == admission.get(native_field, {}).get('sha256'),
            'Stage-credit original review belongs to another native execution/terminal/seal')
    return evaluate_credit(contract, entry)
