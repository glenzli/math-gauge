"""Bind ordinary native A1 written reviews without fabricating CLI imports.

The source-field projection is evaluator metadata created after observation.
Existing review owners validate criteria and compute credit; records composes.
"""
import copy
import hashlib
import json

SCHEMA = 'math-gauge.native-current-written-sources/v1'
PUBLIC_SCHEMA = 'math-gauge.native-current-written-sources-public/v1'


def require(value, message):
    if not value:
        raise ValueError(message)


def validate(root, record, *, policy, external=False):
    from .records import evidence_bytes
    manifest = json.loads(evidence_bytes(root, record['native_current_written_sources']))
    return validate_sources(root, record, manifest, policy=policy, external=external,
                            evidence=evidence_bytes)


def _population(policy, external):
    child = next(x for x in policy['subcategories'] if x['id'] == 'written-argument')
    return child['public_tasks'], child['private_tasks'] if external else 0


def _public(root, record, manifest, policy, evidence):
    public_count, _ = _population(policy, False)
    require(record.get('scope') == 'public-answers-and-combined-aggregates'
            and manifest.get('private_source_sha256') == record.get('native_current_written_sources_private_sha256')
            and isinstance(manifest.get('private_source_sha256'), str)
            and len(manifest['private_source_sha256']) == 64,
            'Public native written evidence needs its opaque complete private source')
    retained = {r['id']:r for r in record['records']}
    rows = manifest.get('rows', [])
    require(len(rows) == len({r['case_id'] for r in rows}) == public_count,
            'Public native written projection changed its fixed population')
    for source in rows:
        sid = source['case_id'] + ':A1'; row = retained.get(sid)
        require(row and source.get('slot_id') == sid and source.get('response') == row.get('response')
                and source.get('review') == row.get('review')
                and source.get('evaluation') == row.get('evaluation'),
                'Public native written source differs from its retained original A1')
        evidence(root, source['response'])
        review = json.loads(evidence(root, source['review']))
        require(review.get('case_id') == source['case_id'] and review.get('phase') == 'A1'
                and review.get('metadata_projection_only') is True
                and review.get('original_response_sha256') == source['response']['sha256']
                and review.get('original_review_sha256') == source['original_review_sha256']
                and review.get('reviewer_kind') == 'ai' and review.get('human_review') == 'pending'
                and review.get('formal_comparison_eligible') is False,
                'Public native written review lost its original response/review identity')
    return {r['case_id'] for r in rows}


def validate_sources(root, record, manifest, *, policy, external=False,
                     evidence=None, native_validator=None):
    from .records import evidence_bytes
    from .agy_evidence import validate_delivery
    from .agy_native_sources import SCHEMA as NATIVE, same
    from .native_assessment_sources import pointer
    from .benchmarks import validate_plan, identity, validate_assessment_policy
    from .catalog import candidate_message, validate_group_contract, assessment_weights
    from .review import _validate_group_review
    from .stage_credit_reviews import evaluate_credit
    evidence = evidence or evidence_bytes
    native_validator = native_validator or validate_delivery
    require(manifest.get('schema') in {SCHEMA, PUBLIC_SCHEMA}
            and manifest.get('version') == '0.1.0' and manifest.get('post_observation') is True
            and manifest.get('execution_freeze_claimed') is False
            and manifest.get('mathematical_judgments_changed') is False
            and manifest.get('model_id') == record.get('model_id')
            and manifest.get('reviewer_kind') == 'ai' and manifest.get('human_review') == 'pending'
            and manifest.get('formal_comparison_eligible') is False and manifest.get('new_candidate_calls') == 0,
            'Native written projection cannot replace execution or mathematical judgments')
    if manifest['schema'] == PUBLIC_SCHEMA:
        require(not external, 'Private native written evidence cannot be an opaque public projection')
        return _public(root, record, manifest, policy, evidence)
    require(external, 'Full native written source validation belongs in the private complete archive')
    inputs = json.loads(evidence(root, manifest['scoring_inputs']))
    plan = validate_plan(inputs['plan']); profile = plan['profile']['data']
    require(profile.get('schema') == 'math-gauge.benchmark-profile/v6'
            and manifest.get('scoring_plan_sha256') == plan['plan_sha256']
            and inputs.get('model_label') == plan.get('model_label') == manifest.get('model_label'),
            'Native written source changed its evaluator plan/model identity')
    original = validate_assessment_policy(profile['assessment_policy'])
    expected = dict(original, version='0.9.0', capability_policy_version='0.3.0', submission_policy_version='0.1.0')
    require(identity(policy) in {identity(original), identity(expected)},
            'Native written metadata transition changed the mathematical scoring policy')
    cases = {c['case_id']:c for c in plan['case_index'] if c['component'] in {'proofs','exploration'}}
    rows = manifest.get('rows', []); public_count, private_count = _population(policy, external)
    require(len(rows) == len(cases) == public_count + private_count
            and len({r['case_id'] for r in rows}) == len(rows)
            and {r['case_id'] for r in rows} == set(cases),
            'Native written sources must cover exactly the current written families')
    retained = {r['id']:r for r in record['records']}
    slots = {r['slot_id']:r for r in inputs['slots']}
    visibility = []
    for source in rows:
        cid = source['case_id']; sid = cid + ':A1'; case = cases[cid]
        row, scored = retained.get(sid), slots.get(sid)
        require(row and scored and source.get('slot_id') == sid
                and row.get('case_id') == scored.get('case_id') == cid
                and row.get('kind') == 'independent' and row.get('parent_id') is None
                and row.get('agy_native_evidence') == source.get('native_evidence')
                and row.get('review') == row.get('source', {}).get('original_mathematical_review') == source.get('original_review')
                and row.get('response') is not None,
                'Native written source needs its own actual A1 and original criterion review')
        native = json.loads(evidence(root, source['native_evidence']))
        require(native.get('schema') == NATIVE and native.get('case_id') == cid and native.get('phase') == 'A1'
                and same(native.get('response'), row['response']),
                'Native written source borrowed a different case/phase/normal final')
        require(native_validator(root, row, evidence).get('delivered') is True,
                'Native written positive credit needs the actual normal A1 delivery')
        request = json.loads(evidence(root, native['input_projection']['logical_request']))
        payload = evidence(root, native['input_projection']['candidate_message'])
        contract_raw = evidence(root, source['case_contract'])
        contract = validate_group_contract(json.loads(contract_raw))
        require(request.get('case_id') == cid and request.get('case_version') == case['version']
                and hashlib.sha256(json.dumps(request, ensure_ascii=False, sort_keys=True).encode()).hexdigest() == case['request_sha256']
                and candidate_message(request).encode() == payload
                and hashlib.sha256(payload).hexdigest() == case['candidate_message_sha256']
                and source['case_contract']['sha256'] == case['group_contract_sha256']
                and contract.get('id') == cid and contract.get('kind') == case['contract_kind']
                and all(case.get(k) == value for k,value in assessment_weights(contract).items()),
                'Native written request or complete criterion contract changed')
        freeze = json.loads(evidence(root, native['acquisition_freeze']))
        actual_case = next(c for c in freeze['cases'] if c['case_id'] == cid)
        require(source.get('visibility') == actual_case.get('visibility') in {'public','private'},
                'Native written public/private projection changed original source visibility')
        visibility.append(source['visibility'])
        original_review = json.loads(evidence(root, source['original_review']))
        fields = source['source_fields']
        answer = evidence(root, row['response']); digest = hashlib.sha256(answer).hexdigest()
        require(original_review.get('case_id') == cid and original_review.get('reviewer_kind') == 'ai'
                and pointer(original_review, fields['response_sha256']) == digest
                and pointer(original_review, fields['contract_sha256']) == case['group_contract_sha256']
                and scored.get('response_sha256') == row.get('source', {}).get('response_sha256') == digest
                and scored.get('review_sha256') == source['original_review']['sha256'],
                'Native written judgment changed its original review/answer/contract bytes')
        entry = {key:copy.deepcopy(pointer(original_review, fields[key])) for key in
                 ('decision','assumption_fidelity','proof_validity','scope_accuracy','unnecessary_restriction')}
        unit_key = {'progressive':'stages','written_proof':'criteria','research_exploration':'dimensions'}.get(contract['kind'])
        require(unit_key is not None and all(not s.get('lean_required') for s in contract.get('stages', [])),
                'Native written source cannot replace Lean or another mathematical review kind')
        entry[unit_key] = copy.deepcopy(pointer(original_review, fields['units']))
        entry['group_contract_sha256'] = case['group_contract_sha256']
        # Mathematical helper context only, derived from validated normal final.
        # It is never stored as an original CLI record or transport status.
        context = {'status':'ok','response_sha256':digest,'request_sha256':case['request_sha256']}
        diagnostic = _validate_group_review(root, {'id':cid,'group_contract':source['case_contract']},
            context, entry, response_text=answer.decode(), retained_contract=contract)
        if contract['kind'] == 'progressive':
            credit = []
            for stage, judged in zip(contract['stages'], entry['stages']):
                require(judged['decision'] in {'pass','fail','partial'}, 'Unresolved native stage must remain unadjudicated')
                earned = stage['points'] if judged['decision'] == 'pass' else 0
                require('earned_points' not in judged or judged['earned_points'] == earned,
                        'Continuous stage credit needs its separate explicit source contract')
                credit.append(dict(id=stage['id'],maximum=stage['points'],earned=earned,reason=judged['notes']))
            computed = evaluate_credit(contract, dict(credit_units=credit,complete=entry['decision']=='pass',findings=[]))
            completion, strict = computed['completion'], computed['strict_pass']
        else:
            completion, strict = diagnostic['completion'], diagnostic['strict_pass']
        require(scored.get('completion') == row.get('evaluation', {}).get('completion') == completion
                and scored.get('strict_pass') is row.get('evaluation', {}).get('strict_pass') is strict
                and ('strict_pass' not in original_review or original_review['strict_pass'] is strict),
                'Native criterion judgment differs from the actual selected scoring slot')
    require(visibility.count('public') == public_count and visibility.count('private') == private_count,
            'Native written source visibility changed fixed public/private denominators')
    return set(cases)


def validate_public_pair(public_root, private_root, public_record, private_record):
    from .records import evidence_bytes
    pub = json.loads(evidence_bytes(public_root, public_record['native_current_written_sources']))
    private_ref = private_record['native_current_written_sources']
    private = json.loads(evidence_bytes(private_root, private_ref))
    require(pub.get('schema') == PUBLIC_SCHEMA and private.get('schema') == SCHEMA
            and pub['private_source_sha256'] == private_ref['sha256']
                == public_record.get('native_current_written_sources_private_sha256'),
            'Public/private native written proofs differ')
    sources = {r['case_id']:r for r in private['rows'] if r['visibility']=='public'}
    require({r['case_id'] for r in pub['rows']} == set(sources), 'Public native written families differ')
    records = {r['id']:r for r in private_record['records']}
    for row in pub['rows']:
        source = sources[row['case_id']]; original_row = records[row['slot_id']]
        raw = json.loads(evidence_bytes(private_root, source['original_review']))
        projected = json.loads(evidence_bytes(public_root, row['review']))
        judgment = projected['judgment']
        units = raw.get('stages', raw.get('criteria', raw.get('dimensions', [])))
        require(row['original_review_sha256'] == source['original_review']['sha256']
                and row['response']['sha256'] == original_row['response']['sha256']
                and {'completion','strict_pass','response_sha256','review_sha256'} <= set(row['evaluation'])
                and all(original_row['evaluation'].get(k) == value for k,value in row['evaluation'].items())
                and all(judgment[k] == raw[k] for k in ('decision','assumption_fidelity','proof_validity','scope_accuracy'))
                and len(judgment['units']) == len(units)
                and all(all(k in original and original[k] == value for k,value in projected_unit.items())
                        for projected_unit,original in zip(judgment['units'],units)),
                'Public native written mathematical projection changed original judgments')
    return True
