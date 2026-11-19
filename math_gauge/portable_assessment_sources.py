"""First assessment provenance for original portable-controller executions.

The release anchor is evaluator-held. Returned run declarations and native A1
launches establish the actual input, parameters and preparation chronology.
This is a retrospective source binding, never a fabricated pre-call Git freeze,
historical score, provider attestation or effective-sandbox certification.
"""
from copy import deepcopy
from datetime import datetime
import hashlib
import json
import re


SCHEMA = 'math-gauge.portable-first-assessment-source/v1'
PUBLIC_SCHEMA = 'math-gauge.portable-first-assessment-source-public/v1'


def _require(condition, message):
    if not condition:
        raise ValueError(message)


def _time(value):
    stamp = datetime.fromisoformat(value.replace('Z', '+00:00'))
    _require(stamp.tzinfo is not None and stamp.utcoffset() is not None,
             'Portable execution timestamps need a timezone')
    return stamp


def validate(root, record, current):
    from .records import evidence_bytes

    return validate_sources(record, current, lambda item: evidence_bytes(root, item))


def validate_sources(record, current, read):
    """Read only bound originals; no filesystem search, model call or scoring."""
    from .benchmarks import validate_assessment_policy
    from .harness import validate_release_anchor, _h_identity, _r_execution

    def document(item):
        return json.loads(read(item))

    _require(record.get('benchmark_version') == '1.0.0'
             and record.get('score_history') is None
             and record.get('source_assessment_admission') is None
             and record.get('retention', {}).get('user_requested') is True,
             'Portable first assessment must preserve actual1.0 source and user selection')
    validate_assessment_policy(current)
    proof = document(record['first_assessment_source'])
    if proof.get('schema') == PUBLIC_SCHEMA:
        _require(record.get('scope') == 'public-answers-and-combined-aggregates'
                 and record.get('formalization_evidence_location') is None
                 and set(proof) == {'schema', 'version', 'model_id', 'source_benchmark_version',
                     'assessment_method_version', 'post_observation', 'new_candidate_calls',
                     'private_source_proof_sha256', 'original_assessment_policy'}
                 and proof.get('version') == '0.1.0'
                 and proof.get('model_id') == record.get('model_id')
                 and proof.get('source_benchmark_version') == '1.0.0'
                 and proof.get('assessment_method_version') == current.get('version') == '0.9.0'
                 and proof.get('post_observation') is True and proof.get('new_candidate_calls') == 0
                 and isinstance(proof.get('private_source_proof_sha256'), str)
                 and re.fullmatch(r'[0-9a-f]{64}', proof['private_source_proof_sha256'])
                 and proof['private_source_proof_sha256']
                     == record.get('first_assessment_source_private_sha256'),
                 'Public portable provenance must be an opaque projection of its private source proof')
        original = validate_assessment_policy(document(proof['original_assessment_policy']))
        _require(current == dict(original, version='0.9.0', capability_policy_version='0.3.0',
                                 submission_policy_version='0.1.0'),
                 'Public portable transition changed its source mathematical policy')
        return original
    _require(proof.get('schema') == SCHEMA and proof.get('version') == '0.1.0'
             and proof.get('model_id') == record.get('model_id')
             and proof.get('source_benchmark_version') == '1.0.0'
             and proof.get('assessment_method_version') == current.get('version') == '0.9.0'
             and proof.get('post_observation') is True
             and proof.get('source_raw_bytes_rewritten') is False
             and proof.get('prior_score_views_existed') is False
             and proof.get('new_candidate_calls') == 0
             and proof.get('provider_identity_verified') is False
             and proof.get('effective_sandbox_verified') is False,
             'Portable source admission cannot invent execution, history or verification')
    adoption = document(proof['user_adoption'])
    _require(adoption.get('post_observation') is True and bool(adoption.get('user_quote'))
             and adoption.get('source_benchmark_version') == '1.0.0'
             and adoption.get('original_physical_effective_ordinals_preserved') is True,
             'Portable first assessment requires source-bound user adoption')
    anchor = document(proof['trusted_release_anchor'])
    plan = validate_release_anchor(anchor)
    _require(anchor['release_version'] == plan['suite']['version'] == '1.0.0',
             'Portable first assessment changed its released task edition')
    original = validate_assessment_policy(deepcopy(plan['profile']['data']['assessment_policy']))
    expected = dict(original, version='0.9.0', capability_policy_version='0.3.0',
                    submission_policy_version='0.1.0')
    _require(current == expected,
             'Portable assessment transition changed frozen mathematical policy')
    dataset = document(proof['original_dataset_manifest'])
    _require(dataset.get('dataset_sha256') == _h_identity(
                 {k: v for k, v in dataset.items() if k != 'dataset_sha256'})
             == anchor['expected_dataset_sha256']
             and dataset.get('base_plan_sha256') == plan['plan_sha256']
             and dataset.get('suite') == plan['suite']
             and dataset.get('runner_sha256') == plan['runner_sha256'],
             'Portable originals do not bind the evaluator-held release anchor')
    source_cases = {row['case_id']: row for row in dataset['cases']}
    cases = {row['case_id']: row for row in plan['case_index']}
    _require(len(source_cases) == len(dataset['cases']) == len(cases) == 39
             and set(source_cases) == set(cases),
             'Portable full admission needs all39 original task identities')
    for cid, row in source_cases.items():
        _require(row['case_version'] == cases[cid]['version']
                 and row['request_sha256'] == cases[cid]['request_sha256']
                 and row['candidate_message_sha256'] == cases[cid]['candidate_message_sha256'],
                 'Portable original candidate input changed: ' + cid)

    sources = proof.get('runs')
    _require(isinstance(sources, list) and bool(sources), 'Portable run sources are missing')
    selected, native_cases, sessions, cwds = set(), set(), set(), set()
    for source in sources:
        run = document(source['original_run_manifest'])
        _require(run.get('run_sha256') == _h_identity(
                     {k: v for k, v in run.items() if k != 'run_sha256'})
                 and run.get('runtime_frozen') is True and run.get('preparation_only') is False
                 and run.get('runtime_sha256') == _h_identity(run['runtime'])
                 and run.get('dataset_sha256') == dataset['dataset_sha256']
                 and run.get('base_plan_sha256') == plan['plan_sha256']
                 and run.get('controller_version') == dataset['controller_version']
                 and run['runtime'].get('fresh_context') is True,
                 'Portable runtime was not frozen against the original dataset')
        ids = run['selected_slot_ids']
        all_ids = set(dataset['selected_slot_ids'])
        _require(isinstance(ids, list) and len(set(ids)) == len(ids)
                 and set(ids).issubset(all_ids) and not selected.intersection(ids)
                 and run['planned'] == dict(dataset['planned'], selected_slots=len(ids)),
                 'Portable run groups overlap or change their fixed denominators')
        selected.update(ids)
        runtime = run['runtime']
        execution = _r_execution(runtime, list(cases))
        selected_cases = {sid.removesuffix(':A1') for sid in ids}
        execution['case_parameters'] = {cid: value for cid, value in execution['case_parameters'].items()
                                        if cid in selected_cases}
        _require(execution == run['execution']
                 and execution['context_policy'].get('independent') == 'fresh'
                 and execution['context_policy'].get('external_correctness_feedback') is False,
                 'Portable frozen execution parameters changed')
        initials = source['native_initials']
        _require(len(initials) == len(ids), 'Portable group lost its original native launches')
        for initial in initials:
            cid = initial['case_id']
            _require(cid in selected_cases and cid not in native_cases,
                     'Portable native initial was omitted, duplicated or borrowed')
            native_cases.add(cid)
            launch = document(initial['launch'])
            metadata = document(initial['metadata'])
            request = document(initial['request'])
            prompt = read(initial['prompt'])
            parameters = dict(execution['parameters'], **execution['case_parameters'].get(cid, {}))
            users = [m['content'] for m in request['messages'] if m.get('role') == 'user']
            systems = [m['content'] for m in request['messages'] if m.get('role') == 'system']
            _require(launch.get('resume') is False and metadata.get('resume') is False
                     and launch.get('session_id') == metadata.get('session_id')
                     and launch['session_id'] not in sessions and launch['cwd'] not in cwds
                     and launch['cwd'] == metadata.get('init', {}).get('cwd')
                     and len(users) == 1 and users[0].encode('utf-8') == prompt
                     and systems == [execution['system_prompt']]
                     and request.get('parameters') == parameters
                     and metadata.get('init', {}).get('model') == parameters['model']
                     and hashlib.sha256(prompt).hexdigest()
                        == launch['prompt_sha256'] == source_cases[cid]['candidate_message_sha256']
                     and launch['prompt_bytes'] == len(prompt)
                     and launch['timeout_seconds'] == execution['budget']['timeout_seconds']
                     and _time(run['created_at']) < _time(launch['started_at'])
                     and metadata['started_at'] == launch['started_at'],
                     'Portable A1 lost its fresh original input, runtime or preparation chronology: ' + cid)
            sessions.add(launch['session_id'])
            cwds.add(launch['cwd'])
    _require(selected == set(dataset['selected_slot_ids'])
             and native_cases == set(cases) and len(selected) == 39,
             'Portable full admission omitted original A1 slots')
    return original
