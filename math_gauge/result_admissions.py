"""Read-only admission of new legacy-source results to a current edition.

This owner binds identities and unchanged public contracts. It never alters
scores, native-delivery rules, attempt budgets, or a sealed release manifest.
"""
import hashlib
import json
from pathlib import Path
import re

from .catalog import Suite, relative_name

SCHEMA = 'math-gauge.result-edition-admission/v1'
VERSION = '0.1.0'
CONDITIONS = ('single_attempt', 'nonlogical_retry_3')
MODES = {'capability': 'capability_results', 'partial': 'assessment_results',
         'strict': 'strict_results'}
POLICIES = {
    'assessment': ('protocol/scoring-policy.json', 'assessment_policy'),
    'strict': ('protocol/strict-scoring-policy.json', 'strict_scoring_policy'),
    'capability': ('protocol/capability-scoring-policy.json', 'capability_scoring_policy'),
    'claim_penalty': ('protocol/claim-penalty-policy.json', 'claim_penalty_policy'),
    'submission': ('protocol/submission-scoring-policy.json', 'submission_policy'),
}
COUNTS = dict(public_a1=25, private_a1=14, combined_a1=39,
              mathematical_families=35, c003_rounds=3)


def _require(value, message):
    if not value:
        raise ValueError(message)


def _descriptor(value):
    _require(isinstance(value, dict) and set(value) == {'path', 'bytes', 'sha256'},
             'Admission needs an exact source descriptor')
    relative_name(value['path'])
    _require(type(value['bytes']) is int and value['bytes'] >= 0
             and isinstance(value['sha256'], str)
             and re.fullmatch(r'[0-9a-f]{64}', value['sha256']),
             'Admission source descriptor has invalid size or hash')
    return value


def _bytes(root, descriptor):
    item = _descriptor(descriptor)
    path = root / item['path']
    _require(not any(p.is_symlink() for p in (path, *path.parents))
             and path.is_file() and path.resolve().is_relative_to(root),
             'Admission source path is missing, linked, or escaping')
    raw = path.read_bytes()
    _require(len(raw) == item['bytes']
             and hashlib.sha256(raw).hexdigest() == item['sha256'],
             'Admission source bytes changed: ' + item['path'])
    return raw


def configured_admissions(edition):
    """Validate declarative routing only; the consumer must also verify files."""
    rows = edition.get('selected_result_admissions', {})
    _require(isinstance(rows, dict), 'Invalid result admission selection')
    fresh = edition.get('selected_result_source_versions', {})
    for model, row in rows.items():
        record = edition.get('selected_result_record_ids', {}).get(model)
        _require(isinstance(model, str) and re.fullmatch(r'[a-z0-9][a-z0-9._-]*', model)
                 and model in edition.get('selected_result_models', [])
                 and isinstance(record, str) and re.fullmatch(r'[a-zA-Z0-9][a-zA-Z0-9._-]*', record)
                 and model not in fresh,
                 'Admission needs a distinct explicit model and record selection')
        _require(isinstance(row, dict) and set(row) == {
            'source_benchmark_version', 'archive_root', 'admission'}
            and edition.get('version') == '1.0.0'
            and row['source_benchmark_version'] == '0.6.0'
            and row['archive_root'] == 'results/v0.6.0',
            'Unsupported result admission edition boundary')
        item = _descriptor(row['admission'])
        expected = f'results/edition-admissions/v{VERSION}/{model}/{record}/admission.json'
        _require(item['path'] == expected, 'Admission manifest path differs from its selected identity')
    return rows


def _archived(root, value, prefix):
    item = _descriptor(value)
    _require(item['path'].startswith(prefix), 'Admission source left its original record archive')
    return _bytes(root, item)


def _record_source(value, prefix):
    item = _descriptor(value)
    return {**item, 'path': prefix + item['path']}


def _public_contracts(root, edition, document, policy, prefix):
    from .records import public_assessment_case_ids

    ids = public_assessment_case_ids(policy)
    rows = document['public_case_contracts']
    _require(isinstance(rows, list) and len(rows) == len(ids) == COUNTS['public_a1']
             and [r.get('case_id') for r in rows] == ids,
             'Admission changed the fixed public case membership')
    suite = Suite.load(root / 'cases')
    _require(suite.metadata['visibility'] == 'public'
             and suite.sha256 == edition['public']['suite_sha256'],
             'Admission current public suite changed')
    for row in rows:
        _require(set(row) == {'case_id', 'current_task', 'current_contract',
                              'source_request', 'source_contract'},
                 'Admission public case includes unsupported fields')
        case = suite.cases[row['case_id']]
        task = suite.case_file(case, case['task'])
        contract = suite.case_file(case, case['group_contract'])
        _require(row['current_task']['path'] == task.relative_to(root).as_posix()
                 and row['current_contract']['path'] == contract.relative_to(root).as_posix(),
                 'Admission current case source is not the catalog contract')
        _bytes(root, row['current_task'])
        current_contract = json.loads(_bytes(root, row['current_contract']))
        original = json.loads(_archived(root, row['source_request'], prefix))
        _require(original == suite.request(case),
                 'Admission source request differs from the current public task')
        _require(json.loads(_archived(root, row['source_contract'], prefix)) == current_contract,
                 'Admission source case contract differs from the current public contract')


def verify_result_admissions(root, edition, sealed_manifest):
    """Bind a new result while retaining the sealed original adoption set.

    Source ordinals or exceptional attempts are disclosure only here. Normal
    record, attempt-condition, native, and shared scoring validators still run.
    """
    rows = configured_admissions(edition)
    if not rows:
        return {}
    root = Path(root).resolve()
    legacy = {r['model_id'] for r in sealed_manifest['selected_records']}
    _require(not legacy.intersection(rows), 'Admission cannot relocate a sealed legacy model')
    sealed_path = root / edition['result_compatibility']['path']
    sealed_sha = hashlib.sha256(sealed_path.read_bytes()).hexdigest()
    checked = {}
    fields = {'schema', 'version', 'visibility', 'model_id', 'record_id',
              'target_benchmark_version', 'source_benchmark_version', 'archive_root',
              'record', 'score_views', 'current_policies', 'public_case_contracts',
              'selection_disclosure', 'sealed_compatibility_sha256', 'counts', 'migration'}
    migration = dict(post_observation=True, new_candidate_calls=0,
                     source_raw_bytes_rewritten=False, mathematical_judgments_changed=False,
                     human_review='pending', formal_comparison_eligible=False)
    for model, selection in rows.items():
        document = json.loads(_bytes(root, selection['admission']))
        record_id = edition['selected_result_record_ids'][model]
        prefix = f"{selection['archive_root']}/{model}/{record_id}/"
        _require(set(document) == fields and document['schema'] == SCHEMA
                 and document['version'] == VERSION and document['visibility'] == 'public'
                 and document['model_id'] == model and document['record_id'] == record_id
                 and document['target_benchmark_version'] == edition['version']
                 and document['source_benchmark_version'] == selection['source_benchmark_version']
                 and document['archive_root'] == selection['archive_root']
                 and document['sealed_compatibility_sha256'] == sealed_sha
                 and document['counts'] == COUNTS and document['migration'] == migration,
                 'Admission identity, scope, sealed manifest, or migration changed')
        _require(document['record']['path'] == prefix + 'record.json',
                 'Admission record path differs from its original selected identity')
        record = json.loads(_archived(root, document['record'], prefix))
        _require(record.get('schema') == 'math-gauge.result-record/v1'
                 and record.get('benchmark_version') == document['source_benchmark_version']
                 and record.get('model_id') == model and record.get('record_id') == record_id
                 and record.get('human_review') == 'pending'
                 and record.get('formal_comparison_eligible') is False,
                 'Admission cannot rewrite the original record edition or qualifications')
        policies = document['current_policies']
        _require(isinstance(policies, dict) and set(policies) == set(POLICIES),
                 'Admission changed its current policy bindings')
        loaded = {}
        for name, (path, record_field) in POLICIES.items():
            _require(policies[name]['path'] == path, 'Admission policy is not the current public policy')
            raw = _bytes(root, policies[name])
            original = _record_source(record[record_field], prefix)
            _require(_archived(root, original, prefix) == raw,
                     'Admission original record policy differs from the current policy')
            loaded[name] = json.loads(raw)
        views = document['score_views']
        _require(isinstance(views, dict) and set(views) == set(MODES),
                 'Admission requires the three original score modes')
        paths = []
        for mode, field in MODES.items():
            _require(isinstance(views[mode], dict) and set(views[mode]) == set(CONDITIONS),
                     'Admission requires both original attempt conditions')
            for condition in CONDITIONS:
                item = views[mode][condition]
                expected = _record_source(record[field][condition], prefix)
                _require(item == expected, 'Admission score view differs from its source record')
                result = json.loads(_archived(root, item, prefix))
                _require(result.get('benchmark_version') == document['source_benchmark_version']
                         and result.get('score_mode') == mode
                         and result.get('attempt_condition') == condition,
                         'Admission score view changed its source edition, mode, or condition')
                paths.append(item['path'])
        _require(len(set(paths)) == 6, 'Admission must preserve six distinct original views')
        disclosure = document['selection_disclosure']
        _require(isinstance(disclosure, dict) and set(disclosure) == {
            'kind', 'retry3_policy_changed', 'actual_ordinals_rewritten',
            'formal_comparison_eligible', 'evidence'}
            and disclosure['kind'] == 'source_bound_selection_disclosure_only'
            and disclosure['retry3_policy_changed'] is False
            and disclosure['actual_ordinals_rewritten'] is False
            and disclosure['formal_comparison_eligible'] is False
            and isinstance(disclosure['evidence'], list) and disclosure['evidence'],
            'Admission disclosure cannot grant an attempt-policy or qualification waiver')
        for item in disclosure['evidence']:
            _archived(root, item, prefix)
        _public_contracts(root, edition, document, loaded['assessment'], prefix)
        checked[model] = document
    return checked
