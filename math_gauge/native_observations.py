"""Source-bound records for independently observed native harness deliveries.

This owner never creates transport receipts, executes answers or certifies a
backend. The existing CLI importer and formal-record validators stay unchanged.
Mathematical aggregation belongs to scoring.py.
"""
import hashlib
import json
import re
from pathlib import Path

from .content_rates import validate_public_rates

SCHEMA = 'math-gauge.native-harness-record/v1'
MATH_SCHEMA = 'math-gauge.native-harness-math/v1'
VERSION = '0.1.0'
SUPPLEMENTED_VERSION = '0.2.0'
SUPPLEMENT_SCHEMA = 'math-gauge.native-source-supplements/v1'
MODES = ('capability', 'partial', 'strict')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def _sha256(value):
    return isinstance(value, str) and re.fullmatch(r'[0-9a-f]{64}', value) is not None


def validate_math_inputs(data, policy):
    """Validate judgments independently of any unsupported execution attestation."""
    require(data.get('schema') == MATH_SCHEMA
            and data.get('version') in (VERSION, SUPPLEMENTED_VERSION)
            and data.get('benchmark_version') == '0.6.0', 'Unsupported native mathematical review')
    if data['version'] == SUPPLEMENTED_VERSION:
        require(_sha256(data.get('source_supplements_sha256')),
                'Supplemented native mathematics needs its separate source manifest')
    require(data.get('reviewer_kind') == 'ai' and data.get('human_review') == 'pending'
            and data.get('formal_comparison_eligible') is False
            and data.get('transport_import_validated') is False,
            'Native judgments cannot upgrade review or transport qualification')
    require(isinstance(data.get('model_label'), str) and bool(data['model_label']),
            'Native harness needs its observed display name')
    tasks = data.get('tasks')
    require(isinstance(tasks, list) and len(tasks) == policy['scope']['initial_slots'],
            'Native mathematical review must retain every current A1 task')
    require(len({t.get('case_id') for t in tasks}) == len(tasks), 'Repeated native case')
    children = {c['id']: c for c in policy['subcategories'] if c['aggregation'] != 'trajectory'}
    for category, child in children.items():
        rows = [t for t in tasks if t.get('subcategory') == category]
        require(len(rows) == child['public_tasks'] + child['private_tasks']
                and len({t['family_id'] for t in rows}) == child['families'],
                'Native review changed a fixed category or family denominator')
    for task in tasks:
        require(task.get('slot_id') == task['case_id'] + ':A1'
                and task.get('subcategory') in children, 'Native review invented a slot/category')
        points, maximum = task.get('points'), task.get('maximum')
        require(type(maximum) is int and maximum > 0, 'Native task needs its original positive maximum')
        require(points is None or type(points) in (int, float) and 0 <= points <= maximum,
                'Native mathematical points exceed the source criterion scale')
        require(task.get('complete') is None or type(task['complete']) is bool,
                'Native completeness must be explicit or unknown')
        core_review = None
        if task.get('strict_completion_case') is not None:
            from .manuscript_completion import validate_core_completion
            require(task['subcategory'] == 'manuscript-completion'
                    and isinstance(task['strict_completion_case'], dict),
                    'Native core completion contract belongs only to its manuscript task')
            core_review = validate_core_completion(task['strict_completion_case'], task)
        else:
            require(task.get('strict_completion_review') is None
                    and task.get('strict_completion_review_source') is None,
                    'Native core completion review needs its selected source contract')
        require(task.get('complete') is not True or points == maximum or core_review is not None,
                'Complete native target contradicts original mathematical credit')
        require(isinstance(task.get('response'), dict) and isinstance(task.get('review'), dict),
                'Native judgments need original answer and review bindings')
        if task['subcategory'] == 'theorem-extension':
            require(task.get('baseline_B') in (0, 1, 2) and task.get('research_R') in (0, 1, 2, 3),
                    'Native theorem extension needs separate original B and R')
        if task['subcategory'] == 'background-check':
            require(task.get('background_R') in (0, 1, 2, 3)
                    and type(task.get('false_endorsement')) is bool,
                    'Native background review needs its original level and endorsement judgment')
            require(not task['false_endorsement'] or task['background_R'] == 0,
                    'Actual false endorsement must force background R0')
    core_tasks = [task for task in tasks if task.get('strict_completion_case') is not None]
    manuscript = policy.get('manuscript_completion', {})
    if manuscript.get('version') == '0.5.0':
        require(data['version'] == SUPPLEMENTED_VERSION and len(core_tasks) == 1
                and core_tasks[0]['case_id'] not in manuscript.get('public_case_ids', []),
                'Native current manuscript policy needs one separate private core completion contract')
    else:
        require(not core_tasks, 'Legacy native manuscript tasks cannot acquire a new completion contract')
    return data


def validate_record(record, policy=None):
    """Validate a native record without passing it off as a CLI result record."""
    require(record.get('schema') == SCHEMA
            and record.get('version') in (VERSION, SUPPLEMENTED_VERSION)
            and record.get('record_kind') == 'native_harness'
            and record.get('benchmark_version') == '0.6.0', 'Unsupported native harness record')
    allowed = {'schema','version','record_kind','benchmark_version','model_id','model_label',
        'backend_sku','human_review','formal_comparison_eligible','transport_import_validated',
        'retention','delivery_counts','harness','cli_export','source_package_sha256','source_run_sha256',
        'source_plan_sha256','mathematical_input_sha256','assessment_policy','assessment_results',
        'capability_results','strict_results','public_task_scores','public_case_ids','public_deliveries',
        'selfcheck_rounds','trajectory','comparison_note'}
    if record['version'] == SUPPLEMENTED_VERSION:
        allowed |= {'original_delivery_counts', 'source_supplements'}
    require(set(record) == allowed, 'Native public record contains unsupported fields')
    require(set(record['harness']) == {'name','version','fork_turns','model_override','effort_override',
        'isolation','local_tools_allowed','search_allowed','tool_network_access','detail','tool_usage'},
        'Native harness metadata contains unsupported fields')
    require(record.get('backend_sku') is None and record.get('human_review') == 'pending'
            and record.get('formal_comparison_eligible') is False
            and record.get('transport_import_validated') is False,
            'Native harness cannot fabricate backend, human or transport qualification')
    require(record.get('harness', {}).get('name') == 'Dot native harness'
            and record['harness'].get('model_override') is None
            and record['harness'].get('effort_override') is None
            and record['harness'].get('fork_turns') == 'none'
            and record['harness'].get('isolation') == 'instruction_only',
            'Native harness identity must preserve its actual observed conditions')
    require(record.get('cli_export', {}).get('runtime_frozen') is False
            and record['cli_export'].get('preparation_only') is True,
            'The original generic export cannot be retroactively frozen')
    require(record.get('retention', {}).get('user_requested') is True,
            'Native archival retention requires explicit selection')
    if record['version'] == VERSION:
        require(record.get('delivery_counts') == {'initial': 38, 'selfcheck': 3},
                'Legacy native archive must retain its original 38+3 deliveries')
    else:
        counts, original, supplements = (record.get(key) for key in
            ('delivery_counts', 'original_delivery_counts', 'source_supplements'))
        require(isinstance(supplements, dict)
                and set(supplements) == {'private_initial_count', 'sha256'}
                and type(supplements['private_initial_count']) is int
                and supplements['private_initial_count'] > 0 and _sha256(supplements['sha256']),
                'Public native supplements may expose only anonymous private count and hash')
        require(isinstance(original, dict) and set(original) == {'initial', 'selfcheck'}
                and type(original['initial']) is int and original['initial'] > 0
                and original['selfcheck'] == 3
                and counts == {'initial': original['initial'] + supplements['private_initial_count'],
                               'selfcheck': 3},
                'Native selected deliveries must preserve a separate original batch count')
    if policy is not None:
        require(record['delivery_counts'] == {'initial': policy['scope']['initial_slots'], 'selfcheck': 3}
                and policy['scope']['alignment_rounds'] == 3,
                'Native selected deliveries differ from the policy population')
    require(re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]*', record.get('model_id', '')),
            'Unsafe native model identifier')
    return record


def read_artifact(root, descriptor):
    from .records import evidence_bytes
    return evidence_bytes(root, descriptor)


def validate_source_supplements(root, supplements, record, math, original_plan):
    """Bind historical private additions without rewriting the original native run.

    The public descriptor is deliberately only a count and an opaque hash. Case
    identifiers, the earlier draft and all operational evidence stay private.
    """
    original_rows = original_plan['case_index']
    original_ids = {row['case_id'] for row in original_rows}
    tasks = {row['case_id']: row for row in math['tasks']}
    require(len(original_ids) == len(original_rows) and original_ids <= set(tasks),
            'Native mathematical review lost an original planned case')
    for row in original_rows:
        family = (row.get('parent_family_id') if row.get('contract_kind') == 'answer_review'
                  else row['family_id'])
        require(tasks[row['case_id']]['family_id'] == family,
                'Native original case changed its mathematical family')
        require(tasks[row['case_id']].get('strict_completion_case') is None,
                'Native original tasks must retain their original completion contracts')
    if record['version'] == VERSION:
        require(supplements is None and math['version'] == VERSION and set(tasks) == original_ids,
                'Legacy native sources cannot silently acquire supplemental deliveries')
        return []
    require(math['version'] == SUPPLEMENTED_VERSION
            and math['source_supplements_sha256'] == record['source_supplements']['sha256'],
            'Native mathematical inputs bind another supplement manifest')
    fields = {'schema', 'version', 'benchmark_version', 'source_plan_sha256', 'source_run_sha256',
              'reviewer_kind', 'human_review', 'formal_comparison_eligible',
              'transport_import_validated', 'tasks'}
    require(isinstance(supplements, dict) and set(supplements) == fields
            and supplements['schema'] == SUPPLEMENT_SCHEMA and supplements['version'] == VERSION
            and supplements['benchmark_version'] == '0.6.0'
            and supplements['source_plan_sha256'] == record['source_plan_sha256']
            and supplements['source_run_sha256'] == record['source_run_sha256'],
            'Native supplement changed its original batch binding')
    require(supplements['reviewer_kind'] == 'ai' and supplements['human_review'] == 'pending'
            and supplements['formal_comparison_eligible'] is False
            and supplements['transport_import_validated'] is False,
            'Native supplement cannot upgrade review or transport qualification')
    rows = supplements['tasks']
    require(isinstance(rows, list) and len(rows) == record['source_supplements']['private_initial_count'],
            'Native supplement count differs from its anonymous projection')
    row_fields = {'case_id', 'slot_id', 'subcategory', 'family_id', 'visibility', 'source_kind',
                  'rubric_timing', 'independent_family', 'post_observation', 'user_selected',
                  'execution_conditions_changed', 'response', 'review', 'task', 'rubric', 'contract',
                  'prior_materials', 'provenance', 'operational_evidence'}
    seen, families = set(), {tasks[cid]['family_id'] for cid in original_ids}
    for row in rows:
        require(isinstance(row, dict) and set(row) == row_fields,
                'Native supplement needs complete historical source bindings')
        cid = row['case_id']
        require(cid not in original_ids and cid not in seen and cid in tasks
                and cid not in record['public_case_ids']
                and row['family_id'] not in families,
                'Native supplement must add a separate private mathematical family')
        require(row['visibility'] == 'private' and row['source_kind'] == 'historical_native_delivery'
                and row['rubric_timing'] == 'post_response' and row['independent_family'] is True
                and row['post_observation'] is True and row['user_selected'] is True
                and row['execution_conditions_changed'] is False,
                'Native supplement must retain its post-observation historical conditions')
        require(all(row[key] == tasks[cid][key] for key in
                    ('slot_id', 'subcategory', 'family_id', 'response', 'review'))
                and row['slot_id'] == cid + ':A1',
                'Native supplement review changed its selected task or original answer')
        require(isinstance(row['prior_materials'], list) and bool(row['prior_materials'])
                and isinstance(row['operational_evidence'], list) and bool(row['operational_evidence']),
                'Native supplement must retain earlier draft and operational evidence')
        for key in ('response', 'review', 'task', 'rubric', 'contract', 'provenance'):
            read_artifact(root, row[key])
        for descriptor in row['prior_materials'] + row['operational_evidence']:
            read_artifact(root, descriptor)
        core_case = tasks[cid].get('strict_completion_case')
        if core_case is not None:
            from .manuscript_completion import validate_core_completion
            core_review = validate_core_completion(core_case, tasks[cid])
            require(core_case['task_sha256'] == row['task']['sha256']
                    and core_case['contract_sha256'] == row['contract']['sha256']
                    and json.loads(read_artifact(root, core_case['strict_completion_policy_source']))
                        == core_case['strict_completion_policy'],
                    'Native core completion policy differs from its retained task contract')
            if core_review is not None:
                require(json.loads(read_artifact(root, tasks[cid]['strict_completion_review_source']))
                            == core_review,
                        'Native core completion verdict differs from its retained review source')
        seen.add(cid)
        families.add(row['family_id'])
    require(set(tasks) == original_ids | seen,
            'Native mathematical tasks differ from original plan plus source supplements')
    require(record['original_delivery_counts']['initial'] == len(original_rows),
            'Native supplement rewrote the original planned population')
    return rows


def project_score(score):
    from .records import project_assessment_score
    public = project_assessment_score(score)
    public.update(record_kind='native_harness', transport_import_validated=False,
                  harness_name='Dot native harness', backend_sku=None)
    return public


def load_public_record(folder, *, public_case_ids=None):
    """Read anonymous scores plus only explicitly selected public answer rows."""
    folder = Path(folder)
    path = folder / 'native-observation.json'
    record = json.loads(path.read_bytes())
    policy = json.loads(read_artifact(folder, record['assessment_policy']))
    validate_record(record, policy)
    require(record['model_id'] == folder.parent.name, 'Native record belongs to another model')
    scores = {}
    for mode, field in (('capability', 'capability_results'), ('partial', 'assessment_results'),
                        ('strict', 'strict_results')):
        scores[mode] = {}
        for condition, descriptor in record[field].items():
            result = json.loads(read_artifact(folder, descriptor))
            require(result.get('score_mode') == mode
                    and result.get('record_kind') == 'native_harness'
                    and result.get('transport_import_validated') is False
                    and result.get('formal_comparison_eligible') is False
                    and result.get('source_bindings', {}).get('mathematical_input_sha256')
                        == record['mathematical_input_sha256'],
                    'Native score lost its record/mode binding')
            require('tasks' not in result and 'case_index' not in result,
                    'Public native aggregate cannot expose private case rows')
            if record['version'] == SUPPLEMENTED_VERSION:
                require(result.get('source_bindings', {}).get('source_supplements_sha256')
                            == record['source_supplements']['sha256']
                        and result.get('coverage', {}).get('initial_slots')
                            == policy['scope']['initial_slots']
                        and result.get('retry_summary', {}).get('effective_attempts')
                            == policy['scope']['initial_slots'],
                        'Native aggregate lost its separate supplement or policy population')
            scores[mode][condition] = result
    rates = validate_public_rates(json.loads((folder / 'content-rates.json').read_bytes()))
    bindings = rates['source_bindings']
    require(bindings['record_sha256'] == digest(path)
            and bindings['assessment_policy_sha256'] == record['assessment_policy']['sha256']
            and bindings['assessment_result_sha256'] == record['assessment_results']['nonlogical_retry_3']['sha256']
            and bindings['method_policy_sha256'] == digest(folder / 'goal-attainment-policy.json')
            and bindings['content_method_policy_sha256'] == digest(folder / 'content-rate-policy.json')
            and bindings['content_review_sha256'] == rates['private_review_sha256'],
            'Native supplemental rates bind another source or policy')
    public_ids = set(record['public_case_ids'])
    if public_case_ids is None:
        catalog = folder.parents[3] / 'cases/catalog.json'
        require(catalog.is_file(), 'A trusted public catalog is required for native projection validation')
        public_case_ids = [row['case_id'] for row in json.loads(catalog.read_bytes())['entries']]
    require(public_ids == set(public_case_ids), 'Native projection includes an unselected or private case')
    require(len(public_ids) == 25 and len(record['public_deliveries']) == 25
            and {r['case_id'] for r in record['public_deliveries']} == public_ids,
            'Native public projection must contain only the 25 public deliveries')
    for row in record['public_deliveries']:
        read_artifact(folder, row['response'])
        read_artifact(folder, row['review'])
    for row in record['selfcheck_rounds']:
        read_artifact(folder, row['response'])
        read_artifact(folder, row['review'])
    return record, scores, rates
