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
MODES = ('capability', 'partial', 'strict')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def validate_math_inputs(data, policy):
    """Validate judgments independently of any unsupported execution attestation."""
    require(data.get('schema') == MATH_SCHEMA and data.get('version') == VERSION
            and data.get('benchmark_version') == '0.6.0', 'Unsupported native mathematical review')
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
        require(task.get('complete') is not True or points == maximum,
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
    return data


def validate_record(record):
    """Validate a native record without passing it off as a CLI result record."""
    require(record.get('schema') == SCHEMA and record.get('version') == VERSION
            and record.get('record_kind') == 'native_harness'
            and record.get('benchmark_version') == '0.6.0', 'Unsupported native harness record')
    allowed = {'schema','version','record_kind','benchmark_version','model_id','model_label',
        'backend_sku','human_review','formal_comparison_eligible','transport_import_validated',
        'retention','delivery_counts','harness','cli_export','source_package_sha256','source_run_sha256',
        'source_plan_sha256','mathematical_input_sha256','assessment_policy','assessment_results',
        'capability_results','strict_results','public_task_scores','public_case_ids','public_deliveries',
        'selfcheck_rounds','trajectory','comparison_note'}
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
    require(record.get('delivery_counts') == {'initial': 38, 'selfcheck': 3},
            'Native archive must retain the full selected trajectory')
    require(re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]*', record.get('model_id', '')),
            'Unsafe native model identifier')
    return record


def read_artifact(root, descriptor):
    from .records import evidence_bytes
    return evidence_bytes(root, descriptor)


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
    record = validate_record(json.loads(path.read_bytes()))
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
