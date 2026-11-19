"""Initial 1.1 assessments of new executions, distinct from historical reassessment.

Original records and shared-scoring reports retain their acquisition/component
identities. This owner authenticates admission and changes only view metadata.
It never evaluates mathematics, retries a candidate, or applies a TX overlay.
"""
from copy import deepcopy
import json
from pathlib import Path

from .theorem_extension_calibration import (
    MODES, CONDITIONS, PUBLIC_CASES, _descriptor, read, document, load_policy, require,
)

VERSION = '0.1.0'
EDITION = '1.1.0'
FIELD = 'current_assessment_admissions'
DIRECTORY = 'results/current-assessment-admissions/v1.1.0/'
SCORE_FIELDS = dict(capability='capability_results', partial='assessment_results', strict='strict_results')


def configured(root, edition, source):
    """Validate only routing; preserve the sealed cohort and its exact transition."""
    entries = edition.get(FIELD, {})
    require(isinstance(entries, dict), 'Initial admissions must be an explicit model mapping')
    if FIELD in edition:
        require(edition.get('version') == EDITION, 'Initial admissions belong only to edition 1.1.0')
    legacy = set(source.get('selected_result_models', [])) | {'dot-underlying-model-20261108'}
    require(not legacy.intersection(entries), 'Initial admission cannot replace a historical model')
    for mid, ref in entries.items():
        require(isinstance(mid, str) and mid and '/' not in mid and '\\' not in mid
                and mid not in {'.', '..'}, 'Unsafe initial admission model identity')
        _descriptor(ref)
        require(ref['path'] == DIRECTORY + mid + '.json', 'Initial admission has a noncanonical path')
    return entries


def selections(root):
    from .editions import source_edition
    root = Path(root)
    edition = json.loads((root / 'benchmark.json').read_bytes())
    return configured(root, edition, source_edition(root, edition))


def _root_ref(folder, ref):
    return dict(_descriptor(ref), path=(folder / ref['path']).as_posix())


def record_paths(root):
    result = {}
    for mid, ref in selections(root).items():
        manifest = document(root, ref)
        require(manifest.get('model_id') == mid, 'Initial admission selects another model')
        record = _descriptor(manifest.get('record'))
        require(record['path'].startswith('results/v1.0.0/' + mid + '/')
                and record['path'].endswith('/record.json'), 'Initial record lost its actual execution archive')
        result[mid] = record['path']
    require(len(set(result.values())) == len(result), 'Initial admissions repeat a record')
    return result


def project_score(score):
    result = deepcopy(score)
    result.update(source_score_contract_version=score['benchmark_version'], benchmark_version=EDITION,
                  source_task_version='1.0.0', assessment_kind='initial')
    return result


def _review(root, review, row, *, source_review, policy_ref, policy, private=False):
    require(not {'old_R', 'new_R'}.intersection(review), 'Initial TX review cannot reuse old reassessment tiers')
    standard = policy['private_standards' if private else 'standards']['sha256']
    require(review.get('initial_assessment_edition') == EDITION
            and review.get('policy_sha256') == policy_ref['sha256']
            and review.get('standard_sha256') == standard
            and review.get('baseline_B') == row['baseline_B']
            and review.get('research_R') == row['research_R']
            and type(review.get('baseline_B')) is int and review['baseline_B'] in range(3)
            and type(review.get('research_R')) is int and review['research_R'] in range(4)
            and review.get('response_sha256') == row['response']['sha256']
            and review.get('source_review') == source_review
            and type(review.get('new_candidate_calls')) is int and review['new_candidate_calls'] == 0
            and review.get('metadata_projection_only') is True,
            'Initial TX wrapper is not bound to the current standard and source tier')
    original = document(root, source_review)
    require(original.get('stage') == 'A1' and original.get('B') == row['baseline_B']
            and original.get('R') == row['research_R']
            and original.get('answer_sha256') == row['response']['sha256'],
            'Initial TX wrapper changed the original mathematical judgment')


def load(root, model_id, *, record=None, scores=None):
    """Check public original records and six views before a metadata-only projection."""
    from .editions import load_assessment_transition
    from .records import validate_record, load_assessment_results
    root = Path(root).resolve()
    ref = selections(root).get(model_id)
    require(ref is not None, 'Model has no initial current admission')
    data = document(root, ref)
    fixed = dict(schema='math-gauge.current-assessment-admission/v1', version=VERSION,
        assessment_kind='initial', benchmark_version=EDITION, source_task_version='1.0.0',
        reviewer_kind='ai', human_review='pending', formal_comparison_eligible=False)
    required = set(fixed) | {'model_id', 'record', 'policy', 'scores', 'public_tasks',
        'public_reviews', 'private_manifest_sha256', 'private_inputs_sha256'}
    require(required <= set(data) <= required | {'historical_cost_source', 'historical_display_source'},
            'Initial public admission contains unsupported or missing fields')
    for key in ('historical_cost_source', 'historical_display_source'):
        if key in data:
            read(root, data[key])
    require(all(type(data.get(k)) is type(v) and data[k] == v for k,v in fixed.items())
            and data.get('model_id') == model_id, 'Invalid initial current assessment identity')
    require(not {'old_R', 'base_reports', 'source_assessment_version'}.intersection(data),
            'Initial assessment cannot pretend to be a historical reassessment')
    record_path = record_paths(root)[model_id]
    folder = Path(record_path).parent
    original = document(root, data['record'])
    require(original.get('model_id') == model_id
            and record_path == f"results/v1.0.0/{model_id}/{original.get('record_id')}/record.json",
            'Initial admission copied another model or record identity')
    require(original.get('benchmark_version') == '1.0.0'
            and original.get('initial_assessment_edition') == EDITION,
            'Initial admission must distinguish execution 1.0 from assessment 1.1')
    if record is not None:
        require(record == original, 'Initial admission received a substituted source record')
    validate_record(root / folder)
    if scores is None:
        scores = {mode:load_assessment_results(root / folder, original, mode=mode) for mode in MODES}
    transition = load_assessment_transition(root)
    require(data.get('policy') == transition['policy'], 'Initial assessment uses another current TX policy')
    policy = load_policy(root, data['policy'])
    first = document(root, _root_ref(folder, original['first_assessment_source']))
    from .portable_assessment_sources import PUBLIC_SCHEMA as PORTABLE_PUBLIC, validate as validate_portable
    if first.get('schema') == PORTABLE_PUBLIC:
        # External1.0 portable runs receive their first1.1 review after return.
        # Original input/runtime evidence is verified separately; the six TX
        # bindings below establish the current review, never a fabricated freeze.
        assessment = document(root, _root_ref(folder, original['assessment_policy']))
        validate_portable(root / folder, original, assessment)
    else:
        freeze = document(root, _root_ref(folder, first['source_freeze']))
        require(first.get('initial_assessment_edition') == EDITION
                and freeze.get('initial_assessment_edition') == EDITION
                and freeze.get('initial_assessment_policy_sha256') == data['policy']['sha256'],
                'Initial assessment was not bound to the current TX standard at source freeze')
    require(set(data.get('scores', {})) == set(MODES), 'Initial assessment needs all three modes')
    for mode in MODES:
        require(set(data['scores'][mode]) == set(CONDITIONS) and set(scores[mode]) == set(CONDITIONS),
                'Initial assessment needs both conditions')
        for condition in CONDITIONS:
            score_ref = data['scores'][mode][condition]
            canonical = document(root, _root_ref(folder, original[SCORE_FIELDS[mode]][condition]))
            require(canonical == scores[mode][condition], 'Initial source arithmetic was substituted')
            score = document(root, score_ref)
            require(score in (canonical, project_score(canonical)),
                    'Initial report differs from validated source arithmetic')
            require(score['metrics']['overall']['exact'] is not None,
                    'Unresolved initial assessment cannot be admitted')
    projections = [ref for ref in original.get('evidence', []) if ref.get('path') == 'public-task-scores.json']
    require(len(projections) == 1, 'Initial record needs one canonical public task projection')
    require(data.get('public_tasks') == _root_ref(folder, projections[0]),
            'Initial public tasks differ from the validated source projection')
    document(root, data['public_tasks'])
    tx = document(root, _root_ref(folder, original['theorem_extension_evidence']))
    rows = {row['case_id']:row for row in tx['records']}
    require(set(rows) == set(PUBLIC_CASES), 'Initial public assessment requires both TX cases')
    require(set(data.get('public_reviews', {})) == set(CONDITIONS), 'Initial TX reviews need both conditions')
    for condition in CONDITIONS:
        entries = data['public_reviews'][condition]
        require(all(set(r) == {'case_id', 'review'} for r in entries)
                and [r.get('case_id') for r in entries] == list(PUBLIC_CASES), 'Initial public TX review set differs')
        for entry in entries:
            row = rows[entry['case_id']]
            read(root, _root_ref(folder, row['response']))
            _review(root, document(root, entry['review']), row,
                    source_review=_root_ref(folder, row['review']), policy_ref=data['policy'], policy=policy)
    from .theorem_extension_calibration import _hash
    require(all(_hash(data.get(k)) for k in ('private_manifest_sha256', 'private_inputs_sha256')),
            'Initial public admission needs opaque private assessment bindings')
    projected = {mode:{condition:project_score(score) for condition,score in views.items()}
                 for mode,views in scores.items()}
    return dict(data, _scores=projected, _selection=ref)


def public_metadata(admission):
    return {key:admission[key] for key in ('assessment_kind', 'benchmark_version',
        'source_task_version', 'policy', 'public_tasks', 'public_reviews')} | {'manifest':admission['_selection']}


def validate_private(public_root, private_root, model_id, manifest_ref):
    """Bind all six initial TX judgments and private reports to public admission.

    Invoke after the ordinary paired record validation; public-only readers never
    fabricate private judgments from anonymous aggregate scores.
    """
    from .records import load_assessment_results, load_theorem_extension_inputs, validate_record
    admission = load(public_root, model_id)
    require(manifest_ref['sha256'] == admission['private_manifest_sha256'],
            'Initial private manifest differs from its public binding')
    manifest = document(private_root, manifest_ref)
    require(manifest.get('schema') == 'math-gauge.initial-assessment-private/v1'
            and manifest.get('version') == VERSION and manifest.get('model_id') == model_id
            and manifest.get('benchmark_version') == EDITION,
            'Invalid private initial assessment identity')
    require(manifest['inputs']['sha256'] == admission['private_inputs_sha256'],
            'Initial private input digest differs')
    inputs = document(private_root, manifest['inputs'])
    require(inputs.get('schema') == 'math-gauge.initial-assessment-inputs/v1'
            and inputs.get('version') == VERSION and inputs.get('model_id') == model_id
            and inputs.get('benchmark_version') == EDITION
            and set(inputs.get('conditions', {})) == set(CONDITIONS),
            'Initial private inputs need the exact model and both conditions')
    require(manifest['record']['path'] == admission['record']['path'],
            'Private initial record is outside the paired execution archive')
    record = document(private_root, manifest['record'])
    public_record = document(public_root, admission['record'])
    require(record.get('initial_assessment_edition') == EDITION
            and record.get('benchmark_version') == '1.0.0'
            and record.get('model_id') == public_record.get('model_id') == model_id
            and record.get('record_id') == public_record.get('record_id'),
            'Private initial record differs from the selected public execution')
    folder = Path(manifest['record']['path']).parent
    public_folder = Path(public_root) / Path(admission['record']['path']).parent
    public_first = document(public_folder, public_record['first_assessment_source'])
    from .portable_assessment_sources import SCHEMA as PORTABLE_PRIVATE, PUBLIC_SCHEMA as PORTABLE_PUBLIC
    if public_first.get('schema') == PORTABLE_PUBLIC:
        require(record['first_assessment_source']['sha256'] == public_first['private_source_proof_sha256']
                and document(Path(private_root) / folder, record['first_assessment_source']).get('schema')
                    == PORTABLE_PRIVATE,
                'Portable public projection must bind the complete private native source proof')
    validate_record(Path(private_root) / folder, formalization_root=public_folder)
    original_inputs = load_theorem_extension_inputs(Path(private_root) / folder, record)
    source_rows = {row['case_id']:row for row in original_inputs['slots']}
    require(len(source_rows) == 6, 'Initial research needs all six source cases')
    policy = load_policy(public_root, admission['policy'])
    require(manifest.get('policy') == admission['policy'], 'Private initial policy differs')
    for condition in CONDITIONS:
        rows = inputs['conditions'][condition]
        require(len(rows) == 6 and {row['case_id'] for row in rows} == set(source_rows),
                'Initial private TX case set differs')
        for row in rows:
            source = source_rows[row['case_id']]
            require(source['status'] == 'response_received_execution_unverified' and
                    all(row[k] == source[k] for k in ('baseline_B', 'research_R'))
                    and row['response'] == _root_ref(folder, source['response']),
                    'Initial TX inputs substituted an original answer or tier')
            read(private_root, row['response'])
            _review(private_root, document(private_root, row['review']), row,
                    source_review=_root_ref(folder, source['review']), policy_ref=admission['policy'],
                    policy=policy, private=row['case_id'] not in PUBLIC_CASES)
    require(set(manifest.get('scores', {})) == set(MODES), 'Private initial assessment requires three modes')
    for mode in MODES:
        scores = load_assessment_results(Path(private_root) / folder, record, mode=mode, public_root=public_folder)
        require(set(manifest['scores'][mode]) == set(CONDITIONS), 'Private initial views need both conditions')
        for condition in CONDITIONS:
            public_score = document(public_root, _root_ref(Path(admission['record']['path']).parent,
                public_record[SCORE_FIELDS[mode]][condition]))
            require(public_score.get('source_bindings', {}).get('private_report_sha256') ==
                    record[SCORE_FIELDS[mode]][condition]['sha256'],
                    'Public initial report does not bind the paired private canonical report')
            require(document(private_root, manifest['scores'][mode][condition]) in
                    (scores[condition], project_score(scores[condition])),
                    'Private initial report differs from shared scoring')
    return manifest, inputs


def historical_cost_source(root):
    """Retain the pre-admission companion bytes, not a filtered new aggregate hash."""
    refs = [document(root, ref).get('historical_cost_source') for ref in selections(root).values()]
    require(refs and all(ref is not None and ref == refs[0] for ref in refs),
            'Initial admissions need one unchanged historical cost source')
    data = document(root, refs[0])
    from .current_results import selected_source_record_paths
    rows = data.get('models', [])
    require(len(rows) == len({r['model_id'] for r in rows})
            and {r['model_id'] for r in rows} == set(selected_source_record_paths(root)),
            'Historical cost companion must contain exactly the sealed source cohort')
    return data


def historical_display_source(root):
    """Return only the single bound pre-admission display, never current metadata."""
    refs = [document(root, ref).get('historical_display_source') for ref in selections(root).values()]
    require(refs and all(ref is not None and ref == refs[0] for ref in refs),
            'Initial admissions need one unchanged historical display source')
    data = document(root, refs[0])
    from .current_results import selected_source_record_paths
    selected = selected_source_record_paths(root)
    models = data.get('models', [])
    require(data.get('benchmark_version') == '1.0.0'
            and len(models) == len(selected) and {m['id'] for m in models} == set(selected)
            and all(m['source_record'] == selected[m['id']] for m in models),
            'Historical display must retain exactly the sealed source records')
    return data
