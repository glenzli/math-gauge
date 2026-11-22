"""Source-bound profile projection of the existing full Lean SMC group.

This evaluator/presentation component makes no new mathematical judgments.
The original engineering reviews and scoring.py continue to own correctness
and arithmetic; the candidate controller never imports this reader.
"""
from copy import deepcopy
import hashlib
import json
from pathlib import Path

from .evidence_retention import read_bytes, is_file
from .mathematical_profile import source_bytes, _require, _text

VERSION = '0.1.0'
EDITION = '1.2.0'
CONDITION = 'nonlogical_retry_3'
AXIS = 'formalization'
POLICY_PATH = 'protocol/formalization-profile.json'
DIRECTORY = 'results/formalization-profile/v0.1.0'
INDEX_PATH = DIRECTORY + '/index.json'
BASE_INDEX = 'results/mathematical-profiles/v0.4.0/index.json'
BOUNDARIES = dict(new_candidate_calls=0, new_mathematical_judgments=0,
    main_scores_modified=False, original_bytes_rewritten=False,
    post_observation=True, human_review='pending', formal_comparison_eligible=False)


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode()


def reference(path, raw):
    return dict(path=str(path), bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())


def load_policy(root):
    raw = read_bytes(Path(root) / POLICY_PATH)
    policy = json.loads(raw)
    fixed = dict(schema='math-gauge.formalization-profile-policy/v1', version=VERSION,
        benchmark_version=EDITION, condition=CONDITION, source_mode='strict',
        source_group='lean', source_weight=35,
        planned_subcategories=3, public_tasks=8, selfcheck_rounds=3, grade_max=4, display_max=100,
        aggregation='reuse-original-family-and-variant-weights',
        stages='same-first-answers-and-three-round-trajectory-in-both-stages',
        whole_task_gate='all-required-task-or-whole-trajectory-conditions-or-zero', **BOUNDARIES)
    _require(set(policy) == set(fixed) | {'axis', 'anchors', 'assessment_policy'}
        and all(type(policy.get(k)) is type(v) and policy[k] == v for k, v in fixed.items()),
        'Unsupported formalization profile policy')
    axis = policy['axis']
    _require(set(axis) == {'id', 'label', 'description'} and axis['id'] == AXIS,
             'Formalization profile needs its own axis')
    for key in ('label', 'description'):
        _require(set(axis[key]) == {'zh', 'en'} and all(_text(v) for v in axis[key].values()),
                 'Formalization profile needs bilingual copy')
    _require(policy['anchors']['path'] == 'protocol/formalization-profile.md'
        and policy['assessment_policy']['path'] == 'protocol/scoring-policy.json',
        'Formalization projection must bind its actual protocol and assessment')
    source_bytes(root, policy['anchors'])
    assessment = json.loads(source_bytes(root, policy['assessment_policy']))
    group = next(g for g in assessment['groups'] if g['id'] == 'lean')
    children = {s['id']: (s['weight'], s['families'], s['public_tasks'])
                for s in assessment['subcategories'] if s['id'] in group['children']}
    _require(group['weight'] == 35 and children == {
        'lean-audit': (10, 2, 4), 'lean-formalization': (15, 2, 4),
        'lean-selfcheck': (10, 1, 1)},
             'Formalization projection cannot change the source denominator')
    return policy, hashlib.sha256(raw).hexdigest()


def selected_source(root, model_id):
    """Resolve the same archived1.1 first-answer report as the revision owner."""
    from .neutral_revision import source_assessment_edition
    from .editions import load_assessment_transition
    source = source_assessment_edition(root)
    ref = (source.get('current_assessment_admissions', {}).get(model_id)
           or load_assessment_transition(root, source)['calibrations'].get(model_id))
    _require(ref is not None, 'No selected first-answer assessment for formalization')
    manifest = json.loads(source_bytes(root, ref))
    _require(manifest.get('model_id') == model_id, 'Selected formalization manifest belongs to another model')
    report = manifest['scores']['strict'][CONDITION]
    record = manifest.get('source_record', manifest.get('record'))
    _require(record is not None, 'Formalization source must retain its original record')
    return dict(manifest=ref, report=report, record=record)


def project_model(root, model_id, baseline_ref, policy, digest):
    from .scoring import profile_formalization_metric
    sources = selected_source(root, model_id)
    report = json.loads(source_bytes(root, sources['report']))
    record = json.loads(source_bytes(root, sources['record']))
    assessment_sha = report.get('source_bindings', {}).get('assessment_policy_sha256')
    if assessment_sha is None and record.get('record_kind') == 'native_harness':
        # Native observations retain their distinct record contract. Their
        # original policy is bound by the native record, not a CLI receipt.
        original = dict(record['assessment_policy'])
        original['path'] = (Path(sources['record']['path']).parent / original['path']).as_posix()
        source_bytes(root, original)
        assessment_sha = original['sha256']
    _require(assessment_sha == policy['assessment_policy']['sha256'],
        'Lean SMC report uses another assessment policy')
    baseline = json.loads(source_bytes(root, baseline_ref))
    _require(baseline['model_id'] == model_id, 'Formalization baseline model differs')
    return dict(schema='math-gauge.formalization-profile-model/v1', version=VERSION,
        benchmark_version=EDITION, condition=CONDITION, model_id=model_id,
        policy_sha256=digest, source_baseline_profile=baseline_ref,
        source_manifest=sources['manifest'], source_report=sources['report'],
        source_record=sources['record'],
        metric=profile_formalization_metric(report), **BOUNDARIES)


def prepare(root):
    """Produce all current source models, including retained historical ones."""
    root = Path(root)
    policy, digest = load_policy(root)
    raw = read_bytes(root / BASE_INDEX)
    baseline = json.loads(raw)
    files, models = {}, {}
    for mid, ref in baseline['models'].items():
        value = project_model(root, mid, ref, policy, digest)
        name = DIRECTORY + '/' + mid + '/profile.json'
        data = encoded(value)
        files[name] = data
        models[mid] = reference(name, data)
    files[INDEX_PATH] = encoded(dict(schema='math-gauge.formalization-profile-index/v1',
        version=VERSION, benchmark_version=EDITION, condition=CONDITION,
        policy_sha256=digest, source_base_index=reference(BASE_INDEX, raw),
        models=models, **BOUNDARIES))
    return files


def install(root):
    """Validate the entire projection before writing; retained model bytes stay fixed."""
    root = Path(root)
    files = prepare(root)
    for name, raw in files.items():
        path = root / name
        if name != INDEX_PATH and path.exists() and read_bytes(path) != raw:
            raise ValueError('Refusing to replace a retained formalization projection: ' + name)
    if is_file(root / INDEX_PATH):
        previous = json.loads(read_bytes(root / INDEX_PATH))['models']
        new = json.loads(files[INDEX_PATH])['models']
        _require(set(previous) <= set(new) and all(new[k] == v for k, v in previous.items()),
                 'Formalization index updates may only append unchanged source models')
    for name, raw in files.items():
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        if not path.exists() or read_bytes(path) != raw:
            path.write_bytes(raw)
    return dict(status='passed', models=len(files)-1, **BOUNDARIES)


def load_public(root, *, benchmark_version):
    """Keep archived1.1/1.0 views and their original seven axes unchanged."""
    root = Path(root)
    if benchmark_version != EDITION or not is_file(root / INDEX_PATH):
        return None
    policy, digest = load_policy(root)
    raw = read_bytes(root / INDEX_PATH)
    index = json.loads(raw)
    expected_fields = {'schema', 'version', 'benchmark_version', 'condition',
                       'policy_sha256', 'source_base_index', 'models'} | set(BOUNDARIES)
    _require(set(index) == expected_fields
        and index['schema'] == 'math-gauge.formalization-profile-index/v1'
        and index['version'] == VERSION and index['benchmark_version'] == EDITION
        and index['condition'] == CONDITION and index['policy_sha256'] == digest
        and all(index[k] == v for k, v in BOUNDARIES.items())
        and index['source_base_index']['path'] == BASE_INDEX,
        'Invalid formalization profile index')
    base = json.loads(source_bytes(root, index['source_base_index']))
    _require(set(index['models']) == set(base['models']),
             'Formalization profile must cover every retained baseline model')
    models = []
    for mid, ref in index['models'].items():
        actual = json.loads(source_bytes(root, ref))
        expected = project_model(root, mid, base['models'][mid], policy, digest)
        _require(actual == expected, 'Formalization profile differs from its bound SMC source')
        models.append(dict(id=mid, metric=deepcopy(actual['metric'])))
    return dict(schema='math-gauge.formalization-profile/v1', version=VERSION,
        benchmark_version=EDITION, axis=deepcopy(policy['axis']), models=models,
        planned_subcategories=3, policy_sha256=digest, source=reference(INDEX_PATH, raw),
        **BOUNDARIES)
