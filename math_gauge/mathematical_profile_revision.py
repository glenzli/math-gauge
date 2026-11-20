"""Authenticate an independent continuation overlay over immutable traits.

Only scoring.py combines grades. This evaluator-side owner binds each review to
the adopted continuation and its actual original task, delivery and attachments.
"""
from copy import deepcopy
import hashlib
import json
import math
from pathlib import Path

from .evidence_retention import read_bytes, is_file
from .mathematical_profile import (
    AXES, BEHAVIOR, CORE_GATE, COMPLETION, ProfileInputs,
    _hash, _text, _require, _pointer, _relative, source_bytes,
    _validate_proof_core, _validate_fidelity_core,
    load_policy as load_base_policy, validate_contracts,
    validate_public as validate_base_public,
)

VERSION = '0.1.0'
EDITION = '1.2.0'
CONDITION = 'nonlogical_retry_3'
REVIEWED_AXES = ('proof', 'fidelity', 'discernment', 'depth', 'closure')
POLICY_PATH = 'protocol/mathematical-profile-revision.json'
DIRECTORY = 'results/mathematical-profile-revisions/v0.1.0'
INDEX_PATH = DIRECTORY + '/index.json'
BASE_INDEX_PATH = 'results/mathematical-profiles/v0.4.0/index.json'


def validate_policy(policy):
    fixed = dict(schema='math-gauge.mathematical-profile-revision-policy/v1',
        version=VERSION, benchmark_version=EDITION, source_scoring_edition='1.1.0',
        condition=CONDITION, base_profile_version='0.4.0', reviewed_axes=list(REVIEWED_AXES),
        original_weight='4/5', revision_weight='1/5',
        initiative='first-answer-only;no-credit-for-invited-research', completion=COMPLETION,
        planned_families=35, family_weights='unchanged-base-contracts;variants-and-C003-nesting-preserved',
        proof_core_gate=CORE_GATE,
        fidelity_core_gate='any-required-core-scope-drift-without-delivered-bridge-caps-grade-at2',
        exempt_tasks='retain-original-profile-judgments;no-full-grade-inference',
        unknowns='retain-fixed-weight-intervals;never-inherit-as-reviewed-revision',
        post_observation=True, reviewer_kind='ai', human_review='pending',
        formal_comparison_eligible=False, new_candidate_calls=0,
        main_scores_modified=False, original_bytes_rewritten=False)
    _require(isinstance(policy, dict) and set(policy) == set(fixed) | {'base_policy', 'anchors'}
             and all(type(policy.get(k)) is type(v) and policy[k] == v for k,v in fixed.items()),
             'Unsupported mathematical-profile continuation policy')
    _require(policy['base_policy'].get('path') == 'protocol/mathematical-profile.json'
             and policy['anchors'].get('path') == 'protocol/mathematical-profile-revision.md',
             'Profile continuation policy must bind its original policy and own protocol')
    return policy


def load_policy(root):
    raw = read_bytes(Path(root) / POLICY_PATH)
    policy = validate_policy(json.loads(raw))
    base_raw = source_bytes(root, policy['base_policy'])
    base_policy, base_digest = load_base_policy(root)
    _require(base_digest == hashlib.sha256(base_raw).hexdigest()
             and base_policy['version'] == policy['base_profile_version'],
             'Continuation overlay changed its first-answer profile source')
    source_bytes(root, policy['anchors'])
    return policy, hashlib.sha256(raw).hexdigest()


def _reference(source):
    return {k:source[k] for k in ('path', 'bytes', 'sha256') if k in source}


def _same_reference(source, expected, repository):
    _require(source == dict(repository=repository, **_reference(expected)),
             'Profile continuation source is not the exact selected artifact')


def _read(roots, source):
    _require(source.get('repository') in roots, 'Unknown profile continuation repository')
    return source_bytes(roots[source['repository']], source)


def _task_sources(row):
    """Reconstruct the only allowable task-local evidence aliases."""
    continuation = row['continuation']
    result = {}
    if row.get('original_task') is not None:
        source = row['original_task']
        result['task'] = dict(repository=source.get('scope', 'private'), **_reference(source))
    for field in ('input', 'answer', 'review', 'failure_evidence', 'cutoff_review', 'cutoff_content'):
        if continuation.get(field) is not None:
            result[field] = dict(repository='private', **_reference(continuation[field]))
    for i, source in enumerate(continuation.get('attachments', [])):
        result['attachment:' + str(i)] = dict(repository='private', **_reference(source))
    return result


def validate_task_review(review, material, *, roots):
    _require(review.get('id') == material['id']
             and set(review.get('axes', {})) == set(REVIEWED_AXES),
             'Continuation profile review needs exactly five independent axes for its own task')
    status = material['revision_ref']['continuation']['status']
    for axis, judgment in review['axes'].items():
        grade, assessment = judgment.get('grade'), judgment.get('assessment_status')
        _require(grade is None or type(grade) is int and 0 <= grade <= 4,
                 'Continuation profile grade must be integer0to4 or unknown')
        _require(_text(judgment.get('reason')) and assessment in
                 {'reviewed', 'operational_zero', 'not_run', 'source_unresolved'},
                 'Continuation profile judgment needs a reason and typed evidence status')
        _require((grade is None) == (assessment in {'not_run', 'source_unresolved'}),
                 'Unreviewed continuation evidence must retain its unknown grade')
        if status == 'not_run':
            _require(grade is None and assessment == 'not_run', 'Unrun continuation cannot inherit a grade')
        else:
            _require(assessment != 'not_run', 'An adopted delivery is not an unrun continuation')
        if assessment == 'operational_zero':
            _require(status == 'delivery_failed' and grade == 0,
                     'Operational zero requires an actual settled delivery failure')
        if assessment == 'source_unresolved':
            _require(_text(judgment.get('missing_evidence')), 'Unknown continuation needs its missing evidence')
        if axis == 'proof':
            _validate_proof_core(judgment)
        if axis == 'fidelity':
            _validate_fidelity_core(judgment)
        entries = judgment.get('evidence')
        _require(isinstance(entries, list) and entries, 'Every continuation trait needs source evidence')
        for entry in entries:
            _require(set(entry) == {'source_id', 'pointer', 'quote'}
                     and entry['source_id'] in material['sources'] and _text(entry['quote']),
                     'Continuation profile evidence must belong to its own exact task')
            source = material['sources'][entry['source_id']]
            raw = _read(roots, source)
            if source['path'].endswith('.json'):
                value = _pointer(json.loads(raw), entry['pointer'])
                text = value if isinstance(value, str) else json.dumps(value, ensure_ascii=False)
            else:
                _require(entry['pointer'] == '', 'Raw continuation evidence cannot have a JSON pointer')
                text = raw.decode('utf-8')
            _require(entry['quote'] in text, 'Continuation profile quote differs from retained original bytes')
    return review


class RevisionProfileInputs:
    """A fully authenticated first-answer profile and adopted five-axis review."""
    def __init__(self, review, materials, *, roots, policy, policy_sha256, materials_sha256, corrections=None):
        validate_policy(policy)
        fixed = dict(version=VERSION, benchmark_version=EDITION, condition=CONDITION,
                     model_id=materials.get('model_id'), policy_sha256=policy_sha256,
                     new_candidate_calls=0)
        _require(materials.get('schema') == 'math-gauge.mathematical-profile-revision-materials/v1'
                 and all(type(materials.get(k)) is type(v) and materials[k] == v for k,v in fixed.items()),
                 'Invalid mathematical-profile continuation materials')
        _require(review.get('schema') == 'math-gauge.mathematical-profile-revision-review/v1'
                 and all(type(review.get(k)) is type(v) and review[k] == v for k,v in fixed.items())
                 and review.get('materials_sha256') == materials_sha256
                 and review.get('reviewer_kind') == 'ai' and review.get('human_review') == 'pending'
                 and review.get('formal_comparison_eligible') is False and _text(review.get('reviewer_id')),
                 'Continuation profile review lost its source identity or AI-review boundary')
        sources = materials.get('sources', {})
        names = {'policy', 'base_review', 'base_materials', 'base_score', 'base_contracts',
                 'base_public_profile', 'public_adoption', 'adoption_inputs'}
        _require(set(sources) == names, 'Continuation materials need the complete exact source chain')
        loaded = {key:json.loads(_read(roots, source)) for key,source in sources.items()}
        _require(loaded['policy'] == policy and sources['policy']['repository'] == 'public'
                 and sources['policy']['path'] == POLICY_PATH
                 and sources['policy']['sha256'] == policy_sha256,
                 'Continuation materials use a different profile policy')
        mid, public_root, private_root = materials['model_id'], roots['public'], roots['private']
        from .neutral_revision import load_transition, load_public, load_inputs, ELIGIBLE
        transition = load_transition(public_root)
        _require(transition is not None and mid in transition['adoptions'],
                 'A pending model cannot inherit the continuation profile')
        _same_reference(sources['public_adoption'], transition['adoptions'][mid], 'public')
        adopted = load_public(public_root, transition['adoptions'][mid])
        adoption_inputs = loaded['adoption_inputs']
        _require(sources['adoption_inputs']['repository'] == 'private'
                 and sources['adoption_inputs']['sha256'] == adopted['private_inputs_sha256']
                 and adoption_inputs['model_id'] == mid,
                 'Profile continuation inputs are not the adopted model and parent answer')
        # This validates actual first-final, terminal/attachment evidence and
        # selected score reviews; no new execution or mathematical review occurs.
        base_reports = {mode:json.loads(source_bytes(private_root, ref))
                        for mode,ref in adoption_inputs['base_reports'].items()}
        load_inputs(private_root, _reference(sources['adoption_inputs']),
                    public_root=public_root, base_reports=base_reports)
        public_index = json.loads(read_bytes(Path(public_root) / BASE_INDEX_PATH))
        private_index = json.loads(read_bytes(Path(private_root) / BASE_INDEX_PATH))
        base_entry = private_index['models'][mid]
        for alias, key in (('base_review', 'review'), ('base_materials', 'source-bindings'),
                           ('base_score', 'score')):
            _same_reference(sources[alias], base_entry[key], 'private')
        _same_reference(sources['base_contracts'], private_index['contracts'], 'private')
        _same_reference(sources['base_public_profile'], public_index['models'][mid], 'public')
        base_policy, base_digest = load_base_policy(public_root)
        _require(base_digest == policy['base_policy']['sha256'], 'First-answer policy bytes changed')
        validate_base_public(loaded['base_public_profile'], base_policy, policy_sha256=base_digest)
        _require(loaded['base_public_profile']['model_id'] == mid,
                 'Continuation profile cannot borrow another model\'s first-answer traits')
        baseline = ProfileInputs(loaded['base_review'], base_policy, loaded['base_contracts'],
            loaded['base_materials'], roots=roots, policy_sha256=base_digest)
        from .scoring import score_mathematical_profile
        base_score = score_mathematical_profile(baseline)
        _require(base_score == loaded['base_score']
                 and base_score['metrics'] == loaded['base_public_profile']['metrics']
                 and loaded['base_public_profile']['private_review_sha256'] == sources['base_review']['sha256']
                 and loaded['base_public_profile']['private_materials_sha256'] == sources['base_materials']['sha256'],
                 'Retained first-answer profile no longer reproduces from its original judgments')
        validate_contracts(loaded['base_contracts'], base_policy)
        contracts = {row['id']:row for row in loaded['base_contracts']['tasks']}
        baselines = {row['id']:row for row in loaded['base_review']['tasks']}
        originals, tasks = adoption_inputs['rows'], materials.get('tasks', [])
        _require(len(tasks) == len(originals) and [r.get('case_id') for r in tasks]
                 == [r['case_id'] for r in originals], 'Profile must cover every and only adopted continuation')
        for index, (material, original) in enumerate(zip(tasks, originals)):
            slot = original['case_id'] + ':A1'
            _require(material.get('id') == slot and material.get('revision_ref') == original
                     and material.get('revision_pointer') == '/rows/' + str(index)
                     and material.get('contract') == contracts.get(slot)
                     and material.get('baseline_judgment') == baselines.get(slot)
                     and original['subcategory'] in ELIGIBLE and contracts[slot]['kind'] == 'initial',
                     'Continuation material substituted its parent, contract or baseline judgment')
            _require(material.get('sources') == _task_sources(original),
                     'Continuation material sources are not the exact adopted task/delivery/attachments')
            for source in material['sources'].values():
                _read(roots, source)
        reviews = review.get('tasks', [])
        _require(len(reviews) == len(tasks) and len({r.get('id') for r in reviews}) == len(tasks)
                 and {r.get('id') for r in reviews} == {r['id'] for r in tasks},
                 'Continuation profile review has missing, duplicate or foreign tasks')
        task_by_id = {row['id']:row for row in tasks}
        for row in reviews:
            validate_task_review(row, task_by_id[row['id']], roots=roots)
        self.review, self.materials = deepcopy(review), deepcopy(materials)
        self.contracts, self.base_score = deepcopy(loaded['base_contracts']), deepcopy(base_score)
        self.base_profile = deepcopy(loaded['base_public_profile'])
        if corrections is not None:
            from .scoring import score_mathematical_profile_baseline_corrections
            self.base_score = score_mathematical_profile_baseline_corrections(
                self.base_score, corrections, model_id=mid)
            self.base_profile['metrics'] = deepcopy(self.base_score['metrics'])
        self.strict_report = deepcopy(adopted['_scores']['strict'])
        self.policy = deepcopy(policy)


_METRIC_KEYS = {'exact', 'confirmed', 'lower', 'upper', 'unknown_weight', 'coverage'}
_PUBLIC_KEYS = {'schema', 'version', 'benchmark_version', 'condition', 'model_id',
    'policy_sha256', 'private_review_sha256', 'private_materials_sha256', 'source_base_profile',
    'source_adoption', 'source_baseline_corrections', 'metrics', 'groups', 'revision_coverage', 'reviewer_kind', 'human_review',
    'formal_comparison_eligible', 'new_candidate_calls', 'main_scores_modified', 'post_observation'}


def validate_public(report, *, policy_sha256):
    _require(set(report) == _PUBLIC_KEYS
             and report.get('schema') == 'math-gauge.mathematical-profile-revision-model/v1'
             and report.get('version') == VERSION and report.get('benchmark_version') == EDITION
             and report.get('condition') == CONDITION and report.get('policy_sha256') == policy_sha256,
             'Unsupported public continuation mathematical profile')
    _require(report['reviewer_kind'] == 'ai' and report['human_review'] == 'pending'
             and report['formal_comparison_eligible'] is False and report['new_candidate_calls'] == 0
             and report['main_scores_modified'] is False and report['post_observation'] is True
             and _hash(report['private_review_sha256']) and _hash(report['private_materials_sha256']),
             'Continuation profile must retain its independent AI-review boundary')
    for field, prefix in (('source_base_profile', 'results/mathematical-profiles/v0.4.0/'),
                           ('source_adoption', 'results/edition-reassessments/v1.2.0/')):
        ref = report[field]
        _require(set(ref) == {'path', 'bytes', 'sha256'} and _hash(ref['sha256'])
                 and type(ref['bytes']) is int and ref['bytes'] > 0,
                 'Public continuation profile source contains unsupported fields')
        _relative(ref['path'])
        _require(ref['path'].startswith(prefix), 'Public profile source is outside its public aggregate layer')
    correction_ref = report['source_baseline_corrections']
    if correction_ref is not None:
        from .mathematical_profile_corrections import INDEX_PATH as CORRECTION_INDEX
        _require(set(correction_ref) == {'path', 'bytes', 'sha256'}
                 and correction_ref['path'] == CORRECTION_INDEX and _hash(correction_ref['sha256'])
                 and type(correction_ref['bytes']) is int and correction_ref['bytes'] > 0,
                 'Public baseline correction binding cannot expose private evidence')
    _require(set(report['metrics']) == set(AXES) and report['groups'] == {},
             'Continuation profiles retain seven axes without additional weighted layers')
    for axis, metric in report['metrics'].items():
        planned, unit = (8, 'benchmark_subcategory') if axis == 'completion' else (35, 'mathematical_family')
        coverage = metric.get('coverage', {})
        _require(set(metric) == _METRIC_KEYS and set(coverage) == {'unit', 'planned', 'reviewed'}
                 and coverage['unit'] == unit and coverage['planned'] == planned
                 and type(coverage['reviewed']) is int and 0 <= coverage['reviewed'] <= planned,
                 'Continuation profile coverage changed its fixed denominator')
        _require(all(type(metric[k]) in (int, float) and math.isfinite(metric[k])
                     and 0 <= metric[k] <= 100 for k in ('confirmed', 'lower', 'upper', 'unknown_weight')),
                 'Invalid continuation profile interval')
        exact = metric['exact']
        _require(exact is None or type(exact) in (int, float) and math.isfinite(exact)
                 and metric['lower'] == exact == metric['upper'], 'Invalid exact continuation profile value')
        _require(metric['lower'] <= metric['confirmed'] <= metric['upper']
                 and abs(metric['upper']-metric['lower']-metric['unknown_weight']) < 1e-8
                 and (exact is None) == (metric['unknown_weight'] > 0),
                 'Continuation unknowns cannot be replaced by first-answer values')
    coverage = report['revision_coverage']
    _require(set(coverage) == {'selected_tasks', 'reviewed_tasks', 'unknown_tasks'}
             and all(type(n) is int and n >= 0 for n in coverage.values())
             and coverage['reviewed_tasks'] + coverage['unknown_tasks'] == coverage['selected_tasks'],
             'Public continuation review coverage must be anonymous and exhaustive')
    return report


def project_public(score, *, policy_sha256, private_review_sha256, private_materials_sha256,
                   source_base_profile, source_adoption, source_baseline_corrections=None):
    """Publish anonymous aggregates and public/opaque byte bindings only."""
    result = dict(schema='math-gauge.mathematical-profile-revision-model/v1',
        version=VERSION, benchmark_version=EDITION, condition=CONDITION, model_id=score['model_id'],
        policy_sha256=policy_sha256, private_review_sha256=private_review_sha256,
        private_materials_sha256=private_materials_sha256,
        source_base_profile=_reference(source_base_profile), source_adoption=_reference(source_adoption),
        source_baseline_corrections=deepcopy(source_baseline_corrections),
        metrics=deepcopy(score['metrics']), groups={}, revision_coverage=deepcopy(score['revision_coverage']),
        reviewer_kind='ai', human_review='pending', formal_comparison_eligible=False,
        new_candidate_calls=0, main_scores_modified=False, post_observation=True)
    return validate_public(result, policy_sha256=policy_sha256)


def load_public_profiles(root, models, *, transition=None):
    if not is_file(Path(root) / INDEX_PATH):
        return None
    from .neutral_revision import load_transition, load_public
    transition = transition or load_transition(root)
    _require(transition is not None, 'Continuation profiles require their adopted edition')
    policy, digest = load_policy(root)
    index = json.loads(read_bytes(Path(root) / INDEX_PATH))
    _require(index.get('schema') == 'math-gauge.mathematical-profile-revision-index/v1'
             and index.get('version') == VERSION and index.get('benchmark_version') == EDITION
             and index.get('policy_sha256') == digest and set(index['models']) == set(transition['adoptions']),
             'Continuation profile index lost the current adoption cohort')
    source_bytes(root, index['source_transition'])
    source_bytes(root, index['base_index'])
    if index.get('baseline_corrections') is not None:
        source_bytes(root, index['baseline_corrections'])
    _require(index['source_transition']['path'] == 'results/edition-reassessments/v1.2.0/transition.json'
             and index['base_index']['path'] == BASE_INDEX_PATH,
             'Continuation profile index substituted its immutable source layer')
    base_index = json.loads(source_bytes(root, index['base_index']))
    from .scoring import profile_strict_completion_metric
    values = []
    for model in models:
        mid = model['id']
        _require(mid in transition['adoptions'], 'Unadopted model cannot inherit a continuation profile')
        ref = index['models'][mid]
        report = validate_public(json.loads(source_bytes(root, ref)), policy_sha256=digest)
        _require(report['model_id'] == mid and report['source_adoption'] == transition['adoptions'][mid]
                 and report['source_base_profile'] == base_index['models'][mid]
                 and report['source_baseline_corrections'] == index.get('baseline_corrections'),
                 'Continuation profile does not bind the current model and parent answer')
        baseline = json.loads(source_bytes(root, report['source_base_profile']))
        adopted = load_public(root, transition['adoptions'][mid])
        _require(baseline.get('model_id') == mid
                 and report['metrics']['initiative'] == baseline['metrics']['initiative']
                 and report['metrics']['completion'] == profile_strict_completion_metric(adopted['_scores']['strict'])
                 and report['revision_coverage']['selected_tasks'] == adopted['revision_counts']['selected'],
                 'Continuation profile changed initiative, official SMC or selected-task count')
        values.append(dict(id=mid, metrics=deepcopy(report['metrics']), groups={},
            revision_coverage=deepcopy(report['revision_coverage']), review_status='ai-reviewed', source=ref))
    base_policy, _ = load_base_policy(root)
    return dict(schema='math-gauge.mathematical-profile-revision/v1', version=VERSION,
        benchmark_version=EDITION, axes=deepcopy(base_policy['axes']), models=values,
        reviewer_kind='ai', human_review='pending', new_candidate_calls=0,
        main_scores_modified=False, method='../../protocol/mathematical-profile-revision.md')
