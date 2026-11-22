"""Bind independent taste reviews of retained theorem-extension answers.

Only anonymous stage-wide metrics leave the evaluator side. The existing
research score and mathematical-profile judgments remain immutable.
"""
import hashlib
import json
from pathlib import Path

from . import mathematical_profile as profiles
from . import mathematical_profile_revision as revision_profiles
from . import neutral_revision as neutral
from .evidence_retention import read_bytes
from .mathematical_profile import _hash, _require, _text
from .open_research import encoded
from .scoring import _average, _bound, _interval, _percent

VERSION = '0.1.0'
EDITION = '1.3.0'
BASE_EDITION = '1.2.0'
CONDITION = 'nonlogical_retry_3'
FAMILIES = 6
UNIT = 'theorem_extension_family'
DIRECTORY = Path('protocol/mathematical-taste/v1.3.0')
POLICY_PATH = DIRECTORY / 'legacy-taste-policy.json'
POLICY_FILE = Path(__file__).resolve().parents[1] / POLICY_PATH
PUBLIC_PATH = DIRECTORY / 'legacy-taste-results.json'
SCOPE_PATH = Path('research-previews/v1.3.0/legacy-taste/scope.json')
CATALOG_SCHEMA = 'math-gauge.legacy-taste-source-catalog/v1'
REVIEW_SCHEMA = 'math-gauge.legacy-taste-review/v1'
PUBLIC_SCHEMA = 'math-gauge.legacy-taste-profile-source/v1'
DELIVERY_STATES = {'active_final': 'normal_final', 'forced_content': 'known_delivery_failure',
                   'blank': 'known_delivery_failure', 'not_run': 'unrun'}
REVIEWER = dict(requested_model='gpt-6.1-sol', requested_effort='max',
                reviewer_kind='ai', human_review='pending',
                backend_identity_independently_verified=False)


def sha256(raw):
    return hashlib.sha256(raw).hexdigest()


def load_policy(path=POLICY_FILE):
    raw = Path(path).read_bytes()
    policy = json.loads(raw)
    fixed = dict(schema='math-gauge.legacy-taste-policy/v1', version=VERSION, edition=EDITION,
                 base_edition=BASE_EDITION, condition=CONDITION, planned_families=FAMILIES,
                 family_weights='equal', review_mode='RMC', candidate_calls=0,
                 affects='mathematical_taste_profile_only')
    _require(set(policy) == set(fixed) | {'private_scope_sha256', 'revision_percent', 'criterion'}
             and all(type(policy.get(k)) is type(v) and policy[k] == v for k, v in fixed.items())
             and _hash(policy['private_scope_sha256']) and _text(policy['criterion'])
             and type(policy['revision_percent']) is int and 0 < policy['revision_percent'] < 100,
             'Invalid fixed legacy taste policy')
    return policy, sha256(raw)


def profile_model_ids(data):
    """Current ranked configurations and the eligible first-answer profile extras."""
    return {row['id'] for row in data.get('models', [])} | {
        row['id'] for row in data.get('profile_models', [])
        if row.get('presentation_eligibility', {}).get('ranked') is not False
    }


def _document(root, ref):
    return json.loads(profiles.source_bytes(root, ref))


def _read(roots, ref):
    _require(ref.get('repository') in roots, 'Unknown legacy taste evidence repository')
    return profiles.source_bytes(roots[ref['repository']], ref)


def _load_scope(raw, policy, roots):
    scope = json.loads(raw)
    _require(sha256(raw) == policy['private_scope_sha256']
             and scope.get('schema') == 'math-gauge.legacy-taste-scope/v1'
             and scope.get('version') == VERSION, 'Legacy taste scope differs from its frozen bytes')
    families = {row['case_id']: row for row in scope['eligible']}
    _require(len(scope['eligible']) == len(families) == FAMILIES
             and len({r['family_id'] for r in families.values()}) == FAMILIES
             and sorted(r['visibility'] for r in families.values()) == ['private'] * 4 + ['public'] * 2
             and all(r['weight'] == dict(numerator=1, denominator=FAMILIES) for r in families.values()),
             'Legacy taste scope must retain six equally weighted original theorem-extension families')
    for row in families.values():
        for ref in row['sources']:
            _read(roots, ref)
    return families


def _indexed_materials(roots, indexes, model_id):
    public_ref = indexes['public']['models'][model_id]
    private = indexes['private']['models'][model_id]
    public = _document(roots['public'], public_ref)
    binding = private['source-bindings']
    _require(private['public_projection'] == public_ref and public['model_id'] == model_id
             and public['private_materials_sha256'] == binding['sha256'],
             'Legacy taste material differs from its actual selected public/private profile binding')
    material = _document(roots['private'], binding)
    _require(material['model_id'] == model_id and material['condition'] == CONDITION,
             'Legacy taste source is a different model or attempt condition')
    return public, material, binding


def _verify_answer(roots, ref, expected_hash):
    _require(ref is not None and ref['sha256'] == expected_hash and _read(roots, ref).strip(),
             'Legacy taste evidence must match the nonempty selected normal final')


def _first_sources(roots, material, families):
    sources = material['sources']
    results = {}
    for row in material['tasks']:
        cid = row['id'].removesuffix(':A1')
        if cid not in families:
            continue
        state = row['selected_state']
        _require(cid not in results and state.get('case_id') == cid
                 and state.get('family_id') == families[cid]['family_id']
                 and state.get('subcategory') == 'theorem-extension',
                 'Legacy taste source substituted its original family')
        classification = (state.get('submission_assessment') or {}).get(
            'classification', state.get('submission_classification'))
        status = DELIVERY_STATES.get(classification, 'source_unresolved')
        review = sources.get('tx-review:' + row['id'])
        if review is not None:
            _read(roots, review)
        evidence = {}
        if status == 'normal_final':
            answer = row['raw_answer']
            _require(sources['answer:' + row['id']] == answer, 'Legacy taste changed the selected final')
            _verify_answer(roots, answer, row['response_sha256'])
            evidence['answer'] = answer
        results[cid] = dict(status=status, response_sha256=row['response_sha256'],
                            evidence=evidence, mathematical_fact_review=review)
    _require(set(results) == set(families), 'Missing fixed first-answer legacy taste family')
    return results


def _revision_sources(roots, inputs_ref, adopted, first, families, model_id):
    _require(inputs_ref['repository'] == 'private' and inputs_ref['sha256'] == adopted['private_inputs_sha256'],
             'Legacy taste continuation must bind the officially adopted source input')
    inputs = json.loads(_read(roots, inputs_ref))
    _require(inputs['model_id'] == adopted['model_id'] == model_id,
             'Legacy taste continuation belongs to another model')
    bases = {mode: _document(roots['private'], ref) for mode, ref in inputs['base_reports'].items()}
    neutral.load_inputs(roots['private'], {k: inputs_ref[k] for k in ('path', 'bytes', 'sha256')},
                        public_root=roots['public'], base_reports=bases)
    results = {}
    for row in inputs['rows']:
        cid = row['case_id']
        if cid not in families:
            continue
        _require(row['family_id'] == families[cid]['family_id'] and row['subcategory'] == 'theorem-extension'
                 and row['first_response_sha256'] == first[cid]['response_sha256'],
                 'Legacy taste continuation changed the selected parent or family')
        final = row['continuation']
        status = {'reviewed': 'normal_final', 'delivery_failed': 'known_delivery_failure',
                  'not_run': 'unrun'}[final['status']]
        evidence, digest, review = {}, None, None
        if status == 'normal_final':
            answer = dict(final['answer'], repository='private')
            digest = answer['sha256']
            _verify_answer(roots, answer, digest)
            evidence['answer'] = answer
            evidence.update({'attachment:' + str(i): dict(ref, repository='private')
                             for i, ref in enumerate(final.get('attachments', []))})
            review = dict(final['review'], repository='private')
        results[cid] = dict(status=status, response_sha256=digest, evidence=evidence,
                            mathematical_fact_review=review, first_response_sha256=row['first_response_sha256'])
    return results


def build_source_catalog(public_root, private_root, scope_raw, policy, baseline_bytes):
    """Reproduce the exact evaluator-only first-answer and adopted-source intake."""
    roots = dict(public=Path(public_root), private=Path(private_root))
    families = _load_scope(scope_raw, policy, roots)
    baseline = json.loads(baseline_bytes)
    transition = neutral.load_transition(public_root)
    _require(baseline['benchmark_version'] == BASE_EDITION and transition is not None
             and {row['id'] for row in baseline['models']} == set(transition['adoptions']),
             'Legacy taste needs the retained 1.2 rank cohort and its actual adoption set')
    indexes = [{which: json.loads(read_bytes(root / path)) for which, root in roots.items()}
               for path in (profiles.INDEX_PATH, revision_profiles.INDEX_PATH)]
    base_policy, base_policy_sha = profiles.load_policy(public_root)
    _, revision_policy_sha = revision_profiles.load_policy(public_root)
    models = {}
    for model_id in sorted(profile_model_ids(baseline)):
        original_public, material, first_ref = _indexed_materials(roots, indexes[0], model_id)
        profiles.validate_public(original_public, base_policy, policy_sha256=base_policy_sha)
        first = _first_sources(roots, material, families)
        revision_ref, inputs_ref, revision = None, None, None
        adoption_ref = transition['adoptions'].get(model_id)
        if adoption_ref is not None:
            revision_public, material, revision_ref = _indexed_materials(roots, indexes[1], model_id)
            revision_profiles.validate_public(revision_public, policy_sha256=revision_policy_sha)
            _require(revision_public['source_adoption'] == adoption_ref,
                     'Legacy taste revision profile belongs to a different adoption')
            adopted = neutral.load_public(public_root, adoption_ref)
            inputs_ref = material['sources']['adoption_inputs']
            revision = _revision_sources(roots, inputs_ref, adopted, first, families, model_id)
        models[model_id] = dict(first_materials=first_ref, revision_materials=revision_ref,
                                adopted_inputs=inputs_ref, first=first, revision=revision)
    return dict(schema=CATALOG_SCHEMA, version=VERSION, edition=EDITION,
                condition=CONDITION, scope_sha256=sha256(scope_raw),
                source_binding=dict(edition=BASE_EDITION, sha256=sha256(baseline_bytes)),
                families=list(families), models=models,
                counts=dict(models=len(models), first=sum(len(m['first']) for m in models.values()),
                            revision=sum(len(m['revision'] or {}) for m in models.values())),
                new_candidate_calls=0)


def _review_grade(row, manuscript, roots):
    fields = {'model_id', 'stage', 'case_id', 'response_sha256', 'assessment_status', 'score',
              'enough_evidence', 'reason', 'valid_scope', 'choice_value', 'condition_cost', 'evidence'}
    _require(set(row) == fields and manuscript['status'] == 'normal_final'
             and row['response_sha256'] == manuscript['response_sha256'],
             'Legacy taste review must bind its own exact delivered response')
    score = row['score']
    if row['assessment_status'] == 'reviewed':
        _require(row['enough_evidence'] is True and type(score) is int and 0 <= score <= 100,
                 'A legacy taste score needs independently reviewable choice evidence')
    else:
        _require(row['assessment_status'] == 'evidence_insufficient'
                 and row['enough_evidence'] is False and score is None,
                 'Insufficient legacy taste evidence must stay unknown')
    _require(all(_text(row[key]) for key in ('reason', 'valid_scope', 'choice_value', 'condition_cost')),
             'A legacy taste review needs mathematical scope, value, and condition-cost reasons')
    _require(isinstance(row['evidence'], list) and row['evidence'],
             'A legacy taste review needs at least one exact quote')
    for entry in row['evidence']:
        _require(set(entry) in ({'quote'}, {'source_id', 'quote'}) and _text(entry.get('quote')),
                 'Invalid legacy taste evidence quote')
        source = manuscript['evidence'].get(entry.get('source_id', 'answer'))
        _require(source is not None and entry['quote'].encode() in _read(roots, source),
                 'Legacy taste quote differs from its own exact final or submitted attachment')
    return score


def _judgments(roots, catalog, catalog_sha256, reviews):
    grades = {}
    for review in reviews:
        fixed = dict(schema=REVIEW_SCHEMA, version=VERSION, edition=EDITION, condition=CONDITION,
                     source_catalog_sha256=catalog_sha256, **REVIEWER)
        _require(set(review) == set(fixed) | {'reviewer_id', 'actual_context', 'judgments'}
                 and all(type(review.get(k)) is type(v) and review[k] == v for k, v in fixed.items())
                 and _text(review['reviewer_id']) and _text(review['actual_context'])
                 and isinstance(review['judgments'], list) and review['judgments'],
                 'Legacy taste review lost its named AI reviewer, actual context, or catalog binding')
        for row in review['judgments']:
            key = row['model_id'], row['stage'], row['case_id']
            mid, stage, cid = key
            model = catalog['models'].get(mid, {})
            material = (model.get(stage) or {}).get(cid) if stage in ('first', 'revision') else None
            _require(key not in grades and material is not None,
                     'Duplicate legacy taste review or unselected model, stage, or family')
            grades[key] = _review_grade(row, material, roots)
    return grades


def _grade_interval(score):
    value = None if score is None else score / 100
    return _interval(None if value is None else dict(lower=value, upper=value, exact=value))


def _metric(intervals, observed):
    low, high, value = _average(intervals)
    exact = _percent(value)
    return dict(lower=exact if exact is not None else _bound(low, lower=True),
                upper=exact if exact is not None else _bound(high, lower=False),
                exact=exact, confirmed=_percent(low),
                coverage=dict(unit=UNIT, planned=FAMILIES, observed=observed,
                              reviewed=sum(row[2] is not None for row in intervals)))


def _model_metrics(model_id, model, scores, policy):
    first, revision = [], []
    observed = dict(first=0, revision=0)
    for cid in model['first']:
        grade = scores.get((model_id, 'first', cid))
        interval = _grade_interval(grade)
        first.append(interval)
        observed['first'] += int(grade is not None)
        if model['revision'] is None:
            continue
        later = scores.get((model_id, 'revision', cid))
        observed['revision'] += int(grade is not None or later is not None)
        if cid in model['revision']:
            weight = policy['revision_percent']
            interval = _average([interval, _grade_interval(later)], [100 - weight, weight])
        revision.append(interval)
    return dict(first=_metric(first, observed['first']),
                revision=_metric(revision, observed['revision']) if revision else None)


def prepare_public(roots, catalog_raw, review_bytes, policy, policy_sha256):
    """Accept only already authenticated catalog bytes and independently supplied reviews."""
    catalog = json.loads(catalog_raw)
    source_sha256 = sha256(catalog_raw)
    grades = _judgments(roots, catalog, source_sha256, [json.loads(raw) for raw in review_bytes])
    models = {mid: _model_metrics(mid, model, grades, policy) for mid, model in catalog['models'].items()}
    return dict(schema=PUBLIC_SCHEMA, version=VERSION, edition=EDITION, condition=CONDITION,
                source_binding=catalog['source_binding'], policy_sha256=policy_sha256,
                source_catalog_sha256=source_sha256, review_sha256=[sha256(raw) for raw in review_bytes],
                reviewer_kind='ai', human_review='pending', post_observation=True, models=models)


def _validate_metric(metric):
    _require(isinstance(metric, dict) and set(metric) == {'lower', 'upper', 'exact', 'confirmed', 'coverage'},
             'Public legacy taste metric includes unsupported private fields')
    coverage = metric['coverage']
    _require(set(coverage) == {'unit', 'planned', 'reviewed', 'observed'}
             and coverage['unit'] == UNIT and coverage['planned'] == FAMILIES
             and all(type(coverage[k]) is int for k in ('planned', 'reviewed', 'observed'))
             and 0 <= coverage['reviewed'] <= coverage['observed'] <= FAMILIES,
             'Public legacy taste coverage changed the fixed family denominator')
    _require(all(type(metric[k]) in (int, float) and 0 <= metric[k] <= 100
                 for k in ('lower', 'upper', 'confirmed'))
             and metric['lower'] <= metric['confirmed'] <= metric['upper']
             and ((metric['exact'] is None and metric['lower'] < metric['upper'] and coverage['reviewed'] < FAMILIES)
                  or (type(metric['exact']) in (int, float) and metric['lower'] == metric['exact'] == metric['upper']
                      and coverage['reviewed'] == FAMILIES))
             and (coverage['observed'] != 0 or (metric['lower'], metric['upper']) == (0, 100)),
             'Public legacy taste result replaced unknowns or credited unreviewed evidence')


def validate_public(report, policy_sha, baseline, baseline_sha):
    """Enforce an aggregate-only allowlist before serving HTML or downloads."""
    fields = {'schema', 'version', 'edition', 'condition', 'source_binding', 'policy_sha256',
              'source_catalog_sha256', 'review_sha256', 'reviewer_kind', 'human_review', 'post_observation', 'models'}
    _require(set(report) == fields and report['schema'] == PUBLIC_SCHEMA and report['version'] == VERSION
             and report['edition'] == EDITION and report['condition'] == CONDITION
             and report['policy_sha256'] == policy_sha
             and report['source_binding'] == dict(edition=BASE_EDITION, sha256=baseline_sha)
             and _hash(report['source_catalog_sha256']) and isinstance(report['review_sha256'], list)
             and all(_hash(value) for value in report['review_sha256'])
             and report['reviewer_kind'] == 'ai' and report['human_review'] == 'pending'
             and report['post_observation'] is True,
             'Public legacy taste report changed source bindings or crosses its privacy boundary')
    ranked = {row['id'] for row in baseline['models']}
    models = report['models']
    _require(set(models) == profile_model_ids(baseline), 'Legacy taste lost the current profile cohort')
    for mid, model in models.items():
        _require(set(model) == {'first', 'revision'} and (model['revision'] is not None) == (mid in ranked),
                 'Legacy taste revised view requires an actually adopted source')
        for metric in (value for value in model.values() if value is not None):
            _validate_metric(metric)
            _require(metric['coverage']['observed'] == 0 or report['review_sha256'],
                     'Measured legacy taste needs an opaque independent review binding')
    return report
