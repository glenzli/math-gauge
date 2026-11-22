"""Named corrections to retained TX reviews, separate from execution and revision.

Original 1.1 assessments and native continuation parents remain immutable.
This component authenticates the review addendum; scoring.py replays the same
claim/submission gates and the same already-adopted continuation.
"""
from copy import deepcopy
from pathlib import Path
import json

from .benchmarks import identity
from .theorem_extension_calibration import (
    CalibrationInputs, CONDITIONS, MODES, PUBLIC_CASES, _source_rows,
    _source_descriptor, document, load_policy, read, require, validate_review,
)

DIRECTORY = 'results/theorem-extension-amendments/v0.1.0'
INDEX_PATH = DIRECTORY + '/index.json'


class ReviewAmendmentInputs(CalibrationInputs):
    """A verified correction to current tiers, never a new mathematical run."""


def load_inputs(public_root, private_root, ref, *, source):
    """Bind each new judgment to the exact current answer, old tier and gates."""
    public_root, private_root = Path(public_root), Path(private_root)
    public, private, source_ref = source
    data = document(private_root, ref)
    require(data.get('schema') == 'math-gauge.theorem-extension-review-amendment-inputs/v1'
            and data.get('version') == '0.1.0' and data.get('source_assessment') == source_ref
            and data.get('base_reports') == private['scores']
            and data.get('new_candidate_calls') == 0
            and data.get('scoring_rules_changed') is False
            and data.get('original_bytes_rewritten') is False
            and data.get('reviewer_kind') == 'ai' and data.get('human_review') == 'pending',
            'TX review amendment lost its immutable current assessment')
    policy = load_policy(public_root, data['policy'])
    audit = document(private_root, data['uniform_audit'])
    require(audit.get('schema') == 'math-gauge.uniform-tx-review-adjudication/v1'
            and audit.get('new_candidate_calls') == 0 and audit.get('scoring_rules_changed') is False,
            'TX amendment needs its explicit final uniform-review selection')
    adopted = {(r['model_id'],r['condition'],r['case_id']):r for r in audit['rows']}
    standard = data['private_standards']
    require({k:standard[k] for k in ('bytes', 'sha256')} == policy['private_standards'],
            'TX amendment selected another private research standard')
    read(private_root, standard)
    original_inputs = document(private_root, private['inputs'])
    record_ref = original_inputs.get('source_record', private.get('record'))
    require(record_ref == data['source_record'], 'TX amendment changed its original record')
    record = document(private_root, record_ref)
    folder = Path(record_ref['path']).parent
    source_inputs = next((record.get(k) for k in
        ('theorem_extension_inputs', 'mathematical_inputs', 'mathematical_input') if record.get(k)), None)
    require(source_inputs is not None, 'TX amendment needs the retained original math input')
    source_inputs = _source_descriptor(folder, source_inputs)
    payload = dict(model_id=data['model_id'], model_label=data['model_label'], record_id=folder.name,
        source_benchmark_version=record.get('benchmark_version') or original_inputs.get('source_benchmark_version'),
        policy_sha256=data['policy']['sha256'], inputs_sha256=ref['sha256'],
        base_identities={}, base_sha256={}, conditions={})
    bases = {m:{c:document(private_root, private['scores'][m][c]) for c in CONDITIONS} for m in MODES}
    for mode in MODES:
        payload['base_identities'][mode] = {c:identity(bases[mode][c]) for c in CONDITIONS}
        payload['base_sha256'][mode] = {c:private['scores'][mode][c]['sha256'] for c in CONDITIONS}
    require(set(data['conditions']) == set(CONDITIONS), 'TX amendment lost an attempt condition')
    for condition in CONDITIONS:
        base = bases['partial'][condition]
        tasks = {t['case_id']:t for t in base['tasks'] if t['subcategory'] == 'theorem-extension'}
        require(len(tasks) == 6 and len(data['conditions'][condition]) == 6
                and {r['case_id'] for r in data['conditions'][condition]} == set(tasks),
                'TX amendment must retain the exact six original families')
        originals, claims, submissions = _source_rows(private_root, record, folder,
            source_inputs, condition, base, public_root)
        rows = []
        for row in data['conditions'][condition]:
            cid, old = row['case_id'], tasks[row['case_id']]
            grade = adopted.get((data['model_id'], condition, cid))
            require(grade is not None and grade['old_B'] == grade['new_B'] == row['baseline_B']
                    and grade['old_R'] == row['old_R'] and grade['new_R'] == row['new_R']
                    and grade['response_sha256'] == old.get('response_sha256'),
                    'TX amendment differs from the final source-bound mathematical review')
            require(row['baseline_B'] == old['research']['baseline_B']
                    and row['old_R'] == old['research']['research_R']
                    and (row['response'] or {}).get('sha256') == old.get('response_sha256')
                    and (row['source_review'] or {}).get('sha256') == old.get('review_sha256'),
                    'TX amendment replaced its original answer, baseline or current tier')
            answer = None if row['response'] is None else read(private_root, row['response'])
            if row['source_review'] is not None:
                read(private_root, row['source_review'])
            review = validate_review(document(private_root, row['new_review']), row=row,
                policy_sha256=data['policy']['sha256'],
                standard_sha256=(policy['standards']['sha256'] if cid in PUBLIC_CASES
                                 else policy['private_standards']['sha256']), answer=answer)
            require(cid in originals and cid in claims and cid in submissions,
                    'TX amendment lost the original claim/submission gate')
            require(submissions[cid]['classification'] == 'active_final' or row['new_R'] == row['old_R'],
                    'A missing or forced original final cannot gain a research tier')
            rows.append(dict(row, review_sha256=row['new_review']['sha256'],
                claim=claims[cid], submission=submissions[cid],
                case=dict(case_id=cid, component='theorem-extension'), status=review['status']))
        payload['conditions'][condition] = rows
    return ReviewAmendmentInputs(json.dumps(payload, ensure_ascii=False, sort_keys=True,
                                            separators=(',', ':')).encode())


def load_public(root, model_id, *, original_baseline=None, original_adoption=None):
    """Read only anonymous projections; private case reviews never enter the UI."""
    root = Path(root)
    if not (root / INDEX_PATH).is_file():
        return None
    index = json.loads((root / INDEX_PATH).read_bytes())
    require(index.get('schema') == 'math-gauge.theorem-extension-review-amendment-index/v1'
            and index.get('version') == '0.1.0' and index.get('new_candidate_calls') == 0
            and index.get('scoring_rules_changed') is False, 'Invalid TX amendment index')
    ref = index['models'].get(model_id)
    if ref is None:
        return None
    data = document(root, ref)
    fields = {'schema','version','model_id','record_id','policy','source_assessment','original_adoption',
        'original_baseline','baseline','revised','public_tasks','public_reviews','private_manifest_sha256',
        'private_inputs_sha256','reviewer_kind','human_review','new_candidate_calls','scoring_rules_changed'}
    require(set(data) == fields and data['schema'] == 'math-gauge.theorem-extension-review-amendment-public/v1'
            and data['model_id'] == model_id and data['version'] == '0.1.0'
            and data['new_candidate_calls'] == 0 and data['scoring_rules_changed'] is False
            and data['reviewer_kind'] == 'ai' and data['human_review'] == 'pending',
            'TX amendment crossed its aggregate-only public boundary')
    load_policy(root, data['policy'])
    source = document(root, data['source_assessment'])
    from .neutral_revision import source_assessment_edition
    from .editions import load_assessment_transition
    edition = source_assessment_edition(root)
    selected = edition.get('current_assessment_admissions', {}).get(model_id)
    selected = selected or load_assessment_transition(root, edition)['calibrations'].get(model_id)
    require(data['source_assessment'] == selected and data['original_baseline'] == source['scores'],
            'TX amendment selected another original assessment or baseline')
    if original_adoption is not None:
        require(data['original_adoption'] == original_adoption,
                'TX amendment changed the selected continuation')
    old = {m:{c:document(root, r) for c,r in refs.items()}
           for m,refs in data['original_baseline'].items()}
    if original_baseline is not None:
        require(old == original_baseline, 'TX amendment changed its retained baseline')
    baseline = {m:{c:document(root,r) for c,r in refs.items()} for m,refs in data['baseline'].items()}
    revised = None if data['revised'] is None else {m:document(root,r) for m,r in data['revised'].items()}
    prior_revision = None
    if data['original_adoption'] is not None:
        from .neutral_revision import load_transition, load_public as load_revision
        require(load_transition(root)['adoptions'].get(model_id) == data['original_adoption'],
                'TX amendment has an unselected revision parent')
        prior_revision = load_revision(root, data['original_adoption'])['_scores']
    for stage in [baseline] + ([] if revised is None else [{m:{'nonlogical_retry_3':r} for m,r in revised.items()}]):
        require(set(stage) == set(MODES), 'TX amendment needs all three score modes')
        for mode, conditions in stage.items():
            for condition, report in conditions.items():
                require(report.get('schema') == 'math-gauge.assessment-score-aggregate/v1'
                        and report['score_mode'] == mode and report['attempt_condition'] == condition
                        and report.get('tx_review_amendment', {}).get('inputs_sha256') == data['private_inputs_sha256']
                        and not {'tasks','rows','conditions','reviews'}.intersection(report),
                        'TX amendment report lost its source or privacy boundary')
                for key in old[mode][condition]['contributions']:
                    if key not in {'theorem-extension','research','earned','overall'}:
                        prior = old[mode][condition] if stage is baseline else prior_revision[mode]
                        require(report['contributions'][key] == prior['contributions'][key],
                                'TX amendment changed an unrelated baseline score')
    require(set(data['public_reviews']) == set(CONDITIONS), 'TX amendment lost a public review condition')
    policy=load_policy(root,data['policy'])
    for rows in data['public_reviews'].values():
        require(len(rows)==len(PUBLIC_CASES) and {r['case_id'] for r in rows} == set(PUBLIC_CASES)
                and all(set(row) == {'case_id','review'} and row['case_id'] in PUBLIC_CASES for row in rows),
                'Private TX review leaked into the public amendment')
        for row in rows:
            document(root,row['review'])
    tasks = {key:document(root, item) for key,item in data['public_tasks'].items()}
    from .records import public_assessment_case_ids
    from .theorem_extension_calibration import _public_task_projection
    ids = public_assessment_case_ids(json.loads((root/'protocol/scoring-policy.json').read_bytes()))
    require(set(tasks) == ({'baseline'} if revised is None else {'baseline','revised'}),
            'TX amendment task projections lost their assessment stage')
    _public_task_projection(tasks['baseline'],public_ids=ids,scores=baseline,benchmark_version='1.1.0')
    for stage,projection in tasks.items():
        require(set(projection.get('public_case_ids',[])) == set(ids), 'TX amendment changed public task coverage')
        require(set(projection['views']) == set(MODES), 'TX amendment task projection lost a score mode')
        for mode, conditions in projection['views'].items():
            require(set(conditions) == (set(CONDITIONS) if stage=='baseline' else {'nonlogical_retry_3'}),
                    'TX amendment moved a task projection to another attempt condition')
            for condition,view in conditions.items():
                report=baseline[mode][condition] if stage=='baseline' else revised[mode]
                require(view['source_report_sha256'] == report['source_bindings']['private_report_sha256'],
                        'TX amendment task projection has another source score report')
                require({r['case_id'] for r in view['tasks']} == set(ids), 'Private TX score leaked into projection')
                for row in view['tasks']:
                    require(set(row) <= {'case_id','completion','strict_pass','response_sha256','review_sha256','neutral_revision'},
                            'Private fields leaked into a TX amendment task projection')
    for condition,rows in data['public_reviews'].items():
        by_id={row['case_id']:row for row in tasks['baseline']['views']['partial'][condition]['tasks']}
        for entry in rows:
            review=document(root,entry['review']);task=by_id[entry['case_id']]
            require(entry['review']['sha256']==task['review_sha256']
                    and review.get('case_id')==entry['case_id']
                    and review.get('answer_sha256')==task['response_sha256']
                    and review.get('policy_sha256')==data['policy']['sha256']
                    and review.get('standard_sha256')==policy['standards']['sha256']
                    and review.get('reviewer_kind')=='ai' and review.get('human_review')=='pending',
                    'TX amendment public review does not bind its actual answer and score')
    return dict(data, _selection=ref, _baseline=baseline, _revised=revised, _public_tasks=tasks)


def project_score(score):
    from .records import project_assessment_score
    value = project_assessment_score(score)
    value['tx_review_amendment'] = deepcopy(score['tx_review_amendment'])
    if score.get('neutral_revision') is not None:
        value['neutral_revision'] = deepcopy(score['neutral_revision'])
    return value


def apply_model(model, amendment, *, revised=False):
    """Attach authenticated score views, leaving execution metadata intact."""
    for mode, refs in amendment['_baseline'].items():
        if mode == 'partial':
            model['combined'] = deepcopy(refs['single_attempt'])
            model['retry']['combined'] = deepcopy(refs['nonlogical_retry_3'])
        else:
            model[mode] = deepcopy(refs)
    if revised:
        require(amendment['_revised'] is not None, 'No reviewed continuation correction exists')
        for mode, report in amendment['_revised'].items():
            if mode == 'partial':
                model['retry']['combined'] = deepcopy(report)
            else:
                model[mode]['nonlogical_retry_3'] = deepcopy(report)
    model['tx_review_amendment'] = {key:deepcopy(amendment[key]) for key in
        ('public_tasks','public_reviews','policy','source_assessment')}
    model['tx_review_amendment']['manifest'] = deepcopy(amendment['_selection'])


def project_profile_completion(profile, scores):
    """Completion is a score projection, independently reviewed traits stay intact."""
    if profile is None:
        return
    from .scoring import profile_strict_completion_metric
    for row in profile['models']:
        if row['id'] in scores:
            row['metrics']['completion'] = profile_strict_completion_metric(scores[row['id']])
