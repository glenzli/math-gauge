#!/usr/bin/env python3
"""Import or reproduce independent continuation traits; never call candidates."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from math_gauge.evidence_retention import read_bytes
from math_gauge.mathematical_profile import source_bytes
from math_gauge.mathematical_profile_revision import (
    VERSION, EDITION, CONDITION, DIRECTORY, INDEX_PATH, BASE_INDEX_PATH,
    RevisionProfileInputs, load_policy, project_public, load_public_profiles,
)
from math_gauge.neutral_revision import load_transition, TRANSITION_PATH
from math_gauge.scoring import score_mathematical_profile_revisions


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode()


def reference(path, raw):
    return dict(path=path, bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())


def _write_immutable(root, files):
    for path, raw in files.items():
        target = Path(root)/path
        if target.exists() and target.read_bytes() != raw:
            raise ValueError('Refusing to replace a retained profile artifact: ' + path)
    for path, raw in files.items():
        target = Path(root)/path
        target.parent.mkdir(parents=True, exist_ok=True)
        if not target.exists():
            target.write_bytes(raw)


def retain_source_relocations(private_root, review_lock_path, freeze_path, baseline_adoption_path=None):
    """Keep original absolute provenance plus a hash-checked portable inventory."""
    private_root, review_lock_path = Path(private_root), Path(review_lock_path)
    lock, freeze = json.loads(review_lock_path.read_bytes()), json.loads(Path(freeze_path).read_bytes())
    entries = {}
    def bind(original, retained):
        raw = read_bytes(private_root/retained)
        ref = reference(retained, raw)
        if isinstance(original, dict):
            if original['sha256'] != ref['sha256'] or original['bytes'] != ref['bytes']:
                raise ValueError('Retained reviewer source does not preserve original bytes')
            name = original['path']
        else:
            name = str(original)
        entries[name] = ref
    bind(review_lock_path, DIRECTORY+'/review-lock.json')
    bind(lock['review_freeze'],DIRECTORY+'/review-freeze.json')
    for mid, ref in lock['model_reviews'].items():
        bind(ref,DIRECTORY+'/'+mid+'/review.json')
    for mid, ref in freeze['models'].items():
        bind(ref,DIRECTORY+'/'+mid+'/source-bindings.json')
    original_root = review_lock_path.parent/'reviews'
    for group in ('root','tx_a','tx_b_ar'):
        retained_root = private_root/DIRECTORY/'source-reviews'/group
        for path in sorted(retained_root.rglob('*.json')):
            bind(original_root/group/path.relative_to(retained_root),path.relative_to(private_root).as_posix())
    result = dict(schema='math-gauge.profile-review-source-relocations/v1',version='0.1.0',
        original_bytes_rewritten=False,source_lock_sha256=hashlib.sha256(review_lock_path.read_bytes()).hexdigest(),
        sources=[dict(original_path=path,retained=ref) for path,ref in sorted(entries.items())])
    _write_immutable(private_root,{DIRECTORY+'/source-relocations.json':encoded(result)})
    if baseline_adoption_path is not None:
        from math_gauge.mathematical_profile_corrections import DIRECTORY as CORRECTIONS
        path=Path(baseline_adoption_path);entries={}
        bind(path,CORRECTIONS+'/adoption.json')
        for name in ('manifest','terra-6.1-max','sol-6.1-xhigh','terra-6.1-xhigh'):
            bind(path.parent/(name+'.json'),CORRECTIONS+'/source-audits/'+name+'.json')
        result.update(source_lock_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
            sources=[dict(original_path=name,retained=ref) for name,ref in sorted(entries.items())])
        _write_immutable(private_root,{CORRECTIONS+'/source-relocations.json':encoded(result)})
    return len(result['sources'])


def import_corrections(root, private_root, adoption_path):
    from math_gauge.mathematical_profile_corrections import (
        BaselineCorrectionInputs, DIRECTORY as FOLDER, INDEX_PATH as INDEX, ADOPTION_PATH,
    )
    from math_gauge.scoring import score_mathematical_profile_baseline_corrections, mathematical_profile_axis_delta
    adoption_path = Path(adoption_path)
    raw = adoption_path.read_bytes()
    adoption = json.loads(raw)
    audits = {}
    for name in ('manifest', 'terra-6.1-max', 'sol-6.1-xhigh', 'terra-6.1-xhigh'):
        value = (adoption_path.parent/(name+'.json')).read_bytes()
        key = 'audit_manifest' if name == 'manifest' else 'audit:' + name
        expected = adoption['sources'][key]
        if (expected['path'] != FOLDER + '/source-audits/' + name + '.json'
                or expected['bytes'] != len(value) or expected['sha256'] != hashlib.sha256(value).hexdigest()):
            raise ValueError('Baseline audit bytes differ from the root acceptance')
        audits[expected['path']] = value
    _write_immutable(private_root, audits)
    corrections = BaselineCorrectionInputs(raw, roots=dict(public=root, private=private_root))
    public_index = json.loads(source_bytes(root, adoption['sources']['public_base_index']))
    private_index = json.loads(source_bytes(private_root, adoption['sources']['private_base_index']))
    public, private = {}, {ADOPTION_PATH:raw}
    public_models, private_models = {}, {}
    for mid in sorted({r['model_id'] for r in corrections.rows}):
        base = json.loads(source_bytes(private_root, private_index['models'][mid]['score']))
        score = score_mathematical_profile_baseline_corrections(base, corrections, model_id=mid)
        original = json.loads(source_bytes(root, public_index['models'][mid]))
        public_report = dict(schema='math-gauge.mathematical-profile-baseline-correction-model/v1',
            version='0.1.0', benchmark_version='1.2.0', model_id=mid, metrics=score['metrics'],
            axis_delta=mathematical_profile_axis_delta(original['metrics'], score['metrics']),
            corrected_tasks=1, corrected_axes=['proof','fidelity','discernment'],
            private_adoption_sha256=corrections.sha256, source_base_profile=public_index['models'][mid],
            reviewer_kind='ai', human_review='pending', post_observation=True,
            new_candidate_calls=0, main_scores_modified=False)
        path, value = FOLDER+'/'+mid+'/profile.json', encoded(public_report)
        public[path] = value;public_models[mid] = reference(path, value)
        path, value = FOLDER+'/'+mid+'/score.json', encoded(score)
        private[path] = value;private_models[mid] = dict(score=reference(path, value),
                                                      public_projection=public_models[mid])
    common = dict(version='0.1.0',benchmark_version='1.2.0',source_profile_version='0.4.0',
        private_adoption_sha256=corrections.sha256,corrected_tasks=3,corrected_axis_judgments=9,
        reviewer_kind='ai',human_review='pending',post_observation=True,new_candidate_calls=0,
        main_scores_modified=False,original_bytes_rewritten=False)
    public[INDEX] = encoded(dict(common,
        schema='math-gauge.mathematical-profile-baseline-correction-index/v1',models=public_models))
    private[INDEX] = encoded(dict(common,
        schema='math-gauge.private-mathematical-profile-baseline-correction-index/v1',models=private_models,
        adoption=reference(ADOPTION_PATH,raw),source_audits={p:reference(p,v) for p,v in audits.items()}))
    _write_immutable(private_root, private)
    _write_immutable(root, public)
    return dict(models=3,corrected_axis_judgments=9,private_adoption_sha256=corrections.sha256)


def derive(root, private_root, review_raw, materials_raw, *, policy=None, policy_sha256=None):
    if policy is None:
        policy, policy_sha256 = load_policy(root)
    review, materials = json.loads(review_raw), json.loads(materials_raw)
    from math_gauge.mathematical_profile_corrections import load_private, INDEX_PATH as CORRECTION_INDEX
    corrections = load_private(root, private_root)
    correction_ref = None if corrections is None else reference(CORRECTION_INDEX, read_bytes(Path(root)/CORRECTION_INDEX))
    inputs = RevisionProfileInputs(review, materials, roots=dict(public=root, private=private_root),
        policy=policy, policy_sha256=policy_sha256,
        materials_sha256=hashlib.sha256(materials_raw).hexdigest(), corrections=corrections)
    score = score_mathematical_profile_revisions(inputs)
    public = project_public(score, policy_sha256=policy_sha256,
        private_review_sha256=hashlib.sha256(review_raw).hexdigest(),
        private_materials_sha256=hashlib.sha256(materials_raw).hexdigest(),
        source_base_profile=materials['sources']['base_public_profile'],
        source_adoption=materials['sources']['public_adoption'], source_baseline_corrections=correction_ref)
    return score, public


def _frozen_materials(freeze, materials_root, model_id):
    path = materials_root / model_id / 'materials.json'
    raw = path.read_bytes()
    if freeze is not None:
        expected = freeze['models'][model_id]
        if len(raw) != expected['bytes'] or hashlib.sha256(raw).hexdigest() != expected['sha256']:
            raise ValueError('Profile continuation materials differ from their review freeze')
    return raw


def import_reviews(root, private_root, paths, materials_root, *, freeze_path=None, review_lock_path=None):
    root, private_root = Path(root), Path(private_root)
    policy, digest = load_policy(root)
    transition = load_transition(root)
    if transition is None:
        raise ValueError('Profile continuations require the currently selected 1.2 adoption')
    by_model = {}
    for path in paths:
        raw = Path(path).read_bytes()
        mid = json.loads(raw)['model_id']
        if mid in by_model:
            raise ValueError('Duplicate profile continuation review for ' + mid)
        by_model[mid] = raw
    if set(by_model) != set(transition['adoptions']):
        raise ValueError('Profile continuation import must cover exactly the current adoption cohort')
    freeze_raw = None if freeze_path is None else Path(freeze_path).read_bytes()
    freeze = None if freeze_raw is None else json.loads(freeze_raw)
    transition_raw, base_index_raw = read_bytes(root / TRANSITION_PATH), read_bytes(root / BASE_INDEX_PATH)
    if freeze is not None and (freeze['policy']['sha256'] != digest
            or freeze['source_transition']['sha256'] != hashlib.sha256(transition_raw).hexdigest()
            or set(freeze['models']) != set(by_model)):
        raise ValueError('Profile continuation review freeze no longer matches its source selection')
    prepared_public, prepared_private, public_models, private_models = {}, {}, {}, {}
    lock_raw = None if review_lock_path is None else Path(review_lock_path).read_bytes()
    if lock_raw is not None:
        lock = json.loads(lock_raw)
        if (set(lock['model_reviews']) != set(by_model)
                or lock['review_freeze']['sha256'] != hashlib.sha256(freeze_raw).hexdigest()
                or any(ref['sha256'] != hashlib.sha256(by_model[mid]).hexdigest()
                       or ref['bytes'] != len(by_model[mid]) for mid,ref in lock['model_reviews'].items())):
            raise ValueError('Root review lock differs from its frozen final review bytes')
        for ref in [*lock['source_manifests'].values(),*[r['review'] for r in lock['task_sources']]]:
            value = Path(ref['path']).read_bytes()
            if ref['bytes'] != len(value) or ref['sha256'] != hashlib.sha256(value).hexdigest():
                raise ValueError('Root review lock lost its original reviewer selection')
        prepared_private[DIRECTORY+'/review-lock.json'] = lock_raw
        source_folder = Path(review_lock_path).parent/'reviews'
        for group in ('root','tx_a','tx_b_ar'):
            for path in sorted((source_folder/group).rglob('*.json')):
                prepared_private[DIRECTORY+'/source-reviews/'+group+'/'+path.relative_to(source_folder/group).as_posix()] = path.read_bytes()
    reviewed_tasks = 0
    # Validate the complete source-bound cohort before writing either repository.
    for mid in transition['adoptions']:
        review_raw = by_model[mid]
        materials_raw = _frozen_materials(freeze, Path(materials_root), mid)
        score, public = derive(root, private_root, review_raw, materials_raw,
                               policy=policy, policy_sha256=digest)
        folder = DIRECTORY + '/' + mid + '/'
        private_models[mid] = {}
        for name, raw in (('review.json', review_raw), ('source-bindings.json', materials_raw),
                          ('score.json', encoded(score))):
            prepared_private[folder+name] = raw
            private_models[mid][name.removesuffix('.json')] = reference(folder+name, raw)
        path, raw = folder + 'profile.json', encoded(public)
        prepared_public[path] = raw
        public_models[mid] = reference(path, raw)
        private_models[mid]['public_projection'] = reference(path, raw)
        reviewed_tasks += score['revision_coverage']['reviewed_tasks']
    common = dict(version=VERSION, benchmark_version=EDITION, condition=CONDITION,
        policy_sha256=digest, source_transition=reference(TRANSITION_PATH, transition_raw),
        base_index=reference(BASE_INDEX_PATH, base_index_raw), reviewer_kind='ai', human_review='pending',
        new_candidate_calls=0, main_scores_modified=False, post_observation=True)
    from math_gauge.mathematical_profile_corrections import INDEX_PATH as CORRECTION_INDEX
    if (root / CORRECTION_INDEX).is_file():
        common['baseline_corrections'] = reference(CORRECTION_INDEX, read_bytes(root / CORRECTION_INDEX))
    if freeze_raw is not None:
        freeze_rel = DIRECTORY + '/review-freeze.json'
        prepared_private[freeze_rel] = freeze_raw
        common['review_freeze_sha256'] = hashlib.sha256(freeze_raw).hexdigest()
    if lock_raw is not None:
        common['private_review_lock_sha256'] = hashlib.sha256(lock_raw).hexdigest()
    prepared_public[INDEX_PATH] = encoded(dict(common,
        schema='math-gauge.mathematical-profile-revision-index/v1', models=public_models))
    prepared_private[INDEX_PATH] = encoded(dict(common,
        schema='math-gauge.private-mathematical-profile-revision-index/v1', models=private_models))
    for base, files in ((private_root, prepared_private), (root, prepared_public)):
        for path, raw in files.items():
            target = base / path
            if target.exists() and target.read_bytes() != raw:
                raise ValueError('Refusing to replace a retained continuation profile artifact: ' + path)
    for base, files in ((private_root, prepared_private), (root, prepared_public)):
        for path, raw in files.items():
            target = base / path
            target.parent.mkdir(parents=True, exist_ok=True)
            if not target.exists():
                target.write_bytes(raw)
    return dict(status='passed', models=len(public_models), reviewed_task_slots=reviewed_tasks,
                component_version=VERSION, benchmark_version=EDITION,
                new_candidate_calls=0, main_scores_modified=False)


def check(root, private_root):
    root, private_root = Path(root), Path(private_root)
    policy, digest = load_policy(root)
    transition = load_transition(root)
    public_index = json.loads(read_bytes(root / INDEX_PATH))
    private_index = json.loads(read_bytes(private_root / INDEX_PATH))
    if (set(public_index['models']) != set(transition['adoptions'])
            or set(private_index['models']) != set(public_index['models'])
            or public_index['policy_sha256'] != digest or private_index['policy_sha256'] != digest):
        raise ValueError('Continuation profile indices differ from the current source-bound cohort')
    reviewed = 0
    for mid, ref in public_index['models'].items():
        private = private_index['models'][mid]
        review_raw = source_bytes(private_root, private['review'])
        materials_raw = source_bytes(private_root, private['source-bindings'])
        score, public = derive(root, private_root, review_raw, materials_raw,
                               policy=policy, policy_sha256=digest)
        if (score != json.loads(source_bytes(private_root, private['score']))
                or encoded(public) != source_bytes(root, ref)
                or private['public_projection'] != ref):
            raise ValueError('Continuation profile no longer reproduces from retained source reviews')
        reviewed += score['revision_coverage']['reviewed_tasks']
    profiles = load_public_profiles(root, [{'id':mid} for mid in transition['adoptions']], transition=transition)
    relocations = private_root/DIRECTORY/'source-relocations.json'
    if relocations.is_file():
        relocated = json.loads(relocations.read_bytes())
        if relocated['source_lock_sha256'] != public_index['private_review_lock_sha256']:
            raise ValueError('Portable reviewer inventory does not bind the accepted source lock')
        for row in relocated['sources']:
            source_bytes(private_root,row['retained'])
    return dict(status='passed', models=len(profiles['models']), reviewed_task_slots=reviewed,
                component_version=VERSION, benchmark_version=EDITION,
                new_candidate_calls=0, main_scores_modified=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--private-root', required=True, type=Path)
    parser.add_argument('--review-dir', action='append', default=[], type=Path)
    parser.add_argument('--materials-root', type=Path)
    parser.add_argument('--freeze', type=Path)
    parser.add_argument('--review-lock', type=Path)
    parser.add_argument('--baseline-adoption', type=Path)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    if args.check:
        result = check(ROOT, args.private_root)
    else:
        if args.materials_root is None or not args.review_dir:
            parser.error('Import requires --materials-root and at least one --review-dir')
        paths = [path for folder in args.review_dir for path in sorted(folder.glob('*.json'))]
        if args.baseline_adoption is not None:
            import_corrections(ROOT, args.private_root, args.baseline_adoption)
        result = import_reviews(ROOT, args.private_root, paths, args.materials_root,
                                freeze_path=args.freeze, review_lock_path=args.review_lock)
        if args.review_lock is not None:
            retain_source_relocations(args.private_root,args.review_lock,args.freeze,args.baseline_adoption)
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
