#!/usr/bin/env python3
"""Import or verify independent trait reviews. Never call candidate models."""
import argparse
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from math_gauge.current_results import selected_current_record_paths
from math_gauge.evidence_retention import read_bytes
from math_gauge.mathematical_profile import (
    VERSION, VERSIONS, EDITION, ProfileInputs, load_policy, source_bytes,
    project_public, load_public_profiles, index_path,
)
from math_gauge.scoring import score_mathematical_profile


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode()


def reference(path, raw):
    return dict(path=path, bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())


def compact_materials(packet):
    value = {k:deepcopy(packet[k]) for k in ('schema', 'benchmark_version', 'version', 'model_id',
        'condition', 'policy_sha256', 'private_contract_sha256', 'sources', 'new_candidate_calls')}
    value['tasks'] = [{k:deepcopy(task[k]) for k in ('id','content_index','goal_index','selected_state',
                                                   'response_sha256','raw_answer')}
                      for task in packet['tasks']]
    return value


def validate_selection(root, model, materials):
    from math_gauge.editions import load_assessment_transition
    selected = selected_current_record_paths(root)
    source = materials['sources']['public_source_record']
    if selected.get(model) != source['path']:
        raise ValueError('Profile materials use an unselected record')
    source_bytes(root, source)
    from math_gauge.current_assessment_admissions import selections
    initial = selections(root).get(model)
    calibration = materials['sources']['initial_assessment' if initial else 'calibration']
    expected = initial or load_assessment_transition(root)['calibrations'][model]
    if calibration['path'] != expected['path'] or calibration['sha256'] != expected['sha256']:
        raise ValueError('Profile materials use a different selected assessment')
    source_bytes(root, calibration)


def derive(root, private_root, review_raw, materials, policy, policy_sha, contracts):
    review = json.loads(review_raw)
    validate_selection(root, review['model_id'], materials)
    inputs = ProfileInputs(review, policy, contracts, materials,
        roots={'public':root, 'private':private_root}, policy_sha256=policy_sha)
    score = score_mathematical_profile(inputs)
    materials_raw = encoded(materials)
    public = project_public(score, policy=policy, policy_sha256=policy_sha,
        private_review_sha256=hashlib.sha256(review_raw).hexdigest(),
        private_materials_sha256=hashlib.sha256(materials_raw).hexdigest(),
        source_record=materials['sources']['public_source_record'],
        source_calibration=materials['sources'].get('calibration'),
        source_initial_assessment=materials['sources'].get('initial_assessment'))
    return score, public, materials_raw


def import_reviews(root, private_root, paths, materials_root, *, component_version=None):
    policy, policy_sha = load_policy(root, version=component_version)
    version = policy['version']
    contract_path = private_root / ('protocol/mathematical-profile/v' + version + '/contracts.json')
    contract_raw = read_bytes(contract_path)
    if hashlib.sha256(contract_raw).hexdigest() != policy['private_contract_sha256']:
        raise ValueError('Private profile contracts changed')
    contracts = json.loads(contract_raw)
    selected = selected_current_record_paths(root)
    by_model = {}
    for path in paths:
        raw = path.read_bytes()
        mid = json.loads(raw)['model_id']
        if mid in by_model:
            raise ValueError('Duplicate profile review for ' + mid)
        by_model[mid] = raw
    if set(by_model) != set(selected):
        raise ValueError('Initial profile import must review exactly the settled leaderboard cohort')
    prepared_public, prepared_private, public_models, private_models = {}, {}, {}, {}
    # Validate the whole cohort before writing either repository.
    for mid, review_raw in by_model.items():
        materials = compact_materials(json.loads((materials_root / mid / 'packet.json').read_bytes()))
        score, public, material_raw = derive(root, private_root, review_raw, materials,
                                           policy, policy_sha, contracts)
        folder = 'results/mathematical-profiles/v' + version + '/' + mid + '/'
        files = {'review.json':review_raw, 'source-bindings.json':material_raw, 'score.json':encoded(score)}
        private_models[mid] = {}
        for name, raw in files.items():
            prepared_private[folder+name] = raw
            private_models[mid][name.removesuffix('.json')] = reference(folder+name, raw)
        path, raw = folder+'profile.json', encoded(public)
        prepared_public[path] = raw
        public_models[mid] = reference(path, raw)
        private_models[mid]['public_projection'] = reference(path, raw)
    common = dict(version=version, benchmark_version=EDITION, policy_sha256=policy_sha,
                  new_candidate_calls=0, main_scores_modified=False,
                  reviewer_kind='ai', human_review='pending')
    path = index_path(version)
    prepared_public[path] = encoded(dict(common,
        schema='math-gauge.mathematical-profile-index/v1', models=public_models))
    prepared_private[path] = encoded(dict(common,
        schema='math-gauge.private-mathematical-profile-index/v1', models=private_models,
        contracts=reference(contract_path.relative_to(private_root).as_posix(), contract_raw)))
    for base, files in ((private_root, prepared_private), (root, prepared_public)):
        for path, raw in files.items():
            target = base / path
            if target.exists() and target.read_bytes() != raw:
                raise ValueError('Refusing to replace a retained profile artifact: ' + path)
    for base, files in ((private_root, prepared_private), (root, prepared_public)):
        for path, raw in files.items():
            target = base / path
            target.parent.mkdir(parents=True, exist_ok=True)
            if not target.exists():
                target.write_bytes(raw)
    return check(root, private_root, component_version=version)


def check(root, private_root, *, component_version=None):
    policy, digest = load_policy(root, version=component_version)
    version = policy['version']
    path = index_path(version)
    public_index = json.loads(read_bytes(root / path))
    private_index = json.loads(read_bytes(private_root / path))
    selected = selected_current_record_paths(root)
    if (public_index.get('version') != version or private_index.get('version') != version
            or public_index.get('policy_sha256') != digest or private_index.get('policy_sha256') != digest
            or set(public_index['models']) != set(private_index['models'])
            or (version == VERSION and set(public_index['models']) != set(selected))):
        raise ValueError('Profile index versions, policies or selected model cohort differ')
    contracts = json.loads(source_bytes(private_root, private_index['contracts']))
    reviewed = 0
    for mid, ref in public_index['models'].items():
        private = private_index['models'][mid]
        review_raw = source_bytes(private_root, private['review'])
        materials_raw = source_bytes(private_root, private['source-bindings'])
        materials = json.loads(materials_raw)
        score, public, rebuilt_materials = derive(root, private_root, review_raw, materials,
                                                 policy, digest, contracts)
        if rebuilt_materials != materials_raw:
            raise ValueError('Profile source bindings changed during reconstruction')
        if encoded(score) != source_bytes(private_root, private['score']):
            raise ValueError('Private profile arithmetic does not reproduce')
        actual = source_bytes(root, ref)
        if encoded(public) != actual or private['public_projection'] != ref:
            raise ValueError('Public profile is not the exact private projection')
        reviewed += len(json.loads(review_raw)['tasks'])
    models = [{'id':mid} for mid in selected]
    profile = load_public_profiles(root, models, benchmark_version=EDITION, component_version=version)
    if load_public_profiles(root, models, benchmark_version='1.0.0') is not None:
        raise ValueError('Historical edition cannot inherit the new profiles')
    return dict(status='passed', benchmark_version=EDITION, component_version=version,
        models=len(profile['models']), reviewed_models=len(public_index['models']),
        reviewed_task_slots=reviewed, planned_families=policy['planned_families'],
        new_candidate_calls=0, main_scores_modified=False, edition1_0_profile=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--private-root', type=Path, required=True)
    parser.add_argument('--review-dir', type=Path, action='append', default=[])
    parser.add_argument('--materials-root', type=Path)
    parser.add_argument('--component-version', choices=VERSIONS)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    if args.check:
        result = check(ROOT, args.private_root, component_version=args.component_version)
    else:
        if not args.review_dir or args.materials_root is None:
            parser.error('Import requires review directories and an explicit materials root')
        paths = [p for folder in args.review_dir for p in sorted(folder.glob('*.json'))]
        result = import_reviews(ROOT, args.private_root, paths, args.materials_root,
                                component_version=args.component_version)
    print(json.dumps(result, ensure_ascii=False))


if __name__ == '__main__':
    main()
