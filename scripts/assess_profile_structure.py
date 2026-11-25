#!/usr/bin/env python3
"""Prepare, adopt and replay independent two-axis profile evidence; no candidate calls."""
import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from math_gauge import profile_structure as owner
from math_gauge.evidence_retention import read_bytes
from math_gauge.scoring import score_profile_structure
from scripts.results_publication import atomic_write


def derive(root, private_root, review_raw, materials_raw):
    policy, policy_hash = owner.load_policy(root)
    contracts = owner.load_contracts(root, private_root, policy)
    review, material = json.loads(review_raw), json.loads(materials_raw)
    owner._need(review.get('materials_sha256') == owner.digest(materials_raw),
                'Structural review does not bind the exact retained material bytes')
    inputs = owner.ProfileStructureInputs(review, material, public_root=root, private_root=private_root,
                                          policy=policy, policy_sha256=policy_hash, contracts=contracts)
    score = score_profile_structure(inputs)
    report = owner.validate_public(owner.project_public(score, policy_hash=policy_hash,
        private_review_sha256=owner.digest(review_raw), private_materials_sha256=owner.digest(materials_raw)),
        policy, policy_hash)
    return score, report


def prepare(root, private_root, reviews, materials_root):
    root, private_root = Path(root), Path(private_root)
    policy, policy_hash = owner.load_policy(root)
    contracts = owner.load_contracts(root, private_root, policy)
    submitted = {}
    for filename in reviews:
        raw = read_bytes(filename)
        review = json.loads(raw)
        mid = review['model_id']
        owner._need(mid not in submitted, 'Duplicate structural profile model review')
        submitted[mid] = raw
    owner._need(set(submitted) == set(contracts['cohort']), 'Structural adoption must retain the complete selected cohort')
    public_files, private_files, public_models, private_models = {}, {}, {}, {}
    for mid in contracts['cohort']:
        material_raw = read_bytes(Path(materials_root) / (mid + '.json'))
        review_raw = submitted[mid]
        score, report = derive(root, private_root, review_raw, material_raw)
        values = dict(review=review_raw, **{'source-bindings': material_raw},
                      score=owner.encoded(score), profile=owner.encoded(report))
        private_models[mid] = {}
        for key, raw in values.items():
            name = f'{owner.DIRECTORY}/{mid}/{key}.json'
            private_files[name] = raw
            private_models[mid][key] = dict(path=name, bytes=len(raw), sha256=owner.digest(raw))
            if key == 'profile':
                public_files[name] = raw
                public_models[mid] = dict(private_models[mid][key])
    common = dict(version=owner.VERSION, edition=owner.EDITION, condition=owner.CONDITION,
                  cohort=contracts['cohort'], policy_sha256=policy_hash, **owner.BOUNDARIES)
    public_files[owner.INDEX_PATH] = owner.encoded(dict(
        schema='math-gauge.profile-structure-index/v1', models=public_models, **common))
    private_files[owner.INDEX_PATH] = owner.encoded(dict(
        schema='math-gauge.private-profile-structure-index/v1', models=private_models, **common))
    return public_files, private_files


def install(root, private_root, reviews, materials_root):
    public_files, private_files = prepare(root, private_root, reviews, materials_root)
    destinations = ((Path(private_root), private_files), (Path(root), public_files))
    for destination, files in destinations:
        index = destination / owner.INDEX_PATH
        owner._need(not index.is_file() or read_bytes(index) == files[owner.INDEX_PATH],
                    'A settled structural profile change needs its separately named amendment')
    for destination, files in destinations:
        for name, raw in files.items():
            if name != owner.INDEX_PATH:
                target = destination / name
                owner._need(not target.is_file() or read_bytes(target) == raw,
                            'A structural profile artifact cannot overwrite different retained evidence')
                atomic_write(target, raw)
        atomic_write(destination / owner.INDEX_PATH, files[owner.INDEX_PATH])
    return len(public_files) - 1


def check(root, private_root):
    root, private_root = Path(root), Path(private_root)
    index = json.loads(read_bytes(private_root / owner.INDEX_PATH))
    policy, policy_hash = owner.load_policy(root)
    contracts = owner.load_contracts(root, private_root, policy)
    owner._need(index.get('schema') == 'math-gauge.private-profile-structure-index/v1'
                and index.get('version') == owner.VERSION and index.get('edition') == owner.EDITION
                and index.get('condition') == owner.CONDITION and index.get('policy_sha256') == policy_hash
                and index.get('cohort') == contracts['cohort'] and owner._boundary(index)
                and set(index.get('models', {})) == set(contracts['cohort']),
                'Private structural index changed its complete cohort or policy identity')
    for mid, refs in index['models'].items():
        review_raw = owner.source_bytes(private_root, refs['review'])
        material_raw = owner.source_bytes(private_root, refs['source-bindings'])
        score, report = derive(root, private_root, review_raw, material_raw)
        owner._need(owner.source_bytes(private_root, refs['score']) == owner.encoded(score)
                    and owner.source_bytes(private_root, refs['profile']) == owner.encoded(report),
                    'Installed structural profile does not replay its selected source judgments')
        public_path = root / owner.DIRECTORY / mid / 'profile.json'
        owner._need(read_bytes(public_path) == owner.encoded(report), 'Public structural aggregate differs from private replay')
    owner.load_public(root, benchmark_version=owner.EDITION)
    return len(index['models'])


def _retained_reference(root, private_root, path):
    filename = Path(path).resolve()
    matches = [(name, Path(directory).resolve()) for name, directory in
               (('public', root), ('private', private_root)) if filename.is_relative_to(Path(directory).resolve())]
    owner._need(len(matches) == 1, 'A profile source supplement must already be retained in one source repository')
    repository, directory = matches[0]
    raw = read_bytes(filename)
    return dict(repository=repository, path=filename.relative_to(directory).as_posix(),
                bytes=len(raw), sha256=owner.digest(raw))


def prepare_review_inputs(root, private_root, packet_index, output, intake_corrections=(), verification_supplements=(),
                          independent_additions=(), independent_verifications=()):
    output = Path(output).resolve()
    owner._need(not any(output.is_relative_to(Path(p).resolve()) for p in (root, private_root)),
                'Prepare reviewer materials outside both source repositories')
    policy, policy_hash = owner.load_policy(root)
    contracts = owner.load_contracts(root, private_root, policy)
    materials = owner.prepare_materials(root, private_root, packet_index, policy, policy_hash, contracts)
    refs = []
    for correction_path in intake_corrections:
        filename = Path(correction_path).resolve()
        matches = [(name, Path(directory).resolve()) for name, directory in
                   (('public', root), ('private', private_root)) if filename.is_relative_to(Path(directory).resolve())]
        owner._need(len(matches) == 1, 'Named source intake must already be retained in one source repository')
        repository, directory = matches[0]
        raw = read_bytes(filename)
        refs.append(dict(repository=repository, path=filename.relative_to(directory).as_posix(),
                         bytes=len(raw), sha256=owner.digest(raw)))
    if refs:
        materials = owner.apply_intake_corrections(materials, refs, public_root=root, private_root=private_root,
            policy=policy, policy_hash=policy_hash, contracts=contracts)
    for supplement_path in verification_supplements:
        filename = Path(supplement_path).resolve()
        matches = [(name, Path(directory).resolve()) for name, directory in
                   (('public', root), ('private', private_root)) if filename.is_relative_to(Path(directory).resolve())]
        owner._need(len(matches) == 1, 'Verification supplement must already be retained in one source repository')
        repository, directory = matches[0]
        raw = read_bytes(filename)
        ref = dict(repository=repository, path=filename.relative_to(directory).as_posix(), bytes=len(raw), sha256=owner.digest(raw))
        materials = owner.apply_verification_supplements(materials, ref, public_root=root, private_root=private_root,
            policy=policy, policy_hash=policy_hash, contracts=contracts)
    if independent_additions or independent_verifications:
        materials = owner.apply_independent_supplements(materials,
            addition_refs=[_retained_reference(root, private_root, p) for p in independent_additions],
            verification_refs=[_retained_reference(root, private_root, p) for p in independent_verifications],
            public_root=root, private_root=private_root, policy=policy, policy_hash=policy_hash, contracts=contracts)
    roots = dict(public=Path(root), private=Path(private_root))
    output.mkdir(parents=True, exist_ok=True)
    for mid, material in materials.items():
        owner.validate_materials(material, policy, policy_hash, contracts, roots)
        raw = owner.encoded(material)
        owner._need(b'/private/tmp/' not in raw, 'Temporary reviewer paths cannot enter adopted source materials')
        filename = output / (mid + '.json')
        owner._need(not filename.exists() or read_bytes(filename) == raw, 'Prepared source snapshot changed')
        if not filename.exists():
            filename.write_bytes(raw)
    return len(materials)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--private-root', type=Path, required=True)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument('--prepare', type=Path)
    action.add_argument('--apply', action='store_true')
    action.add_argument('--check', action='store_true')
    parser.add_argument('--packet-index', type=Path)
    parser.add_argument('--reviews', type=Path)
    parser.add_argument('--intake-correction', type=Path, action='append', default=[])
    parser.add_argument('--verification-supplement', type=Path, action='append', default=[])
    parser.add_argument('--independent-addition', type=Path, action='append', default=[])
    parser.add_argument('--independent-verification', type=Path, action='append', default=[])
    parser.add_argument('--materials-root', type=Path)
    args = parser.parse_args()
    if args.prepare:
        if args.packet_index is None:
            parser.error('--prepare requires --packet-index')
        count = prepare_review_inputs(args.root, args.private_root, args.packet_index, args.prepare,
            args.intake_correction, args.verification_supplement, args.independent_addition, args.independent_verification)
        status = 'prepared'
    elif args.check:
        count = check(args.root, args.private_root)
        status = 'verified'
    else:
        if args.reviews is None or args.materials_root is None:
            parser.error('--apply requires --reviews and --materials-root')
        count = install(args.root, args.private_root, sorted(args.reviews.glob('*.json')), args.materials_root)
        status = 'adopted'
    print(json.dumps(dict(status=status, models=count, candidate_calls=0, main_scores_modified=False,
                         committed=False, pushed=False)))


if __name__ == '__main__':
    main()
