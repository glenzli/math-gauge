#!/usr/bin/env python3
"""Prepare, adopt or replay source-bound initiative reviews; never call a candidate."""
import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from math_gauge import research_initiative as owner
from math_gauge.evidence_retention import read_bytes
from scripts.results_publication import atomic_write


def prepare(root, private_root, reviews):
    root, private_root = Path(root), Path(private_root)
    roots = {'public': root, 'private': private_root}
    policy, policy_hash = owner.load_policy(root)
    contracts = owner.load_contracts(root, private_root, policy)
    materials = owner.prepare_materials(root, private_root, policy, policy_hash, contracts)
    submitted = {}
    for path in reviews:
        raw = read_bytes(path)
        review = json.loads(raw)
        mid = review['model_id']
        owner._need(mid not in submitted, 'Duplicate initiative model review')
        submitted[mid] = review
    owner._need(set(submitted) == set(contracts['cohort']),
                'Initiative adoption must cover the complete retained model cohort')
    public_files, private_files, public_models, private_models = {}, {}, {}, {}
    for mid in contracts['cohort']:
        review, material = submitted[mid], materials[mid]
        owner.validate_review(review, material, policy, policy_hash, roots)
        score = owner.score_review(review)
        report = owner.validate_public(owner.public_projection(review, material, policy_hash), policy, policy_hash)
        files = {'review': owner.encoded(review), 'source-bindings': owner.encoded(material),
                 'score': owner.encoded(score), 'profile': owner.encoded(report)}
        private_models[mid] = {}
        for key, raw in files.items():
            name = f'{owner.DIRECTORY}/{mid}/{key}.json'
            private_files[name] = raw
            private_models[mid][key] = dict(path=name, bytes=len(raw), sha256=owner.digest(raw))
            if key == 'profile':
                public_files[name] = raw
                public_models[mid] = dict(private_models[mid][key])
    common = dict(version=owner.VERSION, edition=owner.EDITION, condition=owner.CONDITION,
                  policy_sha256=policy_hash, **owner.BOUNDARIES)
    public_files[owner.INDEX_PATH] = owner.encoded(dict(
        schema='math-gauge.research-initiative-index/v1', models=public_models, **common))
    private_files[owner.INDEX_PATH] = owner.encoded(dict(
        schema='math-gauge.private-research-initiative-index/v1', models=private_models, **common))
    return public_files, private_files


def install(root, private_root, reviews):
    public_files, private_files = prepare(root, private_root, reviews)
    destinations = ((Path(private_root), private_files), (Path(root), public_files))
    for destination, files in destinations:
        index = destination / owner.INDEX_PATH
        if index.is_file():
            owner._need(read_bytes(index) == files[owner.INDEX_PATH],
                        'Changing a settled initiative review needs a separately named amendment')
    for destination, files in destinations:
        index = destination / owner.INDEX_PATH
        for name, raw in files.items():
            if name != owner.INDEX_PATH:
                atomic_write(destination / name, raw)
        atomic_write(index, files[owner.INDEX_PATH])
    return len(public_files) - 1


def check(root, private_root):
    private_root = Path(private_root)
    index = json.loads(read_bytes(private_root / owner.INDEX_PATH))
    reviews = [private_root / row['review']['path'] for row in index['models'].values()]
    public_files, private_files = prepare(root, private_root, reviews)
    for destination, files in ((Path(root), public_files), (private_root, private_files)):
        for name, raw in files.items():
            owner._need(read_bytes(destination / name) == raw,
                        'Installed initiative evidence or aggregate differs from its selected original source: ' + name)
    owner.load_public(root, benchmark_version=owner.EDITION)
    return len(index['models'])


def prepare_review_inputs(root, private_root, output):
    output = Path(output).resolve()
    owner._need(not any(output.is_relative_to(Path(p).resolve()) for p in (root, private_root)),
                'Keep reviewer preparation outside both source repositories')
    policy, policy_hash = owner.load_policy(root)
    contracts = owner.load_contracts(root, private_root, policy)
    materials = owner.prepare_materials(root, private_root, policy, policy_hash, contracts)
    output.mkdir(parents=True, exist_ok=True)
    for mid, value in materials.items():
        path = output / (mid + '.json')
        raw = owner.encoded(value)
        owner._need(not path.exists() or path.read_bytes() == raw, 'Reviewer preparation changed an existing snapshot')
        if not path.exists():
            path.write_bytes(raw)
    return len(materials)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--private-root', type=Path, required=True)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument('--prepare', type=Path)
    action.add_argument('--apply', action='store_true')
    action.add_argument('--check', action='store_true')
    parser.add_argument('--reviews', type=Path)
    args = parser.parse_args()
    if args.prepare:
        count = prepare_review_inputs(args.root, args.private_root, args.prepare)
        status = 'prepared'
    elif args.check:
        count = check(args.root, args.private_root)
        status = 'verified'
    else:
        if args.reviews is None:
            parser.error('--apply requires --reviews')
        count = install(args.root, args.private_root, sorted(args.reviews.glob('*.json')))
        status = 'adopted'
    print(json.dumps(dict(status=status, models=count, candidate_calls=0,
                         main_scores_modified=False, committed=False, pushed=False)))


if __name__ == '__main__':
    main()
