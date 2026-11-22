#!/usr/bin/env python3
"""Adopt independently reviewed strict taste amendments without changing original reviews."""
import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from math_gauge import legacy_taste as legacy
from math_gauge import legacy_taste_strict as strict
from math_gauge.open_research import encoded
from scripts.results_publication import atomic_write


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--private-root', type=Path)
    parser.add_argument('--catalog', type=Path, required=True)
    parser.add_argument('--review', type=Path, action='append', required=True)
    parser.add_argument('--previous-review', type=Path, action='append', required=True)
    output = parser.add_mutually_exclusive_group()
    output.add_argument('--out', type=Path)
    output.add_argument('--apply', action='store_true')
    output.add_argument('--check', type=Path)
    args = parser.parse_args()
    root = args.root.resolve()
    private = (args.private_root or root.parent / 'math-gauge-private').resolve()
    baseline = (root / 'site/data.json').read_bytes()
    base_policy, base_sha = legacy.load_policy(root / legacy.POLICY_PATH)
    policy, policy_sha = strict.load_policy(root / strict.POLICY_PATH)
    scope = private / legacy.SCOPE_PATH
    catalog = encoded(legacy.build_source_catalog(root, private, scope.read_bytes(), base_policy, baseline))
    if args.catalog.read_bytes() != catalog:
        raise ValueError('Strict taste source catalog differs from actual retained answers')
    old = [file.read_bytes() for file in args.previous_review]
    previous_public = json.loads((root / legacy.PUBLIC_PATH).read_bytes())
    legacy.validate_public(previous_public, base_sha, json.loads(baseline), legacy.sha256(baseline))
    if previous_public['review_sha256'] != [legacy.sha256(raw) for raw in old]:
        raise ValueError('Strict amendments require the actual previously adopted review groups')
    reviews = [file.read_bytes() for file in args.review]
    report = strict.prepare_public(dict(public=root, private=private), catalog, reviews, old,
                                   policy, policy_sha, base_policy, base_sha)
    strict.validate_public(report, policy_sha, json.loads(baseline), legacy.sha256(baseline), policy=policy)
    raw = encoded(report)
    destination = root / strict.PUBLIC_PATH if args.apply else args.out
    if destination:
        if destination.exists() and destination.read_bytes() != raw:
            raise ValueError('Refusing to overwrite a different strict taste adoption')
        atomic_write(destination, raw)
    if args.check and args.check.read_bytes() != raw:
        raise ValueError('Strict taste adoption does not reproduce from its original sources')
    print(json.dumps(dict(status='passed', **report['review_coverage'],
        projection_sha256=legacy.sha256(raw), new_candidate_calls=0)))


if __name__ == '__main__':
    main()
