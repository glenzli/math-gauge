#!/usr/bin/env python3
"""Reproduce legacy taste source bindings and check or prepare the public profile input."""
import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from math_gauge import legacy_taste as taste
from math_gauge.open_research import encoded
from scripts.results_publication import atomic_write


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--private-root', type=Path)
    parser.add_argument('--scope', type=Path)
    parser.add_argument('--catalog', type=Path, help='Exact private source catalogue from reviewer intake')
    parser.add_argument('--review', type=Path, action='append', default=[])
    output = parser.add_mutually_exclusive_group()
    output.add_argument('--out', type=Path, help='Create the explicit public projection file')
    output.add_argument('--apply', action='store_true', help='Install a complete reviewed projection locally')
    output.add_argument('--check', type=Path, help='Compare against an existing public projection')
    output.add_argument('--catalog-out', type=Path, help='Create an evaluator-only source catalogue')
    args = parser.parse_args()
    if (args.out or args.apply or args.check) and not args.review:
        parser.error('A public projection needs at least one independent --review')
    if args.catalog_out and args.review:
        parser.error('Catalogue preparation does not need --review')
    root = args.root.resolve()
    if args.catalog_out and args.catalog_out.resolve().is_relative_to(root):
        parser.error('The evaluator-only source catalogue must stay outside the public repository')
    private = (args.private_root or root.parent / 'math-gauge-private').resolve()
    scope = args.scope or private / taste.SCOPE_PATH
    baseline_raw = (root / 'site/data.json').read_bytes()
    policy, policy_sha = taste.load_policy(root / taste.POLICY_PATH)
    catalog = taste.build_source_catalog(root, private, scope.read_bytes(), policy, baseline_raw)
    catalog_raw = encoded(catalog)
    if args.catalog and args.catalog.read_bytes() != catalog_raw:
        raise ValueError('Legacy taste review catalogue does not reproduce from retained sources')
    if args.catalog_out:
        with args.catalog_out.open('xb') as out:
            out.write(catalog_raw)
    receipt = dict(status='passed', **catalog['counts'], source_catalog_sha256=taste.sha256(catalog_raw),
                   new_candidate_calls=0)
    if args.review:
        reviews = [file.read_bytes() for file in args.review]
        report = taste.prepare_public(dict(public=root, private=private), catalog_raw, reviews, policy, policy_sha)
        taste.validate_public(report, policy_sha, json.loads(baseline_raw), taste.sha256(baseline_raw))
        raw = encoded(report)
        receipt['judgments'] = sum(len(json.loads(review)['judgments']) for review in reviews)
        destination = root / taste.PUBLIC_PATH if args.apply else args.out
        if args.apply:
            delivered = sum(item['status'] == 'normal_final' for model in catalog['models'].values()
                for stage in ('first', 'revision') for item in (model[stage] or {}).values())
            if delivered != receipt['judgments']:
                raise ValueError('Adoption needs an independent assessment of every normal delivery')
        if destination:
            if destination.exists() and destination.read_bytes() != raw:
                raise ValueError('Refusing to overwrite a different legacy taste projection')
            atomic_write(destination, raw)
        if args.check and args.check.read_bytes() != raw:
            raise ValueError('Public legacy taste projection changed or has private fields')
        receipt['projection_sha256'] = taste.sha256(raw)
    print(json.dumps(receipt, ensure_ascii=False))


if __name__ == '__main__':
    main()
