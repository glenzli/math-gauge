#!/usr/bin/env python3
"""Check or locally adopt a separate native research supplement; never call models."""
import argparse
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from math_gauge import independent_research_native as native
from math_gauge import taste_v130 as flow
from scripts.adopt_independent_research_batch import current_index, write_projection
from scripts.adopt_independent_research_external import adoption_lock


def validate_current(root, proposal):
    raw = current_index(root / 'site/data.json')
    if raw is None:
        raise ValueError('The retained baseline is missing')
    baseline = native.value._json(raw)
    if baseline.get('benchmark_version') != '1.2.0':
        raise ValueError('Native admission requires the retained 1.2 baseline')
    native.validate_public(proposal, policies=native.external.policy_bindings(root),
        baseline_hash=native.digest(raw), model_ids=[m['id'] for m in baseline['models']])


def apply_index(root, proposal, expected):
    with adoption_lock(root) as root:
        target = flow._contained(root, native.PUBLIC_PATH.as_posix())
        current = current_index(target)
        if current != expected:
            raise ValueError('Native aggregate changed during source verification')
        validate_current(root, proposal)
        if current is not None:
            prior = native.validate_public(native.value._json(current))
            if any(proposal['models'].get(k) != v for k, v in prior['models'].items()):
                raise ValueError('A settled native judgment needs a separate source-bound correction')
        raw = native.encoded(proposal)
        if raw != current:
            write_projection(target, raw, replace=current is not None)


def check_index(root, proposal):
    with adoption_lock(root) as root:
        validate_current(root, proposal)
        if current_index(root / native.PUBLIC_PATH) != native.encoded(proposal):
            raise ValueError('Installed native aggregate differs from its selected original evidence')


def protect_output(output, root, selection):
    document = native.value._json(selection.read_bytes())
    sources = [root, selection]
    for key in ('registration', 'review_policy'):
        sources.append(flow._safe_absolute(document[key]['path']).parent)
    for row in document['models']:
        sources.extend(flow._safe_absolute(v['path']).parent for v in row.values() if isinstance(v, dict))
    if any(output == source or output.is_relative_to(source) for source in sources):
        raise ValueError('Keep the aggregate proposal outside all source trees')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--selection', type=Path, required=True)
    parser.add_argument('--public-root', type=Path, default=ROOT)
    parser.add_argument('--out', type=Path, required=True)
    action = parser.add_mutually_exclusive_group()
    action.add_argument('--apply', action='store_true')
    action.add_argument('--check', action='store_true')
    args = parser.parse_args()
    root, selection, output = map(flow._safe_absolute, (args.public_root, args.selection, args.out))
    protect_output(output, root, selection)
    previous = current_index(root / native.PUBLIC_PATH) if args.apply else None
    proposal = native.prepare(selection, root)
    if args.check:
        check_index(root, proposal)
    write_projection(output, native.encoded(proposal))
    if args.apply:
        apply_index(root, proposal, previous)
    print(f'Checked {len(proposal["cohort"])} native trajectories; candidate calls: 0; applied: {args.apply}')


if __name__ == '__main__':
    main()
