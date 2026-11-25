#!/usr/bin/env python3
"""Prepare/check a separate user-selected Carbon cutoff adoption; never call a model."""
import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from math_gauge import independent_research_admitted_delivery as admitted
from math_gauge import taste_v130 as flow
from scripts.adopt_independent_research_batch import current_index, write_projection
from scripts.adopt_independent_research_external import adoption_lock


def validate_current(root, proposal):
    raw, parent = admitted.baseline(root, proposal['source_binding']['baseline'])
    current = json.loads(current_index(root/'site/versions/1.2.0/data.json') or b'null')
    old = {m['id']: m for m in parent['models']}
    new = {m['id']: m for m in (current or {}).get('models', [])}
    if json.dumps(old.get(admitted.MODEL), sort_keys=True) != json.dumps(new.get(admitted.MODEL), sort_keys=True):
        raise ValueError('Admitted source differs from its actual current1.2 parent')
    admitted.validate_public(proposal, policies=admitted.external.policy_bindings(root),
                            baseline_hash=admitted.digest(raw), model_ids=new)


def apply_index(root, proposal, expected):
    with adoption_lock(root) as root:
        target = flow._contained(root, admitted.PUBLIC_PATH.as_posix())
        current = current_index(target)
        if current != expected:
            raise ValueError('Admitted aggregate changed during verification')
        validate_current(root, proposal)
        if current is not None and admitted.validate_public(json.loads(current)) != proposal:
            raise ValueError('A settled admitted judgment needs a separate source-bound correction')
        if admitted.encoded(proposal) != current:
            target.parent.mkdir(parents=True, exist_ok=True)
            write_projection(target, admitted.encoded(proposal), replace=current is not None)


def check_index(root, proposal):
    with adoption_lock(root) as root:
        validate_current(root, proposal)
        if current_index(root/admitted.PUBLIC_PATH) != admitted.encoded(proposal):
            raise ValueError('Installed admitted result differs from the actual source and review')


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
    document = json.loads(selection.read_bytes())
    sources = [root, selection.parent]
    for key in ('registration', 'review_policy', 'admission', 'review'):
        sources.append(flow._safe_absolute(document[key]['path']).parent)
    if any(output == source or output.is_relative_to(source) for source in sources):
        raise ValueError('Keep the proposal outside all public/private source trees')
    expected = current_index(root/admitted.PUBLIC_PATH) if args.apply else None
    proposal = admitted.prepare(selection, root)
    if args.check:
        check_index(root, proposal)
    write_projection(output, admitted.encoded(proposal))
    if args.apply:
        apply_index(root, proposal, expected)
    print('Checked one separately admitted trajectory; candidate calls:0; applied:' + str(args.apply))


if __name__ == '__main__':
    main()
