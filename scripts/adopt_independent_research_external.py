#!/usr/bin/env python3
"""Validate and locally admit externally collected research; never call a model."""
import argparse
from contextlib import contextmanager
import fcntl
import os
from pathlib import Path
import stat
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from math_gauge import independent_research_external as external
from math_gauge import taste_v130 as flow
from scripts.adopt_independent_research_batch import LOCK_PATH, current_index, write_projection


@contextmanager
def adoption_lock(root):
    root = flow._safe_absolute(root)
    path = flow._contained(root, LOCK_PATH)
    path.parent.mkdir(mode=0o700, exist_ok=True)
    descriptor = os.open(path, os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW | os.O_NONBLOCK, 0o600)
    with os.fdopen(descriptor, 'rb+') as lock:
        if not stat.S_ISREG(os.fstat(lock.fileno()).st_mode):
            raise ValueError('The adoption lock must be a regular file')
        fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        yield root


def validate_current_sources(root, proposal):
    raw = current_index(flow._contained(root, 'site/data.json'))
    if raw is None:
        raise ValueError('The retained baseline is missing')
    baseline = external.value._json(raw)
    if baseline.get('benchmark_version') != '1.2.0':
        raise ValueError('External adoption requires the retained 1.2 baseline')
    external.validate_public(proposal, policies=external.policy_bindings(root),
        baseline_hash=external.digest(raw), model_ids=[row['id'] for row in baseline['models']])


def apply_index(root, proposal, expected, *, amendment_selection=None):
    with adoption_lock(root) as root:
        target = flow._contained(root, external.PUBLIC_PATH.as_posix())
        current = current_index(target)
        if current != expected:
            raise ValueError('External aggregate changed during its source verification')
        validate_current_sources(root, proposal)
        if current is not None:
            prior = external.value._json(current)
            external.validate_public(prior)
            changed = any(proposal['models'].get(key) != value for key, value in prior['models'].items())
            if changed:
                if amendment_selection is None:
                    raise ValueError('Changing a settled external judgment requires a separate source-bound correction')
                if external.amendment_parent(amendment_selection, proposal, root) != current:
                    raise ValueError('Review correction does not bind the current installed source')
        raw = external.encoded(proposal)
        if current != raw:
            write_projection(target, raw, replace=current is not None)


def check_index(root, proposal):
    with adoption_lock(root) as root:
        validate_current_sources(root, proposal)
        if current_index(flow._contained(root, external.PUBLIC_PATH.as_posix())) != external.encoded(proposal):
            raise ValueError('Installed external aggregate differs from its original selected evidence')


def protect_output(output, root, selection):
    document = external.value._json(selection.read_bytes())
    source_roots = [root, selection.parent]
    for key in ('registration', 'review_policy'):
        source_roots.append(flow._safe_absolute(document[key]).parent)
    source_roots.append(flow._safe_absolute(document['bundle']))
    for model in document['models']:
        source_roots.append(flow._safe_absolute(model['state']))
        source_roots.extend(flow._safe_absolute(model[key]).parent
                            for key in ('review', 'original_review', 'reviewer_observation'))
    source_roots.extend(flow._safe_absolute(ref['path']).parent for ref in document['source_evidence'])
    if any(output.is_relative_to(path) for path in source_roots):
        raise ValueError('Keep the proposal outside the public and private source trees')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--selection', required=True, type=Path)
    parser.add_argument('--public-root', type=Path, default=ROOT)
    parser.add_argument('--out', required=True, type=Path)
    action = parser.add_mutually_exclusive_group()
    action.add_argument('--apply', action='store_true')
    action.add_argument('--check', action='store_true')
    args = parser.parse_args()
    root, selection, output = map(flow._safe_absolute, (args.public_root, args.selection, args.out))
    protect_output(output, root, selection)
    target = root / external.PUBLIC_PATH
    previous = current_index(target) if args.apply else None
    result = external.prepare(selection, root)
    raw = external.encoded(result)
    if args.check:
        check_index(root, result)
    write_projection(output, raw)
    if args.apply:
        amendment = selection if 'review_amendment' in external.value._json(selection.read_bytes()) else None
        apply_index(root, result, previous, amendment_selection=amendment)
    print(f'Checked {len(result["cohort"])} external trajectories; candidate calls: 0; applied: {args.apply}')


if __name__ == '__main__':
    main()
