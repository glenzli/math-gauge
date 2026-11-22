#!/usr/bin/env python3
"""Recompute, check or explicitly install the local independent-research value revision."""

import argparse
import fcntl
import os
from pathlib import Path
import stat
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from math_gauge import independent_research_adoption as adoption
from math_gauge import independent_research_value as value
from math_gauge import taste_v130 as flow
from scripts.adopt_independent_research_batch import LOCK_PATH, current_index, write_projection


def apply_index(root, proposal, *, expected):
    """Atomically extend the separate value projection under the adoption lock."""
    target = flow._contained(root, value.PUBLIC_PATH.as_posix())
    lock_path = flow._contained(root, LOCK_PATH)
    lock_path.parent.mkdir(mode=0o700, exist_ok=True)
    fd = os.open(lock_path, os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW | os.O_NONBLOCK, 0o600)
    with os.fdopen(fd, 'rb+') as lock:
        if not stat.S_ISREG(os.fstat(lock.fileno()).st_mode):
            raise ValueError('The adoption lock must be a regular file')
        fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        current = current_index(target)
        if current != expected:
            raise ValueError('Installed value index changed during verification')
        policy, policy_hash = value.load_policy(flow._contained(root, value.POLICY_PATH.as_posix()))
        adopted, retained, _ = value.load_retained(root, policy)
        value.validate_public(proposal, adopted, retained, policy, policy_hash)
        if current is not None:
            existing = value.validate_public(value._json(current), adopted, retained, policy, policy_hash)
            if any(proposal['models'].get(key) != row for key, row in existing['models'].items()):
                raise ValueError('Adopt accepted value reviews only by extending the current selection')
        raw = adoption.encoded(proposal)
        if current != raw:
            write_projection(target, raw, replace=current is not None)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--public-root', type=Path, default=ROOT)
    parser.add_argument('--replay-root', type=Path, required=True, help='Retained private replay of the selected original run')
    parser.add_argument('--reviews', type=Path, required=True, help='Private directory containing per-model review.json and notes.md')
    parser.add_argument('--out', type=Path, required=True, help='New disposable file for the public aggregate proposal')
    action = parser.add_mutually_exclusive_group()
    action.add_argument('--apply', action='store_true', help='Install the checked aggregate as the new local index')
    action.add_argument('--check', action='store_true', help='Compare the recomputation with the installed index')
    args = parser.parse_args(argv)
    root, replay, reviews, output = map(flow._safe_absolute, (args.public_root, args.replay_root, args.reviews, args.out))
    target = flow._contained(root, value.PUBLIC_PATH.as_posix())
    if any(output.is_relative_to(path) for path in (root, replay, reviews)):
        raise ValueError('Put the disposable proposal outside the public and source trees')
    current = current_index(target) if args.apply or args.check else None
    proposal = value.prepare(replay, reviews, root)
    raw = adoption.encoded(proposal)
    if args.check and current != raw:
        raise ValueError('Installed value index differs from the retained private reviews')
    write_projection(output, raw)
    if args.apply:
        apply_index(root, proposal, expected=current)
    print(f'Checked value revision for {len(proposal["cohort"])} configurations; candidate calls: 0; applied: {args.apply}')


if __name__ == '__main__':
    main()
