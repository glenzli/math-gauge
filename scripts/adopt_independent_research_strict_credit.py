#!/usr/bin/env python3
"""Recompute and optionally install the separate local strict-credit result."""

import argparse
import fcntl
import os
from pathlib import Path
import stat
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from math_gauge import independent_research_adoption as adoption
from math_gauge import independent_research_strict_credit as credit
from math_gauge import taste_v130 as flow
from scripts.adopt_independent_research_batch import LOCK_PATH, current_index, write_projection


def apply_index(root, proposal, *, expected):
    """Install the checked score projection under the existing evaluator lock."""
    target = flow._contained(root, credit.PUBLIC_PATH.as_posix())
    lock_path = flow._contained(root, LOCK_PATH)
    lock_path.parent.mkdir(mode=0o700, exist_ok=True)
    fd = os.open(lock_path, os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW | os.O_NONBLOCK, 0o600)
    with os.fdopen(fd, 'rb+') as lock:
        if not stat.S_ISREG(os.fstat(lock.fileno()).st_mode):
            raise ValueError('The adoption lock must be a regular file')
        fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        current = current_index(target)
        if current != expected:
            raise ValueError('Installed strict-credit result changed during verification')
        policy, digest = credit.load_policy(flow._contained(root, credit.PATH.as_posix()))
        retained, values, _ = credit.load_sources(root, policy)
        credit.validate_public(proposal, retained, values, policy, digest)
        raw = adoption.encoded(proposal)
        if current is None:
            write_projection(target, raw)
        elif current != raw:
            raise ValueError('An installed strict-credit selection requires a new version to change')


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--public-root', type=Path, default=ROOT)
    parser.add_argument('--replay-root', type=Path, required=True, help='Retained private replay of the selected originals')
    parser.add_argument('--value-reviews', type=Path, required=True, help='Original private value review and notes by model')
    parser.add_argument('--allocations', type=Path, required=True, help='Private allocation.json by mixed-outcome model')
    parser.add_argument('--out', type=Path, required=True, help='New file for the public strict-credit proposal')
    action = parser.add_mutually_exclusive_group()
    action.add_argument('--apply', action='store_true', help='Atomically install the checked result')
    action.add_argument('--check', action='store_true', help='Compare the recomputation with the installed result')
    args = parser.parse_args(argv)
    root, replay, reviews, allocations, output = map(flow._safe_absolute, (args.public_root, args.replay_root,
                                                args.value_reviews, args.allocations, args.out))
    if any(output.is_relative_to(path) for path in (root, replay, reviews, allocations)):
        raise ValueError('Keep the proposal outside the public and private source trees')
    target = flow._contained(root, credit.PUBLIC_PATH.as_posix())
    current = current_index(target) if args.apply or args.check else None
    proposal = credit.prepare(replay, reviews, allocations, root)
    raw = adoption.encoded(proposal)
    if args.check and raw != current:
        raise ValueError('Installed strict credit differs from the original reviewed allocation')
    write_projection(output, raw)
    if args.apply:
        apply_index(root, proposal, expected=current)
    print(f'Checked strict credit for {len(proposal["cohort"])} configurations; candidate calls: 0; applied: {args.apply}')


if __name__ == '__main__':
    main()
