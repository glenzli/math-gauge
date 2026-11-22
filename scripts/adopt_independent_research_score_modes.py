#!/usr/bin/env python3
"""Prepare, check or explicitly install the separate 1.3 score-mode overlay."""

import argparse
import fcntl
import json
import os
from pathlib import Path
import stat
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from math_gauge import independent_research_adoption as baseline
from math_gauge import independent_research_score_modes as modes
from math_gauge import taste_v130 as flow
from scripts.adopt_independent_research_batch import LOCK_PATH, current_index, write_projection


def apply_index(root, value, *, expected):
    """Install one validated supplement under the same lock as the original index."""
    root = flow._safe_absolute(root)
    target = flow._contained(root, modes.PUBLIC_PATH.as_posix())
    lock_path = flow._contained(root, LOCK_PATH)
    lock_path.parent.mkdir(mode=0o700, exist_ok=True)
    fd = os.open(lock_path, os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW | os.O_NONBLOCK, 0o600)
    with os.fdopen(fd, 'rb+') as lock:
        if not stat.S_ISREG(os.fstat(lock.fileno()).st_mode):
            raise ValueError('The aggregate writer lock must be a regular file')
        fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        current = current_index(target)
        if current != expected:
            raise ValueError('Installed score-mode overlay changed during verification')
        base_raw = current_index(flow._contained(root, baseline.PUBLIC_PATH))
        if base_raw is None:
            raise ValueError('Original adoption index is required')
        original = baseline.validate_public(json.loads(base_raw))
        policy, policy_hash = modes.load_policy(flow._contained(root, modes.POLICY_PATH.as_posix()))
        modes.validate_public(value, original, flow._sha(base_raw), policy, policy_hash)
        if current is not None:
            prior = json.loads(current)
            modes.validate_public(prior, original, prior['base_index_sha256'], policy, prior['policy_sha256'])
            for identifier, row in prior['models'].items():
                proposed = value['models'].get(identifier)
                if row == proposed:
                    continue
                # An adopted ordinary judgment or completed MC may never be
                # replaced by an incremental install. Only an absent MC can fill.
                if proposed is None or row['mc_source_sha256'] is not None:
                    raise ValueError('Overlay update must retain already selected source rows')
                stripped = dict(proposed, mc_source_sha256=None, axes={
                    axis: dict(grade, mc=None) for axis, grade in proposed['axes'].items()})
                if stripped != row:
                    raise ValueError('Overlay update must retain already selected source rows')
        raw = baseline.encoded(value)
        if current != raw:
            write_projection(target, raw, replace=current is not None)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--public-root', type=Path, default=ROOT)
    parser.add_argument('--selection', required=True, type=Path, help='Private selection binding original bytes')
    parser.add_argument('--out', required=True, type=Path, help='New disposable public aggregate proposal')
    action = parser.add_mutually_exclusive_group()
    action.add_argument('--apply', action='store_true', help='Install the verified overlay beside the original index')
    action.add_argument('--check', action='store_true', help='Compare the verified proposal with the installed overlay')
    args = parser.parse_args(argv)
    root = flow._safe_absolute(args.public_root)
    selection = flow._safe_absolute(args.selection)
    output = flow._safe_absolute(args.out)
    target = flow._contained(root, modes.PUBLIC_PATH.as_posix())
    current = current_index(target) if args.apply or args.check else None
    selection_raw = selection.read_bytes()
    run_root = flow._safe_absolute(json.loads(selection_raw)['run_root'])
    if output in (target, root / baseline.PUBLIC_PATH, root / LOCK_PATH) or output.is_relative_to(run_root / 'workspaces'):
        raise ValueError('The proposal needs a separate location outside candidate workspaces')
    value = modes.prepare(selection, root)
    if selection.read_bytes() != selection_raw:
        raise ValueError('Selection changed during verification')
    raw = baseline.encoded(value)
    if args.check and current != raw:
        raise ValueError('Installed score-mode overlay differs from the original reviewed evidence')
    write_projection(output, raw)
    if args.apply:
        apply_index(root, value, expected=current)
    print(f'Checked score modes for {len(value["cohort"])} configurations; candidate calls: 0; applied: {args.apply}')


if __name__ == '__main__':
    main()
