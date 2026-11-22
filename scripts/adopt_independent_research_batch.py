#!/usr/bin/env python3
"""Validate settled research trajectories and explicitly extend their aggregate index."""
import argparse
import fcntl
import json
import os
from pathlib import Path
import stat
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from math_gauge.independent_research_adoption import (
    PUBLIC_PATH, encoded, prepare, validate_extension, validate_public,
)
from math_gauge import taste_v130 as flow


LOCK_PATH = '.dev-mesh/independent-research-adoption.lock'


def current_index(target):
    """Read exact installed bytes, with absence distinct from invalid content."""
    target = flow._safe_absolute(target)
    try:
        fd = os.open(target, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    except FileNotFoundError:
        return None
    with os.fdopen(fd, 'rb') as stream:
        if not stat.S_ISREG(os.fstat(stream.fileno()).st_mode):
            raise ValueError('The installed aggregate must be a regular file')
        return stream.read()


def write_projection(target, raw, *, replace=False):
    """Install complete bytes atomically; creation is exclusive by default."""
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(dir=target.parent, prefix='.adoption-', delete=False) as stream:
            temporary = Path(stream.name)
            stream.write(raw)
            stream.flush()
            os.fchmod(stream.fileno(), 0o644)
            os.fsync(stream.fileno())
        if replace:
            os.replace(temporary, target)
        else:
            os.link(temporary, target)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def apply_index(public_root, value, *, expected):
    """Compare the original snapshot under the writer lock and extend it atomically."""
    validate_public(value)
    public_root = flow._safe_absolute(public_root)
    target = flow._contained(public_root, PUBLIC_PATH)
    lock_path = flow._contained(public_root, LOCK_PATH)
    lock_path.parent.mkdir(mode=0o700, exist_ok=True)
    fd = os.open(lock_path, os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW | os.O_NONBLOCK, 0o600)
    with os.fdopen(fd, 'rb+') as lock:
        if not stat.S_ISREG(os.fstat(lock.fileno()).st_mode):
            raise ValueError('The aggregate writer lock must be a regular file')
        fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        current = current_index(target)
        if current != expected:
            raise ValueError('Installed aggregate changed during verification. Rebuild from the current selection.')
        if current is not None:
            validate_extension(json.loads(current), value)
        raw = encoded(value)
        if current != raw:
            write_projection(target, raw, replace=current is not None)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--selection', required=True, type=Path)
    parser.add_argument('--public-root', type=Path, default=ROOT)
    parser.add_argument('--out', required=True, type=Path, help='New disposable aggregate proposal, outside candidate work')
    parser.add_argument('--apply', action='store_true', help='Explicitly install or extend the verified local aggregate index')
    parser.add_argument('--check', action='store_true', help='Compare an existing aggregate index against the same original private evidence')
    args = parser.parse_args()
    if args.apply and args.check:
        raise ValueError('Choose adoption or an unchanged-source check')
    public_root = flow._safe_absolute(args.public_root)
    target = flow._contained(public_root, PUBLIC_PATH)
    current = current_index(target) if args.apply else None
    selection = flow._safe_absolute(args.selection)
    selection_raw = selection.read_bytes()
    selected = json.loads(selection_raw)
    output = flow._safe_absolute(args.out)
    if output in (target, public_root / LOCK_PATH):
        raise ValueError('The proposal must be separate from the installed aggregate and its lock')
    if output.is_relative_to(flow._safe_absolute(selected['run_root']) / 'workspaces'):
        raise ValueError('Do not export grades into a candidate workspace')
    value = prepare(selection, public_root)
    if selection.read_bytes() != selection_raw:
        raise ValueError('Selection changed during verification')
    raw = encoded(value)
    if args.check and current_index(target) != raw:
        raise ValueError('Existing public aggregate differs from the original reviewed evidence')
    write_projection(output, raw)
    if args.apply:
        apply_index(public_root, value, expected=current)
    print(f'Checked {len(value["cohort"])} independent reviews; aggregate only; candidate calls by adoption: 0; applied: {args.apply}')


if __name__ == '__main__':
    main()
