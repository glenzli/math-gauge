#!/usr/bin/env python3
"""Validate a whole reviewed cohort, then explicitly install aggregate fields only."""
import argparse
import json
import os
from pathlib import Path
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from math_gauge.independent_research_adoption import PUBLIC_PATH, encoded, prepare
from math_gauge import taste_v130 as flow


def install_new(target, raw):
    """Publish a complete new index atomically without replacing another writer."""
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(dir=target.parent, prefix='.adoption-', delete=False) as stream:
            temporary = Path(stream.name)
            stream.write(raw)
            stream.flush()
            os.fsync(stream.fileno())
        temporary.chmod(0o644)
        os.link(temporary, target)
    finally:
        if temporary is not None:
            temporary.unlink()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--selection', required=True, type=Path)
    parser.add_argument('--public-root', type=Path, default=ROOT)
    parser.add_argument('--out', required=True, type=Path, help='New disposable aggregate proposal, outside candidate work')
    parser.add_argument('--apply', action='store_true', help='Explicitly install the fully verified aggregate index; no Git or site publication')
    parser.add_argument('--check', action='store_true', help='Compare an existing aggregate index against the same original private evidence')
    args = parser.parse_args()
    if args.apply and args.check:
        raise ValueError('Choose adoption or an unchanged-source check')
    value = prepare(args.selection, args.public_root)
    raw = encoded(value)
    selected = json.loads(args.selection.read_bytes())
    output = flow._safe_absolute(args.out)
    if output.is_relative_to(flow._safe_absolute(selected['run_root']) / 'workspaces'):
        raise ValueError('Do not export grades into a candidate workspace')
    if args.check and (args.public_root / PUBLIC_PATH).read_bytes() != raw:
        raise ValueError('Existing public aggregate differs from the original reviewed evidence')
    with output.open('xb') as stream:
        stream.write(raw)
    if args.apply:
        target = args.public_root / PUBLIC_PATH
        install_new(target, raw)
    print(f'Checked {len(value["cohort"])} independent reviews; aggregate only; candidate calls by adoption: 0; applied: {args.apply}')


if __name__ == '__main__':
    main()
