#!/usr/bin/env python3
"""Prepare/check the separately accepted Carbon taste source; never call a candidate."""
import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from math_gauge import legacy_taste_addition as owner
from math_gauge import taste_v130 as flow
from scripts.adopt_independent_research_batch import write_projection


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--public-root', type=Path, default=ROOT)
    parser.add_argument('--private-root', type=Path, required=True)
    parser.add_argument('--reuse-audit', type=Path, required=True)
    parser.add_argument('--parent', required=True, help='Exact immutable parent path relative to public root')
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    public, private, audit, output = map(flow._safe_absolute,
        (args.public_root, args.private_root, args.reuse_audit, args.out))
    if any(output == root or output.is_relative_to(root) for root in (public, private, audit.parent)):
        raise ValueError('Keep the proposal outside all original source trees')
    raw = flow._contained(public, args.parent).read_bytes()
    parent = dict(path=args.parent, bytes=len(raw), sha256=owner.digest(raw))
    result = owner.prepare(audit, public, private, parent)
    if args.check and flow._contained(public, owner.PUBLIC_PATH.as_posix()).read_bytes() != owner.encoded(result):
        raise ValueError('Installed taste addition differs from its exact original proposals')
    write_projection(output, owner.encoded(result))
    print('Checked four accepted taste proposals; new judgments:0; candidate calls:0')


if __name__ == '__main__':
    main()
