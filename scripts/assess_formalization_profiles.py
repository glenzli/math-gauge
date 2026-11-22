#!/usr/bin/env python3
"""Project/check existing verified formalization evidence; never call a model."""
import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from math_gauge.formalization_profile import install, load_public, EDITION, BOUNDARIES


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    if args.write:
        result = install(args.root)
    else:
        value = load_public(args.root, benchmark_version=EDITION)
        if value is None:
            raise ValueError('Formalization profile has not been prepared')
        result = dict(status='passed', models=len(value['models']), **BOUNDARIES)
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
