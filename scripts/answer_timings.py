#!/usr/bin/env python3
"""Verify optional timing supplements and print aggregate-only timing coverage."""
import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from math_gauge.timings import check_pair


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--private-root", type=Path, required=True)
    parser.add_argument("--public-root", type=Path, default=ROOT)
    args = parser.parse_args()
    edition = json.loads((args.public_root / "benchmark.json").read_bytes())
    records = dict(edition["selected_result_record_ids"])
    records["dot-underlying-model-20261108"] = "20261108"
    checked = []
    for model, record_id in records.items():
        relative = Path("results/v0.6.0") / model / record_id
        public, private = args.public_root / relative, args.private_root / relative
        if not (public / "answer-timings.json").exists():
            checked.append({"model_id": model, "status": "not_supplied"})
            continue
        document = check_pair(public, private)
        checked.append({"model_id": model, "status": "passed", "summary": document["summary"]})
    print(json.dumps({"schema": "math-gauge.timing-check/v1", "models": checked,
                      "new_candidate_calls": 0, "scores_modified": False}, ensure_ascii=False))


if __name__ == "__main__":
    main()
