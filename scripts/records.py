#!/usr/bin/env python3
"""Check current user-selected archives; never invoke a model or Lean."""
import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from math_gauge.records import validate_record
from math_gauge.scoring import score_record_inputs


def check(root=ROOT, *, public_root=None):
    root = Path(root).resolve()
    results = []
    for path in sorted((root / "results/v0.6.0").glob("*/*/record.json")):
        folder = path.parent
        record = json.loads(path.read_bytes())
        external = record.get("formalization_evidence_location") == "public_archive"
        if external and public_root is None:
            raise ValueError("Private archives require --public-root for shared engineering evidence")
        evidence_root = (Path(public_root).resolve() / folder.relative_to(root)) if external else folder
        status = validate_record(folder, formalization_root=evidence_root if external else None)
        inputs = json.loads((folder / "scoring-inputs.json").read_bytes())
        review_path = folder / "reviews/alignment.json"
        if not review_path.exists():
            review_path = folder / "alignment-review.json"
        review = json.loads(review_path.read_bytes())
        policy_path = folder / "scoring-policy.json"
        policy = json.loads(policy_path.read_bytes())
        formalization_path = evidence_root / "reviews/formalization.json"
        formalization = json.loads(formalization_path.read_bytes()) if formalization_path.exists() else None
        score = score_record_inputs(inputs, review, policy, formalization_review=formalization)
        retained = json.loads((folder / "result.json").read_bytes())
        expected = retained["metrics"]
        for name, value in expected.items():
            for key in ("exact", "lower", "upper"):
                actual = score["metrics"][name][key]
                target = value[key]
                if (actual is None) != (target is None) or actual is not None and abs(actual - target) > 1e-9:
                    raise ValueError(f"Archived score changed: {folder.name}/{name}/{key}")
        if external:
            aggregate = json.loads((evidence_root / "combined-aggregate.json").read_bytes())
            if (aggregate.get("metrics") != expected or any(
                    aggregate.get(key) != retained.get(key) for key in
                    ("engineering_review_sha256", "scoring_method_version", "source_score_sha256"))):
                raise ValueError("Public combined aggregate differs from the private recomputed record")
        results.append(status)
    if not results:
        raise ValueError("No current formal result records found")
    return {"passed": True, "benchmark_version": "0.6.0", "archives": results,
            "candidate_calls": 0, "lean_compilations": 0}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["check"])
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--public-root", type=Path,
                        help="public repository providing shared engineering evidence for private records")
    args = parser.parse_args()
    try:
        print(json.dumps(check(args.root, public_root=args.public_root), ensure_ascii=False))
    except (ValueError, KeyError, OSError) as error:
        parser.exit(1, str(error) + "\n")


if __name__ == "__main__":
    main()
