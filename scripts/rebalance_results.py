#!/usr/bin/env python3
"""Recompute v0.3 weights from bound original evaluator inputs, without model calls."""

import argparse
import hashlib
import json
from pathlib import Path
import sys
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from math_gauge.scoring import alignment_augmented_score


def digest(data):
    return hashlib.sha256(data).hexdigest()


def recompute(archive, archive_sha256, root=ROOT):
    archive, root = Path(archive), Path(root)
    if digest(archive.read_bytes()) != archive_sha256:
        raise ValueError("Evaluator archive differs from its trusted receipt")
    policy_path = root / "protocol/lean-alignment/engineering-scoring-v0.3.0.json"
    policy_raw = policy_path.read_bytes()
    old_policy = root / "protocol/lean-alignment/engineering-scoring-v0.2.0.json"
    if json.loads(policy_raw)["supersedes_policy_sha256"] != digest(old_policy.read_bytes()):
        raise ValueError("Weight policy does not bind the previous scoring method")
    results = {}
    with tarfile.open(archive) as evidence, tempfile.TemporaryDirectory(prefix="mg-reweight-") as tmp:
        temporary = Path(tmp)
        for model in ("terra", "gemini"):
            review_path = root / f"docs/results/engineering-v0.3.0/{model}-review.json"
            review = json.loads(review_path.read_bytes())
            previous_review = root / f"docs/results/engineering-v0.2.0/{model}-review.json"
            old_review = json.loads(previous_review.read_bytes())
            expected_review = dict(old_review, scoring_version="0.3.0", policy_sha256=digest(policy_raw))
            inherited = review.get("judgments_inherited_from", {})
            if ({k: v for k, v in review.items() if k != "judgments_inherited_from"} != expected_review
                    or inherited.get("sha256") != digest(previous_review.read_bytes())
                    or inherited.get("judgments_changed") is not False):
                raise ValueError("Rebalancing must preserve all existing review judgments")
            for scope, filename in (("public", "result.json"), ("combined", "combined-aggregate.json")):
                prior_path = root / f"docs/results/engineering-v0.2.0/{model}-{scope}.json"
                prior_raw = prior_path.read_bytes()
                prior = json.loads(prior_raw)
                sources = {"policy": policy_path, "alignment_review": review_path,
                           "original_summary": root / f"docs/results/{model}-v0.6.0/{filename}",
                           "source_qualified_score": root / (
                               f"docs/results/engineering-v0.2.0/terra-capability-{scope}.json"
                               if model == "terra" else f"docs/results/gemini-v0.6.0-extension/{filename}")}
                for key, name in (("original_plan", "plan.json"), ("original_report", "report-evaluator.json")):
                    raw = evidence.extractfile(f"evaluator-inputs/{model}/{scope}/{name}").read()
                    path = temporary / f"{model}-{scope}-{name}"
                    path.write_bytes(raw)
                    sources[key] = path
                hashes = {key: digest(path.read_bytes()) for key, path in sources.items()}
                for key in set(sources) - {"policy", "alignment_review"}:
                    if hashes[key] != prior["source_bindings"][key + "_sha256"]:
                        raise ValueError(f"Original scoring evidence changed: {model}/{scope}/{key}")
                result = alignment_augmented_score(sources, expected_sha256=hashes)
                result["weight_change"] = {"previous_version": "0.2.0",
                    "previous_score_sha256": digest(prior_raw), "judgments_changed": False,
                    "new_candidate_calls": 0}
                results[f"{model}-{scope}.json"] = result
    destination = root / "docs/results/engineering-v0.3.0"
    for name, result in results.items():
        (destination / name).write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evidence-archive", type=Path, required=True)
    parser.add_argument("--archive-sha256", required=True, help="trusted hash from the archive receipt")
    args = parser.parse_args()
    for name, result in recompute(args.evidence_archive, args.archive_sha256).items():
        print(f"{name}: {result['metrics']['overall']['exact']:.10f}")


if __name__ == "__main__":
    main()
