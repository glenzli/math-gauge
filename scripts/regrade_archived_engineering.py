#!/usr/bin/env python3
"""Install bound engineering reviews and rescore current records; never call models."""

import argparse
import copy
import hashlib
import json
from pathlib import Path, PurePosixPath
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from math_gauge.records import descriptor, validate_formalization_review, validate_record
from math_gauge.scoring import score_record_inputs

MODELS = ("terra-6.1-max", "gemini-3.8-flash-high")
CASE_IDS = ("LCH01", "LCH02", "HCH02", "MG-C003")


def load(path):
    return json.loads(Path(path).read_bytes())


def write(path, value):
    Path(path).write_text(json.dumps(value, ensure_ascii=False, indent=2, allow_nan=False) + "\n", encoding="utf-8")


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def copy_bound(source, root, relative):
    name = PurePosixPath(relative)
    if name.is_absolute() or ".." in name.parts or "\\" in relative or str(name) != relative:
        raise ValueError("Unsafe engineering evidence destination")
    raw = Path(source["path"]).read_bytes()
    if len(raw) != source["bytes"] or digest(raw) != source["sha256"]:
        raise ValueError("Prepared engineering evidence changed before import")
    target = root / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(raw)
    return descriptor(root, target)


def install_reviews(root, plan, policy_hash):
    if {row["model"] for row in plan["models"]} != set(MODELS) or len(plan["models"]) != 2:
        raise ValueError("Review import must cover both selected models")
    for model in plan["models"]:
        folder = root / "results/v0.6.0" / model["model"] / "20261105"
        inputs = load(folder / "scoring-inputs.json")
        if {case["case_id"] for case in model["cases"]} != set(CASE_IDS) or len(model["cases"]) != 4:
            raise ValueError("Review import must cover all four engineering sources")
        review = {"schema": "math-gauge.formalization-engineering-review/v1", "review_version": "0.1.0",
            "model_label": inputs["model_label"], "reviewer_kind": "ai", "human_review": "pending",
            "formal_comparison_eligible": False, "policy_sha256": policy_hash,
            "source_rule": "selected answer-phase sealed engineering; no source repair or cross-round union",
            "cases": []}
        for source_case in model["cases"]:
            cid = source_case["case_id"]
            case = copy.deepcopy(source_case["review"])
            engineering = f"engineering/formalization/{cid}"
            verification = f"verification/formalization/{cid}"
            case["source_manifest"] = copy_bound(source_case["source_manifest"], folder,
                                                  engineering + "/sealed-project-manifest.json")
            case["source_files"] = {}
            for name, item in source_case["source_files"].items():
                reused = source_case.get("reuse_record_sources", {}).get(name)
                if reused is None:
                    selected = copy_bound(item, folder, engineering + "/" + name)
                else:
                    selected = descriptor(folder, folder / reused)
                    if selected["sha256"] != item["sha256"] or selected["bytes"] != item["bytes"]:
                        raise ValueError("Existing engineering record differs from the audited source")
                case["source_files"][name] = selected
            case["kernel_report"] = copy_bound(source_case["kernel_report"], folder,
                                                 verification + "/kernel-report.json")
            case["case_contract"] = copy_bound(source_case["case_contract"], folder,
                                                 verification + "/case-contract.json")
            case["background_inputs"] = {name: copy_bound(item, folder, verification + "/background/" + name)
                                         for name, item in source_case["background_inputs"].items()}
            case["review_evidence"] = [copy_bound(row["source"], folder, verification + "/" + row["name"])
                                       for row in source_case.get("evidence", [])]
            review["cases"].append(case)
        validate_formalization_review(folder, inputs, review)
        write(folder / "reviews/formalization.json", review)


def refresh_descriptors(root, value):
    if isinstance(value, dict):
        name = value.get("path")
        if isinstance(name, str) and {"path", "bytes", "sha256"} <= value.keys():
            path = PurePosixPath(name)
            if not path.is_absolute() and ".." not in path.parts and (root / name).is_file():
                value.update(descriptor(root, root / name))
        for item in value.values():
            refresh_descriptors(root, item)
    elif isinstance(value, list):
        for item in value:
            refresh_descriptors(root, item)


def project_metrics(metrics):
    """Private inputs are never copied to public files; publish aggregates only."""
    fields = ("exact", "lower", "upper", "complete", "coverage")
    return {name: {**{key: copy.deepcopy(value[key]) for key in fields},
                   "formal_comparison_eligible": False} for name, value in metrics.items()}


def regrade(root=ROOT, *, private_root, review_plan=None):
    root, private_root = Path(root).resolve(), Path(private_root).resolve()
    policy_path = root / "protocol/scoring-policy.json"
    policy_raw = policy_path.read_bytes()
    policy, policy_hash = json.loads(policy_raw), digest(policy_raw)
    if policy["version"] != "0.4.0":
        raise ValueError("Unified engineering regrade requires method0.4.0")
    if review_plan is not None:
        install_reviews(root, load(review_plan), policy_hash)
    totals = {}
    for model in MODELS:
        folder = root / "results/v0.6.0" / model / "20261105"
        inputs = load(folder / "scoring-inputs.json")
        formalization = load(folder / "reviews/formalization.json")
        if formalization["policy_sha256"] != policy_hash:
            raise ValueError("Engineering review binds a different scoring method")
        validate_formalization_review(folder, inputs, formalization)
        review = load(folder / "reviews/alignment.json")
        review.update(scoring_version=policy["version"], policy_sha256=policy_hash)
        write(folder / "reviews/alignment.json", review)
        (folder / "scoring-policy.json").write_bytes(policy_raw)
        totals[model] = {}
        for scope, source, filename in (
                ("public", inputs, "result.json"),
                ("combined", load(private_root / "results/v0.6.0" / model / "20261105/scoring-inputs.json"),
                 "combined-aggregate.json")):
            scored = score_record_inputs(source, review, policy, formalization_review=formalization)
            path = folder / filename
            result = load(path)
            result["metrics"] = project_metrics(scored["metrics"])
            for component in result["profile"]["components"]:
                component["weight"] = policy["capability_component_weights"][scope][component["id"]]
            result["profile"]["overall_weights"] = copy.deepcopy(policy["overall_weights"])
            result["scoring_method_version"] = policy["version"]
            result["source_score_sha256"] = digest(json.dumps(scored, sort_keys=True, ensure_ascii=False).encode())
            result["engineering_review_sha256"] = digest((folder / "reviews/formalization.json").read_bytes())
            result["formal_comparison_eligible"] = False
            if scope == "public":
                result["lean_formalization_breakdown"] = scored["lean_formalization_breakdown"]
                result["alignment_selfcheck"] = scored["alignment_selfcheck"]
            write(path, result)
            totals[model][scope] = scored["metrics"]["overall"]["exact"]
        record = load(folder / "record.json")
        record["formalization_review"] = descriptor(folder, folder / "reviews/formalization.json")
        record["scoring_policy"] = {"method_version": policy["version"],
                                      "source": descriptor(folder, folder / "scoring-policy.json")}
        by_case = {case["case_id"]: case for case in formalization["cases"]}
        for row in record["records"]:
            if row["id"] in {cid + ":A1" for cid in CASE_IDS}:
                case = by_case[row["case_id"]]
                values = [item["complete"] for item in case["obligations"]]
                row["engineering_evaluation"] = {
                    "source_kind": "sealed_workspace", "source_sha256": case["source_sha256"],
                    "complete_count": sum(value is True for value in values), "total": len(values),
                    "unknown_count": sum(value is None for value in values),
                    "reviewer_kind": "ai", "human_review": "pending",
                    "review": record["formalization_review"]}
        refresh_descriptors(folder, record)
        write(folder / "record.json", record)
        validate_record(folder)
    return totals


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--private-root", type=Path, required=True)
    parser.add_argument("--review-plan", type=Path)
    args = parser.parse_args()
    print(json.dumps(regrade(private_root=args.private_root, review_plan=args.review_plan), ensure_ascii=False))


if __name__ == "__main__":
    main()
