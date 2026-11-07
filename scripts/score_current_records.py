#!/usr/bin/env python3
"""Recompute current classified scores from retained evidence, without model calls."""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from math_gauge.records import descriptor, load_retry_inputs, load_theorem_extension_inputs, load_background_check_inputs, project_assessment_score, validate_record
from math_gauge.scoring import score_assessment_record_inputs


def load(path):
    return json.loads(Path(path).read_bytes())


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write(path, value):
    Path(path).write_text(json.dumps(value, ensure_ascii=False, indent=2, allow_nan=False) + "\n", encoding="utf-8")


def retain(private_root, *, public_root=ROOT):
    public_root, private_root = Path(public_root).resolve(), Path(private_root).resolve()
    assessment = load(public_root / "protocol/scoring-policy.json")
    strict = load(public_root / "protocol/strict-scoring-policy.json")
    totals = {}
    for model in load(public_root / "benchmark.json")["selected_result_models"]:
        relative = Path("results/v0.6.0") / model / "20261105"
        public, private = public_root / relative, private_root / relative
        validate_record(public, validate_scores=False)
        validate_record(private, formalization_root=public, validate_scores=False)
        record, private_record = load(public / "record.json"), load(private / "record.json")
        research = load_theorem_extension_inputs(private, private_record, policy=assessment.get("theorem_extension"))
        background = load_background_check_inputs(private,private_record,policy=assessment.get("background_check"))
        original = load(private / "scoring-inputs.json")
        retry = load_retry_inputs(private, private_record, public_root=public, validate_results=False)
        old_retry = load(public / "retry-combined-aggregate.json") if (public / "retry-combined-aggregate.json").exists() else {}
        review_path = private / "reviews/alignment.json"
        if not review_path.exists():
            review_path = private / "alignment-review.json"
        review, source_policy = load(review_path), load(private / "scoring-policy.json")
        engineering = load(public / "reviews/formalization.json")
        for filename, source in (("assessment-policy.json", "scoring-policy.json"),
                                 ("strict-scoring-policy.json", "strict-scoring-policy.json")):
            (public / filename).write_bytes((public_root / "protocol" / source).read_bytes())
        for target in (record, private_record):
            target["assessment_policy"] = descriptor(public, public / "assessment-policy.json")
            target["strict_scoring_policy"] = descriptor(public, public / "strict-scoring-policy.json")
            target["assessment_results"], target["strict_results"] = {}, {}
        totals[model] = {}
        for condition in ("single_attempt", "nonlogical_retry_3"):
            uses_retry = condition == "nonlogical_retry_3" and retry is not None
            inputs = retry if uses_retry else original
            retry_summary = (copy.deepcopy(old_retry["retry_summary"]) if uses_retry else {
                "slots_with_reruns": 0, "source": "original_records_reused_no_new_retry_evidence",
                "all_original_attempts_independently_certified": False})
            totals[model][condition] = {}
            for mode in ("partial", "strict"):
                score = score_assessment_record_inputs(inputs, review, source_policy,
                    formalization_review=engineering, assessment_policy=assessment, strict_policy=strict, mode=mode,
                    theorem_extension_inputs=research,background_check_inputs=background)
                score.update(attempt_condition=condition, retry_summary=retry_summary,
                    scope="combined-evaluator", source_math_policy_version=source_policy["version"],
                    engineering_review_sha256=digest(public / "reviews/formalization.json"),
                    source_bindings={
                        "scoring_inputs_sha256": digest(private / ("retry-scoring-inputs.json" if uses_retry else "scoring-inputs.json")),
                        "source_math_policy_sha256": digest(private / "scoring-policy.json"),
                        "alignment_review_sha256": digest(review_path),
                        "engineering_review_sha256": digest(public / "reviews/formalization.json"),
                        "assessment_policy_sha256": digest(public / "assessment-policy.json"),
                        "strict_policy_sha256": digest(public / "strict-scoring-policy.json")})
                if research is not None:
                    score["source_bindings"]["theorem_extension_inputs_sha256"] = digest(private / private_record["theorem_extension_inputs"]["path"])
                if background is not None:
                    score["source_bindings"]["background_check_inputs_sha256"]=digest(private/private_record["background_check_inputs"]["path"])
                if uses_retry:
                    admission = load(public / record["retry_admission"]["path"])
                    score.update(retry_policy_sha256=admission["policy"]["sha256"],
                                 retry_admission_sha256=record["retry_admission"]["sha256"])
                is_retry = condition == "nonlogical_retry_3"
                private_name = (("strict-retry-result.json" if is_retry else "strict-result.json") if mode == "strict"
                                else "retry-result.json" if is_retry else "result.json")
                public_name = (("strict-retry-combined-aggregate.json" if is_retry else "strict-combined-aggregate.json")
                               if mode == "strict" else "retry-combined-aggregate.json" if is_retry else "combined-aggregate.json")
                write(private / private_name, score)
                aggregate = project_assessment_score(score)
                aggregate["source_bindings"]["private_report_sha256"] = digest(private / private_name)
                write(public / public_name, aggregate)
                key = "strict_results" if mode == "strict" else "assessment_results"
                record[key][condition] = descriptor(public, public / public_name)
                private_record[key][condition] = descriptor(private, private / private_name)
                totals[model][condition][mode] = score["metrics"]["earned"].get("confirmed", score["metrics"]["earned"]["exact"])
        # Public-only score views are retired; original questions, answers,
        # engineering judgments and frozen execution inputs are untouched.
        for filename in ("result.json", "retry-result.json"):
            path = public / filename
            if path.exists():
                path.unlink()
        record.pop("retry_result", None)
        if record.get("retry_admission"):
            record["retry_combined_aggregate"] = descriptor(public, public / "retry-combined-aggregate.json")
            private_record["retry_result"] = descriptor(private, private / "retry-result.json")
        for folder, target in ((public, record), (private, private_record)):
            target["evidence"] = [descriptor(folder, folder / item["path"])
                if item["path"] in {"result.json", "combined-aggregate.json", "retry-result.json", "retry-combined-aggregate.json"}
                else item for item in target["evidence"]
                if not (folder == public and item["path"] in {"result.json", "retry-result.json"})]
            write(folder / "record.json", target)
    active = sum(c["weight"] for c in assessment["subcategories"] if c["status"] == "active")
    return {"benchmark_version": "0.6.0", "scoring_version": assessment["version"], "strict_version": strict["version"],
            "capacity": {"active": active, "under_construction": 100-active, "total": 100}, "totals": totals,
            "candidate_calls": 0, "sealed_engineering_compilations": 0}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--private-root", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(retain(args.private_root), ensure_ascii=False))


if __name__ == "__main__":
    main()
