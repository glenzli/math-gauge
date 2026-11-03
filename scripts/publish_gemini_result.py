#!/usr/bin/env python3
"""Project an already scored Gemini run for public display; never score a run.

Input paths are evaluator-local command arguments and are never serialized.
The shared public_score_projection owns the private-data publication boundary.
"""

import argparse
import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from math_gauge.scoring import public_score_projection


def project(score_path, plan_path, consumption_path):
    raw = score_path.read_bytes()
    source = json.loads(raw)
    plan = json.loads(plan_path.read_text(encoding="utf-8"))
    consumption = json.loads(consumption_path.read_text(encoding="utf-8"))
    private_ids = sorted(row["case_id"] for row in plan["case_index"]
                         if row.get("source_visibility") == "private")
    aliases = {case_id: f"Private-{index:02}" for index, case_id in enumerate(private_ids, 1)}
    if len(aliases) != 3:
        raise ValueError("The dated result requires three private papers")
    result = public_score_projection(source, plan, private_aliases=aliases, metadata={
        "id": "gemini-2026-11-03", "title": "Gemini 3.8 Flash · 综合开发评测",
        "date": "2026-11-03", "requested_model": "gemini-3.8-flash-high",
        "requested_reasoning_effort": "high",
    })
    result["profile"]["version"] = source["profile"]["version"]
    result["profile"]["sha256"] = source["profile"]["sha256"]
    result["profile"]["selection_timing"] = "after_terra_results_before_gemini_run"
    # The shared projection uses composite source names. This run is new rather
    # than historical reuse; changing display provenance does not alter scores.
    for row in result["slot_evidence"] + result["private_records"]:
        row["source_kind"] = "current_private" if row["public_id"].startswith("Private-") else "current_public"
    slots = result["slot_evidence"]
    result["strict_passes"]["all_selected_slots"] = {
        "passed": sum(row["strict_pass"] is True for row in slots),
        "total": len(slots),
        "adjudicated": sum(row["strict_pass"] is not None for row in slots),
    }
    result["source_score_sha256"] = hashlib.sha256(raw).hexdigest()
    result["execution_condition"] = {"track": source["execution_condition"]["track"],
                                     "independent_initial_contexts": True,
                                     "separate_followup_branches": True,
                                     "review_feedback_to_candidate": False}
    result["chapter_completion"] = []
    evidence = {row["slot_id"]: row for row in source["evidence"]}
    chapters = next(row for row in plan["profile"]["data"]["components"] if row["id"] == "chapters")
    for case_id in chapters["case_ids"]:
        if case_id in aliases:
            raise ValueError("Chapter diagnostics must be public")
        diagnostic = evidence[case_id + ":A1"]["group_diagnostic"]
        result["chapter_completion"].append({
            "public_id": case_id, "attempt": "A1", "completed": diagnostic["completed_weight"],
            "total": diagnostic["total_weight"], "unit": "chapter obligation",
        })
    candidate = consumption["formal_candidate"]
    reviewer = consumption["terra_review"]["formal"]
    result["candidate_call_accounting"] = {
        "logical_slots": consumption["fixed_logical_slots"],
        "native_submissions": candidate["local_native_submission_receipts"],
        "retained_quota_interruptions": consumption["retained_historical_quota_failures"],
        "same_context_resumption_submissions": candidate["same_context_resumption_submission_receipts"],
        "quality_retries": 0, "diagnostic_queue_in_score": False,
        "backend_identity_independently_verified": False,
    }
    result["review_status"] = {
        "kind": "ai", "native_terra_primary_review_slots": reviewer["candidate_slots_bound_in_successful_native_results"],
        "root_direct_final_review_slots": 1, "root_sampling_and_arbitration": True,
        "human_approval": "pending",
    }
    result["consumption"] = {
        "candidate": {"native_submissions": candidate["local_native_submission_receipts"],
                      "reported_total_tokens": candidate["tokens"]["observed_attributed_usage_sums"]["total_tokens"]},
        "ai_review": {"native_submissions": reviewer["local_native_submission_receipts"],
                      "reported_total_tokens": reviewer["tokens"]["observed_attributed_usage_sums"]["total_tokens"]},
        "orchestration_and_root_review_tokens": None, "actual_fees": None,
        "reported_tokens_are_observed_aggregates": True,
        "thinking_and_cached_fields_added_to_total": False,
    }
    return result, set(private_ids)


def check_public(result, private_ids):
    """One display-boundary check, independent of mathematical adjudication."""
    expected = {"proofs": 88.3888888889, "lean-audit": 93.3333333333,
                "lean-construction": 98.3333333333, "chapters": 0,
                "exploration": 34.1666666667, "core": 65.5555555556,
                "repeat": 83.3333333333, "neutral": 100, "stance": 87.5,
                "overall": 72.0833333333}
    if result["source_score_sha256"] != "09ee883659bea150d31c8eff90b04f7a982859aa5e3ef9fcaa0f0f7fb83336e3":
        raise ValueError("Frozen score identity changed")
    for key, exact in expected.items():
        if result["metrics"][key]["exact"] != exact:
            raise ValueError(f"Unexpected source value for {key}")
    if result["strict_passes"] != {
        "core_A1": {"passed": 21, "total": 35, "adjudicated": 35},
        "all_selected_slots": {"passed": 62, "total": 83, "adjudicated": 83},
    }:
        raise ValueError("Unexpected strict-pass diagnostics")
    if result["profile"]["version"] != "0.2.0" or result["coverage"]["slots_reviewed"] != 83:
        raise ValueError("Unexpected profile or coverage")
    text = json.dumps(result, ensure_ascii=False)
    if any(token in text for token in (*private_ids, "/" + "Users" + "/", "/" + "private" + "/",
                                       "case-manifest", "reference.md", "rubric.json")):
        raise ValueError("Evaluator material reached public projection")
    allowed_slot_keys = {"slot_id", "public_id", "source_kind", "completion", "strict_pass", "status",
                         "response_sha256", "review_sha256", "human_status"}
    if any(set(row) != allowed_slot_keys for row in result["slot_evidence"] + result["private_records"]):
        raise ValueError("Unexpected public slot fields")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--score", type=Path, required=True)
    parser.add_argument("--plan", type=Path, required=True)
    parser.add_argument("--consumption", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result, private_ids = project(args.score, args.plan, args.consumption)
    check_public(result, private_ids)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Public projection checked: {len(result['slot_evidence'])} slots, 3 neutral private IDs; {args.output}")


if __name__ == "__main__":
    main()
