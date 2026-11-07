"""Source-bound public written replacements over immutable legacy answers.

This module owns the replacement contract. Records owns byte verification;
scoring owns arithmetic. A retired answer never supplies a new task's credit.
"""
import re


def validate_policy(policy):
    required = {
        "schema": "math-gauge.written-replacements-policy/v1", "version": "0.1.0",
        "benchmark_version": "0.6.0", "initial_attempt_labels": ["A1"],
        "category": "written-argument", "family_aggregation": "equal",
        "local_tools_allowed": True, "search_allowed": False,
        "tool_network_access": False, "followups_replace_initial": False,
        "post_observation": True, "human_review": "pending",
        "formal_comparison_eligible": False,
    }
    if not isinstance(policy, dict) or any(policy.get(k) != v for k, v in required.items()):
        raise ValueError("Unsupported written replacement policy")
    pairs = policy.get("replacements")
    if (not isinstance(pairs, list) or len(pairs) != 1
            or pairs[0] != {"retired_case_id": "MG-GR103", "case_id": "MG-PS001",
                            "family_id": "density-sampling-quotient"}):
        raise ValueError("Written replacement differs from the selected task pair")
    return policy


def validate_inputs(data, policy):
    validate_policy(policy)
    if (not isinstance(data, dict)
            or data.get("schema") != "math-gauge.written-replacements-inputs/v1"
            or data.get("policy") != policy or data.get("benchmark_version") != "0.6.0"
            or data.get("attempt_labels") != ["A1"] or data.get("human_review") != "pending"
            or data.get("formal_comparison_eligible") is not False):
        raise ValueError("Invalid source-bound written replacement identity")
    cases, rows = data.get("case_index", []), data.get("slots", [])
    if len(cases) != 1 or len(rows) != 1:
        raise ValueError("Written replacement must retain its fixed case and A1 denominator")
    case, row = cases[0], rows[0]
    pair = policy["replacements"][0]
    criteria = case.get("criteria", [])
    if (case.get("case_id") != pair["case_id"] or case.get("family_id") != pair["family_id"]
            or case.get("replaces") != pair["retired_case_id"]
            or case.get("component") != "proofs" or case.get("source_visibility") != "public"
            or case.get("contract_kind") != "written_proof" or case.get("task_kind") != "written"
            or not criteria or len({c.get("criterion_id") for c in criteria}) != len(criteria)
            or any(not isinstance(c.get("criterion_id"), str) or type(c.get("points")) is not int
                   or c["points"] <= 0 for c in criteria)
            or case.get("total_weight") != sum(c["points"] for c in criteria)
            or any(not re.fullmatch(r"[0-9a-f]{64}", case.get(k, ""))
                   for k in ("task_sha256", "contract_sha256"))):
        raise ValueError("Written replacement changed its selected mathematical contract")
    if (row.get("case_id") != case["case_id"] or row.get("attempt_label") != "A1"
            or row.get("slot_id") != case["case_id"] + ":A1"):
        raise ValueError("Written replacement evidence must be the independent A1")
    status = row.get("status")
    if status == "not_run":
        if any(row.get(k) is not None for k in ("points", "complete", "response", "review", "source_review")):
            raise ValueError("Unrun replacement stays unknown; retired credit cannot be inherited")
    elif status == "delivery_failed":
        if row.get("points") != 0 or row.get("complete") is not False or row.get("response") is not None:
            raise ValueError("Invalid replacement delivery failure")
    elif status == "response_received":
        if (type(row.get("points")) is not int or not 0 <= row["points"] <= case["total_weight"]
                or type(row.get("complete")) is not bool
                or row["complete"] and row["points"] != case["total_weight"]
                or any(not isinstance(row.get(k), dict) for k in ("response", "review", "source_review"))):
            raise ValueError("Replacement completion conflicts with its attributed review")
    else:
        raise ValueError("Unknown written replacement delivery status")
    return data
