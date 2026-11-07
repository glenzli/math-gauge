"""Validate private written additions without rewriting frozen baseline inputs.

This module owns the evidence contract; scoring.py owns all point arithmetic.
"""
import re


def validate_policy(policy):
    required = {
        "schema": "math-gauge.written-additions-policy/v1", "version": "0.1.0",
        "benchmark_version": "0.6.0", "initial_attempt_labels": ["A1"],
        "private_cases": 1, "families": 1, "source_component": "exploration",
        "category": "written-argument", "family_aggregation": "equal",
        "followups_replace_initial": False, "local_tools_allowed": True,
        "search_allowed": False, "tool_network_access": False,
        "post_observation": True, "human_review": "pending",
        "formal_comparison_eligible": False,
    }
    if not isinstance(policy, dict) or any(policy.get(k) != v for k, v in required.items()):
        raise ValueError("Unsupported private written-additions policy")
    return policy


def validate_inputs(data, policy):
    validate_policy(policy)
    if (not isinstance(data, dict)
            or data.get("schema") != "math-gauge.written-additions-inputs/v1"
            or data.get("benchmark_version") != "0.6.0" or data.get("attempt_labels") != ["A1"]
            or data.get("policy") != policy or data.get("human_review") != "pending"
            or data.get("formal_comparison_eligible") is not False):
        raise ValueError("Invalid private written-additions evidence identity")
    cases = data.get("case_index", [])
    if len(cases) != policy["private_cases"]:
        raise ValueError("Written additions must retain their fixed private population")
    index = {}
    families = set()
    for case in cases:
        cid = case.get("case_id")
        criteria = case.get("criteria", [])
        if (not isinstance(cid, str) or not re.fullmatch(r"[A-Za-z0-9_-]+", cid)
                or cid in index or not isinstance(case.get("family_id"), str)
                or not case["family_id"] or case["family_id"] in families
                or case.get("component") != "exploration" or case.get("source_visibility") != "private"
                or case.get("contract_kind") not in {"written_proof", "research_exploration"} or case.get("task_kind") != "written"
                or not criteria or len({c.get("criterion_id") for c in criteria}) != len(criteria)
                or any(not isinstance(c.get("criterion_id"), str) or not c["criterion_id"]
                       or type(c.get("points")) is not int or c["points"] <= 0 for c in criteria)
                or case.get("total_weight") != sum(c["points"] for c in criteria)
                or any(not re.fullmatch(r"[0-9a-f]{64}", case.get(k, ""))
                       for k in ("task_sha256", "contract_sha256"))):
            raise ValueError("Invalid private written-additions mathematical contract")
        index[cid] = case
        families.add(case["family_id"])
    rows = data.get("slots", [])
    if len(rows) != len(index) or {r.get("case_id") for r in rows} != set(index):
        raise ValueError("Written additions must retain every fixed A1 slot")
    for row in rows:
        if row.get("slot_id") != row["case_id"] + ":A1" or row.get("attempt_label") != "A1":
            raise ValueError("Private written additions use independent A1 only")
        status = row.get("status")
        if status == "not_run":
            if any(row.get(k) is not None for k in ("points", "complete", "response", "review")):
                raise ValueError("Unrun written additions stay unknown")
        elif status == "delivery_failed":
            if (row.get("points") != 0 or row.get("complete") is not False
                    or row.get("response") is not None or not isinstance(row.get("execution"), dict)):
                raise ValueError("Invalid written delivery failure")
        elif status == "response_received_execution_unverified":
            maximum = index[row["case_id"]]["total_weight"]
            if (type(row.get("points")) is not int or not 0 <= row["points"] <= maximum
                    or type(row.get("complete")) is not bool
                    or row["complete"] and row["points"] != maximum
                    or any(not isinstance(row.get(k), dict) for k in ("response", "review", "source_review"))):
                raise ValueError("Written mathematical credit and completeness conflict")
        else:
            raise ValueError("Unknown private written-additions answer status")
    return data
