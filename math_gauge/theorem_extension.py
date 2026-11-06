"""Evidence contracts for the single-answer theorem-extension component.

This owner validates selected source cases and original-answer judgments. The
shared scorer owns point conversion and aggregation; no runner lives here.
"""

import re


COMPONENT = "theorem-extension"
PUBLIC_CASE_IDS = ("MG-TX001", "MG-TX002")
POLICY_SCHEMA = "math-gauge.theorem-extension-policy/v1"
INPUT_SCHEMA = "math-gauge.theorem-extension-inputs/v1"


def validate_policy(policy):
    required = {
        "schema": POLICY_SCHEMA, "version": "0.1.0", "benchmark_version": "0.6.0",
        "initial_attempt_labels": ["A1"], "research_invitation": False,
        "followups_replace_initial": False, "research_level_maximum": 3,
        "partial_points": [0, 1, 2, 3],
        "strict_requirements": {"baseline_B": 2, "research_R": 3},
        "public_case_ids": list(PUBLIC_CASE_IDS), "private_cases": 3,
        "families": 5, "component_weight": 10, "family_aggregation": "equal",
        "baseline_points_added_to_research": False,
        "baseline_penalty_points": {"0": 2, "1": 1, "2": 0},
        "per_case_floor": None,
        "absent_extension_is_baseline_failure": False,
        "post_observation": True, "human_review": "pending",
        "formal_comparison_eligible": False,
    }
    if not isinstance(policy, dict) or any(policy.get(k) != v for k, v in required.items()):
        raise ValueError("Unsupported single-answer theorem-extension policy")
    return policy


def split_cases(cases):
    """Separate the new component from the immutable legacy selection pool."""
    return ({cid: case for cid, case in cases.items() if case["component"] != COMPONENT},
            {cid: case for cid, case in cases.items() if case["component"] == COMPONENT})


def selected_cases(cases, selection, *, current_plan=False):
    """Apply the legacy written selection without treating new research as retired."""
    from .case_selection import selected_assessment_cases
    base, extra = split_cases(cases)
    normalized = {cid: dict(case, component="exploration")
                  if case["component"] == "proofs" and
                     case.get("source_visibility", case.get("visibility")) == "private"
                  else case for cid, case in base.items()}
    selected = selected_assessment_cases(normalized, selection, current_plan=current_plan)
    return {cid: case for cid, case in cases.items() if cid in selected or cid in extra}


def validate_inputs(data, policy):
    validate_policy(policy)
    if (not isinstance(data, dict) or data.get("schema") != INPUT_SCHEMA
            or data.get("benchmark_version") != "0.6.0"
            or data.get("attempt_labels") != ["A1"]
            or data.get("research_invitation_included") is not False
            or data.get("formal_comparison_eligible") is not False
            or data.get("human_review") != "pending"):
        raise ValueError("Theorem-extension inputs must retain A1 only and explicit review status")
    cases = data.get("case_index", [])
    index = {case.get("case_id"): case for case in cases}
    if (len(cases) != 5 or len(index) != 5
            or len({case.get("family_id") for case in cases}) != 5
            or {case["case_id"] for case in cases if case.get("source_visibility") == "public"}
               != set(PUBLIC_CASE_IDS)
            or sum(case.get("source_visibility") == "private" for case in cases) != 3):
        raise ValueError("Theorem-extension inputs require the fixed two-public/three-private families")
    for cid, case in index.items():
        if (not isinstance(cid, str) or not re.fullmatch(r"[A-Za-z0-9_-]+", cid)
                or case.get("component") != COMPONENT or case.get("contract_kind") != "written_proof"
                or case.get("task_kind") != "written" or case.get("family_id") != cid
                or any(not re.fullmatch(r"[0-9a-f]{64}", case.get(key, ""))
                       for key in ("task_sha256", "contract_sha256"))
                or case.get("total_weight") != 3
                or case.get("criteria") != [
                    {"criterion_id": "local-refinement", "points": 1},
                    {"criterion_id": "substantive-extension", "points": 1},
                    {"criterion_id": "complete-structure", "points": 1}]):
            raise ValueError("Theorem-extension source contract differs from the selected tier criteria")
    rows = data.get("slots", [])
    if len(rows) != 5 or {r.get("case_id") for r in rows} != set(index):
        raise ValueError("Theorem-extension inputs must retain all five planned answers, including unrun slots")
    seen = set()
    for row in rows:
        cid = row["case_id"]
        if (row.get("slot_id") != cid + ":A1" or row["slot_id"] in seen
                or row.get("attempt_label") != "A1"):
            raise ValueError("A follow-up or repeated slot cannot enter theorem-extension scoring")
        seen.add(row["slot_id"])
        if row.get("status") == "not_run":
            if any(row.get(key) is not None for key in ("baseline_B", "research_R", "response", "review")):
                raise ValueError("An unrun research answer must remain unknown, not a mathematical failure")
        elif row.get("status") == "delivery_failed":
            if (row.get("baseline_B") is not None or row.get("research_R") != 0
                    or row.get("response") is not None or row.get("review") is not None
                    or not isinstance(row.get("failure_reason"), str) or not row["failure_reason"]
                    or not isinstance(row.get("execution"), dict)):
                raise ValueError("Missing final delivery scores zero without inventing a false mathematical judgment")
        elif row.get("status") == "response_received_execution_unverified":
            if (type(row.get("baseline_B")) is not int or row["baseline_B"] not in range(3)
                    or type(row.get("research_R")) is not int or row["research_R"] not in range(4)
                    or any(not isinstance(row.get(key), dict) for key in ("response", "review"))):
                raise ValueError("A research judgment requires separately recorded baseline and extension evidence")
            for key in ("response", "review"):
                if not re.fullmatch(r"[0-9a-f]{64}", row[key].get("sha256", "")):
                    raise ValueError("Research judgments must bind actual source bytes")
        else:
            raise ValueError("Unknown theorem-extension answer status")
    return data
