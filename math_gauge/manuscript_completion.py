"""Source-contract validation for mathematical manuscript tasks.

This module validates judgments, not mathematics. records.py binds original
bytes and execution evidence; scoring.py owns all aggregation.
"""
import re
import json
from pathlib import PurePosixPath


def validate_policy(policy):
    required = {"schema": "math-gauge.manuscript-completion-policy/v1",
        "benchmark_version": "0.6.0", "initial_attempt_labels": ["A1"],
        "source_component": "manuscript-completion",
        "category": "manuscript-completion", "component_weight": 10,
        "family_aggregation": "equal", "ordinary_claim_cap_points": 50,
        "followups_replace_initial": False, "local_tools_allowed": True,
        "search_allowed": False, "tool_network_access": False,
        "post_observation": True, "human_review": "pending", "formal_comparison_eligible": False}
    if not isinstance(policy, dict) or any(policy.get(k) != v for k, v in required.items()):
        raise ValueError("Unsupported manuscript-completion policy")
    population = {"0.1.0": (0, 1, 1), "0.2.0": (0, 2, 2),
                  "0.3.0": (1, 2, 3), "0.4.0": (1, 3, 4)}.get(policy.get("version"))
    public_ids = policy.get("public_case_ids", [])
    expected_public_ids = ["MG-MCP003"] if policy.get("version") in {"0.3.0", "0.4.0"} else []
    if (population != (policy.get("public_cases", 0), policy.get("private_cases"), policy.get("families"))
            or public_ids != expected_public_ids):
        raise ValueError("Manuscript population must match its selected component version")
    return policy


def validate_fidelity(case, row):
    """Validate an explicitly selected, source-bound case judgment, not prose.

    The first case has no fidelity supplement. Unknown answers never inherit a
    fidelity finding from another candidate or the evaluator's reference.
    """
    policy, review = case.get("fidelity_policy"), row.get("fidelity")
    if policy is None:
        if review is not None:
            raise ValueError("Fidelity adjustment needs its selected case contract")
        return None
    if (policy.get("schema") != "math-gauge.manuscript-fidelity-policy/v1"
            or policy.get("version") != "0.2.0" or policy.get("case_id") != case["case_id"]
            or policy.get("task_sha256") != case["task_sha256"]
            or policy.get("adjustment_cap_points") != 50
            or policy.get("level_adjustments") != {"F_PASS": 0, "P30": 30, "P50": 50}
            or policy.get("strict_requires_fidelity_pass") is not True
            or not isinstance(case.get("fidelity_policy_source"), dict)):
        raise ValueError("Invalid source-bound manuscript fidelity contract")
    if row.get("points") is None:
        if review is not None:
            raise ValueError("Unknown manuscript answer cannot acquire a fidelity verdict")
        return None
    if (not isinstance(review, dict) or review.get("level") not in policy["level_adjustments"]
            or type(review.get("adjustment_points")) is not int
            or review["adjustment_points"] != policy["level_adjustments"][review["level"]]
            or type(review.get("passed")) is not bool
            or review["passed"] != (review["level"] == "F_PASS")
            or review.get("reliable_acceptance") is not review["passed"]
            or not isinstance(review.get("root_cause"), str) or not review["root_cause"]
            or not isinstance(review.get("source"), dict)
            or not review["passed"] and row.get("complete") is not False):
        raise ValueError("Manuscript fidelity judgment contradicts its frozen case supplement")
    return review


def validate_inputs(data, policy):
    validate_policy(policy)
    if (not isinstance(data, dict) or data.get("schema") != "math-gauge.manuscript-completion-inputs/v1"
            or data.get("benchmark_version") != "0.6.0" or data.get("attempt_labels") != ["A1"]
            or data.get("policy") != policy or not isinstance(data.get("model_label"), str)
            or data.get("human_review") != "pending" or data.get("formal_comparison_eligible") is not False):
        raise ValueError("Invalid manuscript-completion evidence identity")
    cases = data.get("case_index", [])
    if len(cases) != policy["private_cases"] + policy.get("public_cases", 0):
        raise ValueError("Manuscript tasks retain their fixed public/private population")
    index = {}
    for case in cases:
        cid, criteria = case.get("case_id"), case.get("criteria", [])
        if (not isinstance(cid, str) or not re.fullmatch(r"[A-Za-z0-9_-]+", cid) or cid in index
                or not isinstance(case.get("family_id"), str) or not case["family_id"]
                or case.get("component") != "manuscript-completion"
                or case.get("source_visibility") != ("public" if cid in policy.get("public_case_ids", []) else "private")
                or case.get("contract_kind") != "research_exploration" or case.get("task_kind") != "written"
                or not criteria or len({c.get("criterion_id") for c in criteria}) != len(criteria)
                or any(not isinstance(c.get("criterion_id"), str) or not c["criterion_id"]
                    or type(c.get("points")) is not int or c["points"] <= 0 for c in criteria)
                or case.get("total_weight") != 100 or sum(c["points"] for c in criteria) != 100
                or any(not re.fullmatch(r"[0-9a-f]{64}", case.get(k, ""))
                       for k in ("task_sha256", "contract_sha256"))):
            raise ValueError("Invalid manuscript mathematical contract")
        index[cid] = case
    if not set(policy.get("public_case_ids", [])) <= set(index):
        raise ValueError("Manuscript evidence is missing its selected public task")
    rows = data.get("slots", [])
    if len(rows) != len(index) or {r.get("case_id") for r in rows} != set(index):
        raise ValueError("Manuscript evidence must retain every independent A1 slot")
    for row in rows:
        if row.get("slot_id") != row["case_id"] + ":A1" or row.get("attempt_label") != "A1":
            raise ValueError("Manuscript completion uses independent A1 only")
        status = row.get("status")
        if status == "not_run":
            if any(row.get(k) is not None for k in ("points", "complete", "response", "review", "execution")):
                raise ValueError("Unrun manuscript task must remain unknown")
        elif status == "execution_authentication_failed":
            if (any(row.get(k) is not None for k in ("points", "complete", "response", "review"))
                    or any(not isinstance(row.get(k), dict) for k in
                        ("execution", "execution_result", "execution_plan", "native_request",
                         "native_events", "candidate_input", "physical_request_ledger"))):
                raise ValueError("Unverified execution is unknown mathematics, with retained native evidence")
        elif status == "response_received_execution_unverified":
            if (type(row.get("points")) is not int or not 0 <= row["points"] <= 100
                    or type(row.get("complete")) is not bool or row["complete"] and row["points"] != 100
                    or any(not isinstance(row.get(k), dict) for k in ("response", "review", "execution"))):
                raise ValueError("Manuscript credit contradicts the retained judgment")
        else:
            raise ValueError("Unknown manuscript answer status")
        validate_fidelity(index[row["case_id"]], row)
    return data


def validate_system_exclusion(execution, events, reason, stderr):
    """Only the evidenced historical controller/headless failures are excluded.

    Output exhaustion and normally delivered answers are effective model attempts.
    An operator-written exclusion label alone never establishes a system failure.
    """
    metadata = {k: execution.get(k) for k in ("status", "failure", "failure_reason", "stop_reason", "error")}
    metadata["native_failures"] = [e for e in events if e.get("type", e.get("event"))
        in {"turn.failed", "error", "result"}]
    text = json.dumps(metadata, ensure_ascii=False).lower()
    if any(marker in text for marker in ("max_output_tokens", "max_tokens", "output_exhausted",
            "output_token_limit", "output limit", "token budget", '"length"')):
        raise ValueError("Output exhaustion consumes a model attempt; it is not a pure system exclusion")
    failure = execution.get("failure") or {}
    terminal = [e for e in events if e.get("type", e.get("event")) in {"turn.completed", "turn.failed", "result"}]
    if execution.get("status") != "failed" or failure.get("type") != "RuntimeError":
        raise ValueError("System exclusion lacks its actual failed controller evidence")
    if reason == "controller_interruption_before_first_complete_answer":
        if (terminal or execution.get("exit_code") != -15 or failure.get("message") not in {
                "Unexpected tool or permission event", "Actual process policy query failed",
                "Native sandbox launcher did not transition within one second"}):
            raise ValueError("Controller exclusion contradicts its original failure or native terminal")
        if failure["message"] == "Unexpected tool or permission event":
            if (execution.get("tool_mismatch") or {}).get("tool") != "mcp_tool_call":
                raise ValueError("Excluded discovery mismatch is not the recorded catalog failure")
            completed = [e["item"] for e in events if e.get("type") == "item.completed"
                and isinstance(e.get("item"), dict) and e["item"].get("type") == "mcp_tool_call"]
            if not completed:
                raise ValueError("Catalog exclusion needs original empty metadata results")
            for item in completed:
                result = item.get("result") or {}
                content = result.get("content", [])
                key = {"list_mcp_resources": "resources", "list_mcp_resource_templates": "resourceTemplates"}.get(item.get("tool"))
                if (key is None or item.get("server") != "codex" or item.get("arguments") != {}
                        or item.get("error") is not None or len(content) != 1 or not isinstance(content[0], dict)
                        or content[0].get("type") != "text" or json.loads(content[0]["text"]) != {key: []}):
                    raise ValueError("Catalog exclusion cannot hide real resource access")
    elif reason == "controller_local_edit_alias_false_positive":
        mismatch = execution.get("tool_mismatch") or {}
        edits = [e["step_update"] for e in events if e.get("event") == "step_update"
            and e.get("step_update", {}).get("tool_name") == "edit_file"]
        expected_prefix = execution.get("cwd", "")
        # The native edit event must target its own work area. A controller label
        # cannot exclude a real outside-file request or a normally delivered reply.
        if (failure.get("message") != "Unexpected tool or permission event"
                or execution.get("exit_code") != -9 or mismatch.get("tool") != "edit_file"
                or mismatch.get("answer_reviewed_at_decision") is not False
                or mismatch.get("selection_based_on_answer") is not False
                or not expected_prefix or not edits
                or any(not PurePosixPath(e.get("tool_info", {}).get("parameters", {}).get("Path", "")).is_relative_to(expected_prefix)
                    or ".." in PurePosixPath(e.get("tool_info", {}).get("parameters", {}).get("Path", "")).parts for e in edits)
                or len(terminal) != 1 or terminal[0].get("event") != "result"
                or terminal[0].get("result", {}).get("status") != "ERROR"
                or terminal[0].get("result", {}).get("response", "") != ""):
            raise ValueError("Local edit alias exclusion lacks its original failed in-workspace event")
    elif reason == "native_empty_reply_after_headless_permission_denial":
        if (len(terminal) != 1 or terminal[0].get("event") != "result"
                or terminal[0].get("result", {}).get("status") != "SUCCESS"
                or terminal[0].get("result", {}).get("response") != ""
                or execution.get("exit_code") != -9
                or failure.get("message") != "CLI failed or violated tools policy"
                or "headless mode cannot prompt" not in stderr or "auto-denied" not in stderr):
            raise ValueError("Headless exclusion needs the original empty result and permission failure")
    else:
        raise ValueError("Unsupported system exclusion reason")
