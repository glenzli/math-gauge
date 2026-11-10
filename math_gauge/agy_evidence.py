"""Read-only admission of retained AGY returns and observed local-tool boundaries.

The native result, CLI cleanup and deadline are distinct source facts. This
adapter does not execute tools, grade mathematics or authenticate a backend SKU.
"""
import hashlib
import json
import math


SCHEMA = "math-gauge.agy-native-evidence/v1"
LOCAL_TOOLS = "math-gauge.local-tools-no-search/v1"
TOOLS = {"finish", "manage_task", "run_command", "command_status", "send_command_input",
         "view_file", "write_to_file", "replace_file_content", "multi_replace_file_content",
         "list_dir", "grep_search", "find_by_name", "read_file", "write_file", "edit_file"}


def _load(root, item, evidence):
    return json.loads(evidence(root, item))


def _receipt(root, row, evidence):
    data = _load(root, row["agy_native_evidence"], evidence)
    identity = row.get("slot_id", row.get("id", row["case_id"] + ":A1"))
    labels = [token for token in identity.split(":")[1:] if token in {"A1", "R1", "R2", "R3"}]
    phase = labels[0] if len(labels) == 1 else None
    if (data.get("schema") != SCHEMA or data.get("post_observation") is not True
            or data.get("source_raw_bytes_rewritten") is not False
            or data.get("case_id") != row.get("case_id") or data.get("phase") != phase
            or phase not in {"A1", "R1", "R2", "R3"}):
        raise ValueError("AGY evidence needs its original case and source-bound admission")
    selected = [(row.get("execution"), data["native_execution"]),
                (row.get("original_input"), data["candidate_input"])]
    source = row.get("source", {})
    selected += [(source.get("native_execution"), data["native_execution"]),
                 (source.get("candidate_input"), data["candidate_input"])]
    if any(item is not None and (item.get("sha256"), item.get("bytes")) !=
           (original.get("sha256"), original.get("bytes")) for item, original in selected):
        raise ValueError("AGY source selection differs from its original native request")
    return data


def _execution(root, data, evidence):
    execution = _load(root, data["native_execution"], evidence)
    plan = _load(root, data["native_plan"], evidence)
    candidate = evidence(root, data["candidate_input"])
    request = evidence(root, data["native_request"])
    messages = [json.loads(line) for line in request.splitlines()]
    events_raw = evidence(root, data["native_events"])
    events = [json.loads(line) for line in events_raw.splitlines()]
    dispatch = _load(root, data["dispatch"], evidence)
    if (plan.get("client") != "agy" or execution.get("kind") != "math"
            or dispatch.get("case_id") != data["case_id"]
            or execution.get("request_count") != 1 or execution.get("stdin_write_calls") != 1
            or execution.get("stdin_bytes_written") != len(request)
            or execution.get("argv") != plan.get("argv") or "--sandbox" not in plan.get("argv", [])
            or execution.get("cwd") != plan.get("cwd")
            or execution.get("requested_model") != plan.get("model")
            or execution.get("requested_effort") != plan.get("effort")
            or execution.get("tool_mismatch") is not None
            or plan.get("stdin_sha256") != hashlib.sha256(request).hexdigest()
            or plan.get("prompt_sha256") != hashlib.sha256(candidate).hexdigest()
            or len(messages) != 1 or messages[0].get("event") != "user"
            or messages[0].get("message", {}).get("content") != candidate.decode("utf-8")
            or execution.get("artifact_hashes", {}).get("input/task.md") != data["candidate_input"]["sha256"]
            or execution.get("artifact_hashes", {}).get("output/events.ndjson") != data["native_events"]["sha256"]):
        raise ValueError("AGY evidence changed the original native request or execution")
    return execution, plan, events, dispatch


def validate_local_tools(root, row, execution, evidence):
    """Bind the actual sandbox, native canary and registered live process probes.

    GCP may use command(*) with the native sandbox and OS boundary. The legacy
    unsandboxed(*) deny spelling is not treated as proof of that boundary.
    """
    data = _receipt(root, row, evidence)
    original = _load(root, data["native_execution"], evidence)
    if original != execution:
        raise ValueError("AGY tool evidence belongs to a different native execution")
    plan = _load(root, data["native_plan"], evidence)
    boundary = data["local_tools"]
    settings = _load(root, boundary["settings"], evidence)
    control = _load(root, boundary["native_control"], evidence)
    opened = _load(root, boundary["open_probe"], evidence)
    network = _load(root, boundary["network_probe"], evidence)
    audit = _load(root, boundary["artifact_audit"], evidence)
    report = control.get("report", {})
    control_execution = control.get("execution", {})
    if (plan.get("local_tool_policy") != LOCAL_TOOLS
            or plan.get("tool_network_access") is not False or plan.get("search_allowed") is not False
            or settings.get("enableTerminalSandbox") is not True
            or settings.get("toolPermission") != "proceed-in-sandbox"
            or execution.get("permission_mode") != "proceed-in-sandbox"
            or plan.get("expected_permission_mode") != "proceed-in-sandbox"
            or not {"read_url(*)", "execute_url(*)", "mcp(*)"}.issubset(
                settings.get("permissions", {}).get("deny", []))
            or control.get("passed") is not True or control.get("mathematical_requests") != 0
            or control_execution.get("kind") != "non_math_canary"
            or control_execution.get("requested_model") != execution.get("requested_model")
            or control_execution.get("requested_effort") != execution.get("requested_effort")
            or any(report.get(key) is not True for key in (
                "all_denials_and_allows_passed", "work_roundtrip", "tool_network_denied"))
            or report.get("source_bytes_read") != 0
            or opened.get("passed") is not True or network.get("passed") is not True
            or audit.get("artifact_checks_passed") is not True or audit.get("credential_links_remaining")
            or any(event.get("name") not in TOOLS for event in execution.get("tool_events", []))):
        raise ValueError("AGY local tools lack their original observed isolation boundary")
    reports = boundary.get("process_checks", [])
    registered = [execution.get("parent_identity", {}), *execution.get("workers", [])]
    if not registered or not reports:
        raise ValueError("AGY local tools need registered live process evidence")
    probes = {(item.get("original_path"), item.get("pid")): _load(root, item["evidence"], evidence)
              for item in reports}
    for process in registered:
        probe = probes.get((process.get("policy_evidence"), process.get("pid")))
        if (not probe or probe.get("pid") != process.get("pid") or probe.get("passed") is not True
                or probe.get("prompt_sha256") != data["candidate_input"]["sha256"]
                or not probe.get("checks") or any(item.get("passed") is not True for item in probe["checks"])):
            raise ValueError("AGY registered process lacks a successful original live boundary probe")
    if (opened.get("prompt_sha256") != data["candidate_input"]["sha256"]
            or not opened.get("checks") or any(item.get("passed") is not True for item in opened["checks"])):
        raise ValueError("AGY open probe differs from the original candidate input")
    return data


def validate_delivery(root, row, evidence):
    data = _receipt(root, row, evidence)
    execution, _, events, _ = _execution(root, data, evidence)
    answer = evidence(root, row["response"])
    terminal = _load(root, data["native_terminal_event"], evidence)
    seal = _load(root, data["native_terminal_seal"], evidence)
    qualification = _load(root, data["collection_qualification"], evidence)
    native = [event for event in events if event.get("event") == "result"]
    digest = hashlib.sha256(answer).hexdigest()
    if (data.get("outcome") != "response_received" or not answer.strip()
            or native != [terminal] or terminal.get("result", {}).get("status") != "SUCCESS"
            or terminal.get("result", {}).get("response", "").encode("utf-8") != answer
            or data.get("response", {}).get("sha256") != digest
            or evidence(root, data["response"]) != answer
            or seal.get("native_status") != "SUCCESS" or seal.get("normal_complete_delivery") is not True
            or seal.get("answer_sha256") != digest
            or seal.get("raw_terminal_sha256") != data["native_terminal_event"]["sha256"]
            or qualification.get("collection_status") != "qualified"
            or qualification.get("answer_sha256") != digest
            or not qualification.get("checks")
            or any(value is not True for value in qualification["checks"].values())):
        raise ValueError("AGY delivery lacks its exact first native SUCCESS and sealed answer")
    validate_local_tools(root, row, execution, evidence)
    return dict(delivered=True, native_status="SUCCESS", cli_status=execution.get("status"),
                cli_exit_code=execution.get("exit_code"))


def validate_failure(root, row, evidence):
    """A failed native return or proved deadline is operational zero, not a math verdict."""
    data = _receipt(root, row, evidence)
    execution, _, events, dispatch = _execution(root, data, evidence)
    if (data.get("outcome") != "delivery_failed" or row.get("response") is not None
            or row.get("review") is not None or data.get("mathematical_judgment") != "not_adjudicated"
            or data.get("additional_mathematical_penalty") != 0
            or row.get("evaluation", {}).get("completion") != dict(lower=0, upper=0, exact=0)
            or row.get("evaluation", {}).get("strict_pass") is not False):
        raise ValueError("AGY non-delivery must retain operational zero without a mathematical verdict")
    native = [event for event in events if event.get("event") == "result"]
    if data.get("native_terminal_event") is not None:
        terminal = _load(root, data["native_terminal_event"], evidence)
        seal = _load(root, data["native_terminal_seal"], evidence)
        if (execution.get("status") != "failed" or native != [terminal]
                or terminal.get("result", {}).get("status") != "ERROR"
                or seal.get("native_status") != "ERROR" or seal.get("normal_complete_delivery") is not False
                or seal.get("raw_terminal_sha256") != data["native_terminal_event"]["sha256"]):
            raise ValueError("AGY failure changed its original native ERROR")
    else:
        stopped = _load(root, data["no_native_terminal_seal"], evidence)
        elapsed, limit = execution.get("elapsed_seconds"), dispatch.get("outer_budget_seconds")
        if (native or execution.get("status") != "failed"
                or (execution.get("failure") or {}).get("type") != "TimeoutError"
                or not isinstance(elapsed, (float, int)) or not isinstance(limit, (float, int))
                or not math.isfinite(elapsed) or not math.isfinite(limit) or limit <= 0 or elapsed < limit
                or stopped.get("reason") != "Native process already stopped by execution session after deadline/failure; actual work sealed without editing"):
            raise ValueError("AGY deadline failure needs the actual fixed limit, stop and absent terminal")
    return data
