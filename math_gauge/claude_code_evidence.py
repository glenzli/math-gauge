"""Validate retained Claude Code native bytes without impersonating another client.

This is post-observation archive admission, not provider authentication or proof
that OS isolation was effective. Original CLI cleanup and per-API usage remain
separate from the first final native result and the one outer model attempt.
"""
import hashlib
import json
from datetime import datetime

SCHEMA = "math-gauge.claude-code-native-evidence/v1"
COUNTED_SCHEMA = "math-gauge.claude-code-native-evidence/v2"
OBSERVED_SCHEMA = "math-gauge.claude-code-native-evidence/v3"
LOCAL_TOOLS = {"Bash", "Read", "Write", "Edit", "Glob", "Grep"}


def validate_attempt_history(root, data, read_evidence):
    """Keep physical timeouts counted and prevent retrying a delivered answer.

    This version supports fresh independent A1 invocations only. Seeded
    selfchecks have a separate history/parent audit, not an invented A1 request.
    """
    attempts = data.get("attempts")
    selected = data.get("physical_request")
    if (data.get("schema") not in {COUNTED_SCHEMA, OBSERVED_SCHEMA} or not isinstance(attempts, list)
            or not 1 <= len(attempts) <= 3 or type(selected) is not int
            or selected != len(attempts) or data.get("effective_model_attempt") != selected
            or data.get("post_observation") is not True
            or data.get("source_raw_bytes_rewritten") is not False
            or data.get("provider_identity_verified") is not False
            or data.get("effective_sandbox_verified") is not False):
        raise ValueError("Claude Code counted attempts need their complete physical history")
    previous_cwds, sessions = set(), set()
    condition = None
    delivered = False
    for number, attempt in enumerate(attempts, 1):
        if (attempt.get("physical_request") != number or attempt.get("effective_model_attempt") != number
                or attempt.get("excluded_pure_system_failure") is not False or delivered):
            raise ValueError("Claude Code timeouts cannot be excluded or successful answers retried")
        sources = attempt.get("sources", {})
        required = {"request", "launch", "metadata", "settings", "events", "event_times", "prompt", "answer"}
        if set(sources) != required:
            raise ValueError("Claude Code attempt history lost original source evidence")
        raw = {k: read_evidence(root, sources[k]) for k in required}
        request, launch, meta = (json.loads(raw[k]) for k in ("request", "launch", "metadata"))
        events = [json.loads(line) for line in raw["events"].splitlines() if line.strip()]
        settings = json.loads(raw["settings"])
        init = meta.get("init", {})
        users = [m.get("content") for m in request.get("messages", []) if m.get("role") == "user"]
        network = settings.get("sandbox", {}).get("network", {})
        observed_tools = [b.get("name") for e in events if e.get("type") == "assistant"
                          for b in e.get("message", {}).get("content", []) if b.get("type") == "tool_use"]
        if (len(users) != 1 or users[0].encode("utf-8") != raw["prompt"]
                or launch.get("prompt_bytes") != len(raw["prompt"])
                or launch.get("prompt_sha256") != hashlib.sha256(raw["prompt"]).hexdigest()
                or meta.get("session_id") != launch.get("session_id")
                or init.get("cwd") != launch.get("cwd")
                or init.get("model") != request.get("parameters", {}).get("model")
                or set(init.get("tools", [])) != LOCAL_TOOLS
                or any(t not in LOCAL_TOOLS for t in observed_tools)
                or init.get("mcp_servers") != [] or init.get("skills") != []
                or network.get("strictAllowlist") is not True or network.get("allowedDomains") != []
                or not {"WebFetch", "WebSearch"}.issubset(settings.get("permissions", {}).get("deny", []))):
            raise ValueError("Claude Code attempt lost its exact prompt, initialization or local-tool controls")
        current = (request.get("messages"), request.get("parameters"), launch.get("timeout_seconds"))
        if condition is None:
            condition = current
        if (current != condition or launch.get("resume") is not False or meta.get("resume") is not False
                or launch.get("cwd") in previous_cwds or launch.get("session_id") in sessions):
            raise ValueError("Claude Code retry changed conditions or retained an earlier workspace/session")
        previous_cwds.add(launch.get("cwd"))
        sessions.add(launch.get("session_id"))
        finals = [e for e in events if e.get("type") == "result"]
        delivered = bool(finals and finals[0].get("subtype") == "success"
                         and finals[0].get("is_error") is False and finals[0].get("result", "").strip())
        if attempt.get("outcome") == "delivered":
            if not delivered or number != selected or sources != data.get("sources"):
                raise ValueError("Claude Code selected answer is not its first native delivery")
        elif data.get("schema") == OBSERVED_SCHEMA:
            _validate_observed_failure(attempt, raw, meta, finals)
        elif (attempt.get("outcome") != "timeout_no_final" or delivered or finals or raw["answer"].strip()
              or meta.get("process", {}).get("timed_out") is not True
              or meta.get("status_derivation", {}).get("status") != "timeout"):
            raise ValueError("Claude Code operational zero needs an original timeout without a final")
    if data.get("sources") != attempts[-1]["sources"]:
        raise ValueError("Selected native sources differ from the final admitted physical request")
    if data.get("unclosed_requests"):
        if data.get("schema") != OBSERVED_SCHEMA or delivered:
            raise ValueError("Unclosed requests cannot follow an admitted delivery")
        adoption = json.loads(read_evidence(root, data["unclosed_snapshot_adoption"]))
        if (adoption.get("post_observation") is not True
                or adoption.get("source_raw_bytes_rewritten") is not False
                or adoption.get("no_delivered_answer_scores_zero") is not True):
            raise ValueError("Unclosed snapshots need an explicit source-bound user adoption")
        for number, unclosed in enumerate(data["unclosed_requests"], selected + 1):
            if (number > 3 or unclosed.get("physical_request") != number
                    or unclosed.get("effective_model_attempt") != number
                    or unclosed.get("native_closure_observed") is not False
                    or unclosed.get("outcome") != "no_terminal_in_supplied_snapshot"):
                raise ValueError("Unclosed requests must retain actual numbering and missing closure")
            src = unclosed["sources"]
            if (set(src) - {"request", "launch", "settings", "events", "event_times", "prompt"}
                    or not {"launch", "settings", "events", "event_times", "prompt"} <= set(src)):
                raise ValueError("Unclosed snapshots cannot invent terminal metadata or an answer")
            req = json.loads(read_evidence(root, src["request"])) if "request" in src else None
            launch = json.loads(read_evidence(root, src["launch"]))
            events = [json.loads(line) for line in read_evidence(root, src["events"]).splitlines() if line.strip()]
            settings = json.loads(read_evidence(root, src["settings"]))
            network = settings.get("sandbox", {}).get("network", {})
            init_events = [e for e in events if e.get("type") == "system" and e.get("subtype") == "init"]
            tools = [b.get("name") for e in events if e.get("type") == "assistant"
                     for b in e.get("message", {}).get("content", []) if b.get("type") == "tool_use"]
            prompt = read_evidence(root, src["prompt"])
            users = [m.get("content") for m in (req or {}).get("messages", []) if m.get("role") == "user"]
            argv = launch.get("argv", [])
            options = {flag: argv[argv.index(flag) + 1] for flag in ("--model", "--effort")
                       if argv.count(flag) == 1 and argv.index(flag) + 1 < len(argv)}
            if (any(e.get("type") == "result" for e in events)
                    or req is not None and ((req.get("messages"), req.get("parameters")) != condition[:2]
                        or len(users) != 1 or users[0].encode("utf-8") != prompt)
                    or launch.get("timeout_seconds") != condition[2]
                    or prompt != raw["prompt"]
                    or options != {"--model": condition[1]["model"], "--effort": condition[1]["reasoning_effort"]}
                    or launch.get("prompt_sha256") != hashlib.sha256(prompt).hexdigest()
                    or launch.get("resume") is not False or launch.get("cwd") in previous_cwds
                    or launch.get("session_id") in sessions
                    or network.get("strictAllowlist") is not True or network.get("allowedDomains") != []
                    or any(t not in LOCAL_TOOLS for t in tools)
                    or any(set(e.get("tools", [])) != LOCAL_TOOLS or e.get("mcp_servers") != []
                           or e.get("cwd") != launch.get("cwd") for e in init_events)):
                raise ValueError("Unclosed source snapshot contains a delivery or changed retry conditions")
            previous_cwds.add(launch.get("cwd"))
            sessions.add(launch.get("session_id"))
    return {"delivered": delivered, "physical_request": selected, "effective_model_attempt": selected}


def _validate_observed_failure(attempt, raw, meta, finals):
    """Admit operational zeros from original observations, without relabeling them."""
    process, status = meta.get("process", {}), meta.get("status_derivation", {}).get("status")
    outcome = attempt.get("outcome")
    if raw["answer"].strip():
        raise ValueError("An operational zero cannot discard an original recorded answer")
    if outcome == "empty_success_without_content":
        if (len(finals) != 1 or finals[0].get("subtype") != "success"
                or finals[0].get("is_error") is not False or finals[0].get("result", "").strip()
                or finals[0].get("stop_reason") != "end_turn"
                or finals[0].get("session_id") != meta.get("session_id")
                or status != "ok" or process.get("result_before_deadline") is not True):
            raise ValueError("Empty-success zero requires an actual empty native success")
    elif outcome == "observed_deadline_without_final":
        if (finals or status != "transient_error" or process.get("result_before_deadline") is not False
                or process.get("result_seen_at") is not None
                or datetime.fromisoformat(meta["finished_at"]) < datetime.fromisoformat(meta["deadline_at"])):
            raise ValueError("Observed deadline zero needs elapsed original deadline and no final")
    elif (outcome != "timeout_no_final" or finals or process.get("timed_out") is not True or status != "timeout"):
        raise ValueError("Operational zero needs original evidence of timeout, deadline or empty delivery")


def validate_failure(root, row, read_evidence):
    """Bind a known missing final without manufacturing an ERROR terminal."""
    receipt = json.loads(read_evidence(root, row["delivery_failure"]))
    data = json.loads(read_evidence(root, receipt["native_evidence"]))
    result = validate_attempt_history(root, data, read_evidence)
    if (receipt.get("schema") != "math-gauge.claude-code-delivery-failure/v1"
            or receipt.get("case_id") != row.get("case_id")
            or receipt.get("outcome") != "delivery_failed"
            or receipt.get("mathematical_judgment") != "not_adjudicated"
            or receipt.get("additional_mathematical_penalty") != 0
            or receipt.get("source_raw_bytes_rewritten") is not False or result["delivered"]
            or row.get("response") is not None or row.get("review") is not None):
        raise ValueError("Claude Code failure must preserve missing final and unadjudicated mathematics")
    source = row.get("source", {})
    if source:
        original = json.loads(read_evidence(root, source["slot_record"]))
        if (original.get("slot_id") != row.get("id") or original.get("case_id") != row.get("case_id")
                or original.get("status") != "execution_error" or original.get("started") is not True
                or original.get("response_sha256") is not None or original.get("locked_attempt") is not None
                or source.get("candidate_input") != data["sources"]["prompt"]
                or row.get("evaluation", {}).get("completion") != {"lower": 0, "upper": 0, "exact": 0}
                or row.get("evaluation", {}).get("strict_pass") is not False):
            raise ValueError("Claude Code failure differs from the original frozen slot")
    return receipt


def validate_delivery(root, row, read_evidence):
    """Bind the adapter to its original request, launch, settings and result."""
    item = row.get("external_harness_evidence")
    if not isinstance(item, dict):
        raise ValueError("Claude Code admission needs its native evidence descriptor")
    data = json.loads(read_evidence(root, item))
    if (data.get("schema") not in {SCHEMA, COUNTED_SCHEMA, OBSERVED_SCHEMA} or data.get("post_observation") is not True
            or data.get("source_raw_bytes_rewritten") is not False
            or data.get("provider_identity_verified") is not False
            or data.get("effective_sandbox_verified") is not False
            or data.get("schema") == SCHEMA and
                (data.get("physical_request") != 1 or data.get("effective_model_attempt") != 1)):
        raise ValueError("Claude Code source admission cannot invent authentication or attempts")
    if data["schema"] in {COUNTED_SCHEMA, OBSERVED_SCHEMA}:
        if not validate_attempt_history(root, data, read_evidence)["delivered"]:
            raise ValueError("Claude Code successful admission cannot promote a timeout")
    required = ("request", "launch", "metadata", "settings", "events", "event_times", "prompt", "answer")
    sources = data.get("sources", {})
    if set(sources) != set(required):
        raise ValueError("Claude Code native source inventory is incomplete")
    raw = {key: read_evidence(root, sources[key]) for key in required}
    request, launch, meta, settings = [json.loads(raw[key]) for key in required[:4]]
    events = [json.loads(line) for line in raw["events"].splitlines() if line.strip()]
    times = [json.loads(line) for line in raw["event_times"].splitlines() if line.strip()]
    plan = json.loads(read_evidence(root, row["execution_plan"]))
    execution = json.loads(read_evidence(root, row["execution"]))
    answer = read_evidence(root, row["response"])
    prompt = read_evidence(root, row["original_input"])
    params, init, process = request.get("parameters", {}), meta.get("init", {}), meta.get("process", {})
    argv = launch.get("argv", [])

    def option(name):
        if argv.count(name) != 1 or argv.index(name) + 1 >= len(argv):
            raise ValueError("Claude Code original launch option is missing or ambiguous: " + name)
        return argv[argv.index(name) + 1]

    model, effort = option("--model"), option("--effort")
    users = [message.get("content") for message in request.get("messages", []) if message.get("role") == "user"]
    if (raw["prompt"] != prompt
            or len(users) != 1 or users[0].encode("utf-8") != prompt
            or hashlib.sha256(prompt).hexdigest() != launch.get("prompt_sha256")
            or launch.get("prompt_bytes") != len(prompt)
            or launch.get("resume") is not False or meta.get("resume") is not False
            or launch.get("session_id") != meta.get("session_id")
            or option("--session-id") != meta.get("session_id")
            or params.get("model") != model or params.get("reasoning_effort") != effort
            or init.get("model") != model or launch.get("cwd") != init.get("cwd")
            or plan.get("client") != "claude-code"
            or plan.get("schema") != "math-gauge.claude-code-execution-plan-adapter/v1"
            or plan.get("post_observation") is not True
            or plan.get("native_launch") != sources["launch"]
            or plan.get("model") != model or plan.get("effort") != effort
            or plan.get("argv") != argv or plan.get("cwd") != launch.get("cwd")
            or plan.get("local_tool_policy") != "math-gauge.local-tools-no-search/v1"
            or plan.get("tool_network_access") is not False or plan.get("search_allowed") is not False
            or execution.get("schema") != "math-gauge.claude-code-execution-observation-adapter/v1"
            or execution.get("post_observation") is not True
            or execution.get("native_metadata") != sources["metadata"]
            or execution.get("client") != "claude-code" or execution.get("kind") != "math"
            or execution.get("request_count") != 1 or execution.get("tool_mismatch") is not None
            or execution.get("exit_code") != process.get("exit_code")
            or execution.get("requested_model") != model or execution.get("requested_effort") != effort
            or execution.get("argv") != argv or execution.get("cwd") != launch.get("cwd")):
        raise ValueError("Claude Code observation differs from the actual native request or cleanup")
    if row.get("native_tool_settings") != sources["settings"]:
        raise ValueError("Claude Code settings lost their original source binding")
    offered = set(init.get("tools", []))
    if (offered != LOCAL_TOOLS or set(option("--tools").split(",")) != LOCAL_TOOLS
            or init.get("mcp_servers") != [] or init.get("skills") != []
            or init.get("slash_commands") != [] or init.get("memory_paths") is not None
            or "--strict-mcp-config" not in argv or "--disable-slash-commands" not in argv
            or option("--setting-sources") != "user"):
        raise ValueError("Claude Code offered tools or fresh-context controls differ")
    sandbox = settings.get("sandbox", {})
    network, filesystem = sandbox.get("network", {}), sandbox.get("filesystem", {})
    if (sandbox.get("enabled") is not True or sandbox.get("allowUnsandboxedCommands") is not False
            or network.get("strictAllowlist") is not True or network.get("allowedDomains") != []
            or settings.get("permissions", {}).get("blockReadsOutsideWorkingDirectories") is not True
            or not {"WebFetch", "WebSearch"}.issubset(settings.get("permissions", {}).get("deny", []))
            or settings.get("autoMemoryEnabled") is not False
            or launch.get("cwd") not in filesystem.get("allowRead", [])
            or not filesystem.get("denyRead") or not settings.get("hooks", {}).get("PreToolUse")):
        raise ValueError("Claude Code retained configuration is not local-tools/no-network")
    observed_tools = [block.get("name") for event in events if event.get("type") == "assistant"
        for block in event.get("message", {}).get("content", []) if block.get("type") == "tool_use"]
    if any(name not in offered for name in observed_tools):
        raise ValueError("Claude Code used a tool outside the retained local catalog")
    results = [event for event in events if event.get("type") == "result"]
    first_selection = data.get("first_terminal_selection")
    if len(results) != 1 and not (data["schema"] == COUNTED_SCHEMA and isinstance(first_selection, dict)):
        raise ValueError("Claude Code requires exactly one original native terminal")
    terminal = results[0]
    selected_original_first = False
    if first_selection is not None:
        lines = raw["events"].splitlines(keepends=True)
        index = next(i for i, line in enumerate(lines) if json.loads(line).get("type") == "result")
        end = sum(len(line) for line in lines[:index + 1])
        original_answer = read_evidence(root, first_selection["original_recorded_answer"])
        observed = next((t for t in times if t.get("end_offset", -1) >= end), None)
        if (data["schema"] != COUNTED_SCHEMA or first_selection.get("first_terminal_event_index") != index
                or first_selection.get("first_terminal_end_offset") != end
                or first_selection.get("ignored_later_terminals") != len(results) - 1
                or original_answer != results[-1].get("result", "").encode("utf-8")
                or meta.get("answer_extraction", {}).get("result_text_sha256")
                   != hashlib.sha256(original_answer).hexdigest()
                or observed is None or datetime.fromisoformat(observed["seen_at"])
                   > datetime.fromisoformat(meta["deadline_at"])):
            raise ValueError("Claude Code first terminal selection lost the exact original stream boundary")
        selected_original_first = True
    extraction = data.get("native_payload_extraction")
    if extraction is not None:
        lines = raw["events"].splitlines(keepends=True)
        index = next(i for i, line in enumerate(lines) if json.loads(line).get("type") == "result")
        end = sum(len(line) for line in lines[:index + 1])
        observed = next((t for t in times if t.get("end_offset", -1) >= end), None)
        if (data["schema"] != OBSERVED_SCHEMA or first_selection is not None or len(results) != 1
                or extraction.get("first_terminal_event_index") != index
                or extraction.get("first_terminal_end_offset") != end
                or extraction.get("original_recorded_answer") != sources["answer"]
                or extraction.get("selected_native_answer") != row["response"]
                or meta.get("answer_extraction", {}).get("recorded_response_sha256")
                   != hashlib.sha256(raw["answer"]).hexdigest()
                or meta.get("answer_extraction", {}).get("result_text_sha256")
                   != hashlib.sha256(answer).hexdigest()
                or terminal.get("result", "").encode("utf-8") != answer
                or observed is None or datetime.fromisoformat(observed["seen_at"])
                   > datetime.fromisoformat(meta["deadline_at"])):
            raise ValueError("Native payload extraction must bind exact terminal and original collected bytes")
    elif raw["answer"] != answer:
        raise ValueError("Claude Code recorded answer differs without explicit native extraction")
    if (terminal.get("subtype") != "success" or terminal.get("is_error") is not False
            or terminal.get("result", "").encode("utf-8") != answer or not answer.strip()
            or terminal.get("session_id") != meta.get("session_id")
            or terminal.get("stop_reason") != "end_turn"
            or meta.get("status_derivation", {}).get("status") != "ok"
            or not selected_original_first and meta.get("answer_extraction", {}).get("result_text_sha256")
               != hashlib.sha256(answer).hexdigest()
            or process.get("result_before_deadline") is not True or process.get("timed_out") is not False
            or launch.get("timeout_seconds") != meta.get("timeout_seconds")
            or not times or times[-1].get("end_offset") != len(raw["events"])
            or datetime.fromisoformat(times[-1]["seen_at"]) > datetime.fromisoformat(meta["deadline_at"])):
        raise ValueError("Claude Code final is not an exact successful delivery within its original deadline")
    return {"text": answer.decode("utf-8"), "delivered": True, "native_terminal": terminal,
        "tools_used": sorted(set(observed_tools)), "tool_calls": len(observed_tools),
        "cli_exit_code": process.get("exit_code"), "cli_killed_after_result": process.get("killed_after_result"),
        "requested_model": model, "requested_effort": effort,
        "isolation_basis": "retained_native_configuration_and_event_audit",
        "effective_sandbox_verified": False, "provider_identity_verified": False}
