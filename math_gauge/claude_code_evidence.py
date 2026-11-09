"""Validate retained Claude Code native bytes without impersonating another client.

This is post-observation archive admission, not provider authentication or proof
that OS isolation was effective. Original CLI cleanup and per-API usage remain
separate from the first final native result and the one outer model attempt.
"""
import hashlib
import json
from datetime import datetime

SCHEMA = "math-gauge.claude-code-native-evidence/v1"
LOCAL_TOOLS = {"Bash", "Read", "Write", "Edit", "Glob", "Grep"}


def validate_delivery(root, row, read_evidence):
    """Bind the adapter to its original request, launch, settings and result."""
    item = row.get("external_harness_evidence")
    if not isinstance(item, dict):
        raise ValueError("Claude Code admission needs its native evidence descriptor")
    data = json.loads(read_evidence(root, item))
    if (data.get("schema") != SCHEMA or data.get("post_observation") is not True
            or data.get("source_raw_bytes_rewritten") is not False
            or data.get("provider_identity_verified") is not False
            or data.get("effective_sandbox_verified") is not False
            or data.get("physical_request") != 1 or data.get("effective_model_attempt") != 1):
        raise ValueError("Claude Code source admission cannot invent authentication or attempts")
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
    if (raw["answer"] != answer or raw["prompt"] != prompt
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
    if len(results) != 1:
        raise ValueError("Claude Code requires exactly one original native terminal")
    terminal = results[0]
    if (terminal.get("subtype") != "success" or terminal.get("is_error") is not False
            or terminal.get("result", "").encode("utf-8") != answer or not answer.strip()
            or terminal.get("session_id") != meta.get("session_id")
            or terminal.get("stop_reason") != "end_turn"
            or meta.get("status_derivation", {}).get("status") != "ok"
            or meta.get("answer_extraction", {}).get("result_text_sha256") != hashlib.sha256(answer).hexdigest()
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
