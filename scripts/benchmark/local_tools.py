"""Opt-in native local computation permissions; no requests or mathematical judgments."""

from pathlib import Path
import json

from common import helper, load, save

TRACK = "math-gauge.local-tools-no-search/v1"
AGY_LOCAL_TOOLS = ("finish", "run_command", "command_status", "send_command_input", "view_file",
                   "write_to_file", "replace_file_content", "multi_replace_file_content",
                   "list_dir", "grep_search", "find_by_name")
CODEX_LOCAL_EVENTS = frozenset({"command_execution", "file_change"})
AGY_LOCAL_EVENTS = frozenset(AGY_LOCAL_TOOLS + ("read_file", "write_file", "manage_task"))


def allowed_event_tool(plan, name, *, allow_search=False):
    if plan.get("local_tool_policy") == TRACK:
        if allow_search:
            return False
        return name in (AGY_LOCAL_EVENTS if plan["client"] == "agy" else CODEX_LOCAL_EVENTS)
    return ((plan["client"] == "agy" and name in {"finish", "manage_task"})
            or (allow_search and name in {"search_web", "web_search"}))


def configure_local_tools(root, plan, extension):
    """Extend only the prepared fresh session; evaluator material stays denied."""
    if plan.get("local_tool_policy"):
        raise ValueError("Local tool policy already applied")
    profile = root / "runtime/outer.sb"
    policy = profile.read_text()
    # Native shell tools apply their own per-command filesystem/network profile.
    # macOS cannot initialize that profile while inheriting the parent's sandbox.
    # Only the native sandbox launcher crosses this boundary; its child receives
    # the native restricted profile, verified by real command capability controls.
    policy += '\n(allow process-exec (with no-sandbox) (literal "/usr/bin/sandbox-exec"))\n'
    if plan["client"] == "codex":
        settings = load(root / "runtime/codex-settings.json")
        changes = {"features.shell_tool": True, "features.unified_exec": True,
                   "features.code_mode_host": True,
                   "permissions.isolated-cli.filesystem": {
                       ":minimal": "read", str(root / "input"): "read",
                       str(root / "work"): "write", str(root / "output"): "write",
                       str(root / "runtime/tmp"): "write"},
                   "permissions.isolated-cli.network.enabled": False,
                   "web_search": "disabled"}
        for runtime in ("/usr/local", "/opt/homebrew", "/Library/Frameworks/Python.framework"):
            if Path(runtime).is_dir():
                changes["permissions.isolated-cli.filesystem"][runtime] = "read"
        settings.update(changes)
        for index, value in enumerate(plan["argv"]):
            if index and plan["argv"][index - 1] == "--config":
                key = value.split("=", 1)[0]
                if key in changes:
                    plan["argv"][index] = key + "=" + helper.toml(changes[key])
            if value == "--cd":
                plan["argv"][index + 1] = str(root / "work")
        plan["cwd"] = str(root / "work")
        save(root / "runtime/codex-settings.json", settings)
    else:
        # Keep the existing helper's agent artifact identifier for audit compatibility.
        # Its actual tools and command policy are explicitly frozen here and in plan.json.
        agent = root / "work/.agents/agents/text-only.md"
        agent.write_text("---\nname: text-only\ndescription: Local computation capability configuration.\ntools:\n"
                         + "".join("  - " + name + "\n" for name in AGY_LOCAL_TOOLS)
                         + "mainAgent: true\nsubagent: false\nmodel: inherit\ncommandExecutionPolicy: sandbox\n---\n")
        settings = {"permissions": {
            "allow": ["read_file(" + str(root / "input") + ")", "read_file(" + str(root / "work") + ")",
                      "write_file(" + str(root / "work") + ")"],
            "deny": ["read_url(*)", "execute_url(*)", "mcp(*)", "unsandboxed(*)"]},
            "toolPermission": "proceed-in-sandbox", "agentMode": "accept-edits",
            "allowNonWorkspaceAccess": False, "enableTerminalSandbox": True,
            "artifactReviewPolicy": "always-proceed"}
        save(root / "runtime/task-settings.json", settings)
        save(root / "state/antigravity-cli/settings.json", settings)
        plan["expected_permission_mode"] = "proceed-in-sandbox"
        cache = str(Path.home() / ".gemini/sandbox")
        original = '(require-not (subpath ' + json.dumps(str(root)) + '))'
        policy = policy.replace(original, original + ' (require-not (subpath ' + json.dumps(cache) + '))')
        plan["native_tool_profile_cache"] = cache
        extension["changes"].append({"purpose": "Native AGY per-command sandbox profile cache only; no history or credentials", "path": cache})
    profile.write_text(policy)
    plan["local_tool_policy"] = TRACK
    plan["tool_network_access"] = False
    plan["search_allowed"] = False
    extension["changes"].append({"purpose": "User-selected local computation with no network or search",
                                  "track": TRACK, "work_directory": str(root / "work"),
                                  "agent_artifact_compatibility_name": "text-only" if plan["client"] == "agy" else None})

