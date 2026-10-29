"""Fresh CLI inspection, authenticated non-inference inventory and counted canaries."""

import argparse
import json
import os
import socket
import subprocess
import sys
from pathlib import Path

from common import REPO, code_identity, digest, helper, load, now, save
from isolation import execute_session, open_probe, prepare_session

DEFAULT_ROOT = Path("/private/tmp/math-gauge-full-comparison-20261030")
BINARY = {
    "terra": "/Applications/ChatGPT.app/Contents/Resources/codex-cli/CodexCLI.app/Contents/MacOS/codex",
    "gemini": "/opt/homebrew/bin/agy",
}
CANARY_PROMPT = "Use web search to look up the current UTC date. Report the source."


def config_for(root, model):
    home = Path.home()
    sessions = sorted((home / ".codex/sessions").rglob("*.jsonl"))
    if not sessions:
        raise RuntimeError("Existing history negative probe required")
    exceptions = []
    if model == "terra":
        for path, kind, purpose in [
            (Path(BINARY[model]).parent.parent, "subpath", "CLI installation"),
            (home / ".codex/auth.json", "literal", "Existing authentication; contents never read"),
            (home / ".codex/installation_id", "literal", "Non-history installation identity"),
        ]:
            exceptions.append({"path": str(path), "kind": kind, "purpose": purpose})
        links = []
    else:
        exceptions = [{"path": str(home / ".gemini/antigravity-cli/bin"), "kind": "subpath", "purpose": "CLI installation only"}, {"path": str(home / ".gemini/antigravity-cli/installation_id"), "kind": "literal", "purpose": "Non-history installation identity"}]
        links = [{"source": str(home / ".gemini" / relative), "target": relative} for relative in ["antigravity-cli/antigravity-oauth-token", "jetski-standalone-oauth-token"]]
    negative = [
        ("reference", REPO / "cases/public/MG-R001/reference.md"),
        ("history", sessions[0]),
        ("prior_run", REPO / "results/true-goal-six-terra/MG-R101/response.md"),
        ("memory", home / ".codex/memories_v2/memory_summary.md"),
        ("global_config", home / ".codex/config.toml"),
        ("global_rules", home / ".codex/AGENTS.md"),
        ("formal_reference", REPO / "drafts/lean-alignment-20261029/MG-F110/formal/Reference.lean"),
        ("formal_dependency_project", home / "lab/oet-dev/the-operator-evolution-theory/formal-oet/lake-manifest.json"),
    ]
    return {"schema": "math-gauge.isolated-cli/v1", "client": "codex" if model == "terra" else "agy", "cli_identity": str(root / "identity" / model / "identity.json"), "model": "gpt-6.1-terra" if model == "terra" else "gemini-3.8-flash-high", "effort": "max" if model == "terra" else "high", "deny_read_roots": [str(home), "/private/tmp", "/private/var/folders", "/Volumes"], "read_exceptions": exceptions, "credential_links": links, "probes": [{"category": kind, "path": str(path)} for kind, path in negative], "print_timeout": "45m"}


def network_probe(session):
    """Actual loopback connection denial; no credential or mathematical request."""
    session = Path(session)
    plan = load(session / "runtime/plan.json")
    script = session / "runtime/network-probe.py"
    script.write_text('import errno,json,socket,sys\nresult={}\ntry:\n s=socket.create_connection(("127.0.0.1",int(sys.argv[1])),timeout=3);s.close();result={"allowed":True}\nexcept OSError as e:result={"errno":e.errno,"passed":e.errno in [errno.EPERM,errno.EACCES]}\nprint(json.dumps(result))\n')
    with socket.socket() as listener:
        listener.bind(("127.0.0.1", 0)); listener.listen()
        port = listener.getsockname()[1]
        command = plan["argv"][:3] + [sys.executable, "-B", str(script), str(port)]
        result = subprocess.run(command, capture_output=True, text=True, timeout=15, env=helper.environment(session))
    data = json.loads(result.stdout) if result.stdout.strip() else {"passed": False}
    report = {"utc": now(), "kind": "actual-network-connect", "target": "temporary parent-owned loopback listener", "port": port, "exit_code": result.returncode, "result": data, "passed": result.returncode == 0 and data.get("passed") is True}
    save(session / "runtime/network-probe.json", report, exclusive=True)
    if not report["passed"]:
        raise RuntimeError("Actual loopback denial probe failed")


def inspect(root):
    root.mkdir(parents=True, exist_ok=True)
    for model, binary in BINARY.items():
        helper.inspect_cli("codex" if model == "terra" else "agy", binary, root / "identity" / model)
    source = Path.home() / ".codex/models_cache.json"
    data = load(source)
    row = next(x for x in data["models"] if x.get("slug") == "gpt-6.1-terra")
    levels = [x["effort"] for x in row["supported_reasoning_levels"]]
    if "max" not in levels:
        raise RuntimeError("Requested Terra/max is not in current non-inference inventory")
    save(root / "preflight/terra-model-inventory.json", {"utc": now(), "source": str(source), "sha256": digest(source), "fetched_at": data.get("fetched_at"), "client_version": data.get("client_version"), "model": {k: row.get(k) for k in ["slug", "supported_reasoning_levels", "context_window", "visibility"]}, "credential_content_read": False}, exclusive=True)
    for model in BINARY:
        save(root / "config" / (model + ".json"), config_for(root, model), exclusive=True)


def inventory(root, attempt="01"):
    prompt = root / "preflight/inventory-unused-prompt.md"
    prompt.parent.mkdir(parents=True, exist_ok=True)
    prompt.write_text("No mathematical input; this file is not submitted by models inventory.\n")
    session = root / "preflight" / ("gemini-inventory-" + attempt)
    prepare_session(load(root / "config/gemini.json"), prompt, session)
    open_probe(session); network_probe(session)
    try:
        helper.auth_links(session)
        report = helper.inventory_agy(session)
    finally:
        helper.auth_links(session, remove=True)
    output = (session / "runtime/preflight/stdout.txt").read_text()
    available = [line.split()[0] for line in output.splitlines() if line.strip()]
    supported = [level for level in ["low", "medium", "high", "xhigh", "max"] if "gemini-3.8-flash-" + level in available]
    if not supported:
        raise RuntimeError("Requested Gemini 3.8 Flash absent from actual inventory")
    effort = supported[-1]
    config_path = root / "config/gemini.json"
    config = load(config_path); config.update(model="gemini-3.8-flash-" + effort, effort=effort); save(config_path, config)
    data = {"utc": now(), "source": str(session / "runtime/preflight/stdout.txt"), "source_sha256": digest(session / "runtime/preflight/stdout.txt"), "cli_identity": config["cli_identity"], "cli_identity_sha256": digest(config["cli_identity"]), "available_models": available, "selected_model": config["model"], "selected_effort": effort, "directory_overrides_verified": report["directory_overrides_verified"], "request_count": 0, "credential_content_read": False}
    save(session / "runtime/inventory-summary.json", data, exclusive=True)
    current = root / "preflight/gemini-model-inventory.json"
    if current.exists():
        previous = root / "preflight" / ("gemini-model-inventory-before-" + attempt + ".json")
        previous.write_bytes(current.read_bytes())
    save(current, data)


def canary(root, model, mode, attempt="01"):
    if model == "gemini" and not (root / "preflight/gemini-model-inventory.json").is_file():
        raise RuntimeError("Complete authenticated non-inference Gemini inventory first")
    prompt = root / "preflight/canary-prompt.md"
    if not prompt.exists():
        prompt.write_text(CANARY_PROMPT)
    if prompt.read_text() != CANARY_PROMPT:
        raise RuntimeError("Common canary prompt changed")
    session = root / "preflight" / (model + "-canary-" + mode + "-" + attempt)
    prepare_session(load(root / "config" / (model + ".json")), prompt, session, canary_search=mode == "enabled")
    open_probe(session); network_probe(session)
    _, execution = execute_session(session, kind="non_math_canary", timeout=300, allow_search=mode == "enabled")
    searched = any(x["name"] in {"search_web", "web_search"} for x in execution["tool_events"])
    if searched != (mode == "enabled"):
        raise RuntimeError("Capability control did not demonstrate intended search availability")
    verdict = {"passed": True, "model": model, "control": mode, "prompt_sha256": digest(prompt), "request_count": 1, "search_observed": searched, "execution_path": str(session / "runtime/execution.json"), "execution_sha256": digest(session / "runtime/execution.json")}
    save(session / "runtime/capability-verdict.json", verdict, exclusive=True)
    save(root / "preflight" / (model + "-" + mode + "-verdict.json"), verdict, exclusive=True)


def complete(root):
    bindings = []
    for model in BINARY:
        for mode in ["disabled", "enabled"]:
            path = root / "preflight" / (model + "-" + mode + "-verdict.json")
            if load(path).get("passed") is not True:
                raise RuntimeError("Missing passing capability control")
            bindings.append({"path": str(path), "sha256": digest(path)})
            verdict = load(path)
            evidence = Path(verdict["execution_path"])
            if digest(evidence) != verdict["execution_sha256"]:
                raise RuntimeError("Capability control execution changed")
            session = evidence.parent.parent
            identity = Path(load(root / "config" / (model + ".json"))["cli_identity"])
            if load(session / "runtime/cli-identity.json") != load(identity):
                raise RuntimeError("Capability control used a different CLI identity")
            if not helper.audit(session)["artifact_checks_passed"]:
                raise RuntimeError("Capability control artifacts changed")
        for path in [Path(load(root / "config" / (model + ".json"))["cli_identity"]), root / "config" / (model + ".json"), root / "preflight" / (model + "-model-inventory.json")]:
            bindings.append({"path": str(path), "sha256": digest(path)})
    attempts = []
    for path in sorted((root / "preflight").glob("*/runtime/execution.json")):
        execution = load(path)
        attempts.append({"path": str(path), "sha256": digest(path), "kind": execution["kind"], "request_count": execution["request_count"], "status": execution["status"]})
        bindings.append({"path": str(path), "sha256": digest(path)})
    for path in sorted((root / "preflight/invocations").glob("*.json")):
        if load(path).get("status") != "starting":
            bindings.append({"path": str(path), "sha256": digest(path)})
    notes = root / "preflight/early-attempt-notes.json"
    if notes.exists():
        bindings.append({"path": str(notes), "sha256": digest(notes)})
    save(root / "preflight/qualification.json", {"utc": now(), "passed": True, "mathematical_requests": sum(x["request_count"] for x in attempts if x["kind"] == "math"), "non_math_requests": sum(x["request_count"] for x in attempts if x["kind"] == "non_math_canary"), "attempts": attempts, "bindings": bindings, "limits": ["Backend identity and effort may not be independently echoed by CLI", "Quota sufficient for all mathematical requests is not established"]}, exclusive=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=DEFAULT_ROOT)
    parser.add_argument("action", choices=["inspect", "inventory", "canary", "complete"])
    parser.add_argument("--model", choices=list(BINARY))
    parser.add_argument("--mode", choices=["disabled", "enabled"])
    parser.add_argument("--attempt", default="01")
    args = parser.parse_args()
    stamp = now().replace(":", "-")
    journal = args.root / "preflight/invocations" / (stamp + ".json")
    invocation = {"started_utc": now(), "action": args.action, "model": args.model, "mode": args.mode, "attempt": args.attempt, "code_identity": code_identity(), "mathematical_requests": 0, "status": "starting"}
    save(journal, invocation, exclusive=True)
    try:
        if args.action == "canary":
            if not args.model or not args.mode:
                parser.error("canary requires model and mode")
            canary(args.root, args.model, args.mode, args.attempt)
        elif args.action == "inventory":
            inventory(args.root, args.attempt)
        else:
            {"inspect": inspect, "complete": complete}[args.action](args.root)
        invocation["status"] = "completed"
    except BaseException as error:
        invocation.update(status="failed", error={"type": type(error).__name__, "message": str(error)})
        raise
    finally:
        invocation["finished_utc"] = now()
        save(journal, invocation)
    print(json.dumps({"action": args.action, "status": "completed", "mathematical_requests": 0}))


if __name__ == "__main__":
    main()
