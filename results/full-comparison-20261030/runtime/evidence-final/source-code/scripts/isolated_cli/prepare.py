"""Prepare and audit isolated CLI runs; never submit a task for inference.

The generated macOS policy is a starting point whose real file-open and PID
checks must pass on the target machine. This is deliberately not a launcher.
"""

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ENVIRONMENT_KEYS = (
    "HOME", "CODEX_HOME", "USER", "LOGNAME", "SHELL", "PATH", "LANG", "LC_ALL",
    "LC_CTYPE", "TERM", "HTTPS_PROXY", "HTTP_PROXY", "ALL_PROXY", "NO_PROXY",
    "https_proxy", "http_proxy", "all_proxy", "no_proxy", "SSL_CERT_FILE",
    "SSL_CERT_DIR",
)
REQUIRED_FLAGS = {
    "codex": (
        "--ignore-user-config", "--ignore-rules", "--strict-config", "--ephemeral",
        "--skip-git-repo-check", "--json", "--model", "--cd",
        "--output-last-message", "--config",
    ),
    "agy": (
        "--gemini_dir", "--app_data_dir", "--new-project", "--agent",
        "--input-format", "--output-format", "--model", "--effort",
        "--disable-slash-commands", "--sandbox", "--print-timeout", "--log-file",
    ),
}
UNADVERTISED_AGY_FLAGS = {"--gemini_dir", "--app_data_dir"}
TEXT_ONLY_AGENT = """---
name: text-only
description: Text response capability configuration.
tools:
  - finish
mainAgent: true
subagent: false
model: inherit
commandExecutionPolicy: off
---
"""
DISABLED_CODEX_FEATURES = (
    "apps", "plugins", "memories", "browser_use", "browser_use_external",
    "computer_use", "multi_agent", "multi_agent_v2", "shell_tool", "unified_exec",
    "code_mode_host", "image_generation", "view_image", "hooks", "skill_search",
    "workspace_dependencies", "shell_snapshot", "goals", "recommended_plugins",
)


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def save(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("x", encoding="utf-8") as stream:
        json.dump(value, stream, ensure_ascii=False, indent=2)
        stream.write("\n")


def absolute(value, *, exists=True):
    if not isinstance(value, str) or not Path(value).is_absolute():
        raise ValueError("Paths must be explicitly supplied absolute paths")
    path = Path(value).resolve(strict=exists)
    if any(c in str(path) for c in ("\n", "\r", "\0")):
        raise ValueError("Control characters are not supported in paths")
    return path


def environment(run_dir=None):
    # HOME and CODEX_HOME keep their original values. No secret values are logged.
    env = {key: os.environ[key] for key in ENVIRONMENT_KEYS if key in os.environ}
    env["AGY_CLI_DISABLE_AUTO_UPDATE"] = "1"
    if run_dir is not None:
        env["TMPDIR"] = str(run_dir / "runtime/tmp")
    return env


def inspect_cli(client, binary, destination):
    """Record the selected executable, version and help without inference."""
    selected = shutil.which(binary) if not Path(binary).is_absolute() else binary
    if not selected:
        raise ValueError("CLI executable not found; supply its actual path")
    selected = Path(selected).absolute()
    resolved = selected.resolve(strict=True)
    if not resolved.is_file() or not os.access(resolved, os.X_OK):
        raise ValueError("CLI must be an executable file")
    destination = Path(destination)
    destination.mkdir(parents=True, exist_ok=False, mode=0o700)
    before = sha256(resolved)
    commands = [[str(selected), "--version"], [str(selected), "--help"]]
    if client == "codex":
        commands.append([str(selected), "exec", "--help"])
    records = []
    help_text = ""
    for index, argv in enumerate(commands):
        completed = subprocess.run(
            argv, cwd=destination, env=environment(), capture_output=True, timeout=30
        )
        for channel in ("stdout", "stderr"):
            (destination / f"{index}-{channel}.txt").write_bytes(
                getattr(completed, channel)
            )
        records.append({"argv": argv, "exit_code": completed.returncode})
        if index:
            help_text += completed.stdout.decode("utf-8", errors="replace")
            help_text += completed.stderr.decode("utf-8", errors="replace")
    absent = [
        flag for flag in REQUIRED_FLAGS[client]
        if not re.search(r"(?<![\w-])" + re.escape(flag) + r"(?![\w-])", help_text)
    ]
    # agy 1.4.9 accepted these directory flags even when short help omitted them.
    # Their actual behavior is an independent no-inference preflight gate.
    unadvertised = [x for x in absent if client == "agy" and x in UNADVERTISED_AGY_FLAGS]
    missing = [x for x in absent if x not in unadvertised]
    identity = {
        "schema": "math-gauge.cli-identity/v1", "client": client,
        "selected_binary": str(selected), "resolved_binary": str(resolved),
        "sha256": before, "version": (destination / "0-stdout.txt").read_text().strip(),
        "commands": records, "missing_required_flags": missing,
        "unadvertised_directory_flags": unadvertised,
        "directory_overrides_verified": False,
        "binary_unchanged": before == sha256(resolved), "recorded_utc": now(),
        "model_availability_verified": False,
    }
    save(destination / "identity.json", identity)
    if missing or not identity["binary_unchanged"] or any(
        item["exit_code"] for item in records
    ) or not identity["version"]:
        raise ValueError("CLI inspection failed; keep its evidence and stop")
    return identity


def toml(value):
    if isinstance(value, dict):
        return "{" + ", ".join(json.dumps(k) + " = " + toml(v) for k, v in value.items()) + "}"
    return json.dumps(value, ensure_ascii=False)


def sb_string(value):
    return json.dumps(str(value), ensure_ascii=False)


def prepare(config):
    allowed = {
        "schema", "client", "cli_identity", "prompt", "run_dir", "model", "effort",
        "deny_read_roots", "read_exceptions", "credential_links", "probes",
        "sandbox_exec", "print_timeout",
    }
    if set(config) - allowed or config.get("schema") != "math-gauge.isolated-cli/v1":
        raise ValueError("Unknown configuration keys or schema")
    client = config["client"]
    if client not in REQUIRED_FLAGS:
        raise ValueError("Client must be agy or codex")
    identity_path = absolute(config["cli_identity"])
    identity = load(identity_path)
    binary = absolute(identity["selected_binary"])
    if (
        identity.get("client") != client or identity.get("missing_required_flags") != []
        or identity.get("binary_unchanged") is not True
        or not identity.get("version") or sha256(binary) != identity["sha256"]
        or any(x["exit_code"] for x in identity["commands"])
    ):
        raise ValueError("CLI identity is missing, unsupported or changed; inspect again")
    prompt_path = absolute(config["prompt"])
    prompt = prompt_path.read_bytes()
    text = prompt.decode("utf-8")
    run_dir = absolute(config["run_dir"], exists=False)
    if run_dir.exists() or not run_dir.parent.is_dir():
        raise ValueError("Run directory must be new and its parent must already exist")
    for key in ("model", "effort"):
        if not isinstance(config.get(key), str) or not config[key].strip():
            raise ValueError(f"Explicit {key} required")
    roots = [absolute(value) for value in config["deny_read_roots"]]
    if not roots or any(not p.is_dir() or p == Path(p.anchor) for p in roots):
        raise ValueError("Non-root deny directories are required")
    exceptions = []
    for item in config.get("read_exceptions", []):
        if (
            set(item) != {"path", "kind", "purpose"}
            or item.get("kind") not in {"literal", "subpath"}
            or not item.get("purpose")
        ):
            raise ValueError("Read exceptions require literal/subpath kind and purpose")
        exceptions.append({**item, "path": str(absolute(item["path"]))})
    links = []
    for item in config.get("credential_links", []):
        if set(item) != {"source", "target"}:
            raise ValueError("Credential links contain locations only")
        source = absolute(item["source"])
        target = Path(item["target"])
        if (
            client != "agy" or target.is_absolute() or ".." in target.parts
            or str(target) in {"", "."}
        ):
            raise ValueError("Credential link target must be relative to fresh agy state")
        if not source.is_file():
            raise ValueError("Credential source must already be a file")
        links.append({"source": str(source), "target": target.as_posix()})
        exceptions.append({"path": str(source), "kind": "literal", "purpose": "authentication"})
    probes = []
    for item in config["probes"]:
        if set(item) != {"category", "path"}:
            raise ValueError("Probe entries contain category and path only")
        path = absolute(item["path"])
        if not path.is_file() or path.is_relative_to(run_dir):
            raise ValueError("Negative probes must be existing files outside the new run")
        if not any(path.is_relative_to(root) for root in roots):
            raise ValueError("Every negative probe must be covered by a deny root")
        if any(
            path == Path(x["path"])
            or (x["kind"] == "subpath" and path.is_relative_to(x["path"]))
            for x in exceptions
        ):
            raise ValueError("Read exception would expose a negative probe")
        probes.append({"category": item["category"], "path": str(path), "exists_before_run": True})
    if not {"reference", "history", "prior_run"}.issubset({x["category"] for x in probes}):
        raise ValueError("Reference, history and prior_run negative probes are required")
    sandbox = config.get("sandbox_exec") or shutil.which("sandbox-exec")
    if not sandbox:
        raise ValueError("macOS sandbox-exec unavailable; do not weaken the policy")
    sandbox = absolute(sandbox)
    if not sandbox.is_file() or not os.access(sandbox, os.X_OK):
        raise ValueError("sandbox-exec must be an existing executable")
    # Validate everything before creating the new run. Credential contents are never read.
    run_dir.mkdir(mode=0o700)
    for name in ("input", "work", "state", "output", "runtime/tmp"):
        (run_dir / name).mkdir(parents=True, mode=0o700)
    (run_dir / "input/task.md").write_bytes(prompt)
    shutil.copyfile(Path(__file__).with_name("probe.py"), run_dir / "runtime/probe.py")
    save(run_dir / "runtime/cli-identity.json", identity)
    denied = []
    for root in roots:
        exclusions = [f"(require-not (subpath {sb_string(run_dir)}))"]
        exclusions += [f"(require-not ({x['kind']} {sb_string(x['path'])}))" for x in exceptions]
        denied.append(
            "(deny file-read-data (require-all (subpath " + sb_string(root)
            + ") " + " ".join(exclusions) + "))"
        )
        denied.append(
            "(deny file-write* (require-all (subpath " + sb_string(root)
            + ") (require-not (subpath " + sb_string(run_dir) + "))))"
        )
    profile = (
        "(version 1)\n(allow default)\n" + "\n".join(denied)
        + '\n(deny network-outbound (remote ip "localhost:*"))\n'
    )
    (run_dir / "runtime/outer.sb").write_text(profile, encoding="utf-8")
    settings = {}
    argv = [str(sandbox), "-f", str(run_dir / "runtime/outer.sb"), str(binary)]
    if client == "agy":
        agent_path = run_dir / "work/.agents/agents/text-only.md"
        agent_path.parent.mkdir(parents=True)
        agent_path.write_text(TEXT_ONLY_AGENT, encoding="utf-8")
        # One JSON event occupies one physical line, with the exact task as content.
        request = {"event": "user", "message": {"content": text}}
        (run_dir / "runtime/request.ndjson").write_text(
            json.dumps(request, ensure_ascii=False) + "\n", encoding="utf-8"
        )
        settings = {
            "permissions": {"deny": [
                "read_file(*)", "write_file(*)", "read_url(*)", "execute_url(*)",
                "command(*)", "mcp(*)",
            ]},
            "toolPermission": "strict",
        }
        save(run_dir / "runtime/task-settings.json", settings)
        argv += [
            "--gemini_dir", str(run_dir / "state"),
            "--app_data_dir", "antigravity-cli", "--new-project",
            "--agent", "text-only", "--input-format", "stream-json",
            "--output-format", "stream-json", "--model", config["model"],
            "--effort", config["effort"], "--disable-slash-commands", "--sandbox",
            "--print-timeout", config.get("print_timeout", "20m"),
            "--log-file", str(run_dir / "output/agy.log"),
        ]
        stdin_path = run_dir / "runtime/request.ndjson"
    else:
        settings = {
            "model_reasoning_effort": config["effort"], "approval_policy": "never",
            "web_search": "disabled", "project_doc_max_bytes": 0,
            "default_permissions": "isolated-cli",
            "permissions.isolated-cli.filesystem": {
                ":minimal": "read", str(run_dir / "input"): "read",
                str(run_dir / "output"): "write",
            },
            "permissions.isolated-cli.network.enabled": False,
            **{"features." + key: False for key in DISABLED_CODEX_FEATURES},
            "features.skip_host_skill_discovery": True,
        }
        argv += [
            "exec", "--ignore-user-config", "--ignore-rules", "--strict-config",
            "--ephemeral", "--skip-git-repo-check", "--json",
            "--model", config["model"], "--cd", str(run_dir / "input"),
            "--output-last-message", str(run_dir / "output/response.md"),
        ]
        for key, value in settings.items():
            argv += ["--config", key + "=" + toml(value)]
        argv += ["-"]
        save(run_dir / "runtime/codex-settings.json", settings)
        stdin_path = run_dir / "input/task.md"
    save(run_dir / "runtime/probes.json", {
        "positive": str(run_dir / "input/task.md"),
        "sha256": sha256(run_dir / "input/task.md"), "negative": probes,
    })
    plan = {
        "schema": "math-gauge.isolated-cli-plan/v1", "status": "prepared-not-executed",
        "prepared_utc": now(), "client": client,
        "model": config["model"], "effort": config["effort"],
        "run_dir": str(run_dir), "prompt_source": str(prompt_path),
        "prompt_sha256": hashlib.sha256(prompt).hexdigest(),
        "argv": argv, "cwd": str(run_dir / ("work" if client == "agy" else "input")),
        "stdin_file": str(stdin_path), "stdin_sha256": sha256(stdin_path),
        "environment_keys": sorted(environment(run_dir)),
        "environment_overrides": {
            "TMPDIR": str(run_dir / "runtime/tmp"),
            "AGY_CLI_DISABLE_AUTO_UPDATE": "1",
        },
        "credential_links": links, "deny_read_roots": list(map(str, roots)),
        "read_exceptions": exceptions,
        "manual_gates": [
            "prove model/effort availability",
            "review complete deny roots and exceptions",
            "record paired non-math capability canary for this CLI/config",
            "verify actual parent and worker PIDs before submitting task",
            "record every attempt and pre-answer tool mismatch decision",
            "remove authentication links and exclude state from evidence",
        ],
    }
    if client == "agy":
        plan["manual_gates"].append(
            "apply and verify agy strict task-settings at the version-specific location"
        )
    save(run_dir / "runtime/plan.json", plan)
    save(run_dir / "runtime/attempt-ledger.json", {"attempts": [], "tool_mismatch_decisions": []})
    save(run_dir / "runtime/execution.template.json", {
        "attempt_id": None, "argv": argv,
        "requested_model": config["model"], "requested_effort": config["effort"],
        "observed_model": None, "observed_effort": None, "request_count": 0,
        "started_utc": None, "request_utc": None, "finished_utc": None,
        "exit_code": None, "parent_pid": None, "worker_pids": [],
        "model_observation_evidence": None, "tool_canary_evidence": None,
    })
    artifacts = {}
    for path in sorted(run_dir.rglob("*")):
        if path.is_file() and not path.is_symlink():
            artifacts[path.relative_to(run_dir).as_posix()] = sha256(path)
    save(run_dir / "runtime/prepared-hashes.json", artifacts)
    return plan


def auth_links(run_dir, remove=False):
    root = Path(run_dir).resolve()
    plan = load(root / "runtime/plan.json")
    changed = []
    for item in plan["credential_links"]:
        relative = Path(item["target"])
        if relative.is_absolute() or ".." in relative.parts or str(relative) in {"", "."}:
            raise ValueError("Unsafe credential link target in plan")
        target = root / "state" / relative
        if not target.parent.resolve().is_relative_to(root / "state"):
            raise ValueError("Credential link parent escapes fresh state")
        if remove:
            if target.is_symlink() and str(target.resolve()) == item["source"]:
                target.unlink()
                changed.append(item["target"])
            elif target.exists() or target.is_symlink():
                raise ValueError("Refusing to remove anything except the expected credential link")
        else:
            target.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
            target.symlink_to(item["source"])
            changed.append(item["target"])
    if remove:
        save(root / "runtime/credential-cleanup.json", {
            "utc": now(), "removed_only_links": changed,
            "original_credentials_modified": False,
        })
    return changed


def inventory_agy(run_dir):
    """Run only `models` with closed stdin, preserving a no-inference attempt.

    This phase may authenticate and use the network. It is separate from task
    submission and does not establish model/tool availability by itself.
    """
    root = Path(run_dir).resolve()
    plan = load(root / "runtime/plan.json")
    if plan["client"] != "agy":
        raise ValueError("This inventory phase is only for agy")
    pre_audit = audit(root)
    if (
        not pre_audit["artifact_checks_passed"]
        or "open-probe" not in pre_audit["runtime_reports_present"]
    ):
        raise ValueError("A matching successful real-open probe is required before inventory")
    destination = root / "runtime/preflight"
    destination.mkdir(exist_ok=False)
    state = root / "state"

    def state_entries():
        # Names only, never read or hash runtime state or credential contents.
        return sorted(
            p.relative_to(state).as_posix() for p in state.rglob("*")
            if p.is_file() and not p.is_symlink()
        )

    before = state_entries()
    argv = plan["argv"][:4] + [
        "--gemini_dir", str(state), "--app_data_dir", "antigravity-cli",
        "--log-file", str(destination / "agy.log"), "models",
    ]
    record = {
        "id": "directory-inventory", "kind": "inventory", "started_utc": now(),
        "request_count": 0, "status": "starting",
        "reason": "Verify unadvertised directory flags without task submission",
        "evidence": ["runtime/preflight/command.json", "runtime/preflight/report.json"],
    }
    ledger_path = root / "runtime/attempt-ledger.json"
    ledger = load(ledger_path)
    ledger["attempts"].append(record)
    ledger_path.write_text(json.dumps(ledger, indent=2) + "\n", encoding="utf-8")
    save(destination / "command.json", {
        "argv": argv, "cwd": plan["cwd"],
        "environment_keys": sorted(environment(root)), "stdin": "DEVNULL",
        "model_inference_requested": False,
    })
    code = None
    error = None
    try:
        with (
            (destination / "stdout.txt").open("xb") as out,
            (destination / "stderr.txt").open("xb") as err,
        ):
            completed = subprocess.run(
                argv, cwd=plan["cwd"], env=environment(root),
                stdin=subprocess.DEVNULL, stdout=out, stderr=err, timeout=120,
            )
            code = completed.returncode
    except (OSError, subprocess.SubprocessError) as exc:
        error = type(exc).__name__ + ": " + str(exc)
    after = state_entries()
    identity = load(root / "runtime/cli-identity.json")
    unchanged = sha256(identity["selected_binary"]) == identity["sha256"]
    generated = sorted(set(after) - set(before))
    generated_in_app_data = [name for name in generated if name.startswith("antigravity-cli/")]
    report = {
        "exit_code": code, "error": error, "finished_utc": now(),
        "state_root": str(state), "new_state_file_names": generated,
        "new_app_data_file_names": generated_in_app_data,
        "directory_overrides_verified": (
            code == 0 and bool(generated_in_app_data) and unchanged
        ),
        "cli_sha256_unchanged": unchanged, "request_count": 0,
        "model_inference_requested": False, "model_availability_verified": False,
        "limits": (
            "New files in the requested fresh state/antigravity-cli plus successful "
            "models command. OS probes and explicit denied global state remain "
            "required; no task was submitted. No new app-data file means "
            "inconclusive, not proof that flags are unsupported."
        ),
    }
    save(destination / "report.json", report)
    record.update(
        status="completed" if report["directory_overrides_verified"] else "failed",
        finished_utc=report["finished_utc"],
    )
    ledger_path.write_text(json.dumps(ledger, indent=2) + "\n", encoding="utf-8")
    if not report["directory_overrides_verified"]:
        raise ValueError("AGY directory preflight failed; preserve evidence and stop")
    return report


def audit(run_dir):
    root = Path(run_dir).resolve()
    plan = load(root / "runtime/plan.json")
    expected = load(root / "runtime/prepared-hashes.json")
    errors = []
    prepared_names = {
        "input/task.md", "runtime/probe.py", "runtime/cli-identity.json",
        "runtime/outer.sb", "runtime/probes.json", "runtime/plan.json",
        "runtime/attempt-ledger.json", "runtime/execution.template.json",
    }
    prepared_names.update(
        {"runtime/request.ndjson", "runtime/task-settings.json", "work/.agents/agents/text-only.md"}
        if plan["client"] == "agy" else {"runtime/codex-settings.json"}
    )
    if set(expected) != prepared_names:
        errors.append("Prepared manifest differs from the fixed artifact whitelist")
    for name in prepared_names.intersection(expected):
        digest = expected[name]
        # The ledger changes with attempts; retain its initial hash as provenance.
        if name == "runtime/attempt-ledger.json":
            continue
        path = root / name
        if (
            path.is_symlink() or not path.resolve().is_relative_to(root)
            or not path.is_file() or sha256(path) != digest
        ):
            errors.append("Prepared artifact changed: " + name)
    identity = load(root / "runtime/cli-identity.json")
    if sha256(identity["selected_binary"]) != identity["sha256"]:
        errors.append("CLI binary changed")
    if {p.name for p in (root / "input").iterdir()} != {"task.md"}:
        errors.append("Candidate input directory has unexpected files")
    reports = {}
    probes = load(root / "runtime/probes.json")
    probe_paths = [probes["positive"]] + [x["path"] for x in probes["negative"]]
    for name in ("open-probe", "parent-pid-check", "worker-pid-check"):
        path = root / "runtime" / (name + ".json")
        if path.is_file():
            reports[name] = load(path)
            report = reports[name]
            checks = report.get("checks", [])
            kind = "actual-file-open" if name == "open-probe" else "live-pid-policy-query"
            role = None if name == "open-probe" else name.split("-")[0]
            if (
                report.get("passed") is not True
                or report.get("prompt_sha256") != plan["prompt_sha256"]
                or report.get("kind") != kind or report.get("role") != role
                or [x.get("path") for x in checks] != probe_paths
                or not all(x.get("passed") is True for x in checks)
            ):
                errors.append("Failed or mismatched OS evidence: " + name)
    links_remaining = [
        x["target"] for x in plan["credential_links"]
        if (root / "state" / x["target"]).is_symlink()
    ]
    ledger = load(root / "runtime/attempt-ledger.json")
    for item in ledger.get("tool_mismatch_decisions", []):
        if (
            item.get("answer_reviewed_at_decision") is not False
            or item.get("selection_based_on_answer") is not False
            or not item.get("decided_utc") or not item.get("evidence")
        ):
            errors.append("Tool mismatch decision lacks pre-answer evidence")
    manifest = []
    # Only these data-free runtime records and raw outputs are eligible for review.
    names = list(prepared_names) + [
        "runtime/prepared-hashes.json", "runtime/execution.json",
        "runtime/credential-cleanup.json",
    ]
    names += ["runtime/" + x + ".json" for x in reports]
    names += ["runtime/preflight/" + x for x in (
        "command.json", "report.json", "stdout.txt", "stderr.txt", "agy.log",
    )]
    names += ["output/" + x for x in (
        "events.ndjson", "stderr.txt", "response.md", "result-event.json", "agy.log",
    )]
    for name in sorted(set(names)):
        path = root / name
        if path.is_file() and not path.is_symlink() and path.resolve().is_relative_to(root):
            manifest.append({"path": name, "bytes": path.stat().st_size, "sha256": sha256(path)})
    directory_report = root / "runtime/preflight/report.json"
    directory_verified = (
        load(directory_report).get("directory_overrides_verified") is True
        if directory_report.is_file() else False
    )
    return {
        "audit_utc": now(), "artifact_checks_passed": not errors, "errors": errors,
        "runtime_reports_present": sorted(reports), "runtime_reports_complete": len(reports) == 3,
        "agy_directory_preflight_complete": directory_verified if plan["client"] == "agy" else None,
        "credential_links_remaining": links_remaining, "requested_model": plan["model"],
        "requested_effort": plan["effort"], "argv": plan["argv"], "attempt_ledger": ledger,
        "files": manifest, "state_included": False, "isolation_certified": False,
        "limits": (
            "Local artifact/probe-record audit only. Verify PID identities, effective "
            "tool canaries, model identity, attempt completeness and the one actual "
            "stdin submission from raw evidence. This helper never submits the "
            "mathematical task."
        ),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="action", required=True)
    inspect = commands.add_parser("inspect")
    inspect.add_argument("--client", choices=sorted(REQUIRED_FLAGS), required=True)
    inspect.add_argument("--binary", required=True)
    inspect.add_argument("--out", required=True)
    prep = commands.add_parser("prepare")
    prep.add_argument("--config", required=True)
    for action in ("audit", "link-auth", "unlink-auth", "inventory-agy"):
        item = commands.add_parser(action)
        item.add_argument("--run-dir", required=True)
        if action == "audit":
            item.add_argument("--out", required=True)
    args = parser.parse_args()
    try:
        if args.action == "inspect":
            result = inspect_cli(args.client, args.binary, args.out)
        elif args.action == "prepare":
            result = prepare(load(args.config))
        elif args.action == "audit":
            result = audit(args.run_dir)
            save(args.out, result)
            if not result["artifact_checks_passed"]:
                return 1
        elif args.action == "inventory-agy":
            result = inventory_agy(args.run_dir)
        else:
            result = {"links": auth_links(args.run_dir, remove=args.action == "unlink-auth")}
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return 0
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        print("isolated-cli: " + str(error), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
