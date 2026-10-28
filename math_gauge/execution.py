"""Execution ownership: adapter invocation and immutable attempt records; no grading."""

import hashlib
import json
import os
import signal
import subprocess
import time
from datetime import datetime, timezone
from pathlib import Path

from . import __version__
from .catalog import digest_bytes, read_json, safe_file, write_json


def now():
    return datetime.now(timezone.utc).isoformat()


def runner_fingerprint():
    h = hashlib.sha256()
    for p in sorted(Path(__file__).parent.glob("*.py")):
        h.update(p.name.encode() + b"\0" + p.read_bytes())
    return h.hexdigest()


def invoke(command, request, cwd, timeout):
    if not command or not all(isinstance(x, str) for x in command):
        raise ValueError("Command must be a nonempty argv array")
    proc = subprocess.Popen(
        command,
        cwd=cwd,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        encoding="utf-8",
        start_new_session=(os.name == "posix"),
    )
    try:
        stdout, stderr = proc.communicate(
            json.dumps(request, ensure_ascii=False), timeout=timeout
        )
        return (
            stdout,
            stderr,
            proc.returncode,
            "ok" if proc.returncode == 0 and stdout.strip() else "error",
        )
    except subprocess.TimeoutExpired:
        if os.name == "posix":
            os.killpg(proc.pid, signal.SIGKILL)
        else:
            proc.kill()
        stdout, stderr = proc.communicate()
        return stdout, stderr, proc.returncode, "timeout"


def run(
    suite, destination, ids=None, replay=None, command=None, model=None, timeout=120
):
    if (replay is None) == (command is None):
        raise ValueError("Choose exactly one of replay or command")
    if timeout <= 0:
        raise ValueError("Timeout must be positive")
    selected = suite.select(ids)
    if any(c["status"] == "retired" for c in selected):
        raise ValueError("Retired cases cannot be run")
    if command is not None and (
        not isinstance(command, list)
        or not command
        or not all(isinstance(x, str) for x in command)
    ):
        raise ValueError("Command must be a nonempty argv array")
    if command is not None and not model:
        raise ValueError("Command mode requires a model/adapter label")
    responses = read_json(replay) if replay else None
    if responses is not None:
        if not isinstance(responses, dict) or any(
            not isinstance(responses.get(c["id"]), str) for c in selected
        ):
            raise ValueError(
                "Replay requires a string response for every selected case"
            )
    dest = Path(destination).resolve()
    if dest.is_relative_to(suite.root):
        raise ValueError("Run directory must be outside the question suite")
    dest.mkdir(parents=True, exist_ok=False)
    metadata = {
        "schema": "math-gauge.run/v1",
        "created_at": now(),
        "runner_version": __version__,
        "runner_sha256": runner_fingerprint(),
        "suite_id": suite.metadata["id"],
        "suite_version": suite.metadata["version"],
        "suite_sha256": suite.sha256,
        "visibility": suite.metadata["visibility"],
        "origin": "replay" if replay else "command",
        "model_label": "replay-fixture" if replay else model,
        "model_identity_verified": False,
        "timeout_seconds": timeout,
        "command": command,
        "cases": [],
    }
    for c in selected:
        metadata["cases"].append(
            {
                "id": c["id"],
                "version": c["version"],
                "track": c["track"],
                "case_approved": c["status"] == "approved"
                and c["review"]["human"] == "approved",
            }
        )
    write_json(dest / "run.json", metadata)
    failures = 0
    for c in selected:
        case_dir = dest / c["id"]
        request = suite.prepare(c, case_dir / "solver")
        started = time.monotonic()
        if responses is not None:
            stdout, stderr, exit_code, status = responses[c["id"]], "", 0, "ok"
        else:
            try:
                stdout, stderr, exit_code, status = invoke(
                    command, request, case_dir / "solver", timeout
                )
            except OSError as error:
                stdout, stderr, exit_code, status = "", str(error), None, "error"
        failures += status != "ok"
        data = stdout.encode("utf-8")
        (case_dir / "response.md").write_bytes(data)
        (case_dir / "stderr.txt").write_text(stderr, encoding="utf-8")
        write_json(
            case_dir / "record.json",
            {
                "case_id": c["id"],
                "status": status,
                "exit_code": exit_code,
                "request_sha256": digest_bytes(
                    json.dumps(request, ensure_ascii=False, sort_keys=True).encode()
                ),
                "response_sha256": digest_bytes(data),
                "elapsed_seconds": round(time.monotonic() - started, 6),
                "finished_at": now(),
            },
        )
    metadata["completed_at"] = now()
    metadata["execution_failures"] = failures
    write_json(dest / "run.json", metadata)
    return metadata


def check_lean(suite, ids=None, timeout=60):
    expected = suite.metadata["lean_toolchain"].split(":v")[-1]
    version = subprocess.run(
        ["lean", "--version"],
        cwd=suite.root,
        capture_output=True,
        text=True,
        timeout=10,
    )
    if version.returncode or f"version {expected}" not in version.stdout:
        raise ValueError(
            f"Lean {expected} required; got {version.stdout.strip()} {version.stderr.strip()}"
        )
    checks = []
    for case in suite.select(ids):
        for name in case["lean_checks"]:
            p = safe_file(suite.root, name)
            result = subprocess.run(
                ["lean", str(p)],
                cwd=suite.root,
                capture_output=True,
                text=True,
                timeout=timeout,
            )
            # This records kernel/compiler evidence for fixed audit files, not semantic agreement.
            checks.append(
                {
                    "case_id": case["id"],
                    "file": name,
                    "sha256": digest_bytes(p.read_bytes()),
                    "exit_code": result.returncode,
                    "output": result.stdout,
                    "stderr": result.stderr,
                }
            )
    return {
        "schema": "math-gauge.lean-check/v1",
        "created_at": now(),
        "suite_sha256": suite.sha256,
        "lean_version": version.stdout.strip(),
        "checks": checks,
        "all_compiled": all(c["exit_code"] == 0 for c in checks),
        "semantic_alignment_inferred": False,
    }
