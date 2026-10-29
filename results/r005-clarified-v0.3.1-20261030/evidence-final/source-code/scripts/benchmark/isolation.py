"""Compose existing CLI preparation with live process and event checks."""

import collections
import ctypes
import json
import os
import signal
import subprocess
import sys
import threading
import time
from pathlib import Path

from common import REPO, digest, helper, load, now, save


def prepare_session(config, prompt, destination, *, canary_search=False):
    """No inference. Keep base helper hashes plus explicit extension history."""
    config = dict(config, prompt=str(Path(prompt).resolve()), run_dir=str(Path(destination).resolve()))
    proxy_exception = config.pop("proxy_exception", None)
    plan = helper.prepare(config)
    root = Path(destination)
    original = load(root / "runtime/prepared-hashes.json")
    extension = {"utc": now(), "base_prepared_sha256": original, "changes": []}
    if proxy_exception is not None:
        if plan["client"] != "codex" or proxy_exception.get("endpoint") != "127.0.0.1:7897":
            raise ValueError("Only the verified existing Terra system proxy exception is supported")
        for evidence in proxy_exception["evidence"]:
            if digest(evidence["path"]) != evidence["sha256"]:
                raise ValueError("System proxy evidence changed")
        profile = root / "runtime/outer.sb"
        # macOS SBPL accepts only "localhost" or "*", not a literal IPv4 host.
        profile.write_text(profile.read_text() + '\n(allow network-outbound (remote ip "localhost:7897"))\n')
        extension["changes"].append({"purpose": "Verified existing model-service system proxy; other loopback ports remain denied", **proxy_exception})
        plan["proxy_exception"] = {**proxy_exception, "sbpl_address": "localhost:7897", "scope_note": "SBPL loopback address family alias; exact port only"}
    if plan["client"] == "codex":
        settings = load(root / "runtime/codex-settings.json")
        additions = {"sqlite_home": str(root / "state/sqlite"), "log_dir": str(root / "state/log")}
        settings.update(additions)
        if canary_search:
            settings["web_search"] = "live"
            settings["features.code_mode_host"] = True
            for index, value in enumerate(plan["argv"]):
                if value.startswith("web_search="):
                    plan["argv"][index] = 'web_search="live"'
                if value.startswith("features.code_mode_host="):
                    plan["argv"][index] = 'features.code_mode_host=true'
        save(root / "runtime/codex-settings.json", settings)
        for key, value in additions.items():
            plan["argv"][-1:-1] = ["--config", key + "=" + helper.toml(value)]
        # Existing successful CLI requires writeback of this non-secret identity.
        installation = Path.home() / ".codex/installation_id"
        profile = root / "runtime/outer.sb"
        profile.write_text(profile.read_text() + '\n(allow file-write* (literal ' + json.dumps(str(installation)) + '))\n')
        extension["changes"].append({"purpose": "Fresh SQLite/log locations and exact non-history installation identity writeback", "installation_id_path": str(installation), "installation_id_before_sha256": digest(installation)})
    else:
        settings = load(root / "runtime/task-settings.json")
        save(root / "state/antigravity-cli/settings.json", settings)
        extension["changes"].append({"purpose": "Apply the existing strict task-settings to AGY's actual fresh-state location", "settings_sha256": digest(root / "state/antigravity-cli/settings.json")})
        if canary_search:
            agent = root / "work/.agents/agents/text-only.md"
            agent.write_text(agent.read_text().replace("  - finish\n", "  - finish\n  - search_web\n"))
            extension["changes"].append({"purpose": "Positive non-math capability control only", "added_tool": "search_web"})
    save(root / "runtime/plan.json", plan)
    save(root / "runtime/prepared-hashes.json", {name: digest(root / name) for name in original})
    save(root / "runtime/preparation-extension.json", extension, exclusive=True)
    return plan


def open_probe(root):
    root = Path(root)
    plan = load(root / "runtime/plan.json")
    command = plan["argv"][:3] + [sys.executable, "-B", str(root / "runtime/probe.py"), "--manifest", str(root / "runtime/probes.json"), "--out", str(root / "runtime/open-probe.json")]
    completed = subprocess.run(command, capture_output=True, env=helper.environment(root), timeout=30)
    save(root / "runtime/open-probe-command.json", {"argv": command, "exit_code": completed.returncode, "stderr": completed.stderr.decode(errors="replace")})
    if completed.returncode or not load(root / "runtime/open-probe.json")["passed"]:
        raise RuntimeError("Actual isolated file-open probe failed")


def process_tree():
    result = subprocess.run(["/bin/ps", "-axo", "pid=,ppid=,comm="], capture_output=True, text=True, timeout=10)
    if result.returncode:
        raise RuntimeError("Cannot inspect process identities")
    rows = {}
    for line in result.stdout.splitlines():
        fields = line.strip().split(None, 2)
        if len(fields) == 3:
            pid, parent = map(int, fields[:2])
            rows[pid] = {"pid": pid, "ppid": parent, "executable_name": fields[2]}
    return rows


def descendants(rows, pid):
    result, pending = [], [pid]
    while pending:
        parent = pending.pop()
        children = [row for row in rows.values() if row["ppid"] == parent]
        result.extend(children)
        pending.extend(row["pid"] for row in children)
    return result


def executable(pid):
    library = ctypes.CDLL("/usr/lib/libproc.dylib")
    library.proc_pidpath.argtypes = [ctypes.c_int, ctypes.c_void_p, ctypes.c_uint32]
    buffer = ctypes.create_string_buffer(4096)
    if library.proc_pidpath(pid, buffer, len(buffer)) <= 0:
        raise RuntimeError("Cannot identify actual process executable")
    return buffer.value.decode()


def check_pid(root, pid, role, suffix=""):
    root = Path(root)
    output = root / "runtime" / (role + "-pid-check" + suffix + ".json")
    command = [sys.executable, "-B", str(root / "runtime/probe.py"), "--manifest", str(root / "runtime/probes.json"), "--pid", str(pid), "--role", role, "--out", str(output)]
    result = subprocess.run(command, capture_output=True, timeout=20)
    if pid not in process_tree():
        raise ProcessLookupError("Process exited before live policy query completed")
    if result.returncode or not load(output)["passed"]:
        raise RuntimeError("Actual process policy query failed")
    return {"pid": pid, "executable": executable(pid), "policy_evidence": str(output)}


def stop_process(proc):
    if proc.poll() is not None:
        return
    children = descendants(process_tree(), proc.pid)
    for pid in [row["pid"] for row in reversed(children)] + [proc.pid]:
        try:
            os.kill(pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
    try:
        proc.wait(timeout=10)
    except subprocess.TimeoutExpired:
        for pid in [row["pid"] for row in reversed(children)] + [proc.pid]:
            try:
                os.kill(pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        proc.wait(timeout=10)


def execute_session(root, *, kind, timeout=2700, allow_search=False):
    """One stdin submission. The caller must enforce the mathematical release gate."""
    root = Path(root)
    plan = load(root / "runtime/plan.json")
    if kind not in {"math", "non_math_canary"} or (kind == "math" and allow_search):
        raise ValueError("Invalid execution kind/tool configuration")
    if (root / "runtime/execution.json").exists():
        raise ValueError("Session already attempted; never retry in-place")
    audit = helper.audit(root)
    if not audit["artifact_checks_passed"] or not load(root / "runtime/open-probe.json")["passed"]:
        raise RuntimeError("Prepared session or actual-open proof invalid")
    if digest(plan["stdin_file"]) != plan["stdin_sha256"]:
        raise RuntimeError("Frozen stdin changed")
    if plan["client"] == "agy" and digest(root / "state/antigravity-cli/settings.json") != digest(root / "runtime/task-settings.json"):
        raise RuntimeError("Actual AGY settings differ from the frozen strict configuration")
    execution = {"kind": kind, "started_utc": now(), "requested_model": plan["model"], "requested_effort": plan["effort"], "observed_model": None, "observed_effort": None, "request_count": 0, "status": "starting", "argv": plan["argv"], "cwd": plan["cwd"], "parent_pid": None, "workers": [], "tool_events": [], "tool_mismatch": None, "final_answer_reviewed": False}
    save(root / "runtime/execution.json", execution, exclusive=True)
    ledger_path = root / "runtime/attempt-ledger.json"
    ledger = load(ledger_path)
    attempt = {"id": kind + "-1", "kind": kind, "started_utc": now(), "request_count": 0, "status": "starting", "reason": "One preplanned fresh-session submission", "evidence": ["runtime/execution.json", "output/events.ndjson"]}
    ledger["attempts"].append(attempt)
    save(ledger_path, ledger)
    identity = load(root / "runtime/cli-identity.json")
    baseline = process_tree()
    proc, threads, parse_errors = None, [], []
    metrics = {"events": collections.Counter(), "usage": None, "result_count": 0}
    mismatch = threading.Event()
    started = time.monotonic()

    def output_reader():
        with (root / "output/events.ndjson").open("xb") as stream:
            for raw in iter(proc.stdout.readline, b""):
                stream.write(raw); stream.flush()
                try:
                    event = json.loads(raw)
                except (ValueError, UnicodeDecodeError):
                    parse_errors.append("non-JSON event")
                    continue
                tag = event.get("type", event.get("event"))
                metrics["events"][tag] += 1
                tool = None
                if plan["client"] == "codex":
                    item = event.get("item", {})
                    typ = item.get("type") if isinstance(item, dict) else None
                    if typ and typ not in {"agent_message", "reasoning", "error", "todo_list"}:
                        tool = typ
                    if tag == "turn.completed":
                        metrics["usage"] = event.get("usage")
                    for key, target in [("model", "observed_model"), ("reasoning_effort", "observed_effort"), ("effort", "observed_effort")]:
                        if isinstance(event.get(key), str):
                            execution[target] = event[key]
                else:
                    if tag == "init":
                        init = event.get("init", {})
                        execution["observed_model"] = init.get("model")
                        execution["permission_mode"] = init.get("permission_mode")
                        execution["observed_agent"] = init.get("agent")
                        if init.get("permission_mode") != "strict" or init.get("agent") != "text-only":
                            tool = "UNEXPECTED_AGENT_OR_PERMISSION_MODE"
                    step = event.get("step_update", {})
                    if step.get("step_type") == "tool":
                        tool = step.get("tool_name", "UNKNOWN_TOOL")
                    if tag == "result":
                        metrics["result_count"] += 1
                        result = event.get("result", {})
                        metrics["usage"] = result.get("usage")
                        execution["result_status"] = result.get("status")
                        (root / "output/result-event.json").write_bytes(raw)
                        (root / "output/response.md").write_bytes(result.get("response", "").encode("utf-8"))
                if tool:
                    execution["tool_events"].append({"utc": now(), "name": tool, "event": tag})
                    allowed = (plan["client"] == "agy" and tool in {"finish", "manage_task"}) or (allow_search and tool in {"search_web", "web_search"})
                    if not allowed and not mismatch.is_set():
                        execution["tool_mismatch"] = {"decided_utc": now(), "tool": tool, "answer_reviewed_at_decision": False, "selection_based_on_answer": False, "evidence": "output/events.ndjson"}
                        mismatch.set()
                for observed, requested in [("observed_model", "model"), ("observed_effort", "effort")]:
                    if execution.get(observed) is not None and execution[observed] != plan[requested]:
                        execution["tool_mismatch"] = {"decided_utc": now(), "tool": "MODEL_IDENTITY_MISMATCH", "answer_reviewed_at_decision": False, "selection_based_on_answer": False, "evidence": "output/events.ndjson"}
                        mismatch.set()

    def error_reader():
        with (root / "output/stderr.txt").open("xb") as stream:
            for block in iter(lambda: proc.stderr.read(8192), b""):
                stream.write(block); stream.flush()

    failure = None
    try:
        if plan["client"] == "agy":
            helper.auth_links(root)
        proc = subprocess.Popen(plan["argv"], cwd=plan["cwd"], env=helper.environment(root), stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        execution["parent_pid"] = proc.pid
        threads = [threading.Thread(target=output_reader), threading.Thread(target=error_reader)]
        for thread in threads:
            thread.start()
        time.sleep(0.2)
        if proc.poll() is not None or proc.pid in baseline:
            raise RuntimeError("Client exited before request or is not a new process")
        parent = check_pid(root, proc.pid, "parent")
        if Path(parent["executable"]).resolve() != Path(identity["resolved_binary"]).resolve():
            raise RuntimeError("Actual client differs from inspected binary")
        parent["executable_sha256"] = digest(parent["executable"])
        execution["parent_identity"] = parent
        execution["workers"].append(check_pid(root, proc.pid, "worker"))
        execution["worker_structure"] = "In-process client/worker, as in same-binary historical runs; all later descendants are also policy-queried."
        seen = {proc.pid}
        execution.update(request_count=1, request_utc=now(), status="submitted")
        attempt.update(request_count=1, request_utc=execution["request_utc"], status="submitted")
        save(root / "runtime/execution.json", execution); save(ledger_path, ledger)
        payload = Path(plan["stdin_file"]).read_bytes()
        written = proc.stdin.write(payload); proc.stdin.flush(); proc.stdin.close()
        if written != len(payload):
            raise RuntimeError("Incomplete stdin submission")
        execution["stdin_bytes_written"] = written
        execution["stdin_write_calls"] = 1
        while proc.poll() is None:
            if mismatch.is_set():
                raise RuntimeError("Unexpected tool or permission event")
            if time.monotonic() - started > timeout:
                raise TimeoutError("Per-case time limit reached")
            for row in descendants(process_tree(), proc.pid):
                if row["pid"] not in seen:
                    try:
                        evidence = check_pid(root, row["pid"], "worker", "-" + str(len(seen)))
                    except ProcessLookupError:
                        execution.setdefault("transient_children", []).append({**row, "utc": now(), "status": "exited-before-policy-query-completed", "policy_basis": "inherits launcher's OS policy; no successful live policy query claimed"})
                        seen.add(row["pid"])
                        continue
                    evidence["new_since_prelaunch"] = row["pid"] not in baseline
                    if not evidence["new_since_prelaunch"]:
                        raise RuntimeError("Unexpected preexisting worker")
                    execution["workers"].append(evidence); seen.add(row["pid"])
            time.sleep(0.5)
        for thread in threads:
            thread.join(timeout=10)
        if mismatch.is_set() or proc.returncode:
            raise RuntimeError("CLI failed or violated tools policy")
        if plan["client"] == "agy" and (metrics["result_count"] != 1 or execution.get("result_status") != "SUCCESS"):
            raise RuntimeError("AGY did not return exactly one successful result")
        if plan["client"] == "agy" and execution.get("permission_mode") != "strict":
            raise RuntimeError("AGY strict permission metadata was not observed")
        if parse_errors:
            raise RuntimeError("Unexpected non-JSON output; retain raw evidence")
        response = root / "output/response.md"
        if not response.is_file() or not response.read_bytes().strip():
            raise RuntimeError("Final response absent or empty")
        execution["status"] = "completed"
    except BaseException as error:
        failure = {"type": type(error).__name__, "message": str(error)}
        execution["status"] = "failed"
        if proc:
            try:
                stop_process(proc)
            except BaseException as cleanup_error:
                execution["cleanup_failure"] = {"type": type(cleanup_error).__name__, "message": str(cleanup_error)}
    finally:
        for thread in threads:
            thread.join(timeout=10)
        if plan["client"] == "agy":
            helper.auth_links(root, remove=True)
        execution.update(finished_utc=now(), elapsed_seconds=round(time.monotonic() - started, 3), exit_code=proc.returncode if proc else None, failure=failure, parse_errors=parse_errors, event_counts=dict(metrics["events"]), usage=metrics["usage"])
        execution["artifact_hashes"] = {name: digest(root / name) for name in ["input/task.md", "output/events.ndjson", "output/stderr.txt", "output/response.md"] if (root / name).is_file()}
        save(root / "runtime/execution.json", execution)
        attempt.update(status=execution["status"], finished_utc=execution["finished_utc"], failure=failure)
        if execution["tool_mismatch"]:
            ledger["tool_mismatch_decisions"].append(execution["tool_mismatch"])
        save(ledger_path, ledger)
    if failure:
        raise RuntimeError(json.dumps(failure))
    return (root / "output/response.md").read_bytes().decode("utf-8"), execution
