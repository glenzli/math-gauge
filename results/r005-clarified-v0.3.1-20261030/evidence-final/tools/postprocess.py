"""Read-only execution audit and explicit-whitelist evidence archive; no inference.

This is postprocessing, outside the frozen runner. It never modifies source evidence.
Missing execution evidence is unknown, not a zero-request observation.
"""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import sys
from datetime import datetime, timezone

REPO = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO / "scripts/benchmark"))
from common import Suite, candidate_message, digest, load, text_digest, verify_release

DEFAULT_ROOT = Path("/private/tmp/math-gauge-full-comparison-20261030")
RUNTIME_NAMES = {
    "plan.json", "prepared-hashes.json", "cli-identity.json", "probes.json",
    "outer.sb", "probe.py", "open-probe.json", "open-probe-command.json",
    "network-probe.json", "preparation-extension.json", "attempt-ledger.json",
    "execution.json", "execution.template.json", "credential-cleanup.json",
    "task-settings.json", "codex-settings.json", "request.ndjson",
}
OUTPUT_NAMES = {"events.ndjson", "stderr.txt", "response.md", "result-event.json", "agy.log"}
QUEUE_NAMES = {
    "freeze.json", "root-release.json", "snapshot-plan.json", "catalog.frozen.json",
    "queue-start.json", "progress.ndjson", "queue-status.json", "queue-final.json",
    "model-runs.json", "queue-console.log",
}
SECRET_PATTERNS = [
    ("credential-value", re.compile(rb'"(?:access_token|refresh_token|id_token|api_key)"\s*:\s*"[^"\s]+"')),
    ("bearer-value", re.compile(rb'(?i)authorization\s*[:=]\s*["\x27]?bearer\s+[A-Za-z0-9._~-]{12,}')),
    ("api-key-value", re.compile(rb'\bsk-(?:proj-)?[A-Za-z0-9_-]{20,}')),
]


def now():
    return datetime.now(timezone.utc).isoformat()


def write_new(path, data):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("x", encoding="utf-8") as stream:
        json.dump(data, stream, ensure_ascii=False, indent=2)
        stream.write("\n")


def read_if(path):
    return load(path) if path.is_file() else None


def within(path, root):
    path = Path(path)
    if path.is_symlink() or not path.resolve().is_relative_to(root.resolve()):
        raise ValueError("Evidence path escaped its declared root: " + str(path))
    return path


def raw_events(path, client):
    result = {"counts": {}, "tools": [], "observed_model": None, "observed_effort": None,
              "permission_mode": None, "agent": None, "parse_errors": 0, "results": []}
    counts = Counter()
    for line in path.read_bytes().splitlines():
        try:
            event = json.loads(line)
        except (ValueError, UnicodeDecodeError):
            result["parse_errors"] += 1
            continue
        tag = event.get("type", event.get("event"))
        counts[tag] += 1
        if client == "codex":
            item = event.get("item", {})
            kind = item.get("type") if isinstance(item, dict) else None
            if kind and kind not in {"agent_message", "reasoning", "error", "todo_list"}:
                result["tools"].append(kind)
            for key, target in [("model", "observed_model"), ("reasoning_effort", "observed_effort"), ("effort", "observed_effort")]:
                if isinstance(event.get(key), str):
                    result[target] = event[key]
        else:
            if tag == "init":
                init = event.get("init", {})
                result.update(observed_model=init.get("model"), permission_mode=init.get("permission_mode"), agent=init.get("agent"))
            step = event.get("step_update", {})
            if step.get("step_type") == "tool":
                result["tools"].append(step.get("tool_name", "UNKNOWN_TOOL"))
            if tag == "result":
                value = event.get("result", {})
                result["results"].append({"status": value.get("status"), "response_sha256": text_digest(value.get("response", ""))})
    result["counts"] = dict(counts)
    return result


def audit_case(root, item, model, final_row):
    cid = item["case_id"]
    session = within(item["sessions"][model], root)
    directory = root / "records" / model / cid
    case_dir = directory / cid
    execution = read_if(session / "runtime/execution.json")
    record = read_if(case_dir / "record.json")
    receipt = read_if(case_dir / "execution-assessment.json")
    metadata = read_if(directory / "run.json")
    ledger = load(session / "runtime/attempt-ledger.json")
    row = {"case_id": cid, "model": model, "request_count": None, "request_count_basis": "missing-execution-evidence",
           "status": "pending", "integrity_errors": [], "checks": {}, "valid_execution": False,
           "receipt_present": receipt is not None, "evidence": {}}
    if execution is not None and type(execution.get("request_count")) is int and execution["request_count"] in (0, 1):
        row.update(request_count=execution["request_count"], request_count_basis="runtime/execution.json")
    if execution is None and final_row and final_row.get("status") == "not-started-after-operational-failure":
        proof = final_row.get("request_count") == 0 and not ledger["attempts"] and metadata is None and receipt is None and record is None
        if proof:
            row.update(status="not-started-proven", request_count=0, request_count_basis="final-queue-row-and-empty-session-ledger")
            return row
        row["integrity_errors"].append("Inconsistent not-started evidence")
    if record is None or receipt is None or metadata is None or execution is None:
        if final_row:
            row["status"] = "missing-terminal-evidence"
            row["integrity_errors"].append("Final queue row lacks standard run/record/receipt/execution")
        elif execution:
            row["status"] = "in-progress" if execution.get("status") in {"starting", "submitted"} else "terminal-evidence-pending"
        return row

    checks = row["checks"]
    plan = load(session / "runtime/plan.json")
    identity = load(session / "runtime/cli-identity.json")
    request = load(case_dir / "solver/request.json")
    request_hash = text_digest(json.dumps(request, ensure_ascii=False, sort_keys=True))
    message_hash = text_digest(candidate_message(request))
    response_hash = digest(case_dir / "response.md")
    expected_label = plan["model"] + "/" + plan["effort"]
    row.update(run_id=metadata.get("run_id"), model_label=metadata.get("model_label"))
    checks["run_identity"] = bool(metadata.get("run_id")) and receipt.get("run_id") == metadata["run_id"] and receipt.get("model_label") == metadata.get("model_label") == expected_label
    checks["single_case_run"] = metadata.get("origin") == "command" and len(metadata.get("cases", [])) == 1 and metadata["cases"][0]["id"] == cid
    checks["case_version_suite"] = metadata["cases"][0]["version"] == item["version"] and metadata["suite_sha256"] == item["suite_sha256"]
    checks["request_hash"] = request_hash == record["request_sha256"] == receipt.get("request_sha256") == item["request_sha256"]
    checks["message_hash"] = message_hash == record["candidate_message_sha256"] == receipt.get("candidate_message_sha256") == item["candidate_message_sha256"] == digest(session / "input/task.md")
    checks["response_hash"] = response_hash == record["response_sha256"] == receipt.get("response_sha256")
    checks["receipt_execution_hash"] = receipt.get("evidence", {}).get("execution_sha256") == digest(session / "runtime/execution.json")
    checks["request_count_agrees"] = row["request_count"] is not None and receipt.get("mathematical_request_count") == row["request_count"]
    attempts = [x for x in ledger["attempts"] if x.get("kind") == "math"]
    checks["one_attempt_ledger"] = len(attempts) == 1 and attempts[0].get("request_count") == row["request_count"]
    checks["requested_identity"] = execution.get("requested_model") == receipt.get("requested_model") == plan["model"] and execution.get("requested_effort") == receipt.get("requested_effort") == plan["effort"]
    checks["raw_artifact_hashes"] = all(digest(within(session / name, session)) == expected for name, expected in execution.get("artifact_hashes", {}).items())
    checks["receipt_raw_hashes"] = receipt.get("evidence", {}).get("raw_artifacts") == execution.get("artifact_hashes")
    local_audit = receipt.get("evidence", {}).get("local_audit", {})
    checks["receipt_file_manifest"] = bool(local_audit.get("files")) and all(digest(within(session / x["path"], session)) == x["sha256"] for x in local_audit.get("files", []))
    checks["credential_links_removed"] = all(not (session / "state" / x["target"]).is_symlink() for x in plan["credential_links"])
    checks["solver_attachment_bytes"] = all(within(case_dir / "solver" / f["name"], case_dir / "solver").read_bytes() == f["content"].encode("utf-8") for f in request["files"])

    success = execution.get("status") == "completed" and record.get("status") == "ok"
    if success:
        raw = raw_events(session / "output/events.ndjson", plan["client"])
        row["raw_event_summary"] = raw
        allowed = {"finish", "manage_task"} if plan["client"] == "agy" else set()
        checks["tool_condition"] = set(raw["tools"]).issubset(allowed) and execution.get("tool_mismatch") is None
        checks["tool_event_record_matches_raw"] = [x["name"] for x in execution.get("tool_events", [])] == raw["tools"]
        checks["required_raw_hashes_present"] = set(execution.get("artifact_hashes", {})) == {"input/task.md", "output/events.ndjson", "output/stderr.txt", "output/response.md"}
        checks["raw_event_parse"] = raw["parse_errors"] == 0
        checks["observed_identity_preserved"] = all(raw[k] == execution.get(k) == receipt.get(k) and (raw[k] is None or raw[k] == plan[p]) for k, p in [("observed_model", "model"), ("observed_effort", "effort")])
        checks["one_stdin_write"] = row["request_count"] == 1 and execution.get("stdin_write_calls") == 1 and execution.get("stdin_bytes_written") == Path(plan["stdin_file"]).stat().st_size
        checks["response_raw_bytes"] = (case_dir / "response.md").read_bytes() == (session / "output/response.md").read_bytes()
        checks["parent_identity"] = execution["parent_identity"]["executable_sha256"] == identity["sha256"] and execution["parent_identity"]["pid"] == execution["parent_pid"]
        checks["parent_policy"] = load(session / "runtime/parent-pid-check.json")["passed"] is True
        checks["worker_policies"] = bool(execution["workers"]) and all(load(within(x["policy_evidence"], session))["passed"] is True for x in execution["workers"])
        checks["file_and_network_probes"] = load(session / "runtime/open-probe.json")["passed"] is True and load(session / "runtime/network-probe.json")["passed"] is True
        if plan["client"] == "agy":
            checks["effective_agent_permission"] = raw["permission_mode"] == "strict" and raw["agent"] == "text-only"
            checks["one_success_result"] = len(raw["results"]) == 1 and raw["results"][0] == {"status": "SUCCESS", "response_sha256": response_hash}
        else:
            checks["one_success_turn"] = raw["counts"].get("turn.completed") == 1 and not raw["counts"].get("turn.failed")
        checks["receipt_qualified"] = receipt.get("valid_for_comparison") is True
    else:
        checks["failure_not_qualified"] = receipt.get("valid_for_comparison") is False
    row["integrity_errors"] += [key for key, passed in checks.items() if not passed]
    row["status"] = "integrity-failed" if row["integrity_errors"] else ("valid-completed-execution" if success else "failure-evidence-retained")
    row["valid_execution"] = success and not row["integrity_errors"]
    for path in [directory / "run.json", case_dir / "record.json", case_dir / "execution-assessment.json", case_dir / "response.md", session / "runtime/execution.json"]:
        row["evidence"][str(path)] = digest(path)
    return row


def audit(root):
    root = root.resolve()
    freeze = verify_release(root / "runtime", root / "runtime/root-release.json")
    final = read_if(root / "runtime/queue-final.json")
    final_rows = {(x["model"], x["case_id"]): x for x in final["results"]} if final else {}
    global_checks = {}
    start = load(root / "runtime/queue-start.json")
    global_checks["queue_start_release_bound"] = start["release_sha256"] == digest(root / "runtime/root-release.json") and start["freeze_sha256"] == digest(root / "runtime/freeze.json")
    progress = [json.loads(line) for line in (root / "runtime/progress.ndjson").read_text().splitlines()]
    starts, active, finished, phases = set(), set(), set(), []
    sequencing_ok = True
    for event in progress:
        model, cid, status = event["model"], event.get("case_id"), event["status"]
        key = (model, cid)
        if status == "model-phase-started":
            phases.append(model)
            if model == "gemini" and sum(m == "terra" for m, _ in finished) != 41:
                sequencing_ok = False
        if status == "starting":
            if key in starts:
                sequencing_ok = False
            starts.add(key); active.add(key)
            if len(active) > 2 or len({m for m, _ in active}) > 1:
                sequencing_ok = False
        if status in {"completed", "failed", "launcher-failed"}:
            if key not in active:
                sequencing_ok = False
            active.discard(key)
            if status == "completed":
                finished.add(key)
    global_checks["unique_starts_and_two_slot_sequential_phases"] = sequencing_ok and phases in [["terra"], ["terra", "gemini"]]
    if final:
        planned = {(model, item["case_id"]) for model in freeze["model_order"] for item in freeze["cases"]}
        global_checks["final_all_planned_rows_once"] = len(final["results"]) == len(final_rows) == len(planned) and set(final_rows) == planned
        global_checks["final_no_active_cases"] = not active
        global_checks["final_queue_files_present"] = all((root / "runtime" / name).is_file() for name in QUEUE_NAMES)
    rows = []
    for model in freeze["model_order"]:
        for item in freeze["cases"]:
            try:
                row = audit_case(root, item, model, final_rows.get((model, item["case_id"])))
            except (OSError, ValueError, KeyError, TypeError) as error:
                row = {"case_id": item["case_id"], "model": model, "request_count": None, "status": "audit-evidence-error", "valid_execution": False, "integrity_errors": [type(error).__name__ + ": " + str(error)]}
            rows.append(row)
    run_ids = [x["run_id"] for x in rows if x.get("run_id")]
    global_checks["unique_standard_run_ids"] = len(run_ids) == len(set(run_ids))
    if final:
        index = load(root / "runtime/model-runs.json")
        indexed = [str(Path(path).resolve()) for paths in index["model_runs"].values() for path in paths]
        actual = [str(path.parent.resolve()) for path in (root / "records").glob("*/*/run.json")]
        global_checks["final_run_index_complete_unique"] = len(indexed) == len(set(indexed)) and set(indexed) == set(actual)
    return {"schema": "math-gauge.runtime-integrity-audit/v1", "utc": now(), "reviewer": "/root/alignment_research",
            "postprocessor_sha256": digest(__file__), "freeze_sha256": digest(root / "runtime/freeze.json"),
            "queue_terminal": final is not None, "planned": len(rows), "known_request_count": sum(x["request_count"] for x in rows if x["request_count"] is not None),
            "unknown_request_count_rows": sum(x["request_count"] is None for x in rows), "valid_executions": sum(x["valid_execution"] for x in rows),
            "integrity_error_rows": sum(bool(x["integrity_errors"]) for x in rows), "global_checks": global_checks, "global_integrity_passed": all(global_checks.values()), "statuses": dict(Counter(x["status"] for x in rows)), "rows": rows,
            "mathematical_scoring_performed": False, "limitations": ["Runtime-author integrity audit, not an independent code audit or human approval", "No backend identity is invented when the client does not echo it", "Unknown or missing executions are never counted as zero requests"]}


def collect_archive_files(root, freeze):
    files = {}

    def add(source, target=None):
        source = Path(source)
        if source.is_file() and not source.is_symlink():
            target = Path(target) if target else source.relative_to(root)
            if target.is_absolute() or ".." in target.parts or "state" in target.parts:
                raise ValueError("Archive target is outside whitelist: " + str(target))
            if target in files and files[target] != source:
                raise ValueError("Duplicate archive target")
            files[target] = source

    for name in QUEUE_NAMES:
        add(root / "runtime" / name)
    for model in freeze["model_order"]:
        add(root / "config" / (model + ".json"))
        config = load(root / "config" / (model + ".json"))
        identity = within(config["cli_identity"], root)
        for path in identity.parent.iterdir():
            if path.suffix in {".json", ".txt"}:
                add(path)
        for item in freeze["cases"]:
            cid = item["case_id"]
            session = within(item["sessions"][model], root)
            for name in RUNTIME_NAMES:
                add(session / "runtime" / name)
            for path in (session / "runtime").glob("*-pid-check*.json"):
                if re.fullmatch(r"(parent|worker)-pid-check(?:-\d+)?\.json", path.name):
                    add(path)
            for name in OUTPUT_NAMES:
                add(session / "output" / name)
            add(session / "work/.agents/agents/text-only.md")
            add(session / "input/task.md")
            directory = root / "records" / model / cid
            for name in ["run.json", "reviews.json", "summary.json"]:
                add(directory / name)
            for name in ["response.md", "stderr.txt", "record.json", "execution-assessment.json"]:
                add(directory / cid / name)
            solver = directory / cid / "solver"
            for name in ["request.json", "prompt.md"]:
                add(solver / name)
            if (solver / "request.json").is_file():
                for attachment in load(solver / "request.json")["files"]:
                    add(within(solver / attachment["name"], solver))
    for snapshot in freeze["suite_snapshots"]:
        suite = Suite.load(within(snapshot["root"], root))
        names = {"suite.json", "sources.json", *suite.metadata["cases"]}
        for case in suite.cases.values():
            names.update(case[k] for k in ["task", "reference", "rubric"])
            names.update(case.get("evaluator_files", []))
            names.update(case["lean_checks"])
            names.update(x["source"] for x in case["solver_files"])
        for name in names:
            add(within(suite.root / name, suite.root))
    for relative in freeze["code_identity"]:
        add(within(REPO / relative, REPO), Path("source-code") / relative)
    for path in (REPO / "math_gauge").glob("*.py"):
        add(path, Path("source-code/math_gauge") / path.name)
    add(Path(__file__), "postprocess.py")
    add(Path(__file__).with_name("replay_comparison.py"), "replay_comparison.py")
    # Existing canary/identity archive already has its own explicit whitelist manifest.
    preflight = Path(__file__).parent / "preflight-evidence"
    if (preflight / "manifest.json").is_file():
        add(preflight / "manifest.json", "preflight-evidence/manifest.json")
        for row in load(preflight / "manifest.json")["files"]:
            path = within(preflight / row["path"], preflight)
            if digest(path) != row["sha256"]:
                raise ValueError("Archived preflight evidence changed")
            add(path, Path("preflight-evidence") / row["path"])
    return files


def archive(root, destination):
    if not (root / "runtime/queue-final.json").is_file():
        raise ValueError("Refuse final archive while the queue is still active")
    if destination.exists():
        raise ValueError("Archive destination must be new")
    report = audit(root)
    freeze = load(root / "runtime/freeze.json")
    files = collect_archive_files(root, freeze)
    prepared, blocked = [], []
    for relative, source in sorted(files.items()):
        data = source.read_bytes()
        matches = [name for name, pattern in SECRET_PATTERNS if pattern.search(data)]
        if matches:
            blocked.append({"source": str(source), "patterns": matches})
        prepared.append((relative, source, data, hashlib.sha256(data).hexdigest()))
    if blocked:
        raise ValueError("Sensitive-value scan blocked archive paths: " + json.dumps(blocked))
    destination.mkdir(parents=True)
    manifest = []
    for relative, source, data, expected in prepared:
        if digest(source) != expected:
            raise ValueError("Source changed during archive preparation: " + str(source))
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        if digest(target) != expected:
            raise ValueError("Archive byte verification failed")
        manifest.append({"path": str(relative), "source": str(source), "bytes": len(data), "sha256": expected})
    write_new(destination / "integrity-audit.json", report)
    manifest.append({"path": "integrity-audit.json", "source": "generated-from-frozen-evidence", "bytes": (destination / "integrity-audit.json").stat().st_size, "sha256": digest(destination / "integrity-audit.json")})
    result = {"schema": "math-gauge.final-execution-archive/v1", "utc": now(), "files": manifest, "source_root": str(root),
              "queue_terminal": True, "state_credentials_binaries_excluded": True, "secret_value_scan": "Known patterns checked; no claim of universal detection",
              "integrity_audit_sha256": digest(destination / "integrity-audit.json"), "integrity_error_rows": report["integrity_error_rows"], "unknown_request_count_rows": report["unknown_request_count_rows"], "mathematical_scoring_performed": False}
    result["global_integrity_passed"] = report["global_integrity_passed"]
    write_new(destination / "manifest.json", result)
    return {"archive": str(destination), "files": len(manifest), "manifest_sha256": digest(destination / "manifest.json"), "integrity_error_rows": report["integrity_error_rows"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["audit", "archive"])
    parser.add_argument("--root", type=Path, default=DEFAULT_ROOT)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.action == "audit":
        report = audit(args.root)
        write_new(args.output, report)
        print(json.dumps({k: report[k] for k in ["planned", "queue_terminal", "known_request_count", "unknown_request_count_rows", "valid_executions", "integrity_error_rows", "statuses"]}))
    else:
        print(json.dumps(archive(args.root, args.output)))


if __name__ == "__main__":
    main()
