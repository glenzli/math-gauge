"""Append-only external answer collection and one-file return packaging.

This owner never invokes a model. Issued requests and observed raw files remain
separate from the immutable dataset/run and from evaluator judgments. Its portable
functions are embedded from this source, not reimplemented in a second runner.
"""

import inspect
import json
import os
import shutil
import tempfile
import zipfile
from contextlib import contextmanager
from datetime import datetime, timezone
from pathlib import Path

from .harness import (
    DATASET_SCHEMA, SIMPLE_DATASET_SCHEMA, RUN_SCHEMA, COMPACT_CONTROLLER, _h_require, _h_digest,
    _h_identity, _h_hash, _h_object, _h_relative, _h_path, _h_root, _h_file, _h_build_request,
    _r_json, _r_write, _inspect_release_dataset_contents, inspect_release_run,
    freeze_release_runtime, release_candidate_request, release_submission_template,
    _h_is_neutral, _h_schema_matches, _h_neutral_root, _neutral_runtime, _NEUTRAL_WIRE_ACTIVE,
)
from .reliability import _bytes, _readable, _slot_path, _transport_result

COLLECTION_SCHEMA = "math-gauge.answer-collection/v1"
ANSWERS_SCHEMA = "math-gauge.answers-archive/v1"
_REQUEST_RECEIPT = "math-gauge.issued-request/v1"
_SKIP_SCHEMA = "math-gauge.skipped-slot/v1"
identity = _h_identity


def _a_json_bytes(value):
    return (json.dumps(value, ensure_ascii=False, indent=2, allow_nan=False) + "\n").encode("utf-8")


def _a_descriptor(name, raw):
    _h_relative(name)
    return {"path": name, "bytes": len(raw), "sha256": _h_digest(raw)}


def _a_read(root, descriptor):
    _h_object(descriptor, {"path", "bytes", "sha256"}, "collected file descriptor")
    raw = _h_file(root, descriptor["path"]).read_bytes()
    _h_require(type(descriptor["bytes"]) is int and descriptor["bytes"] >= 0
               and _h_hash(descriptor["sha256"]) and len(raw) == descriptor["bytes"]
               and _h_digest(raw) == descriptor["sha256"], "Collected original file changed")
    return raw


def _a_roots(run_root, responses, *, create=False):
    run_root = _h_root(run_root)
    run = inspect_release_run(run_root)
    root = _h_path(responses)
    _h_require(not root.is_relative_to(run_root) and not run_root.is_relative_to(root),
               "Responses must be separate from the immutable run")
    if create:
        root.parent.mkdir(parents=True, exist_ok=True)
        with _a_lock(root):
            if not root.exists():
                root.mkdir(exist_ok=False)
                _r_write(root / "collection.json", {"schema": COLLECTION_SCHEMA,
                    "run_sha256": run["run_sha256"], "dataset_sha256": run["dataset_sha256"],
                    "created_at": datetime.now(timezone.utc).isoformat()})
    _h_require(root.is_dir(), "Responses directory does not exist; issue a request first")
    header = _r_json(_h_file(root, "collection.json").read_bytes())
    _h_object(header, {"schema", "run_sha256", "dataset_sha256", "created_at"}, "answer collection")
    _h_require(header["schema"] == COLLECTION_SCHEMA and header["run_sha256"] == run["run_sha256"]
               and header["dataset_sha256"] == run["dataset_sha256"]
               and isinstance(header["created_at"], str), "Responses bind a different frozen run")
    return run_root, run, root


@contextmanager
def _a_lock(root):
    lock = root.parent / (root.name + ".collection-lock")
    try:
        lock.mkdir()
    except FileExistsError as error:
        raise ValueError("Another collection operation is active; retain its request/attempt records") from error
    try:
        yield
    finally:
        lock.rmdir()


def _a_publish(folder, files):
    """Publish a complete new request/attempt directory without overwriting history."""
    folder.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix=".new-evidence-", dir=folder.parent) as temp:
        staging = Path(temp) / "evidence"
        staging.mkdir()
        for name, raw in files.items():
            _h_relative(name)
            path = staging / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)
        folder.mkdir(exist_ok=False)
        try:
            os.replace(staging, folder)
        except BaseException:
            folder.rmdir()
            raise


def _a_timing(metadata):
    result = {}
    parsed = {}
    for key in ("started_at", "finished_at"):
        value = metadata.get(key)
        if value is None:
            continue
        try:
            stamp = datetime.fromisoformat(value.replace("Z", "+00:00"))
            _h_require(stamp.utcoffset() is not None, "Declared timestamps need a timezone")
        except (AttributeError, TypeError, ValueError) as error:
            raise ValueError("Invalid observed attempt timestamp") from error
        parsed[key], result[key] = stamp, value
    if len(parsed) == 2:
        _h_require(parsed["finished_at"] >= parsed["started_at"], "Observed timing is reversed")
    elapsed = metadata.get("elapsed_seconds")
    if elapsed is not None:
        _h_require(type(elapsed) in (int, float) and elapsed >= 0,
                   "Observed elapsed time must be nonnegative")
        _h_identity(elapsed)
        result["elapsed_seconds"] = elapsed
    return result


def _a_recovery_policy(run_sha256, policy):
    """Accept only an explicit caller-supplied operational amendment, never archive authority."""
    if policy is None:
        return None
    _h_require(isinstance(policy, dict) and policy.get("schema") == "math-gauge.local-transport-recovery/v1"
               and policy.get("run_sha256") == run_sha256
               and policy.get("unknown_usage") == "retain-unknown-use-known-lower-bound"
               and _h_hash(policy.get("frozen_runner_sha256"))
               and _h_hash(policy.get("installed_runner_sha256")), "Invalid explicit transport recovery policy")
    entries = policy.get("attempts")
    _h_require(isinstance(entries, list) and bool(entries), "Transport recovery needs exact failed attempts")
    seen = set()
    for entry in entries:
        _h_require(isinstance(entry, dict) and isinstance(entry.get("slot_id"), str)
                   and entry.get("number") == 1 and _h_hash(entry.get("metadata_sha256"))
                   and entry.get("response_sha256") == _h_digest(b""),
                   "Transport recovery is limited to bound unreadable first attempts")
        key = (entry["slot_id"], entry["number"])
        _h_require(key not in seen, "Duplicate transport recovery attempt")
        seen.add(key)
    _h_identity(policy)
    return policy


def _a_recovery_allows(policy, slot_id, attempt):
    if policy is None or "total_tokens" in attempt.get("usage", {}):
        return False
    response, metadata = attempt.get("response", {}), attempt.get("metadata_source") or {}
    return any(entry["slot_id"] == slot_id and entry["number"] == attempt["number"]
               and attempt["status"] in {"transient_error", "timeout"}
               and response.get("bytes") == 0 and response.get("sha256") == entry["response_sha256"]
               and metadata.get("sha256") == entry["metadata_sha256"] for entry in policy["attempts"])


def _a_parallel(run):
    """New controller snapshots relax cross-slot order, never branch ancestry."""
    return _h_schema_matches(run.get("controller_version"), COMPACT_CONTROLLER)


def _a_serial_budget(run):
    """Unknown future usage needs serialization when one cumulative cap is shared."""
    return not _a_parallel(run) or any(
        run["execution"]["budget"].get(key) is not None
        for key in ("max_transport_attempts", "max_total_tokens"))


def _a_budget(run, rows, recovery_policy=None):
    budget = run["execution"]["budget"]
    maximum, limit = budget.get("max_transport_attempts"), budget.get("max_total_tokens")
    attempts, known, complete = 0, 0, True
    stopped = maximum == 0 or limit == 0
    reason = "cumulative_budget_exhausted" if stopped else None
    for row in rows.values():
        for attempt in row["attempts"]:
            _h_require(not stopped, "Collection continued after its frozen total budget stopped execution")
            attempts += 1
            usage = attempt["usage"]
            known += usage.get("total_tokens", 0)
            if "total_tokens" not in usage:
                complete = False
                if limit is not None and not _a_recovery_allows(recovery_policy, row["slot_id"], attempt):
                    stopped, reason = True, "usage_unavailable_for_total_token_budget"
            if maximum is not None and attempts >= maximum:
                stopped, reason = True, reason or "cumulative_budget_exhausted"
            if limit is not None and known >= limit:
                stopped, reason = True, reason or "total_token_budget_exhausted"
            if (attempt["status"] == "budget_exhausted" and not attempt["readable"]
                    and not _a_parallel(run)):
                stopped, reason = True, reason or "adapter_budget_exhausted"
    result = {"transport_attempts": attempts, "known_total_tokens": known,
            "token_usage_complete": complete, "total_tokens": known if complete else None,
            "stopped": stopped, "stop_reason": reason}
    if recovery_policy is not None:
        result["local_transport_recovery_sha256"] = _h_identity(recovery_policy)
    return result


def _a_inspect(run_root, responses, *, allow_submission=False, recovery_policy=None):
    """Recheck every immutable issue/attempt and derive explicit frozen slot states."""
    if _h_neutral_root(run_root):
        return _neutral_runtime()._a_inspect(run_root, responses, allow_submission=allow_submission,
                                           recovery_policy=recovery_policy)
    run_root, run, root = _a_roots(run_root, responses)
    recovery_policy = _a_recovery_policy(run["run_sha256"], recovery_policy)
    dataset = _inspect_release_dataset_contents(run_root / "dataset")
    slots = {s["slot_id"]: s for s in dataset["slots"]}
    selected = set(run["selected_slot_ids"])
    view = dict(dataset, execution=run["execution"], slots=[s for s in dataset["slots"] if s["slot_id"] in selected])
    expected = {"collection.json"}
    rows, locked, states = {}, {}, []
    earlier_unfinished = False
    serial = _a_serial_budget(run)
    for sid in run["selected_slot_ids"]:
        prefix = _slot_path(sid)
        folder = root / prefix
        row = {"slot_id": sid, "requests": [], "attempts": [], "skip": None}
        parent = slots[sid]["parent_slot"]
        ancestors, previous = {}, parent
        while previous is not None and previous in locked:
            ancestors[previous] = locked[previous]
            previous = slots[previous]["parent_slot"]
        parent_ready = parent is None or (parent in locked and previous is None)
        for number in (1, 2):
            request_base = prefix + f"/requests/{number}"
            receipt_path = root / request_base / "receipt.json"
            attempt_base = prefix + f"/attempts/{number}"
            record_path = root / attempt_base / "record.json"
            if not receipt_path.exists():
                _h_require(not record_path.exists(), "Recorded attempt has no issued request")
                continue
            _h_require(parent_ready and (not serial or not earlier_unfinished),
                       "Issued requests lack readable branch parents or changed a serialized budget order")
            _h_require(number == len(row["requests"]) + 1, "Issued request ordering changed")
            if number == 2:
                _h_require(len(row["attempts"]) == 1 and not row["attempts"][0]["readable"]
                           and row["attempts"][0]["status"] in {"transient_error", "timeout"},
                           "Retry follows a readable answer or non-retryable failure")
            request_name = request_base + "/request.json"
            raw = _h_file(root, request_name).read_bytes()
            request = _r_json(raw)
            receipt = _r_json(_h_file(root, request_base + "/receipt.json").read_bytes())
            _h_object(receipt, {"schema", "slot_id", "number", "issued_at", "request_sha256",
                                "projected_request_sha256"}, "issued request receipt")
            projected = _h_build_request(run_root / "dataset", view, sid, ancestors)
            _h_require(receipt["schema"] == _REQUEST_RECEIPT and receipt["slot_id"] == sid
                       and receipt["number"] == number and isinstance(receipt["issued_at"], str)
                       and receipt["request_sha256"] == _h_digest(raw)
                       and receipt["projected_request_sha256"] == _h_identity(request)
                       and request == projected, "Issued canonical request changed")
            expected.update({request_name, request_base + "/receipt.json"})
            row["requests"].append({"raw": raw, "value": request, "receipt": receipt, "path": request_name})
            if not record_path.exists():
                continue
            attempt = _r_json(_h_file(root, attempt_base + "/record.json").read_bytes())
            fields = {"number", "status", "projected_request_sha256", "response", "stderr", "usage",
                      "exit_code", "recorded_at", "usage_source", "metadata_source"}
            _h_object(attempt, fields | (set(attempt) & {"started_at", "finished_at", "elapsed_seconds"}),
                      "collected attempt")
            _h_require(attempt["number"] == number and attempt["projected_request_sha256"] == _h_identity(request)
                       and isinstance(attempt["recorded_at"], str)
                       and (attempt["exit_code"] is None or type(attempt["exit_code"]) is int),
                       "Attempt binding or order changed")
            for key, suffix in (("response", "response.md"), ("stderr", "stderr.txt")):
                _h_require(attempt[key]["path"] == attempt_base + "/" + suffix, "Attempt file path changed")
                expected.add(attempt[key]["path"])
            response = _a_read(root, attempt["response"])
            stderr = _a_read(root, attempt["stderr"])
            result = _transport_result({"stdout": response, "stderr": stderr, "status": attempt["status"],
                                        "usage": attempt["usage"], "exit_code": attempt["exit_code"]})
            for key, suffix in (("usage_source", "usage.json"), ("metadata_source", "metadata.json")):
                descriptor = attempt[key]
                if descriptor is None:
                    continue
                _h_require(descriptor["path"] == attempt_base + "/" + suffix, "Observed metadata path changed")
                data = _a_read(root, descriptor)
                original = _r_json(data)
                _h_require(isinstance(original, dict), "Observed usage and metadata must be objects")
                if key == "usage_source":
                    _h_require(original == result["usage"], "Observed original usage changed")
                else:
                    _h_require(_a_timing(original) == {k: attempt[k] for k in
                        ("started_at", "finished_at", "elapsed_seconds") if k in attempt},
                        "Observed original timing changed")
                expected.add(descriptor["path"])
            _h_require(attempt["usage_source"] is not None or not result["usage"],
                       "Unknown usage must remain unknown")
            _a_timing(attempt)
            expected.add(attempt_base + "/record.json")
            row["attempts"].append(dict(attempt, readable=_readable(response) is not None))
            if _readable(response) is not None:
                locked[sid] = response
        skip_name = prefix + "/skip.json"
        if (root / skip_name).exists():
            skip = _r_json(_h_file(root, skip_name).read_bytes())
            _h_object(skip, {"schema", "slot_id", "reason", "recorded_at"}, "missing slot declaration")
            _h_require(skip["schema"] == _SKIP_SCHEMA and skip["slot_id"] == sid
                       and isinstance(skip["reason"], str) and skip["reason"].strip()
                       and isinstance(skip["recorded_at"], str) and sid not in locked
                       and len(row["requests"]) == len(row["attempts"])
                       and (not serial or not earlier_unfinished),
                       "Missingness declaration changed or discarded an outstanding/readable response")
            row["skip"] = skip
            expected.add(skip_name)
        if sid in locked:
            state = "responded"
        elif len(row["requests"]) > len(row["attempts"]):
            state = "awaiting_response"
        elif row["skip"]:
            state = "skipped" if not row["attempts"] else "execution_error"
        elif row["attempts"]:
            last = row["attempts"][-1]
            state = "retryable" if len(row["attempts"]) == 1 and last["status"] in {"transient_error", "timeout"} else "execution_error"
        elif parent is not None and parent not in locked:
            state = "blocked"
        else:
            state = "pending"
        terminal = state in {"responded", "skipped", "execution_error", "blocked"}
        if not terminal:
            earlier_unfinished = True
        states.append({"slot_id": sid, "state": state, "attempts": len(row["attempts"]),
                       "reason": row["skip"]["reason"] if row["skip"] else
                                 ("parent_without_readable_response" if state == "blocked" else None)})
        rows[sid] = row
    expected_dirs = {str(parent) for name in expected for parent in Path(name).parents if str(parent) != "."}
    for path in root.rglob("*"):
        _h_require(not path.is_symlink(), "Symlinks are not permitted in collected responses")
        name = path.relative_to(root).as_posix()
        _h_require((path.is_file() and (name in expected or (allow_submission and name == "submission.json")))
                   or (path.is_dir() and name in expected_dirs), "Unlisted collected file or directory: " + name)
    return {"run": run, "dataset": dataset, "root": root, "rows": rows, "locked": locked, "states": states,
            "files": sorted(expected), "budget": _a_budget(run, rows, recovery_policy)}


def inspect_answer_collection(run_root, responses, *, recovery_policy=None):
    result = _a_inspect(run_root, responses, recovery_policy=recovery_policy)
    return {"run_sha256": result["run"]["run_sha256"], "slots": result["states"], "budget": result["budget"]}


def issue_answer_request(run_root, responses, slot_id, output, *, recovery_policy=None):
    if _h_neutral_root(run_root):
        return _neutral_runtime().issue_answer_request(run_root, responses, slot_id, output,
                                                     recovery_policy=recovery_policy)
    run_root, run, root = _a_roots(run_root, responses, create=True)
    out = _h_path(output)
    _h_require(not out.exists() and not out.is_relative_to(run_root) and not out.is_relative_to(root),
               "Request output must be a new file outside the immutable run and collected responses")
    with _a_lock(root):
        state = _a_inspect(run_root, root, recovery_policy=recovery_policy)
        selected = next((s for s in state["states"] if s["slot_id"] == slot_id), None)
        _h_require(selected is not None and selected["state"] in {"pending", "awaiting_response", "retryable"},
                   "Slot is locked, skipped or blocked by its own parent, or is not selected")
        if _a_serial_budget(run):
            first = next(s for s in state["states"] if s["state"] in {"pending", "awaiting_response", "retryable"})
            _h_require(first["slot_id"] == slot_id,
                       "Request must follow frozen slot order for this controller or shared cumulative budget")
        _h_require(not state["budget"]["stopped"], "Frozen total execution budget has stopped")
        row = state["rows"][slot_id]
        if selected["state"] == "awaiting_response":
            issued = row["requests"][-1]
            raw = issued["raw"]
        else:
            dataset = state["dataset"]
            slots = {s["slot_id"]: s for s in dataset["slots"]}
            ancestors, parent = {}, slots[slot_id]["parent_slot"]
            while parent is not None:
                ancestors[parent] = state["locked"][parent]
                parent = slots[parent]["parent_slot"]
            request = release_candidate_request(run_root, slot_id, ancestors)
            raw, number = _a_json_bytes(request), len(row["requests"]) + 1
            receipt = {"schema": _REQUEST_RECEIPT, "slot_id": slot_id, "number": number,
                       "issued_at": datetime.now(timezone.utc).isoformat(),
                       "request_sha256": _h_digest(raw), "projected_request_sha256": _h_identity(request)}
            _a_publish(root / _slot_path(slot_id) / "requests" / str(number),
                       {"request.json": raw, "receipt.json": _a_json_bytes(receipt)})
        out.parent.mkdir(parents=True, exist_ok=True)
        with out.open("xb") as stream:
            stream.write(raw)
    return _r_json(raw)


def record_answer_attempt(run_root, responses, slot_id, request_path, response_path, *, status,
                          stderr_path=None, usage_path=None, metadata_path=None, exit_code=None, recovery_policy=None):
    if _h_neutral_root(run_root):
        return _neutral_runtime().record_answer_attempt(
            run_root, responses, slot_id, request_path, response_path, status=status,
            stderr_path=stderr_path, usage_path=usage_path, metadata_path=metadata_path,
            exit_code=exit_code, recovery_policy=recovery_policy)
    run_root, run, root = _a_roots(run_root, responses)
    request_raw = _h_path(request_path).read_bytes()
    response = _h_path(response_path).read_bytes()
    stderr = _h_path(stderr_path).read_bytes() if stderr_path else b""
    usage_raw = _h_path(usage_path).read_bytes() if usage_path else None
    metadata_raw = _h_path(metadata_path).read_bytes() if metadata_path else None
    usage = _r_json(usage_raw) if usage_raw is not None else {}
    metadata = _r_json(metadata_raw) if metadata_raw is not None else {}
    _h_require(isinstance(metadata, dict), "Observed provider metadata must be a JSON object")
    result = _transport_result({"stdout": response, "stderr": stderr, "status": status,
                                "usage": usage, "exit_code": exit_code})
    _h_require(exit_code is None or type(exit_code) is int, "Observed exit code must be integral or unknown")
    with _a_lock(root):
        state = _a_inspect(run_root, root, recovery_policy=recovery_policy)
        _h_require(slot_id in state["rows"], "Unknown selected slot")
        row = state["rows"][slot_id]
        _h_require(len(row["requests"]) == len(row["attempts"]) + 1,
                   "Issue a new exact request before recording this attempt; recorded attempts cannot be overwritten")
        issued = row["requests"][-1]
        _h_require(request_raw == issued["raw"], "Recorded response does not bind the exact issued request file")
        _h_require(not state["budget"]["stopped"], "Frozen total execution budget has stopped")
        number = len(row["attempts"]) + 1
        prefix = _slot_path(slot_id) + f"/attempts/{number}/"
        attempt = {"number": number, "status": result["status"],
                   "projected_request_sha256": _h_identity(issued["value"]),
                   "response": _a_descriptor(prefix + "response.md", response),
                   "stderr": _a_descriptor(prefix + "stderr.txt", stderr), "usage": result["usage"],
                   "exit_code": exit_code, "recorded_at": datetime.now(timezone.utc).isoformat(),
                   "usage_source": _a_descriptor(prefix + "usage.json", usage_raw) if usage_raw is not None else None,
                   "metadata_source": _a_descriptor(prefix + "metadata.json", metadata_raw) if metadata_raw is not None else None,
                   **_a_timing(metadata)}
        files = {"response.md": response, "stderr.txt": stderr, "record.json": _a_json_bytes(attempt)}
        if usage_raw is not None:
            files["usage.json"] = usage_raw
        if metadata_raw is not None:
            files["metadata.json"] = metadata_raw
        _a_publish(root / prefix, files)
        checked = _a_inspect(run_root, root, recovery_policy=recovery_policy)
        return next(s for s in checked["states"] if s["slot_id"] == slot_id)


def skip_answer_slot(run_root, responses, slot_id, reason, *, recovery_policy=None):
    if _h_neutral_root(run_root):
        return _neutral_runtime().skip_answer_slot(run_root, responses, slot_id, reason,
                                                 recovery_policy=recovery_policy)
    run_root, run, root = _a_roots(run_root, responses, create=True)
    _h_require(isinstance(reason, str) and reason.strip(), "Record a concrete missingness reason")
    with _a_lock(root):
        state = _a_inspect(run_root, root, recovery_policy=recovery_policy)
        selected = next((s for s in state["states"] if s["slot_id"] == slot_id), None)
        _h_require(selected is not None and selected["state"] in {"pending", "retryable", "awaiting_response"},
                   "Cannot skip a locked, skipped or parent-blocked slot, or a slot that is not selected")
        if _a_serial_budget(run):
            first = next(s for s in state["states"] if s["state"] in {"pending", "awaiting_response", "retryable"})
            _h_require(first["slot_id"] == slot_id, "Missingness must follow the frozen serialized budget order")
        _h_require(selected["state"] != "awaiting_response", "Record the outstanding attempt, including any failure, before skipping")
        folder = root / _slot_path(slot_id)
        folder.mkdir(parents=True, exist_ok=True)
        _r_write(folder / "skip.json", {"schema": _SKIP_SCHEMA, "slot_id": slot_id, "reason": reason,
                                        "recorded_at": datetime.now(timezone.utc).isoformat()})
        return next(s for s in _a_inspect(run_root, root, recovery_policy=recovery_policy)["states"] if s["slot_id"] == slot_id)


def _a_submission(state, *, origin, declared_external_calls):
    if not _NEUTRAL_WIRE_ACTIVE and _h_is_neutral(state["run"]):
        return _neutral_runtime()._a_submission(state, origin=origin, declared_external_calls=declared_external_calls)
    _h_require(origin in {"fixture", "replay", "external"}, "Declare fixture, replay or external origin")
    _h_require(type(declared_external_calls) is int and declared_external_calls >= 0,
               "Explicitly declare the known external call count; it cannot be inferred from attempt records")
    _h_require(origin == "external" or declared_external_calls == 0, "Fixture/replay submissions cannot declare real model calls")
    result = {
        "schema": "math-gauge.harness-submission/v2", "dataset_sha256": state["run"]["dataset_sha256"],
        "run_sha256": state["run"]["run_sha256"], "runtime_sha256": state["run"]["runtime_sha256"],
        "origin": origin, "fixture_only": origin != "external", "declared_external_calls": declared_external_calls,
        "slots": []}
    for sid, row in state["rows"].items():
        if not row["attempts"]:
            continue
        attempts = [{k: v for k, v in attempt.items() if k != "readable"} for attempt in row["attempts"]]
        result["slots"].append({"slot_id": sid, "projected_request": row["requests"][0]["value"], "attempts": attempts})
    result["artifacts"] = [_a_descriptor(name, _h_file(state["root"], name).read_bytes()) for name in state["files"]]
    return result


def pack_answer_archive(run_root, responses, destination, *, origin="fixture", declared_external_calls=None,
                        recovery_policy=None):
    if _h_neutral_root(run_root):
        return _neutral_runtime().pack_answer_archive(
            run_root, responses, destination, origin=origin,
            declared_external_calls=declared_external_calls, recovery_policy=recovery_policy)
    run_root, run, root = _a_roots(run_root, responses, create=True)
    _h_require(origin != "external" or declared_external_calls is not None,
               "External origin requires an explicitly observed declared-external-calls count")
    calls = 0 if declared_external_calls is None else declared_external_calls
    dest = _h_path(destination)
    _h_require(not dest.exists() and not dest.is_relative_to(run_root) and not dest.is_relative_to(root),
               "Answers ZIP must be a new file outside the immutable run and responses")
    with _a_lock(root):
        state = _a_inspect(run_root, root, recovery_policy=recovery_policy)
        submission = _a_submission(state, origin=origin, declared_external_calls=calls)
        dataset = _inspect_release_dataset_contents(run_root / "dataset")
        contents = {"submission/" + name: _h_file(root, name).read_bytes() for name in state["files"]}
        contents["submission/submission.json"] = _a_json_bytes(submission)
        for path in sorted(run_root.rglob("*")):
            if path.is_file():
                contents["run/" + path.relative_to(run_root).as_posix()] = path.read_bytes()
        manifest = {"schema": ANSWERS_SCHEMA, "release_version": dataset["release_version"],
            "suite": dataset["suite"], "dataset_sha256": run["dataset_sha256"],
            "run_sha256": run["run_sha256"], "base_plan_sha256": run["base_plan_sha256"],
            "slot_states": state["states"], "budget": state["budget"],
            "files": {name: {"bytes": len(raw), "sha256": _h_digest(raw)} for name, raw in sorted(contents.items())}}
        contents["answers.json"] = _a_json_bytes(manifest)
        dest.parent.mkdir(parents=True, exist_ok=True)
        created = False
        try:
            with dest.open("xb") as stream:
                created = True
                with zipfile.ZipFile(stream, "w", compression=zipfile.ZIP_DEFLATED) as archive:
                    for name, raw in sorted(contents.items()):
                        info = zipfile.ZipInfo(name, date_time=(1980, 1, 1, 0, 0, 0))
                        info.create_system, info.external_attr = 3, 0o100644 << 16
                        info.compress_type = zipfile.ZIP_DEFLATED
                        archive.writestr(info, raw)
        except BaseException:
            if created:
                dest.unlink()
            raise
    return {"archive": str(dest), "sha256": _h_digest(dest.read_bytes()), "run_sha256": run["run_sha256"],
            "origin": origin, "fixture_only": origin != "external", "declared_external_calls": calls,
            "slots": state["states"], "budget": state["budget"]}


def _simple_controller_main():
    import argparse
    import sys
    parser = argparse.ArgumentParser(description="Math Gauge portable preparation and answer collection; never calls a model")
    commands = parser.add_subparsers(dest="command", required=True)
    default_dataset = str(Path(__file__).resolve().parent.parent)
    check = commands.add_parser("check")
    check.add_argument("--dataset", "--bundle", default=default_dataset)
    check.add_argument("--run")
    check.add_argument("--responses")
    for name in ("prepare", "freeze"):
        sub = commands.add_parser(name)
        sub.add_argument("--dataset", "--bundle", default=default_dataset)
        sub.add_argument("--runtime", required=True)
        sub.add_argument("--target", action="append", dest="targets")
        sub.add_argument("--out", required=True)
    for name in ("request", "record", "skip", "pack"):
        sub = commands.add_parser(name)
        sub.add_argument("--run", required=True)
        sub.add_argument("--responses", required=True)
        if name in {"request", "record", "skip"}:
            sub.add_argument("--slot", required=True)
        if name in {"request", "pack"}:
            sub.add_argument("--out", required=True)
        if name == "record":
            sub.add_argument("--request", required=True)
            sub.add_argument("--response", required=True)
            sub.add_argument("--status", required=True, choices=("ok", "transient_error", "timeout", "permanent_error", "budget_exhausted"))
            sub.add_argument("--stderr")
            sub.add_argument("--usage")
            sub.add_argument("--metadata")
            sub.add_argument("--exit-code", type=int)
        if name == "skip":
            sub.add_argument("--reason", required=True)
        if name == "pack":
            sub.add_argument("--origin", choices=("fixture", "replay", "external"), default="fixture")
            sub.add_argument("--declared-external-calls", type=int)
    args = parser.parse_args()
    try:
        if args.command == "check":
            if args.responses:
                _h_require(args.run is not None, "Collection checks require --run")
                result = inspect_answer_collection(args.run, args.responses)
            else:
                value = inspect_release_run(args.run) if args.run else _inspect_release_dataset_contents(args.dataset)
                result = {k: value[k] for k in ("schema", "dataset_sha256", "base_plan_sha256", "planned")}
                result["candidate_calls"] = 0
        elif args.command in {"prepare", "freeze"}:
            value = freeze_release_runtime(args.dataset, _r_json(_h_path(args.runtime).read_bytes()), args.out, targets=args.targets)
            result = {k: value[k] for k in ("run_sha256", "dataset_sha256", "runtime_sha256", "selected_slot_ids", "planned")}
        elif args.command == "request":
            issue_answer_request(args.run, args.responses, args.slot, args.out)
            result = {"slot_id": args.slot, "request": str(_h_path(args.out)), "candidate_calls": 0}
        elif args.command == "record":
            result = record_answer_attempt(args.run, args.responses, args.slot, args.request, args.response,
                status=args.status, stderr_path=args.stderr, usage_path=args.usage,
                metadata_path=args.metadata, exit_code=args.exit_code)
        elif args.command == "skip":
            result = skip_answer_slot(args.run, args.responses, args.slot, args.reason)
        else:
            result = pack_answer_archive(args.run, args.responses, args.out,
                origin=args.origin, declared_external_calls=args.declared_external_calls)
        sys.stdout.write(json.dumps(result, ensure_ascii=False, indent=2, allow_nan=False) + "\n")
    except (ValueError, OSError, KeyError, TypeError) as error:
        parser.error(str(error))


def portable_answer_source():
    functions = (_bytes, _readable, _slot_path, _transport_result, _a_json_bytes, _a_descriptor,
                 _a_read, _a_roots, _a_lock, _a_publish, _a_timing, _a_recovery_policy,
                 _a_recovery_allows, _a_parallel, _a_serial_budget, _a_budget, _a_inspect,
                 inspect_answer_collection, issue_answer_request, record_answer_attempt,
                 skip_answer_slot, _a_submission, pack_answer_archive, _simple_controller_main)
    header = "import os\nimport tempfile\nimport zipfile\nfrom contextlib import contextmanager\nidentity = _h_identity\n"
    constants = {"COLLECTION_SCHEMA": COLLECTION_SCHEMA, "ANSWERS_SCHEMA": ANSWERS_SCHEMA,
                 "_REQUEST_RECEIPT": _REQUEST_RECEIPT, "_SKIP_SCHEMA": _SKIP_SCHEMA}
    return header + "\n".join(k + " = " + repr(v) for k, v in constants.items()) + "\n\n" + "\n\n".join(
        inspect.getsource(function).rstrip() for function in functions)
