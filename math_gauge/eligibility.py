"""Source-bound execution admissibility, separate from mathematical review.

Import copies an explicit list of raw files; it never executes a client.  The
machine checks provenance links and observed values.  A separately attributed
human audit judges external authenticity, process attribution and disclosure.
Neither file hashes nor an attributed audit authenticate provider internals.
"""

import copy
import errno
import json
import os
import re
import shutil
import tempfile
from contextlib import contextmanager
from datetime import datetime, timedelta
from functools import wraps
from pathlib import Path

from .benchmarks import identity
from .catalog import digest_bytes, relative_name
from .execution import now

SUBMISSION = "math-gauge.execution-eligibility-submission/v1"
RECEIPT = "math-gauge.execution-eligibility-receipt/v1"
SNAPSHOT = "math-gauge.execution-eligibility-snapshot/v1"
REQUIREMENTS = "math-gauge.execution-requirements/v1"
AUDIT_CHECKS = ("external_authenticity", "provider_metadata_origin", "process_attribution",
                "attempt_completeness", "no_answer_selection", "context_completeness",
                "tool_control_validity", "read_exception_review")
AUDIT_SOURCE_KINDS = {
    "external_authenticity": {"provider-metadata", "invocation", "isolation", "ledger"},
    "provider_metadata_origin": {"provider-metadata", "provider-response"},
    "process_attribution": {"isolation", "invocation"}, "attempt_completeness": {"ledger"},
    "no_answer_selection": {"ledger", "cli-events"}, "context_completeness": {"context"},
    "tool_control_validity": {"tool-control", "cli-events", "isolation"},
    "read_exception_review": {"policy", "isolation"},
}
PROTECTED = {"reference", "history", "prior_run", "memory", "global_config"}
KINDS = {"provider-request", "provider-metadata", "provider-response", "stderr",
         "cli-events", "invocation", "context", "isolation", "ledger", "policy", "tool-control", "network-probe", "client-output"}
ORIGINS = {"provider-return", "request", "client", "os", "operator"}
INTERNAL_BOOKKEEPING = {"finish", "manage_task"}
LIMITS = ("Integrity and declared observation checks only; human attribution is recorded, "
          "not identity-authenticated. External source authenticity and provider internals "
          "cannot be proved by these hashes.")


def _require(condition, message):
    if not condition:
        raise ValueError(message)


class _IntegrityError(ValueError):
    """Malformed, escaping, missing or changed source evidence cannot be audited away."""


def _integrity(condition, message):
    if not condition:
        raise _IntegrityError(message)


def _hash(value):
    return isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value) is not None


def _text(value):
    return isinstance(value, str) and bool(value.strip())


def _time(value):
    try:
        parsed = datetime.fromisoformat(value.replace("Z", "+00:00"))
        _require(parsed.utcoffset() is not None, "Execution evidence timestamps need a timezone")
        return parsed
    except (TypeError, AttributeError, ValueError) as error:
        raise ValueError("Invalid execution evidence timestamp") from error


def _root(value):
    path = Path(value).absolute()
    # macOS publishes these two system-owned aliases. Canonicalize only these
    # exact prefixes; arbitrary source/artifact symlinks remain forbidden.
    for alias in ("var", "tmp"):
        prefix = Path("/") / alias
        if path.is_relative_to(prefix) and prefix.is_symlink() and prefix.resolve() == Path("/private") / alias:
            path = Path("/private") / alias / path.relative_to(prefix)
    for part in (path, *path.parents):
        _require(not part.is_symlink(), "Execution evidence roots cannot contain symlinks")
    return path.resolve()


def _file(root, name):
    relative_name(name)
    path = Path(root) / name
    for part in (path, *path.parents):
        if part == Path(root):
            break
        _require(not part.is_symlink(), "Execution evidence paths cannot contain symlinks")
    _require(path.is_file() and path.resolve().is_relative_to(root),
             "Missing or escaping execution evidence file: " + name)
    return path


def _json_file(root, name):
    try:
        return json.loads(_file(root, name).read_bytes())
    except (json.JSONDecodeError, UnicodeDecodeError) as error:
        raise ValueError("Execution evidence is not valid JSON: " + name) from error


def _write_new(path, value):
    for part in (path, *path.parents):
        _require(not part.is_symlink(), "Execution evidence output cannot contain symlinks")
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("x", encoding="utf-8") as stream:
        stream.write(json.dumps(value, ensure_ascii=False, indent=2) + "\n")


@contextmanager
def _audit_lock(root):
    base = _root(root) / "eligibility"
    base.mkdir(exist_ok=True)
    _require(not base.is_symlink(), "Execution audit directory cannot be a symlink")
    lock = base / ".write-lock"
    try:
        lock.mkdir()
    except FileExistsError as error:
        raise ValueError("Execution audit writer is already active; retry after it finishes") from error
    try:
        yield
    finally:
        lock.rmdir()


def _serialized(function):
    @wraps(function)
    def wrapped(root, *args, **kwargs):
        with _audit_lock(root):
            return function(root, *args, **kwargs)
    return wrapped


def _structured(function):
    @wraps(function)
    def wrapped(*args, **kwargs):
        try:
            return function(*args, **kwargs)
        except (KeyError, TypeError, AttributeError, OverflowError) as error:
            raise _IntegrityError("Malformed execution evidence structure") from error
    return wrapped


def _run(root, meta=None, records=None):
    from .reliability import inspect_reliability_run
    # Caller-supplied objects are an optimization only if they are the exact
    # result of the normal immutable-run inspector.
    inspected_meta, inspected_records = inspect_reliability_run(root)
    if meta is not None:
        _require(meta == inspected_meta, "Execution eligibility received stale run metadata")
    if records is not None:
        _require(records == inspected_records, "Execution eligibility received stale slot records")
    return inspected_meta, inspected_records


def _ancestors(record, records):
    result = []
    parent = record.get("parent_slot")
    while parent is not None:
        _require(parent in records, "Execution evidence lacks its parent provenance")
        row = records[parent]
        result.append({key: row.get(key) for key in ("slot_id", "evidence_id", "response_sha256",
                                                    "history_sha256", "material_sha256")})
        parent = row.get("parent_slot")
    return list(reversed(result))


def _binding(root, meta, record, records):
    from .reliability import _slot_path
    attempts = []
    for row in record["attempts"]:
        prefix = _slot_path(record["slot_id"]) + f"/attempts/{row['number']}"
        attempts.append({**{key: row.get(key) for key in ("number", "response_sha256", "stderr_sha256",
                          "projected_request_sha256", "status", "started_at", "finished_at")},
                         "record_sha256": digest_bytes(_file(root, prefix + "/record.json").read_bytes())})
    return {"plan_sha256": meta["plan_sha256"],
            "execution_contract_sha256": meta["execution_contract_sha256"],
            "origin_run_id": record["evidence_origin_run_id"],
            "slot_record_sha256": meta["slot_record_sha256"][record["slot_id"]],
            **{key: record.get(key) for key in ("slot_id", "evidence_id", "response_sha256",
               "history_sha256", "projected_request_sha256", "material_sha256")},
            "ancestors": _ancestors(record, records), "attempts": attempts}


def execution_eligibility_templates(root):
    """Return unapproved forms and the exact source observation contract.

    Observation references use an artifact path plus an RFC 6901 JSON pointer;
    optional ``line`` selects one 1-based NDJSON line.  Omitting the pointer
    references raw bytes (for response text, stderr, policy and event logs).
    """
    root = _root(root)
    meta, records = _run(root)
    slots = []
    for sid, record in records.items():
        slots.append({"schema": SUBMISSION, "slot_id": sid,
                      "binding": _binding(root, meta, record, records), "artifacts": [],
                      "observations": {"attempts": [
                          {"number": a["number"], "submission_state": "unknown",
                           "request": {k: None for k in ("messages", "parameters", "request_id")},
                           "backend": {k: None for k in ("provider", "model", "reasoning_effort", "parameters", "request_id")},
                           "response": {"text": None, "request_id": None},
                           "stderr": None, "events": None, "invocation": None,
                           "context": None, "isolation": None} for a in record["attempts"]], "ledger": None},
                      "audit": {"reviewer": "", "reviewer_kind": "human", "reviewed_at": None,
                                "decision": "unresolved", "checks": {key: {
                                    "decision": "unresolved", "rationale": "", "sources": []}
                                    for key in AUDIT_CHECKS}}})
    return {"schema": "math-gauge.execution-eligibility-templates/v1", "run_id": meta["run_id"],
            "limits": LIMITS, "slots": slots}


class _Sources:
    def __init__(self, root, descriptors):
        root = self.root = _root(root)
        self.files = {}
        _require(isinstance(descriptors, list), "Execution artifacts must be an explicit list")
        for item in descriptors:
            _require(isinstance(item, dict) and set(item) == {"path", "bytes", "sha256", "kind", "origin"},
                     "Execution artifact needs path, bytes, sha256, kind and origin")
            name = item["path"]
            relative_name(name)
            _require(name not in self.files and item["kind"] in KINDS and item["origin"] in ORIGINS,
                     "Duplicate or unsupported execution artifact")
            # No state/authentication directories are ever recursively imported.
            _require(not {"state", ".git", ".codex"}.intersection(Path(name).parts),
                     "Execution evidence cannot include state or configuration directories")
            data = _file(root, name).read_bytes()
            _require(type(item["bytes"]) is int and item["bytes"] == len(data)
                     and _hash(item["sha256"]) and item["sha256"] == digest_bytes(data),
                     "Execution artifact bytes or hash changed: " + name)
            self.files[name] = (copy.deepcopy(item), data)

    def get(self, reference, kind=None):
        _integrity(isinstance(reference, dict) and set(reference) <= {"artifact", "pointer", "line"}
                 and isinstance(reference.get("artifact"), str), "Invalid execution source reference")
        name = reference["artifact"]
        relative_name(name)
        _integrity(name in self.files, "Execution source is absent from the artifact manifest")
        descriptor, data = self.files[name]
        _require(kind is None or descriptor["kind"] in ({kind} if isinstance(kind, str) else set(kind)),
                 "Execution observation has the wrong source kind")
        if kind in {"provider-metadata", "provider-response"}:
            _require(descriptor["origin"] == "provider-return", "Backend evidence is request echo or another non-provider source")
        if kind == "provider-request":
            _require(descriptor["origin"] == "request", "Request evidence has a mismatched source origin")
        if "pointer" not in reference:
            _integrity("line" not in reference, "NDJSON references need a JSON pointer")
            return data
        if "line" in reference:
            line = reference["line"]
            _integrity(type(line) is int and 0 < line <= len(data.splitlines()), "Invalid NDJSON source line")
            data = data.splitlines()[line - 1]
        try:
            value = json.loads(data)
        except (ValueError, UnicodeDecodeError) as error:
            raise _IntegrityError("Execution source pointer does not identify JSON") from error
        pointer = reference["pointer"]
        _integrity(isinstance(pointer, str) and (pointer == "" or pointer.startswith("/")),
                 "Invalid execution JSON pointer")
        try:
            for part in pointer.split("/")[1:] if pointer else ():
                _integrity(re.search(r"~(?![01])", part) is None, "Invalid execution JSON pointer escape")
                part = part.replace("~1", "/").replace("~0", "~")
                if isinstance(value, list):
                    _integrity(re.fullmatch(r"0|[1-9][0-9]*", part) is not None, "Invalid source array index")
                    value = value[int(part)]
                else:
                    value = value[part]
        except (KeyError, IndexError, TypeError) as error:
            raise _IntegrityError("Execution source pointer is missing") from error
        return value


def _requirements(meta):
    runtime = meta["plan"].get("runtime")
    _require(runtime is None or isinstance(runtime, dict), "Frozen execution runtime must be an object")
    runtime = runtime or {}
    if "execution_requirements" not in runtime:
        return None
    value = runtime["execution_requirements"]
    _require(isinstance(value, dict) and value.get("schema") == REQUIREMENTS,
             "Unsupported frozen execution requirements")
    _require("provider" not in value or _text(value["provider"]), "Frozen provider identity must be text")
    for key in ("allowed_tools", "internal_tools", "denied_categories", "read_exceptions"):
        _require(isinstance(value.get(key), list), "Execution requirements must freeze " + key)
    for key in ("allowed_tools", "internal_tools", "denied_categories"):
        _require(all(_text(x) for x in value[key]) and len(value[key]) == len(set(value[key])),
                 "Frozen execution lists need unique text values")
    _require(PROTECTED <= set(value["denied_categories"]) and _text(value.get("tool_control_tool")),
             "Execution requirements omit protected categories or tool control")
    _require(value["allowed_tools"] == meta["plan"]["context_policy"]["tools_allowed"]
             and not set(value["allowed_tools"]).intersection(value["internal_tools"])
             and set(value["internal_tools"]) <= INTERNAL_BOOKKEEPING
             and value["tool_control_tool"] not in value["allowed_tools"] + value["internal_tools"],
             "Execution requirements contradict the frozen no-tool context policy")
    for key in ("model_aliases", "effort_aliases"):
        aliases = value.get(key, {})
        _require(isinstance(aliases, dict) and all(_text(k) and isinstance(v, list)
                 and all(_text(x) for x in v) for k, v in aliases.items()), "Invalid pre-frozen backend alias map")
    for exception in value["read_exceptions"]:
        _require(isinstance(exception, dict) and set(exception) == {"kind", "path", "purpose"}
                 and exception["kind"] in {"literal", "subpath"} and _text(exception["path"])
                 and Path(exception["path"]).is_absolute() and _text(exception["purpose"]),
                 "Frozen read exceptions require exact absolute paths and purposes")
    return value


def validate_execution_requirements(plan):
    """Check an optional frozen requirement contract before any transport call."""
    _require(isinstance(plan, dict), "Execution requirements need a benchmark plan")
    return copy.deepcopy(_requirements({"plan": plan}))


def _matches(actual, wanted, aliases):
    return actual == wanted or actual in aliases.get(wanted, [])


def _parameters(actual, wanted, requirements):
    _require(isinstance(actual, dict) and set(actual) == set(wanted),
             "Observed effective parameters differ from the frozen request")
    for key, value in wanted.items():
        aliases = requirements.get("model_aliases" if key == "model" else "effort_aliases", {})
        _require(_matches(actual[key], value, aliases) if key in {"model", "reasoning_effort"}
                 else type(actual[key]) is type(value) and actual[key] == value,
                 "Observed effective parameter mismatch: " + key)


def _audit(value, sources, finished):
    _require(isinstance(value, dict) and value.get("decision") in {"accept", "reject", "unresolved"},
             "Execution audit needs an explicit decision")
    checks = value.get("checks", {})
    _require(isinstance(checks, dict) and set(checks) == set(AUDIT_CHECKS), "Execution audit check inventory changed")
    reasons = []
    if value.get("reviewer_kind") != "human":
        reasons.append("execution_audit_not_human")
    if not _text(value.get("reviewer")) or value.get("reviewed_at") is None:
        reasons.append("execution_audit_unattributed")
    else:
        _require(_time(value["reviewed_at"]) >= finished, "Execution audit predates the evidence it judges")
    if value["decision"] != "accept":
        reasons.append("execution_audit_" + value["decision"])
    for key, check in checks.items():
        _require(isinstance(check, dict) and check.get("decision") in {"verified", "rejected", "unresolved"}
                 and isinstance(check.get("sources"), list), "Malformed execution audit check")
        for ref in check["sources"]:
            sources.get(ref)
        cited_kinds = {sources.files[ref["artifact"]][0]["kind"] for ref in check["sources"]}
        if (check["decision"] != "verified" or not _text(check.get("rationale"))
                or not AUDIT_SOURCE_KINDS[key] <= cited_kinds):
            reasons.append("execution_audit_" + key + "_unverified")
    return reasons


def _checks(report, manifest, role=None, pid=None):
    paths = [manifest["positive"]] + [x["path"] for x in manifest["negative"]]
    rows = report.get("checks", [])
    _require(report.get("kind") == ("actual-file-open" if role is None else "live-pid-policy-query")
             and report.get("role") == role and (pid is None or report.get("pid") == pid)
             and report.get("prompt_sha256") == manifest["sha256"]
             and report.get("passed") is True and [x.get("path") for x in rows] == paths
             and all(x.get("passed") is True for x in rows), "Incomplete or mismatched actual OS probe evidence")
    for number, row in enumerate(rows):
        _require(row.get("expected") == ("allowed" if number == 0 else "denied"),
                 "OS probe expected permissions changed")
        if role is None and number:
            _require(row.get("outcome") == "DENIED" and type(row.get("errno")) is int
                     and row["errno"] in {errno.EPERM, errno.EACCES},
                     "A missing probe file or other error is not a denied open")
        if role is None and number == 0:
            _require(row.get("observed_sha256") == manifest["sha256"],
                     "The positive file-open probe lacks the observed input hash")
        if role is not None:
            result = row.get("result")
            _require(type(result) is int and (result == 0 if number == 0 else result > 0),
                     "Actual PID permission result contradicts the probe")
    _time(report.get("utc"))


def _isolation(value, sources, requirements, invocation, input_sha256, evaluator_files, events_ref):
    _require(isinstance(value, dict), "Actual isolation observations must be an object")
    policy = sources.get(value.get("policy"), "policy")
    _require(digest_bytes(policy) == value.get("policy_sha256"), "Applied isolation policy hash changed")
    roots = value.get("deny_roots")
    _require(isinstance(roots, list) and roots and all(isinstance(x, str) and Path(x).is_absolute() for x in roots),
             "Isolation evidence lacks explicit protected roots")
    _require(value.get("read_exceptions") == requirements["read_exceptions"],
             "Unexplained isolation read exceptions")
    manifest = value.get("probe_manifest", {})
    negative = manifest.get("negative", [])
    _require(isinstance(negative, list) and set(requirements["denied_categories"]) <= {
        x.get("category") for x in negative} and manifest.get("sha256") == input_sha256
        and isinstance(manifest.get("positive"), str) and Path(manifest["positive"]).is_absolute(),
        "Isolation probes omit actual input or protected categories")
    _require(len({x.get("path") for x in negative}) == len(negative), "Duplicate negative isolation probes")
    _require({x["sha256"] for x in evaluator_files} <= {
        x.get("sha256_before_run") for x in negative if x.get("category") == "reference"},
        "Reference/rubric probes do not bind this execution's protected evaluator material")
    original_root = value.get("evaluator_root")
    _require(isinstance(original_root, str) and Path(original_root).is_absolute()
             and any(Path(original_root).is_relative_to(root) for root in roots),
             "Protected roots omit the execution's evaluator directory")
    for evaluator in evaluator_files:
        expected_path = str(Path(original_root) / evaluator["path"])
        _require(any(x.get("category") == "reference" and x.get("path") == expected_path
                     and x.get("sha256_before_run") == evaluator["sha256"] for x in negative),
                 "Protected probes must open this execution's frozen reference and rubric")
    for row in negative:
        path = row.get("path")
        _require(isinstance(path, str) and Path(path).is_absolute() and row.get("exists_before_run") is True
                 and any(Path(path).is_relative_to(root) for root in roots),
                 "Negative isolation probe was absent or outside protected roots")
        for exception in value["read_exceptions"]:
            _require(isinstance(exception, dict) and _text(exception.get("purpose"))
                     and exception.get("kind") in {"literal", "subpath"}
                     and isinstance(exception.get("path"), str) and Path(exception["path"]).is_absolute(),
                     "Read exceptions require exact paths and purposes")
            _require(not (path == exception["path"] or exception["kind"] == "subpath"
                         and Path(path).is_relative_to(exception["path"])), "An exception permits a protected probe")
    opened = value.get("open_probe", {})
    _checks(opened, manifest)
    _require(_time(opened["utc"]) <= _time(invocation["submitted_at"]), "File-open probes occurred after submission")
    processes = value.get("processes", [])
    parents = [x for x in processes if x.get("role") == "parent"]
    workers = [x for x in processes if x.get("role") == "worker"]
    _require(len(parents) == 1 and workers and len(processes) == len(parents) + len(workers),
             "Isolation evidence must identify the actual parent and every worker")
    parent = parents[0]
    _require(parent.get("pid") == invocation.get("parent_pid"), "Invocation parent PID attribution mismatch")
    pids = []
    for process in processes:
        pid = process.get("pid")
        _require(type(pid) is int and pid > 0 and type(process.get("ppid")) is int
                 and _hash(process.get("executable_sha256"))
                 and _time(invocation["started_at"]) <= _time(process.get("started_at")) <= _time(invocation["finished_at"]),
                 "Actual process identity or lifetime evidence is missing")
        if process["role"] == "worker":
            _require(process["ppid"] == parent["pid"] or pid == parent["pid"]
                     and value.get("in_process_worker") is True, "Actual worker lacks parent provenance")
        pids.append((process["role"], pid))
    _require(len(set(pids)) == len(pids), "Duplicate actual process evidence")
    reports = value.get("pid_checks", [])
    _require(len(reports) == len(processes) and {(x.get("role"), x.get("pid")) for x in reports} == set(pids),
             "Actual worker permission evidence is incomplete")
    for report in reports:
        _checks(report, manifest, report["role"], report["pid"])
        process = next(x for x in processes if (x["role"], x["pid"]) == (report["role"], report["pid"]))
        _require(_time(process["started_at"]) <= _time(report["utc"]) <= _time(invocation["finished_at"]),
                 "PID evidence is outside the identified process lifetime")
        if report["role"] == "parent":
            _require(_time(report["utc"]) <= _time(invocation["submitted_at"]), "Parent policy was checked after submission")
    inheritance = value.get("policy_inheritance", {})
    _require(inheritance.get("parent_pid") == parent["pid"]
             and inheritance.get("worker_pids") == [x["pid"] for x in workers]
             and _time(parent["started_at"]) <= _time(inheritance.get("verified_at")) <= _time(invocation["submitted_at"]),
             "Worker policy inheritance was not bound before submission")
    state = value.get("fresh_state", {})
    _require(isinstance(state.get("path"), str) and Path(state["path"]).is_absolute()
             and state.get("initial_entries") == [] and state.get("resumed_from") is None
             and _time(state.get("created_at")) <= _time(invocation["started_at"]), "Fresh candidate state is unverified")
    tools = value.get("tools", {})
    _require(tools.get("effective_allowed") == requirements["allowed_tools"]
             and tools.get("internal") == requirements["internal_tools"] and isinstance(tools.get("calls"), list),
             "Effective tool permissions differ from the frozen requirement")
    allowed = set(requirements["allowed_tools"] + requirements["internal_tools"])
    _require(all(isinstance(x, dict) and x.get("name") in allowed for x in tools["calls"]),
             "Actual invocation used a tool outside its frozen permissions")
    registry_ref, calls_ref = tools.get("registry"), tools.get("call_records")
    _require(isinstance(registry_ref, dict) and isinstance(calls_ref, dict)
             and registry_ref.get("artifact") == calls_ref.get("artifact") == events_ref["artifact"],
             "Effective tool registry and calls must come from this invocation's event log")
    registry = sources.get(registry_ref, "cli-events")
    calls = sources.get(calls_ref, "cli-events")
    _require(isinstance(registry, list) and all(isinstance(x, dict) for x in registry)
             and len({x.get("name") for x in registry}) == len(registry)
             and all(isinstance(x, dict) and _text(x.get("name"))
                     and x.get("classification") in {"candidate", "internal"}
                     and x.get("permission") in {"allowed", "denied"}
                     and (x["classification"] != "internal" or x["name"] in INTERNAL_BOOKKEEPING) for x in registry)
             and sorted(x["name"] for x in registry if x["classification"] == "candidate" and x["permission"] == "allowed")
             == sorted(requirements["allowed_tools"])
             and sorted(x["name"] for x in registry if x["classification"] == "internal" and x["permission"] == "allowed")
             == sorted(requirements["internal_tools"]) and calls == tools["calls"],
             "Effective event registry/calls contradict frozen candidate/internal permissions")
    controls = tools.get("controls", {})
    denied = sources.get(controls.get("denied"), "tool-control")
    enabled = sources.get(controls.get("enabled"), "tool-control")
    tool = requirements["tool_control_tool"]
    _require(isinstance(denied, dict) and isinstance(enabled, dict)
             and denied.get("prompt_sha256") == enabled.get("prompt_sha256")
             and _hash(denied.get("prompt_sha256"))
             and denied.get("tool") == enabled.get("tool") == tool
             and denied.get("effective_tools") == requirements["allowed_tools"]
             and enabled.get("effective_tools") == requirements["allowed_tools"] + [tool]
             and denied.get("result") == "denied" and enabled.get("result") == "succeeded"
             and _text(denied.get("request_id")) and _text(enabled.get("request_id"))
             and denied["request_id"] != enabled["request_id"]
             and _time(denied.get("finished_at")) <= _time(invocation["submitted_at"])
             and _time(enabled.get("finished_at")) <= _time(invocation["submitted_at"]),
             "Effective tool capability lacks paired source-bound controls")
    network_refs = value.get("network_probes", [])
    _require(isinstance(network_refs, list), "Isolation network probes need raw source references")
    network = [sources.get(ref, "network-probe") for ref in network_refs]
    for probe in network:
        _require(isinstance(probe, dict) and (probe.get("role"), probe.get("pid")) in pids
                 and probe.get("target") in {"localhost", "internet"} and _text(probe.get("address"))
                 and type(probe.get("port")) is int and 0 < probe["port"] <= 65535,
                 "Actual network probe lacks its process and attempted endpoint")
        process = next(x for x in processes if (x["role"], x["pid"]) == (probe["role"], probe["pid"]))
        _require(_time(process["started_at"]) <= _time(probe.get("utc")) <= _time(invocation["finished_at"]),
                 "Actual network probe is outside the identified process lifetime")
        _require(probe.get("result") == "denied" and (
            probe.get("kind") == "live-pid-network-query" and type(probe.get("result_code")) is int and probe["result_code"] > 0
            or probe.get("kind") == "actual-connect" and type(probe.get("errno")) is int
            and probe["errno"] in {errno.EACCES, errno.EPERM}), "Network denial lacks a policy or actual connect result")
    _require({("parent", parent["pid"], "localhost")} | {("worker", x["pid"], "internet") for x in workers}
             <= {(x["role"], x["pid"], x["target"]) for x in network},
             "Isolation evidence omits actual parent/worker network probes")
    return state["path"]


@_structured
def _validate(root, meta, records, record, submission, sources):
    from .reliability import _slot_path
    _integrity(isinstance(submission, dict) and submission.get("schema") == SUBMISSION
             and submission.get("slot_id") == record["slot_id"]
             and submission.get("binding") == _binding(root, meta, record, records),
             "Execution submission binds different original evidence")
    reasons = []
    if record.get("origin", meta["origin"]) != "command":
        reasons.append("execution_origin_not_command")
        if record.get("origin", meta["origin"]) == "external_import":
            reasons.append("external_origin_unverified")
    if not record.get("started") or record.get("response_sha256") is None:
        reasons.append("execution_without_original_response")
    requirements = _requirements(meta)
    if requirements is None:
        reasons.append("execution_requirements_unfrozen")
    observations = submission.get("observations", {})
    rows = observations.get("attempts", [])
    _integrity(isinstance(rows, list) and all(isinstance(x, dict) and type(x.get("number")) is int for x in rows)
               and [x.get("number") for x in rows] == [x["number"] for x in record["attempts"]],
             "Execution source must retain every transport attempt in order")
    projected = (_json_file(root, _slot_path(record["slot_id"]) + "/projected-request.json")
                 if record["attempts"] else None)
    parameters = projected["parameters"] if projected is not None else {}
    if not _text(parameters.get("model")):
        reasons.append("requested_model_unfrozen")
    if "reasoning_effort" in parameters:
        _require(_text(parameters["reasoning_effort"]), "Requested reasoning effort must be explicit text")
    for key in ("max_output_tokens", "max_completion_tokens"):
        if key in parameters:
            _require(type(parameters[key]) is int and parameters[key] > 0, "Requested output cap must be a positive integer")
    sessions, states, request_ids = [], [], []
    finished = max((_time(x["finished_at"]) for x in record["attempts"]), default=_time(meta["created_at"]))
    for observation, attempt in zip(rows, record["attempts"]):
        number = attempt["number"]
        submission_state = observation.get("submission_state", "unknown")
        _integrity(submission_state in {"submitted", "not-submitted", "unknown"},
                   "Attempt submission_state must be submitted, not-submitted or unknown")
        if submission_state == "unknown":
            reasons.append(f"attempt_{number}_submission_state_unverified")
            continue
        if submission_state == "not-submitted":
            invocation = sources.get(observation.get("invocation"), "invocation")
            error = sources.get(observation.get("stderr"), "stderr")
            events = sources.get(observation.get("events"), "cli-events")
            raw = sources.get(observation.get("response", {}).get("text"), "client-output")
            if isinstance(raw, str):
                raw = raw.encode("utf-8")
            _require(isinstance(invocation, dict) and attempt["readable_text"] is False
                     and attempt["status"] in {"transient_error", "permanent_error", "timeout", "budget_exhausted"}
                     and isinstance(raw, bytes) and not raw.strip() and digest_bytes(raw) == attempt["response_sha256"]
                     and isinstance(error, bytes) and digest_bytes(error) == attempt["stderr_sha256"]
                     and isinstance(events, bytes) and events
                     and invocation.get("events_sha256") == digest_bytes(events)
                     and invocation.get("argv") == meta["execution_contract"]["command"]
                     and invocation.get("request_sha256") == record["projected_request_sha256"]
                     and invocation.get("response_sha256") == attempt["response_sha256"]
                     and invocation.get("stderr_sha256") == attempt["stderr_sha256"]
                     and type(invocation.get("request_count")) is int and invocation["request_count"] == 0
                     and invocation.get("request_id") is None and invocation.get("submitted_at") is None
                     and invocation.get("failure_stage") in {"startup", "before-submission"}
                     and _text(invocation.get("failure_reason"))
                     and invocation.get("transport_status") == attempt["status"]
                     and type(invocation.get("exit_code")) is type(attempt.get("exit_code"))
                     and invocation.get("exit_code") == attempt.get("exit_code")
                     and type(invocation.get("timeout_seconds")) in (int, float)
                     and invocation["timeout_seconds"] == meta["timeout_seconds"],
                     "Unsubmitted attempt lacks source-bound local failure and zero request evidence")
            start, finish = (_time(invocation.get(k)) for k in ("started_at", "finished_at"))
            _require(_time(attempt["started_at"]) <= start <= finish <= _time(attempt["finished_at"])
                     and _time(invocation.get("deadline_at")) == start + timedelta(seconds=meta["timeout_seconds"]),
                     "Unsubmitted local failure timing differs from its original transport attempt")
            _require(all(ref is None for group in ("request", "backend") for ref in observation.get(group, {}).values())
                     and observation["response"].get("request_id") is None,
                     "Unsubmitted attempt cannot assert a provider request or response")
            continue
        # Null values remain unknown. An accept checkbox never supplies them.
        groups = {"request": ("messages", "parameters", "request_id"),
                  "backend": ("provider", "model", "parameters", "request_id") +
                             (("reasoning_effort",) if "reasoning_effort" in parameters else ()),
                  "response": ("text", "request_id")}
        complete = True
        for group, fields in groups.items():
            row = observation.get(group)
            _require(isinstance(row, dict), "Malformed execution observation group")
            for field in fields:
                if row.get(field) is None:
                    reasons.append(f"attempt_{number}_{group}_{field}_unverified")
                    complete = False
        for field in ("stderr", "events", "invocation", "context", "isolation"):
            if observation.get(field) is None:
                reasons.append(f"attempt_{number}_{field}_unverified")
                complete = False
        if not complete or requirements is None or not _text(parameters.get("model")):
            continue
        request = {k: sources.get(observation["request"][k], "provider-request") for k in groups["request"]}
        backend = {k: sources.get(observation["backend"][k], "provider-metadata") for k in groups["backend"]}
        response = {k: sources.get(observation["response"][k], "provider-response") for k in groups["response"]}
        _require(_text(request["request_id"]) and request["request_id"] == backend["request_id"] == response["request_id"],
                 "Provider request/response metadata lacks the same invocation identity")
        _require(request["messages"] == projected["messages"], "Actual candidate messages differ from frozen history")
        _parameters(request["parameters"], parameters, requirements)
        _parameters(backend["parameters"], parameters, requirements)
        if (backend["model"] is None or backend["provider"] is None
                or "reasoning_effort" in parameters and backend.get("reasoning_effort") is None):
            reasons.append(f"attempt_{number}_backend_observation_unknown")
        else:
            _require(_text(backend["provider"]) and _matches(backend["model"], parameters["model"], requirements.get("model_aliases", {}))
                     and ("reasoning_effort" not in parameters or _matches(backend["reasoning_effort"],
                          parameters["reasoning_effort"], requirements.get("effort_aliases", {}))),
                     "Observed backend model or effort differs from frozen request")
            if "provider" in requirements:
                _require(backend["provider"] == requirements["provider"], "Observed backend provider mismatch")
        text = response["text"]
        raw = text.encode("utf-8") if isinstance(text, str) else text
        _require(isinstance(raw, bytes) and digest_bytes(raw) == attempt["response_sha256"],
                 "Original provider response does not match the locked transport evidence")
        error = sources.get(observation["stderr"], "stderr")
        events = sources.get(observation["events"], "cli-events")
        _require(isinstance(error, bytes) and isinstance(events, bytes) and events
                 and digest_bytes(error) == attempt["stderr_sha256"], "Original stderr/event evidence is incomplete or changed")
        invocation = sources.get(observation["invocation"], "invocation")
        _require(isinstance(invocation, dict) and invocation.get("argv") == meta["execution_contract"]["command"]
                 and invocation.get("request_sha256") == record["projected_request_sha256"]
                 and invocation.get("response_sha256") == attempt["response_sha256"]
                 and invocation.get("stderr_sha256") == attempt["stderr_sha256"]
                 and invocation.get("events_sha256") == digest_bytes(events)
                 and invocation.get("request_id") == request["request_id"]
                 and type(invocation.get("request_count")) is int and invocation["request_count"] == 1
                 and invocation.get("transport_status") == attempt["status"]
                 and type(invocation.get("exit_code")) is type(attempt.get("exit_code"))
                 and invocation.get("exit_code") == attempt.get("exit_code")
                 and type(invocation.get("timeout_seconds")) in (int, float)
                 and invocation["timeout_seconds"] == meta["timeout_seconds"],
                 "Original invocation, attempt or timeout contract mismatch")
        start, submit, finish = (_time(invocation.get(k)) for k in ("started_at", "submitted_at", "finished_at"))
        _require(_time(attempt["started_at"]) <= start <= submit <= finish <= _time(attempt["finished_at"])
                 and _time(invocation.get("deadline_at")) == start + timedelta(seconds=meta["timeout_seconds"]),
                 "Original invocation timing or frozen deadline mismatch")
        mode = invocation.get("session_mode")
        _require(mode in {"stateful", "stateless"}
                 and (_text(invocation.get("session_id")) if mode == "stateful" else invocation.get("session_id") is None),
                 "Invocation needs its actual stateful identity or explicit stateless transport")
        context = sources.get(observation["context"], "context")
        _require(isinstance(context, dict) and context.get("session_id") == invocation.get("session_id")
                 and context.get("session_mode") == mode
                 and context.get("supplied_messages_complete") is True and context.get("hidden_session") is False
                 and context.get("fresh") is True and context.get("resumed_from") is None
                 and context.get("history_sha256") == record["history_sha256"]
                 and context.get("messages") == projected["messages"]
                 and context.get("ancestors") == submission["binding"]["ancestors"]
                 and context.get("excluded_context") == ["prior_answers", "peer_branches", "review_material", "memory"],
                 "Fresh context, branch ancestry or peer exclusion evidence mismatch")
        isolation = sources.get(observation["isolation"], "isolation")
        if record["evidence_origin_run_id"] == meta["run_id"]:
            _require(isolation.get("evaluator_root") == str(root), "Isolation probes target an unrelated evaluator directory")
        evaluator_files = [meta["inputs"][record["case_id"]][key] for key in ("reference", "rubric")]
        state = _isolation(isolation, sources, requirements, invocation,
                           digest_bytes(json.dumps(projected, ensure_ascii=False).encode("utf-8")), evaluator_files,
                           observation["events"])
        if mode == "stateful":
            sessions.append(invocation["session_id"])
        states.append(state)
        request_ids.append(request["request_id"])
    _require(len(set(sessions)) == len(sessions) and len(set(states)) == len(states),
             "Transport retries reused candidate state or conversation")
    _require(len(set(request_ids)) == len(request_ids), "Transport retries reused a provider request identity")
    if observations.get("ledger") is None:
        reasons.append("attempt_ledger_unverified")
    else:
        ledger = sources.get(observations["ledger"], "ledger")
        expected = [{"evidence_id": record["evidence_id"], "number": a["number"],
                     "request_sha256": record["projected_request_sha256"],
                     "response_sha256": a["response_sha256"], "stderr_sha256": a["stderr_sha256"],
                     "status": a["status"], "request_count": {"submitted": 1, "not-submitted": 0}.get(
                         observation.get("submission_state"))} for a, observation in zip(record["attempts"], rows)]
        _require(isinstance(ledger, dict) and ledger.get("origin_run_id") == record["evidence_origin_run_id"]
                 and ledger.get("attempts") == expected and isinstance(ledger.get("other_activity"), list),
                 "Original attempt ledger is incomplete or mismatched")
        _require(all(type(x.get("number")) is int and (type(x.get("request_count")) is int or x.get("request_count") is None)
                     for x in ledger["attempts"]), "Attempt ledger counts must be integers")
        origin_manifest = sources.get(ledger.get("origin_manifest"), "ledger")
        _require(isinstance(origin_manifest, dict) and origin_manifest.get("run_id") == record["evidence_origin_run_id"]
                 and origin_manifest.get("plan_sha256") == meta["plan_sha256"]
                 and origin_manifest.get("execution_contract_sha256") == meta["execution_contract_sha256"]
                 and identity(origin_manifest.get("execution_contract")) == meta["execution_contract_sha256"]
                 and origin_manifest.get("slot_record_sha256", {}).get(record["slot_id"])
                     == submission["binding"]["slot_record_sha256"], "Original generation manifest provenance mismatch")
        if record["evidence_origin_run_id"] == meta["run_id"]:
            _require(origin_manifest == _json_file(root, "run.json"),
                     "Origin manifest omits this run's original generation/peer inventory")
        peers = [{"evidence_id": eid, "slot_id": item["slot_id"],
                  "slot_record_sha256": item["slot_record_sha256"], "transport_attempts": item["transport_attempts"]}
                 for eid, item in sorted(origin_manifest.get("budget_evidence", {}).items())
                 if eid != record["evidence_id"]]
        _require(ledger.get("peer_provenance") == peers,
                 "Attempt ledger omits known original peer generation provenance")
        for activity in ledger["other_activity"]:
            _require(isinstance(activity, dict) and _text(activity.get("id"))
                     and activity.get("kind") in {"inspection", "inventory", "startup", "non_math_canary", "math"}
                     and type(activity.get("request_count")) is int and activity["request_count"] >= 0
                     and isinstance(activity.get("sources"), list) and activity["sources"],
                     "Related activity lacks explicit provenance")
            for ref in activity["sources"]:
                sources.get(ref)
    reasons.extend(_audit(submission.get("audit"), sources, finished))
    return {"eligible": not reasons, "reasons": sorted(set(reasons)), "sessions": sessions,
            "states": states, "request_ids": request_ids, "observation_errors": []}


@_structured
def _assess(root, meta, records, record, submission, sources):
    """Rejecting a genuine bad observation must not require altering its bytes.

    Files, references, attempt inventory and original-generation binding always
    pass hard integrity checks first. A human rejection may then retain a failed
    admissibility observation and its deterministic diagnostic as ineligible.
    """
    _integrity(isinstance(submission, dict) and submission.get("schema") == SUBMISSION
               and submission.get("slot_id") == record["slot_id"]
               and submission.get("binding") == _binding(root, meta, record, records),
               "Execution submission binds different original evidence")
    observations = submission.get("observations")
    _integrity(isinstance(observations, dict) and isinstance(observations.get("attempts"), list),
               "Malformed execution observation inventory")
    rows = observations["attempts"]
    _integrity(all(isinstance(x, dict) and type(x.get("number")) is int for x in rows)
               and [x["number"] for x in rows] == [x["number"] for x in record["attempts"]],
               "Execution source must retain every transport attempt in order")
    for row in rows:
        _integrity(all(isinstance(row.get(key), dict) for key in ("request", "backend", "response")),
                   "Malformed execution observation groups")
    visited = set()

    def check_references(value):
        if isinstance(value, dict):
            if "artifact" in value:
                token = identity(value)
                if token not in visited:
                    visited.add(token)
                    check_references(sources.get(value))
            else:
                for nested in value.values():
                    check_references(nested)
        elif isinstance(value, list):
            for nested in value:
                check_references(nested)

    check_references(observations)
    check_references(submission.get("audit"))
    try:
        return _validate(root, meta, records, record, submission, sources)
    except _IntegrityError:
        raise
    except ValueError as error:
        audit = submission.get("audit", {})
        _require(audit.get("decision") == "reject", str(error))
        _integrity(audit.get("reviewer_kind") == "human" and _text(audit.get("reviewer"))
                   and audit.get("reviewed_at") is not None, "Rejecting observations requires an attributed human audit")
        finished = max((_time(x["finished_at"]) for x in record["attempts"]), default=_time(meta["created_at"]))
        reasons = _audit(audit, sources, finished)
        _integrity(any(x.get("decision") == "rejected" and _text(x.get("rationale")) and x.get("sources")
                       for x in audit["checks"].values()), "Rejecting observations requires a sourced rejection rationale")
        sessions, states, request_ids = [], [], []
        for observation in rows:
            if observation.get("invocation") is not None:
                invocation = sources.get(observation["invocation"])
                _integrity(isinstance(invocation, dict), "Malformed rejected invocation")
                if invocation.get("session_mode") == "stateful" and _text(invocation.get("session_id")):
                    sessions.append(invocation["session_id"])
                if _text(invocation.get("request_id")):
                    request_ids.append(invocation["request_id"])
            if observation.get("isolation") is not None:
                isolation = sources.get(observation["isolation"])
                _integrity(isinstance(isolation, dict), "Malformed rejected isolation record")
                state = isolation.get("fresh_state", {}).get("path")
                if _text(state):
                    states.append(state)
        return {"eligible": False, "reasons": sorted(set(reasons + ["execution_observation_rejected"])),
                "sessions": sessions, "states": states, "request_ids": request_ids, "observation_errors": [str(error)]}


def _load_snapshot(root, selector=None):
    base = root / "eligibility"
    if not base.exists():
        _require(selector is None, "Requested execution audit snapshot does not exist")
        return {}, None
    _require(not base.is_symlink(), "Execution audit directory cannot be a symlink")
    if not (base / "current.json").exists():
        _require(selector is None and not list((base / "snapshots").glob("*.json")),
                 "Execution audit snapshot index is missing")
        return {}, None
    index = _json_file(root, "eligibility/current.json")
    _require(isinstance(index, dict) and set(index) == {"schema", "snapshot_sha256"}
             and index["schema"] == "math-gauge.execution-eligibility-index/v1" and _hash(index["snapshot_sha256"]),
             "Unsupported execution audit snapshot index")
    chosen = selector or index["snapshot_sha256"]
    _require(_hash(chosen), "Execution audit snapshot selector must be its SHA-256")
    selected = None
    digest = index["snapshot_sha256"]
    seen = set()
    while digest is not None:
        _require(_hash(digest) and digest not in seen, "Execution audit snapshot chain is invalid")
        seen.add(digest)
        value = _json_file(root, f"eligibility/snapshots/{digest}.json")
        _require(isinstance(value, dict) and value.get("schema") == SNAPSHOT
                 and value.get("snapshot_sha256") == digest
                 and identity({k: v for k, v in value.items() if k != "snapshot_sha256"}) == digest
                 and isinstance(value.get("receipts"), dict), "Append-only execution audit snapshot changed")
        for eid, receipt in value["receipts"].items():
            _require(_hash(eid) and _hash(receipt), "Invalid original evidence/audit identity")
        if digest == chosen:
            selected = value
        digest = value.get("previous_snapshot_sha256")
    _require(selected is not None, "Requested execution audit snapshot is outside the retained chain")
    return selected["receipts"], {"sha256": chosen, "latest_sha256": index["snapshot_sha256"],
                                  "historical": chosen != index["snapshot_sha256"]}


def _receipt(root, digest, _seen=None):
    _seen = set() if _seen is None else _seen
    _require(digest not in _seen, "Execution audit revision chain is cyclic")
    _seen.add(digest)
    relative = f"eligibility/receipts/{digest}/receipt.json"
    receipt = _json_file(root, relative)
    _require(isinstance(receipt, dict) and receipt.get("schema") == RECEIPT
             and receipt.get("receipt_sha256") == digest
             and identity({k: v for k, v in receipt.items() if k != "receipt_sha256"}) == digest,
             "Immutable execution eligibility receipt changed")
    _require(_hash(receipt.get("verifier_sha256")), "Execution eligibility import verifier identity is missing")
    submission = receipt.get("submission", {})
    _require(receipt.get("audit_sha256") == identity(submission.get("audit")), "Execution audit identity changed")
    previous = receipt.get("previous_receipt_sha256")
    if previous is not None:
        _require(_hash(previous), "Execution audit revision has invalid prior identity")
        prior, _, _ = _receipt(root, previous, _seen)
        _require(prior.get("submission", {}).get("binding") == submission.get("binding"),
                 "Execution audit revision changes original generation provenance")
    return receipt, _Sources(root / f"eligibility/receipts/{digest}/artifacts", submission.get("artifacts")), relative


def _append_snapshot(root, receipts, previous, expected_index=None):
    base = root / "eligibility"
    if base.exists():
        _require(not base.is_symlink(), "Execution audit directory cannot be a symlink")
    current_path = base / "current.json"
    if current_path.exists():
        _require(_json_file(root, "eligibility/current.json").get("snapshot_sha256") == expected_index,
                 "Execution audit snapshot changed concurrently")
    else:
        _require(expected_index is None, "Expected execution audit snapshot disappeared")
    value = {"schema": SNAPSHOT, "created_at": now(), "previous_snapshot_sha256": previous,
             "receipts": dict(sorted(receipts.items()))}
    value["snapshot_sha256"] = identity(value)
    _write_new(base / "snapshots" / (value["snapshot_sha256"] + ".json"), value)
    index = {"schema": "math-gauge.execution-eligibility-index/v1", "snapshot_sha256": value["snapshot_sha256"]}
    temporary = base / (".current-" + value["snapshot_sha256"] + ".json")
    _write_new(temporary, index)
    os.replace(temporary, current_path)
    return {"sha256": value["snapshot_sha256"], "latest_sha256": value["snapshot_sha256"], "historical": False}


@_serialized
def import_execution_eligibility(root, slot_id, source, destination=None, *, revise=False, expected_snapshot=None):
    """Freeze an explicit external evidence submission and append its audit.

    ``source`` is a submission JSON file; relative artifact paths are resolved
    only under its directory.  ``destination`` optionally exports the result
    JSON to a new file; canonical receipts always stay inside this run.
    """
    root, source = _root(root), Path(source).absolute()
    source_root = _root(source.parent)
    submission = _json_file(source_root, source.name)
    meta, records = _run(root)
    _require(slot_id in records, "Unknown execution eligibility slot")
    sources = _Sources(source_root, submission.get("artifacts"))
    result = _assess(root, meta, records, records[slot_id], submission, sources)
    saved, prior = _load_snapshot(root)
    previous = prior["sha256"] if prior else None
    if expected_snapshot is not None:
        _require(expected_snapshot == previous, "Execution audit differs from expected snapshot")
    eid = records[slot_id]["evidence_id"]
    _require(eid not in saved or revise and expected_snapshot == previous,
             "Execution audit exists; explicit revise and expected_snapshot are required")
    for other_record in records.values():
        other_eid = other_record["evidence_id"]
        if other_eid == eid or other_eid not in saved:
            continue
        old_receipt, old_sources, _ = _receipt(root, saved[other_eid])
        old_result = _assess(root, meta, records, other_record, old_receipt["submission"], old_sources)
        for field in ("sessions", "states", "request_ids"):
            _require(not set(result[field]).intersection(old_result[field]),
                     "Independent/peer execution evidence reused " + field)
    receipt = {"schema": RECEIPT, "imported_at": now(), "verifier_sha256": digest_bytes(Path(__file__).read_bytes()),
               "previous_receipt_sha256": saved.get(eid), "submission": copy.deepcopy(submission),
               "audit_sha256": identity(submission["audit"]), "integrity_result": result, "limits": LIMITS}
    receipt["receipt_sha256"] = identity(receipt)
    digest = receipt["receipt_sha256"]
    base = root / "eligibility"
    base.mkdir(exist_ok=True)
    _require(not base.is_symlink(), "Execution audit directory cannot be a symlink")
    receipts_dir = base / "receipts"
    receipts_dir.mkdir(exist_ok=True)
    _require(not receipts_dir.is_symlink(), "Execution receipt directory cannot be a symlink")
    staging = Path(tempfile.mkdtemp(prefix=".import-", dir=receipts_dir))
    try:
        for name, (_, data) in sources.files.items():
            output = staging / "artifacts" / name
            output.parent.mkdir(parents=True, exist_ok=True)
            with output.open("xb") as stream:
                stream.write(data)
        # Empty source sets still have an explicit, empty artifact directory.
        (staging / "artifacts").mkdir(exist_ok=True)
        _write_new(staging / "receipt.json", receipt)
        _require(not (receipts_dir / digest).exists(), "Immutable execution receipt already exists")
        staging.rename(receipts_dir / digest)
    finally:
        if staging.exists():
            shutil.rmtree(staging)
    updated = dict(saved, **{eid: digest})
    snapshot = _append_snapshot(root, updated, previous, previous)
    value = {**verify_execution_eligibility(root)["slots"][slot_id], "integrity_eligible": result["eligible"]}
    if destination is not None:
        _write_new(Path(destination), value)
    return value


def copy_execution_eligibility(source_root, destination, evidence_ids=None):
    """Copy selected immutable original audits before dependent candidate calls.

    Destination need not have run.json yet. No source path is used later to
    recover an audit; the copied raw files remain independently checkable.
    """
    with _audit_lock(destination):
        return _copy_execution_eligibility(source_root, destination, evidence_ids)


def _copy_execution_eligibility(source_root, destination, evidence_ids=None):
    source_root, destination = _root(source_root), _root(destination)
    saved, source_snapshot = _load_snapshot(source_root)
    wanted = set(saved) if evidence_ids is None else set(evidence_ids)
    saved = {eid: digest for eid, digest in saved.items() if eid in wanted}
    if not saved:
        return None
    target, current = _load_snapshot(destination)
    def copy_receipt(digest):
        receipt, sources, _ = _receipt(source_root, digest)
        previous_receipt = receipt.get("previous_receipt_sha256")
        if previous_receipt is not None:
            copy_receipt(previous_receipt)
        target_dir = destination / f"eligibility/receipts/{digest}"
        if target_dir.exists():
            _receipt(destination, digest)
            return
        _root(target_dir.parent)
        target_dir.mkdir(parents=True)
        _write_new(target_dir / "receipt.json", receipt)
        for name, (_, data) in sources.files.items():
            path = target_dir / "artifacts" / name
            path.parent.mkdir(parents=True, exist_ok=True)
            with path.open("xb") as stream:
                stream.write(data)
        (target_dir / "artifacts").mkdir(exist_ok=True)

    for eid, digest in saved.items():
        _require(eid not in target or target[eid] == digest, "Conflicting inherited execution audits")
        copy_receipt(digest)
        target[eid] = digest
    previous = current["sha256"] if current else None
    return _append_snapshot(destination, target, previous, previous)


def verify_execution_eligibility(root, meta=None, records=None, *, audit_snapshot=None):
    """Re-open and revalidate every selected audit, then enforce ancestry/peers."""
    root = _root(root)
    meta, records = _run(root, meta, records)
    saved, snapshot = _load_snapshot(root, audit_snapshot)
    result, sessions, states, request_ids = {}, {}, {}, {}
    for sid, record in records.items():
        eid = record["evidence_id"]
        digest = saved.get(eid)
        row = {"slot_id": sid, "evidence_id": eid, "eligible": False,
               "reasons": ["execution_evidence_missing"], "receipt_path": None, "receipt_sha256": None,
               "integrity_eligible": False, "integrity_reasons": ["execution_evidence_missing"],
               "observation_errors": [],
               "audit_sha256": None, "audit_snapshot": snapshot,
               "observed_sessions": [], "observed_states": [], "observed_request_ids": []}
        if digest is not None:
            receipt, sources, relative = _receipt(root, digest)
            checked = _assess(root, meta, records, record, receipt["submission"], sources)
            _require(checked == receipt.get("integrity_result"), "Recomputed execution evidence result changed")
            row.update({k: checked[k] for k in ("eligible", "reasons")}, receipt_path=relative,
                       receipt_sha256=digest, audit_sha256=receipt["audit_sha256"],
                       integrity_eligible=checked["eligible"], integrity_reasons=list(checked["reasons"]),
                       observation_errors=list(checked["observation_errors"]),
                       observed_sessions=checked["sessions"], observed_states=checked["states"],
                       observed_request_ids=checked["request_ids"])
            for value, index, label in ((checked["sessions"], sessions, "session"), (checked["states"], states, "state"),
                                        (checked["request_ids"], request_ids, "provider request identity")):
                for key in value:
                    if key in index and index[key] != sid:
                        raise ValueError("Independent/peer invocations reused candidate " + label)
                    index[key] = sid
        if record.get("origin", meta["origin"]) != "command":
            row["eligible"] = False
            row["reasons"] = sorted(set(row["reasons"] + ["execution_origin_not_command"]))
            if record.get("origin", meta["origin"]) == "external_import":
                row["reasons"] = sorted(set(row["reasons"] + ["external_origin_unverified"]))
        parent = record.get("parent_slot")
        if parent is not None and (parent not in result or not result[parent]["eligible"]):
            row["eligible"] = False
            row["reasons"] = sorted(set(row["reasons"] + ["ancestor_execution_ineligible"]))
        result[sid] = row
    return {"schema": "math-gauge.execution-eligibility/v1", "slots": result, "audit_snapshot": snapshot,
            "verifier_sha256": digest_bytes(Path(__file__).read_bytes()),
            "eligible": bool(result) and all(x["eligible"] for x in result.values()),
            "reasons": sorted({reason for x in result.values() for reason in x["reasons"]}), "limits": LIMITS}
