"""Import externally produced answers without executing a candidate or adapter.

The source submission, bundle and every referenced file are frozen locally.
Declared transport metadata is retained as a declaration, never as evidence of
local process execution, provider identity, isolation or human approval.
"""

import copy
import json
import math
import os
import re
import tempfile
import uuid
from datetime import datetime
from pathlib import Path

from .benchmarks import identity, select_slots, validate_plan
from .catalog import digest_bytes, relative_name, write_json
from .eligibility import _file, _root
from .execution import extract_candidate_lean, now, runner_fingerprint
from .reliability import (
    PARSER_VERSION, PARAMETERS, _bind_suite, _budget_descriptor, _budget_totals,
    _execution_manifest_hash, _freeze_inputs, _messages_for, _new_slot_record,
    _parameters, _raw, _readable, _runtime, _save_material, _slot_path,
    _transport_result, _validate_schedule, compose_material,
)

SUBMISSION = "math-gauge.harness-submission/v1"
RECEIPT = "math-gauge.harness-import/v1"
ORIGIN = "external_import"
SOURCE_ORIGINS = {"external", "fixture", "replay"}
LIMITS = ("External source declarations are not authenticated. This importer makes zero "
          "candidate calls and does not establish provider identity, process isolation, "
          "complete external call accounting or formal comparison eligibility.")


def _require(condition, message):
    if not condition:
        raise ValueError(message)


def _json(raw):
    def pairs(items):
        value = {}
        for key, item in items:
            _require(key not in value, "Duplicate JSON key in harness submission")
            value[key] = item
        return value

    try:
        value = json.loads(raw, object_pairs_hook=pairs)
        identity(value)  # Non-finite numbers cannot enter any metadata field.
        return value
    except (UnicodeDecodeError, json.JSONDecodeError, TypeError, OverflowError) as error:
        raise ValueError("Invalid harness submission JSON") from error


class _SourceFiles:
    """One exact inventory, with no case aliases, symlinks or descriptor drift."""

    def __init__(self, root):
        self.root = _root(root)
        self.files = {}
        self.descriptors = {}
        self.folded = {}

    def read(self, descriptor):
        _require(isinstance(descriptor, dict), "Source file descriptor must be an object")
        name = descriptor.get("path")
        relative_name(name)
        _require(type(descriptor.get("bytes")) is int and descriptor["bytes"] >= 0
                 and isinstance(descriptor.get("sha256"), str)
                 and re.fullmatch(r"[0-9a-f]{64}", descriptor["sha256"]) is not None,
                 "Source descriptor needs bytes and SHA-256")
        folded = name.casefold()
        _require(folded not in self.folded or self.folded[folded] == name,
                 "Case-aliased source file paths")
        canonical = {key: descriptor[key] for key in ("path", "bytes", "sha256")}
        if name in self.descriptors:
            _require(self.descriptors[name] == canonical, "Conflicting source file descriptors")
            return self.files[name]
        raw = _file(self.root, name).read_bytes()
        _require(len(raw) == canonical["bytes"] and digest_bytes(raw) == canonical["sha256"],
                 "Harness source file hash or size changed: " + name)
        self.folded[folded] = name
        self.descriptors[name], self.files[name] = canonical, raw
        return raw


def _submission(value, manifest, plan, sources):
    _require(isinstance(value, dict) and value.get("schema") == SUBMISSION,
             "Unsupported harness submission")
    _require(value.get("bundle_sha256") == manifest["bundle_sha256"]
             and value.get("plan_sha256") == plan["plan_sha256"]
             and value.get("runtime_sha256") == plan["runtime_sha256"],
             "Harness submission binds a different bundle, plan or runtime")
    _require(isinstance(value.get("origin"), str) and value["origin"] in SOURCE_ORIGINS
             and type(value.get("fixture_only")) is bool,
             "Submission needs explicit external/fixture/replay origin and fixture_only")
    _require(value["origin"] == "external" or value["fixture_only"] is True,
             "Replay or fixture evidence cannot become a real model result")
    _require(type(value.get("declared_external_calls")) is int
             and value["declared_external_calls"] >= 0,
             "Submission needs a nonnegative declared external call count")
    _require(not value["fixture_only"] or value["declared_external_calls"] == 0,
             "Fixture submissions cannot declare real candidate calls")
    slots = value.get("slots")
    _require(isinstance(slots, list), "Submission slots must be a list")
    index = {}
    allowed = set(manifest["selected_slot_ids"])
    for row in slots:
        _require(isinstance(row, dict) and isinstance(row.get("slot_id"), str),
                 "Each submitted slot needs its identity")
        sid = row["slot_id"]
        _require(sid in allowed and sid not in index, "Unknown or duplicate submitted slot")
        _require(isinstance(row.get("attempts"), list) and 1 <= len(row["attempts"]) <= 2,
                 "Submitted slots must retain one or two ordered transport attempts")
        _require(isinstance(row.get("projected_request"), dict),
                 "Submitted slot lacks its exact candidate conversation")
        index[sid] = row
    _require(list(index) == [sid for sid in manifest["selected_slot_ids"] if sid in index],
             "Submitted slots changed their frozen sequential order")
    artifacts = value.get("artifacts", [])
    _require(isinstance(artifacts, list), "Submission artifacts must be a list")
    seen = set()
    for descriptor in artifacts:
        raw = sources.read(descriptor)
        name = descriptor["path"].casefold()
        _require(name not in seen, "Duplicate submission artifact")
        seen.add(name)
    return index


def _timing(row):
    result = {key: row.get(key) for key in ("started_at", "finished_at", "elapsed_seconds")}
    parsed = {}
    for key in ("started_at", "finished_at"):
        value = result[key]
        if value is None:
            continue
        try:
            stamp = datetime.fromisoformat(value.replace("Z", "+00:00"))
            _require(stamp.utcoffset() is not None, "Declared attempt timestamp needs a timezone")
            parsed[key] = stamp
        except (AttributeError, TypeError, ValueError) as error:
            raise ValueError("Invalid declared external attempt timestamp") from error
    if len(parsed) == 2:
        _require(parsed["finished_at"] >= parsed["started_at"], "Declared external attempt timing is reversed")
    elapsed = result["elapsed_seconds"]
    _require(elapsed is None or (type(elapsed) in (int, float) and math.isfinite(elapsed) and elapsed >= 0),
             "Invalid declared external elapsed time")
    return result


def _attempt(row, number, projected_hash, prefix, sources):
    _require(isinstance(row, dict) and type(row.get("number")) is int and row["number"] == number,
             "Submitted attempt ordering changed")
    _require(row.get("projected_request_sha256") == projected_hash,
             "External attempt uses a different frozen request")
    raw, stderr = sources.read(row.get("response")), sources.read(row.get("stderr"))
    _require(row.get("status") in {"ok", "transient_error", "permanent_error", "timeout", "budget_exhausted"},
             "Invalid submitted transport status")
    _require("usage" in row and (row.get("exit_code") is None or type(row["exit_code"]) is int),
             "Submitted attempt needs original usage and an integral or null exit code")
    result = _transport_result({"stdout": raw, "stderr": stderr, "status": row["status"],
                                "exit_code": row.get("exit_code"), "usage": row["usage"]})
    generated = row.get("generated_files", [])
    _require(isinstance(generated, list), "Generated files must be a list")
    generated_files, names = [], set()
    for item in generated:
        _require(isinstance(item, dict), "Generated file descriptor must be an object")
        name = item.get("name")
        relative_name(name)
        _require(name.casefold() not in names, "Duplicate generated file name")
        names.add(name.casefold())
        data = sources.read(item)
        extraction = item.get("extraction")
        _require(isinstance(extraction, dict) and set(extraction) == {"response_sha256", "start_byte", "end_byte"},
                 "Generated files need an exact original response extraction")
        start, end = extraction["start_byte"], extraction["end_byte"]
        _require(extraction["response_sha256"] == digest_bytes(raw)
                 and type(start) is int and type(end) is int and 0 <= start <= end <= len(raw)
                 and raw[start:end] == data,
                 "Generated file differs from its original response extraction")
        if name.lower().endswith(".lean"):
            try:
                delivered = extract_candidate_lean(raw.decode("utf-8"))
            except (UnicodeDecodeError, ValueError) as error:
                raise ValueError("Submitted Lean file is not a named original answer block") from error
            _require(any(x["name"] == name and x["start_byte"] == start and x["end_byte"] == end
                         and x["content"].encode() == data for x in delivered),
                     "Submitted Lean file does not match its named original answer block")
        generated_files.append({"name": name, "path": "external-import/files/" + item["path"],
                                "bytes": len(data), "sha256": digest_bytes(data),
                                "extraction": copy.deepcopy(extraction)})
    attempt = {"status": result["status"], "exit_code": result["exit_code"], "usage": result["usage"],
               "number": number, **_timing(row), "timing_origin": "external-declaration",
               "response_path": prefix + "/response.md", "response_sha256": digest_bytes(raw),
               "stderr_sha256": digest_bytes(stderr), "readable_text": _readable(raw) is not None,
               "projected_request_sha256": projected_hash,
               "external_source": copy.deepcopy(row), "generated_files": generated_files}
    return attempt, raw, stderr


def _validate_runtime(plan):
    _require(plan.get("runtime_frozen") is True,
             "External answers require a runtime frozen before execution")
    runtime = _runtime(plan)
    parameters = _parameters(runtime)
    budget, retry = runtime["budget"], runtime.get("retry", {})
    timeout = budget.get("timeout_seconds")
    _require(type(timeout) in (int, float) and timeout > 0, "External answers need a frozen positive timeout")
    _require(isinstance(retry, dict) and retry.get("max_attempts", 2) == 2,
             "Reliability permits the frozen two-attempt maximum")
    wait = retry.get("wait_seconds", 0)
    codes = retry.get("retryable_exit_codes", [75])
    _require(type(wait) in (int, float) and 0 <= wait <= 60 and isinstance(codes, list)
             and all(type(code) is int for code in codes), "Invalid frozen transport retry policy")
    case_parameters = budget.get("case_parameters", {})
    _require(isinstance(case_parameters, dict)
             and set(case_parameters) <= {x["case_id"] for x in plan["case_index"]}
             and all(isinstance(value, dict) and not set(value) - PARAMETERS for value in case_parameters.values()),
             "Invalid frozen case generation parameters")
    maximum, limit = budget.get("max_transport_attempts"), budget.get("max_total_tokens")
    _require((maximum is None or (type(maximum) is int and maximum >= 0))
             and (limit is None or (type(limit) in (int, float) and limit >= 0)),
             "Invalid frozen total execution budget")
    return runtime, parameters


def _execution_contract(runtime, parameters, submitted):
    return {"origin": ORIGIN, "command": None, "timeout_seconds": runtime["budget"]["timeout_seconds"],
            "adapter_identity": runtime.get("adapter_identity"), "parameters": parameters,
            "budget": runtime["budget"], "context_transport": "external-visible-history",
            "parser_version": PARSER_VERSION, "source_origin": submitted["origin"],
            "fixture_only": submitted["fixture_only"]}


def _snapshot(bundle_root, source_raw, sources, dest, manifest):
    base = dest / "external-import"
    base.mkdir()
    (base / "submission.json").write_bytes(source_raw)
    for name, raw in sources.files.items():
        path = base / "files" / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)
    bundle = base / "bundle"
    bundle.mkdir()
    names = ["manifest.json", *manifest["files_sha256"]]
    bundle_files = {}
    for name in names:
        raw = _file(bundle_root, name).read_bytes()
        path = bundle / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)
        bundle_files[name] = {"bytes": len(raw), "sha256": digest_bytes(raw)}
    receipt = {"schema": RECEIPT, "source_submission_sha256": digest_bytes(source_raw),
               "source_files": list(sources.descriptors.values()), "bundle_files": bundle_files,
               "bundle_sha256": manifest["bundle_sha256"], "plan_sha256": manifest["plan_sha256"],
               "limits": LIMITS}
    write_json(base / "receipt.json", receipt)
    return {"receipt_path": "external-import/receipt.json",
            "receipt_sha256": digest_bytes((base / "receipt.json").read_bytes())}


def _ingest(plan, suite, dest, manifest, submitted, index, sources):
    runtime, parameters = _validate_runtime(plan)
    prompts = _validate_schedule(plan)
    targets = manifest["targets"]
    selected = select_slots(plan, targets)
    _require([x["slot_id"] for x in selected] == manifest["selected_slot_ids"],
             "Exported slot projection differs from the frozen plan")
    requests, inputs = _freeze_inputs(plan, suite, dest)
    budget = runtime["budget"]
    contract = _execution_contract(runtime, parameters, submitted)
    meta = {"schema": "math-gauge.reliability-run/v1", "run_id": uuid.uuid4().hex,
            "created_at": now(), "plan_sha256": plan["plan_sha256"],
            "runner_sha256": plan["runner_sha256"], "parser_version": PARSER_VERSION,
            "origin": ORIGIN, "source_origin": submitted["origin"], "fixture_only": submitted["fixture_only"],
            "model_label": plan["model_label"], "model_identity_verified": False, "command": None,
            "timeout_seconds": budget["timeout_seconds"], "execution_targets": targets,
            "selected_slot_ids": manifest["selected_slot_ids"], "context_transport": "external-visible-history",
            "fresh_context_declared": runtime.get("fresh_context", False), "fresh_context_verified": False,
            "candidate_tools_verified_disabled": False, "execution_contract": contract,
            "execution_contract_sha256": identity(contract), "candidate_calls": 0,
            "external_candidate_calls_declared": submitted["declared_external_calls"],
            "transport_attempts": 0, "known_total_tokens": 0, "total_tokens": 0,
            "token_usage_complete": True, "budget_stop_reason": None,
            "budget_scope": "current-run-plus-explicit-reuse-evidence",
            "unseen_plan_fragments_accounted_for": False, "prior_budget_evidence": {}, "budget_evidence": {},
            "prior_transport_attempts": 0, "prior_known_total_tokens": 0,
            "inputs": inputs, "slot_record_sha256": {}, "reused_from": {}, "status": "imported",
            "external_origin_verified": False, "import_limits": LIMITS}
    write_json(dest / "plan.json", plan)
    meta["plan_file_sha256"] = digest_bytes((dest / "plan.json").read_bytes())
    records, materials = {}, {}
    maximum, limit = budget.get("max_transport_attempts"), budget.get("max_total_tokens")
    stopped = (maximum == 0 or limit == 0)
    if stopped:
        meta["budget_stop_reason"] = "cumulative_budget_exhausted"
    for slot in selected:
        sid = slot["slot_id"]
        folder = dest / _slot_path(sid)
        folder.mkdir(parents=True)
        record = _new_slot_record(slot, prompts, ORIGIN, meta["run_id"])
        record["fixture_only"] = submitted["fixture_only"]
        record["source_origin"] = submitted["origin"]
        row = index.get(sid)
        messages = _messages_for(slot, requests, prompts, records, dest, runtime)
        if row is None:
            if messages is None:
                record.update(status="blocked", reason="parent_without_readable_response")
            else:
                record["reason"] = "budget_exhausted" if stopped else "submission_missing"
        else:
            _require(messages is not None, "Submitted followup has no readable original branch parent")
            projected = {"schema": "math-gauge.conversation/v1", "messages": messages,
                         "parameters": dict(parameters, **budget.get("case_parameters", {}).get(slot["case_id"], {}))}
            _require(row["projected_request"] == projected,
                     "Submitted visible history, branch or generation parameters changed")
            history = [{"role": x["role"], "content": x["content"],
                        "content_sha256": digest_bytes(x["content"].encode())} for x in messages]
            write_json(folder / "history.json", history)
            write_json(folder / "projected-request.json", projected)
            record.update(started=True, history_sha256=identity(history), projected_request_sha256=identity(projected))
            for number, external in enumerate(row["attempts"], 1):
                _require(not stopped, "Submission continued after its frozen total budget stopped execution")
                _require(record["locked_attempt"] is None, "Submission retried a locked readable answer")
                if number == 2:
                    _require(record["attempts"][0]["status"] in {"transient_error", "timeout"},
                             "Submission retried a permanent transport failure")
                prefix = _slot_path(sid) + f"/attempts/{number}"
                attempt, raw, stderr = _attempt(external, number, identity(projected), prefix, sources)
                attempt_dir = dest / prefix
                attempt_dir.mkdir(parents=True)
                (attempt_dir / "response.md").write_bytes(raw)
                (attempt_dir / "stderr.txt").write_bytes(stderr)
                write_json(attempt_dir / "record.json", attempt)
                record["attempts"].append(attempt)
                meta["transport_attempts"] += 1
                meta["known_total_tokens"] += attempt["usage"].get("total_tokens", 0)
                if "total_tokens" not in attempt["usage"]:
                    meta["token_usage_complete"] = False
                    if limit is not None:
                        stopped = True
                        meta["budget_stop_reason"] = "usage_unavailable_for_total_token_budget"
                if maximum is not None and meta["transport_attempts"] >= maximum:
                    stopped = True
                    meta["budget_stop_reason"] = meta["budget_stop_reason"] or "cumulative_budget_exhausted"
                if limit is not None and meta["known_total_tokens"] >= limit:
                    stopped = True
                    meta["budget_stop_reason"] = meta["budget_stop_reason"] or "total_token_budget_exhausted"
                if attempt["readable_text"]:
                    record.update(status="responded", reason=None, locked_attempt=number,
                                  response_path=attempt["response_path"], response_sha256=attempt["response_sha256"])
                else:
                    record.update(status="execution_error", reason=attempt["status"])
                    if attempt["status"] == "budget_exhausted":
                        stopped = True
                        meta["budget_stop_reason"] = meta["budget_stop_reason"] or "adapter_budget_exhausted"
        material = compose_material(slot, _raw(dest, record), materials.get(slot.get("parent_slot")))
        _save_material(dest, slot, material)
        record["material_sha256"] = material[0]["material_sha256"]
        write_json(folder / "record.json", record)
        meta["slot_record_sha256"][sid] = digest_bytes((folder / "record.json").read_bytes())
        records[sid], materials[sid] = record, material
        if record["attempts"]:
            meta["budget_evidence"][record["evidence_id"]] = _budget_descriptor(dest, _slot_path(sid) + "/record.json")
    totals = _budget_totals(meta["budget_evidence"])
    meta.update(cumulative_transport_attempts=totals["transport_attempts"],
                cumulative_known_total_tokens=totals["known_total_tokens"],
                cumulative_token_usage_complete=totals["token_usage_complete"],
                cumulative_total_tokens=totals["known_total_tokens"] if totals["token_usage_complete"] else None,
                total_tokens=totals["known_total_tokens"] if totals["token_usage_complete"] else None,
                completed_at=now(), execution_failures=sum(r["status"] in {"blocked", "execution_error"} for r in records.values()),
                unrun_slots=[sid for sid, record in records.items() if not record["started"]])
    return meta


def import_harness_submission(bundle_root, submission_path, plan, suite, destination):
    """Validate and atomically publish an immutable, provisional imported run."""
    from .harness import inspect_harness_bundle
    from .reliability import inspect_reliability_run

    validate_plan(plan)
    _require(plan["runner_sha256"] == runner_fingerprint(),
             "Runner source changed after the benchmark plan was frozen")
    _bind_suite(plan, suite)
    _validate_schedule(plan)
    _validate_runtime(plan)
    bundle_root = _root(bundle_root)
    manifest = inspect_harness_bundle(bundle_root, plan=plan, suite=suite)
    source_path = Path(submission_path).absolute()
    source_root = _root(source_path.parent)
    source_raw = _file(source_root, source_path.name).read_bytes()
    value = _json(source_raw)
    sources = _SourceFiles(source_root)
    index = _submission(value, manifest, plan, sources)
    dest = _root(destination)
    _require(not dest.exists(), "Harness import output already exists")
    _require(not dest.is_relative_to(suite.root) and not dest.is_relative_to(bundle_root),
             "Import output must be outside its suite and candidate bundle")
    dest.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix=".math-gauge-import-", dir=dest.parent) as temp:
        staging = Path(temp) / "run"
        staging.mkdir()
        try:
            meta = _ingest(plan, suite, staging, manifest, value, index, sources)
            meta["external_import"] = _snapshot(bundle_root, source_raw, sources, staging, manifest)
            meta["execution_manifest_sha256"] = _execution_manifest_hash(meta)
            write_json(staging / "run.json", meta)
            inspect_reliability_run(staging)
            # mkdir is the no-clobber reservation; a failed validation never
            # leaves an accepted directory, and an existing output is untouched.
            dest.mkdir()
            try:
                os.replace(staging, dest)
            except BaseException:
                dest.rmdir()
                raise
            return meta
        except (KeyError, TypeError, AttributeError, OverflowError) as error:
            raise ValueError("Malformed harness submission structure") from error


def inspect_import_sources(root, meta, records):
    """Recheck retained external evidence; shared reliability inspection calls this."""
    from .harness import inspect_harness_bundle

    root = _root(root)
    descriptor = meta.get("external_import")
    _require(isinstance(descriptor, dict) and descriptor.get("receipt_path") == "external-import/receipt.json",
             "External import source receipt is missing")
    receipt_raw = _file(root, descriptor["receipt_path"]).read_bytes()
    _require(digest_bytes(receipt_raw) == descriptor.get("receipt_sha256"), "External import receipt changed")
    receipt = _json(receipt_raw)
    _require(receipt.get("schema") == RECEIPT, "Unsupported external import receipt")
    source_raw = _file(root, "external-import/submission.json").read_bytes()
    _require(digest_bytes(source_raw) == receipt.get("source_submission_sha256"), "Original external submission changed")
    source = _json(source_raw)
    bundle = root / "external-import/bundle"
    manifest = inspect_harness_bundle(bundle, plan=meta["plan"])
    _require(manifest["bundle_sha256"] == receipt.get("bundle_sha256")
             and manifest["plan_sha256"] == receipt.get("plan_sha256"), "Imported bundle binding changed")
    for name, expected in receipt["bundle_files"].items():
        raw = _file(bundle, name).read_bytes()
        _require(len(raw) == expected["bytes"] and digest_bytes(raw) == expected["sha256"], "Retained bundle bytes changed")
    sources = _SourceFiles(root / "external-import/files")
    index = _submission(source, manifest, meta["plan"], sources)
    runtime, parameters = _validate_runtime(meta["plan"])
    _require(meta["origin"] == ORIGIN and meta.get("command") is None and meta.get("candidate_calls") == 0
             and meta.get("external_candidate_calls_declared") == source["declared_external_calls"]
             and meta.get("source_origin") == source["origin"] and meta.get("fixture_only") is source["fixture_only"]
             and meta["execution_contract"] == _execution_contract(runtime, parameters, source)
             and meta["model_label"] == meta["plan"]["model_label"]
             and meta["timeout_seconds"] == runtime["budget"]["timeout_seconds"]
             and meta["context_transport"] == "external-visible-history",
             "External import origin or call declarations changed")
    _require(meta["selected_slot_ids"] == manifest["selected_slot_ids"], "Imported selected slots changed")
    for sid, record in records.items():
        _require(record.get("origin") == ORIGIN and record.get("fixture_only") is source["fixture_only"]
                 and record.get("source_origin") == source["origin"], "Imported slot origin changed")
        row = index.get(sid)
        _require(bool(row) == record["started"], "Imported started/missing slot state changed")
        if row is None:
            continue
        _require(identity(row["projected_request"]) == record["projected_request_sha256"]
                 and len(row["attempts"]) == len(record["attempts"]), "Imported request or attempt inventory changed")
        for number, external in enumerate(row["attempts"], 1):
            prefix = _slot_path(sid) + f"/attempts/{number}"
            attempt, raw, stderr = _attempt(external, number, record["projected_request_sha256"], prefix, sources)
            _require(attempt == record["attempts"][number - 1]
                     and _file(root, attempt["response_path"]).read_bytes() == raw
                     and _file(root, prefix + "/stderr.txt").read_bytes() == stderr,
                     "Imported attempt differs from its retained original source")
    _require(list(sources.descriptors.values()) == receipt.get("source_files"), "Retained source inventory changed")
    totals = _budget_totals(meta["budget_evidence"])
    _require(meta["known_total_tokens"] == totals["known_total_tokens"]
             and meta["token_usage_complete"] is totals["token_usage_complete"]
             and meta["total_tokens"] == (totals["known_total_tokens"] if totals["token_usage_complete"] else None),
             "External import usage declarations changed")
