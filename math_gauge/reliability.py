"""Immutable multi-turn execution and KEEP/FULL material composition; no grading.

The full benchmark plan stays on the evaluator side. Each adapter invocation
receives only the whitelisted candidate conversation and frozen generation
parameters. Material records never replace the original assistant response.
"""

import copy
import json
import re
import shutil
import tempfile
import time
import uuid
from pathlib import Path

from .benchmarks import identity, select_slots, validate_plan
from .catalog import (candidate_message, digest_bytes, read_json, safe_file,
                      validate_group_contract, write_json)
from .execution import extract_candidate_lean, invoke_conversation, now, runner_fingerprint

PARSER_VERSION = "math-gauge.keep-full/v1"
PARAMETERS = {"model", "reasoning_effort", "temperature", "top_p", "seed",
              "max_output_tokens", "max_completion_tokens"}


def _request_hash(request):
    # Keep the established single-answer request identity.
    return digest_bytes(json.dumps(request, ensure_ascii=False, sort_keys=True).encode())


def _bytes(value):
    if isinstance(value, bytes):
        return value
    if isinstance(value, str):
        return value.encode("utf-8")
    raise ValueError("Transport output must be bytes or UTF-8 text")


def _readable(raw):
    try:
        value = raw.decode("utf-8")
        return value if value.strip() else None
    except UnicodeDecodeError:
        return None


def _slot_path(slot_id):
    # Slot IDs are protocol identities, not arbitrary filesystem names.
    if not isinstance(slot_id, str) or not re.fullmatch(r"[A-Za-z0-9_-]+:(?:A[123]|(?:neutral|affirm|deny):[12])", slot_id):
        raise ValueError("Invalid reliability slot identity")
    return "slots/" + slot_id.replace(":", "/")


def _raw(root, record):
    if record.get("response_path") is None:
        return None
    data = safe_file(root, record["response_path"]).read_bytes()
    if digest_bytes(data) != record.get("response_sha256"):
        raise ValueError("Frozen reliability response changed")
    return data


def _validate_schedule(plan):
    rows = plan["slots"]
    case_ids = [x["case_id"] for x in plan["case_index"]]
    focus_ids = [x["case_id"] for x in plan["reliability"]["selection"]["cases"]]
    expected = {f"{cid}:A{i}" for cid in case_ids for i in (1, 2, 3)}
    expected |= {f"{cid}:{arm}:{rnd}" for cid in focus_ids
                 for arm in ("neutral", "affirm", "deny") for rnd in (1, 2)}
    if len(rows) != len(expected) or {r["slot_id"] for r in rows} != expected:
        raise ValueError("Reliability plan must retain its complete fixed denominator")
    prompts = plan["reliability"]["prompts"]["messages"]
    messages = {p["message_id"]: p for p in prompts}
    wanted_messages = expected - {f"{cid}:A{i}" for cid in case_ids for i in (1, 2, 3)}
    if len(messages) != len(prompts) or set(messages) != wanted_messages:
        raise ValueError("Frozen followup prompt coverage changed")
    earlier = set()
    for slot in rows:
        sid, cid = slot["slot_id"], slot["case_id"]
        _slot_path(sid)
        if slot["kind"] == "independent":
            if (sid != f"{cid}:{slot.get('attempt_label')}" or slot.get("context") != "fresh"
                    or slot.get("parent_slot") is not None):
                raise ValueError("Independent context binding changed")
        else:
            arm, rnd = slot.get("arm"), slot.get("round")
            parent = f"{cid}:A1" if rnd == 1 else f"{cid}:{arm}:1"
            message = messages.get(sid, {})
            if (slot["kind"] != "followup" or sid != f"{cid}:{arm}:{rnd}"
                    or slot.get("parent_slot") != parent or parent not in earlier
                    or slot.get("context") != "branch-history-only"
                    or slot.get("message_id") != sid
                    or (message.get("case_id"), message.get("arm"), message.get("round")) != (cid, arm, rnd)
                    or message.get("role") != "user"
                    or not isinstance(message.get("content"), str)
                    or digest_bytes(message["content"].encode()) != message.get("content_sha256")):
                raise ValueError("Followup crosses its frozen branch or prompt identity")
        earlier.add(sid)
    return messages


def _bind_suite(plan, suite):
    if plan["suite"] != {"id": suite.metadata["id"], "version": suite.metadata["version"],
                          "sha256": suite.sha256}:
        raise ValueError("Reliability plan binds a different suite")
    if {r["case_id"] for r in plan["case_index"]} != set(suite.cases):
        raise ValueError("Reliability case inventory changed")
    for row in plan["case_index"]:
        case = suite.cases[row["case_id"]]
        request = suite.request(case)
        contract_raw = safe_file(suite.root, case["group_contract"]).read_bytes()
        contract = validate_group_contract(json.loads(contract_raw))
        stages = [{"stage_id": s["id"], "points": s["points"], "lean_required": s["lean_required"]}
                  for s in contract["stages"]]
        if (case["version"] != row["version"] or _request_hash(request) != row["request_sha256"]
                or digest_bytes(candidate_message(request).encode()) != row["candidate_message_sha256"]
                or digest_bytes(contract_raw) != row["group_contract_sha256"]
                or stages != row["stages"] or sum(s["points"] for s in stages) != row["total_weight"]):
            raise ValueError("Reliability case input, contract or stage weight changed")


def _parameters(runtime):
    parameters = runtime.get("candidate_parameters", {})
    if not isinstance(parameters, dict) or set(parameters) - PARAMETERS:
        raise ValueError("Only whitelisted generation parameters may reach the adapter")
    parameters = copy.deepcopy(parameters)
    output = runtime.get("budget", {}).get("output_tokens")
    if output is not None:
        if type(output) is not int or output <= 0:
            raise ValueError("Output token budget must be a positive integer")
        if "max_output_tokens" in parameters and parameters["max_output_tokens"] != output:
            raise ValueError("Generation parameters contradict the frozen output budget")
        parameters["max_output_tokens"] = output
    return parameters


def _runtime(plan):
    return copy.deepcopy(plan.get("runtime") or {"budget": {}})


def _messages_for(slot, requests, prompts, records, root, runtime):
    messages = []
    if runtime.get("system_prompt") is not None:
        if not isinstance(runtime["system_prompt"], str):
            raise ValueError("System prompt must be frozen text")
        messages.append({"role": "system", "content": runtime["system_prompt"]})
    messages.append({"role": "user", "content": candidate_message(requests[slot["case_id"]])})
    if slot["kind"] == "followup":
        cid = slot["case_id"]
        a1 = _raw(root, records[f"{cid}:A1"])
        if a1 is None or _readable(a1) is None:
            return None
        messages.append({"role": "assistant", "content": a1.decode("utf-8")})
        if slot["round"] == 2:
            predecessor = f"{cid}:{slot['arm']}:1"
            first = _raw(root, records[predecessor])
            if first is None or _readable(first) is None:
                return None
            messages.extend([{"role": "user", "content": prompts[predecessor]["content"]},
                             {"role": "assistant", "content": first.decode("utf-8")}])
        messages.append({"role": "user", "content": prompts[slot["message_id"]]["content"]})
    return messages


def _mixed_modes(body):
    fence = None
    for line in body.decode("utf-8").splitlines():
        match = re.match(r"^ {0,3}(`{3,}|~{3,})", line)
        if match:
            token = match.group(1)
            if fence is None:
                fence = token
            elif token[0] == fence[0] and len(token) >= len(fence):
                fence = None
            continue
        if fence is None and line in {"KEEP", "FULL"}:
            return True
    return False


def compose_material(slot, raw, parent=None):
    """Resolve exact body bytes, without normalizing anything after the mode line.

    Returns (descriptor, body, rationale). The descriptor's identity includes
    current response, immediate parent material, origin span and current KEEP
    rationale. An invalid parent never falls back to the branch's A1.
    """
    sid = slot["slot_id"]
    base = {"schema": "math-gauge.reliability-material/v1", "parser_version": PARSER_VERSION,
            "slot_id": sid, "response_sha256": digest_bytes(raw) if raw is not None else None,
            "parent_slot": slot.get("parent_slot"),
            "parent_material_sha256": parent[0]["material_sha256"] if parent else None,
            "parent_response_sha256": parent[0]["response_sha256"] if parent else None,
            "mode": None, "status": "unresolved", "format_status": "invalid",
            "issues": [], "body_origin": None, "raw_body_span": None,
            "body_sha256": None, "rationale_sha256": None, "files": []}
    body = rationale = None
    if raw is None or _readable(raw) is None:
        base["issues"] = ["no_readable_response"]
    elif slot["kind"] == "independent":
        body = raw
        base.update(mode="INITIAL", status="resolved", format_status="valid",
                    body_origin={"slot_id": sid, "response_sha256": digest_bytes(raw),
                                 "start_byte": 0, "end_byte": len(raw)},
                    raw_body_span={"start_byte": 0, "end_byte": len(raw), "sha256": digest_bytes(raw)})
    else:
        offset = 0
        for line in raw.splitlines(keepends=True):
            if not line.strip():
                offset += len(line)
                continue
            mode = line.rstrip(b"\r\n")
            offset += len(line)
            break
        else:
            mode = b""
        if mode not in {b"KEEP", b"FULL"}:
            base["issues"] = ["missing_or_invalid_mode"]
        else:
            base["mode"] = mode.decode()
            payload = raw[offset:]
            base["raw_body_span"] = {"start_byte": offset, "end_byte": len(raw),
                                     "sha256": digest_bytes(payload)}
            if _mixed_modes(payload):
                base["issues"] = ["mixed_modes"]
            elif mode == b"FULL":
                body = payload
                base.update(status="resolved", format_status="valid",
                            body_origin={"slot_id": sid, "response_sha256": digest_bytes(raw),
                                         "start_byte": offset, "end_byte": len(raw)})
            else:
                rationale = payload
                if parent is None or parent[0]["status"] != "resolved":
                    base["issues"] = ["unresolved_immediate_parent"]
                else:
                    body = parent[1]
                    base.update(status="resolved", format_status="valid",
                                body_origin=copy.deepcopy(parent[0]["body_origin"]))
                    # These are explicit edit forms, not an attempt at deciding
                    # mathematical meaning. Ambiguity stays for format review.
                    text = payload.decode("utf-8")
                    if re.search(r"```(?:lean|diff)|~~~(?:lean|diff)|(?:替换|修改为|更正为)|\b(?:replace|patch|diff)\b", text, re.I):
                        base["format_status"] = "review_required"
                        base["issues"] = ["keep_contains_possible_replacement"]
    if body is not None:
        base["body_sha256"] = digest_bytes(body)
        try:
            files = extract_candidate_lean(body.decode("utf-8"))
            base["files"] = [{"name": item["name"], "sha256": digest_bytes(item["content"].encode()),
                              "start_byte": item["start_byte"], "end_byte": item["end_byte"]}
                             for item in files]
        except ValueError as error:
            base["source_extraction_note"] = str(error)
    if rationale is not None:
        base["rationale_sha256"] = digest_bytes(rationale)
    base["material_sha256"] = identity(base)
    return base, body, rationale


def _save_material(root, slot, material):
    descriptor, body, rationale = material
    folder = Path(root) / _slot_path(slot["slot_id"])
    write_json(folder / "material.json", descriptor)
    for name, data in (("material-body.md", body), ("keep-rationale.md", rationale)):
        if data is not None:
            (folder / name).write_bytes(data)


def _transport_result(value):
    if isinstance(value, (str, bytes)):
        value = {"stdout": value, "status": "ok"}
    if not isinstance(value, dict) or value.get("status", "ok") not in {
        "ok", "transient_error", "permanent_error", "timeout", "budget_exhausted"}:
        raise ValueError("Invalid adapter transport result")
    usage = value.get("usage", {})
    if not isinstance(usage, dict) or any(
        not isinstance(k, str) or type(v) not in (int, float) or v < 0
        for k, v in usage.items()
    ):
        raise ValueError("Transport usage must contain nonnegative numeric fields")
    identity(usage)
    return {"stdout": _bytes(value.get("stdout", b"")),
            "stderr": _bytes(value.get("stderr", b"")),
            "status": value.get("status", "ok"), "exit_code": value.get("exit_code"),
            "usage": usage}


def _budget_descriptor(root, record_path):
    """Usage evidence includes the original record and all raw transport files."""
    root = Path(root).resolve()
    path = safe_file(root, record_path)
    record = read_json(path)
    known_tokens = 0
    complete = True
    for number, attempt in enumerate(record["attempts"], 1):
        prefix = path.parent.relative_to(Path(root)) / "attempts" / str(number)
        if (read_json(safe_file(root, str(prefix / "record.json"))) != attempt
                or digest_bytes(safe_file(root, str(prefix / "response.md")).read_bytes()) != attempt["response_sha256"]
                or digest_bytes(safe_file(root, str(prefix / "stderr.txt")).read_bytes()) != attempt["stderr_sha256"]):
            raise ValueError("Original transport budget evidence changed")
        usage = attempt.get("usage", {})
        if "total_tokens" not in usage:
            complete = False
        else:
            count = usage["total_tokens"]
            if type(count) not in (int, float) or count < 0:
                raise ValueError("Invalid original transport token usage")
            known_tokens += count
    return {"evidence_id": record["evidence_id"], "slot_id": record["slot_id"],
            "record_path": record_path, "slot_record_sha256": digest_bytes(path.read_bytes()),
            "transport_attempts": len(record["attempts"]), "known_total_tokens": known_tokens,
            "token_usage_complete": complete}


def _budget_totals(evidence):
    return {"transport_attempts": sum(v["transport_attempts"] for v in evidence.values()),
            "known_total_tokens": sum(v["known_total_tokens"] for v in evidence.values()),
            "token_usage_complete": all(v["token_usage_complete"] for v in evidence.values())}


def execute_reliability_run(plan, suite, destination, command=None, replay=None, *,
                            timeout=None, adapter=None, targets=None, reuse_runs=None):
    """Execute one pre-frozen projection, retaining every attempted transport.

    adapter is an explicitly fixture-only offline seam. replay is a JSON object
    indexed by slot ID; values may be raw text or ordered transport-result lists.
    A new subprocess/fresh message array is evidence about local transport only,
    never independent verification of a provider's hidden conversation state.
    """
    validate_plan(plan)
    if plan.get("runner_sha256") != runner_fingerprint():
        raise ValueError("Runner source changed after the benchmark plan was frozen")
    prompts = _validate_schedule(plan)
    _bind_suite(plan, suite)
    selected = select_slots(plan, targets)
    reusable = {}
    prior_evidence = {}
    for previous in reuse_runs or ():
        previous_root = Path(previous).resolve()
        previous_meta, previous_records = inspect_reliability_run(previous_root)
        if previous_meta["plan_sha256"] != plan["plan_sha256"]:
            raise ValueError("Reusable dependencies require the same complete frozen plan")
        for sid, record in previous_records.items():
            if sid in reusable and reusable[sid][1]["evidence_id"] != record["evidence_id"]:
                raise ValueError("Conflicting original generation evidence for a reusable slot")
            reusable[sid] = (previous_root, record, previous_meta)
        for eid, descriptor in previous_meta.get("budget_evidence", {}).items():
            if eid in prior_evidence and prior_evidence[eid][1]["slot_record_sha256"] != descriptor["slot_record_sha256"]:
                raise ValueError("Conflicting cumulative budget evidence")
            prior_evidence[eid] = (previous_root, descriptor)
    if sum(x is not None for x in (command, replay, adapter)) != 1:
        raise ValueError("Choose exactly one command, replay or offline fixture adapter")
    runtime = _runtime(plan)
    if command is not None and not plan.get("runtime_frozen"):
        raise ValueError("Freeze runtime, model, budget and adapter identity before execution")
    frozen_timeout = runtime["budget"].get("timeout_seconds")
    if frozen_timeout is None:
        if command is not None:
            raise ValueError("Real command execution requires a frozen timeout_seconds budget")
        frozen_timeout = 120
    if timeout is not None and timeout != frozen_timeout:
        raise ValueError("Timeout override differs from the frozen runtime budget")
    timeout = frozen_timeout
    if type(timeout) not in (int, float) or timeout <= 0:
        raise ValueError("Timeout must be positive")
    parameters = _parameters(runtime)
    if command is not None and (not isinstance(command, list) or not command
                               or not all(isinstance(x, str) and x for x in command)):
        raise ValueError("Command must be a nonempty argv array")
    if adapter is not None and not callable(adapter):
        raise ValueError("Offline fixture adapter must be callable")
    responses = read_json(replay) if isinstance(replay, (str, Path)) else replay
    if replay is not None and (not isinstance(responses, dict) or any(
        s["slot_id"] not in responses for s in selected)):
        raise ValueError("Replay must cover every selected slot")
    retry = runtime.get("retry", {})
    if not isinstance(retry, dict) or retry.get("max_attempts", 2) != 2:
        raise ValueError("Reliability permits exactly the frozen two-attempt maximum")
    wait = retry.get("wait_seconds", 0)
    codes = retry.get("retryable_exit_codes", [75])
    if type(wait) not in (int, float) or not 0 <= wait <= 60 or not isinstance(codes, list) or any(type(c) is not int for c in codes):
        raise ValueError("Invalid frozen transport retry policy")
    budget = runtime["budget"]
    if not isinstance(budget, dict):
        raise ValueError("Frozen budget must be an object")
    case_parameters = budget.get("case_parameters", {})
    if (not isinstance(case_parameters, dict)
            or not set(case_parameters) <= {c["case_id"] for c in plan["case_index"]}
            or any(not isinstance(v, dict) or set(v) - PARAMETERS for v in case_parameters.values())):
        raise ValueError("Case budgets must be a whitelisted parameter projection for known cases")
    maximum = budget.get("max_transport_attempts")
    token_limit = budget.get("max_total_tokens")
    if ((maximum is not None and (type(maximum) is not int or maximum < 0))
            or (token_limit is not None and (type(token_limit) not in (int, float) or token_limit < 0))):
        raise ValueError("Invalid total execution budget")
    dest = Path(destination).resolve()
    if dest.is_relative_to(suite.root):
        raise ValueError("Reliability output must be outside the question suite")
    dest.mkdir(parents=True, exist_ok=False)
    write_json(dest / "plan.json", plan)
    origin = "command" if command is not None else "replay" if replay is not None else "fixture"
    execution_contract = {"origin": origin, "command": command, "timeout_seconds": timeout,
                          "adapter_identity": runtime.get("adapter_identity"),
                          "parameters": parameters, "budget": budget,
                          "context_transport": "visible-history-replay", "parser_version": PARSER_VERSION}
    for _, _, previous_meta in reusable.values():
        if previous_meta.get("execution_contract_sha256") != identity(execution_contract):
            raise ValueError("Reusable dependencies have a different adapter or execution contract")
    inherited_budget = {}
    for eid, (previous_root, descriptor) in prior_evidence.items():
        source = safe_file(previous_root, descriptor["record_path"]).parent
        target = dest / "budget-evidence" / eid
        shutil.copytree(source, target)
        inherited_budget[eid] = _budget_descriptor(dest, str((target / "record.json").relative_to(dest)))
    prior_usage = _budget_totals(inherited_budget)
    meta = {"schema": "math-gauge.reliability-run/v1", "run_id": uuid.uuid4().hex,
            "created_at": now(), "plan_sha256": plan["plan_sha256"],
            "plan_file_sha256": digest_bytes((dest / "plan.json").read_bytes()),
            "runner_sha256": runner_fingerprint(), "parser_version": PARSER_VERSION,
            "origin": origin, "model_label": plan.get("model_label"),
            "model_identity_verified": False, "command": command,
            "timeout_seconds": timeout, "execution_targets": targets,
            "selected_slot_ids": [s["slot_id"] for s in selected],
            "context_transport": "visible-history-replay",
            "fresh_context_declared": runtime.get("fresh_context", False),
            "fresh_context_verified": False, "candidate_tools_verified_disabled": False,
            "execution_contract": execution_contract, "execution_contract_sha256": identity(execution_contract),
            "candidate_calls": 0, "transport_attempts": 0, "total_tokens": 0, "known_total_tokens": 0,
            "token_usage_complete": True, "budget_stop_reason": None,
            "budget_scope": "current-run-plus-explicit-reuse-evidence",
            "unseen_plan_fragments_accounted_for": False,
            "prior_budget_evidence": inherited_budget, "budget_evidence": dict(inherited_budget),
            "prior_transport_attempts": prior_usage["transport_attempts"],
            "prior_known_total_tokens": prior_usage["known_total_tokens"],
            "inputs": {}, "slot_record_sha256": {}, "status": "running"}
    meta["reused_from"] = {
        s["slot_id"]: {"run_id": reusable[s["slot_id"]][2]["run_id"],
                       "plan_sha256": plan["plan_sha256"],
                       "source_root": str(reusable[s["slot_id"]][0]),
                       "evidence_id": reusable[s["slot_id"]][1]["evidence_id"],
                       "slot_record_sha256": reusable[s["slot_id"]][2]["slot_record_sha256"][s["slot_id"]]}
        for s in selected if s["slot_id"] in reusable}
    meta["execution_manifest_sha256"] = identity({k: meta[k] for k in (
        "plan_sha256", "execution_targets", "selected_slot_ids", "reused_from",
        "command", "timeout_seconds", "origin", "context_transport", "prior_budget_evidence", "budget_scope")})
    requests = {}
    for case in plan["case_index"]:
        cid = case["case_id"]
        request = suite.prepare(suite.cases[cid], dest / "inputs" / cid / "solver")
        if _request_hash(request) != case["request_sha256"]:
            raise ValueError("Candidate preparation changed the frozen request")
        prompt_path = dest / "inputs" / cid / "solver" / "prompt.md"
        if prompt_path.read_bytes() != request["task"].encode("utf-8"):
            raise ValueError("Candidate preparation changed the original task bytes")
        contract_path = dest / "inputs" / cid / "review-contract.json"
        contract_path.write_bytes(safe_file(suite.root, case["group_contract"]).read_bytes())
        meta["inputs"][cid] = {"request": f"inputs/{cid}/solver/request.json",
                               "contract": f"inputs/{cid}/review-contract.json"}
        for kind in ("reference", "rubric"):
            source = safe_file(suite.root, suite.cases[cid][kind]).read_bytes()
            extension = ".md" if kind == "reference" else ".json"
            target = dest / "inputs" / cid / (kind + extension)
            target.write_bytes(source)
            meta["inputs"][cid][kind] = {"path": str(target.relative_to(dest)), "sha256": digest_bytes(source)}
        requests[cid] = request
    write_json(dest / "run.json", meta)
    records, materials = {}, {}
    stopped = ((maximum is not None and prior_usage["transport_attempts"] >= maximum)
               or (token_limit is not None and (not prior_usage["token_usage_complete"]
                                               or prior_usage["known_total_tokens"] >= token_limit)))
    if stopped:
        meta["budget_stop_reason"] = ("usage_unavailable_for_total_token_budget"
                                      if not prior_usage["token_usage_complete"] else "cumulative_budget_exhausted")
    for slot in selected:
        sid = slot["slot_id"]
        folder = dest / _slot_path(sid)
        if sid in reusable:
            previous_root, previous_record, previous_meta = reusable[sid]
            shutil.copytree(previous_root / _slot_path(sid), folder)
            record = read_json(folder / "record.json")
            parent = materials.get(slot.get("parent_slot"))
            material = compose_material(slot, _raw(dest, record), parent)
            if material[0] != previous_record["material"]:
                raise ValueError("Reusable dependency does not share the exact parent material")
            records[sid], materials[sid] = record, material
            meta["slot_record_sha256"][sid] = previous_meta["slot_record_sha256"][sid]
            write_json(dest / "run.json", meta)
            continue
        folder.mkdir(parents=True)
        record = {"schema": "math-gauge.reliability-slot/v1", "slot_id": sid,
                  "case_id": slot["case_id"], "started": False,
                  "status": "not_run", "reason": None, "attempts": [],
                  "locked_attempt": None, "response_path": None, "response_sha256": None,
                  "history_sha256": None, "projected_request_sha256": None,
                  "material_sha256": None, "parent_slot": slot.get("parent_slot"),
                  "prompt_sha256": prompts[sid]["content_sha256"] if sid in prompts else None}
        record["origin"] = origin
        record["evidence_origin_run_id"] = meta["run_id"]
        record["evidence_id"] = identity({"run_id": meta["run_id"], "slot_id": sid})
        messages = _messages_for(slot, requests, prompts, records, dest, runtime)
        if stopped:
            record["reason"] = "budget_exhausted"
        elif messages is None:
            record.update(status="blocked", reason="parent_without_readable_response")
        else:
            projected = {"schema": "math-gauge.conversation/v1", "messages": messages,
                         "parameters": parameters}
            # Per-case budgets stay fixed across attempts and branches. The
            # entire accounting policy is evaluator-side; only this explicit
            # request parameter projection reaches a candidate adapter.
            slot_parameters = case_parameters.get(slot["case_id"], {})
            projected["parameters"] = dict(parameters, **slot_parameters)
            history = [{"role": m["role"], "content_sha256": digest_bytes(m["content"].encode()),
                        "content": m["content"]} for m in messages]
            write_json(folder / "history.json", history)
            write_json(folder / "projected-request.json", projected)
            record.update(history_sha256=identity(history), projected_request_sha256=identity(projected))
            for number in (1, 2):
                if ((maximum is not None and prior_usage["transport_attempts"] + meta["transport_attempts"] >= maximum)
                        or (token_limit is not None and prior_usage["known_total_tokens"] + meta["known_total_tokens"] >= token_limit)):
                    stopped = True
                    meta["budget_stop_reason"] = "cumulative_budget_exhausted"
                    record["reason"] = "budget_exhausted"
                    break
                record["started"] = True
                attempt_dir = folder / "attempts" / str(number)
                attempt_dir.mkdir(parents=True)
                started = now()
                tick = time.monotonic()
                try:
                    if replay is not None:
                        value = responses[sid]
                        if isinstance(value, list):
                            value = value[number - 1] if number <= len(value) else {
                                "status": "permanent_error", "stderr": "Replay has no next transport attempt"}
                    elif adapter is not None:
                        value = adapter(copy.deepcopy(projected))
                    else:
                        # A fresh local workspace contains only whitelisted
                        # attachments; evaluator files are never copied here.
                        with tempfile.TemporaryDirectory(prefix="math-gauge-conversation-") as temp:
                            workspace = Path(temp)
                            for item in requests[slot["case_id"]]["files"]:
                                path = workspace / item["name"]
                                path.parent.mkdir(parents=True, exist_ok=True)
                                path.write_bytes(item["content"].encode())
                            value = invoke_conversation(command, projected, workspace, timeout,
                                                        retryable_exit_codes=codes)
                except (TimeoutError, ConnectionError) as error:
                    value = {"status": "transient_error", "stderr": str(error)}
                except OSError as error:
                    value = {"status": "permanent_error", "stderr": str(error)}
                except (ValueError, TypeError) as error:
                    value = {"status": "permanent_error", "stderr": str(error)}
                try:
                    result = _transport_result(value)
                except ValueError as error:
                    # Broken metadata must not erase a response which already
                    # contains readable assistant text.
                    response = value.get("stdout", b"") if isinstance(value, dict) else b""
                    result = {"stdout": _bytes(response) if isinstance(response, (str, bytes)) else b"",
                              "stderr": str(error).encode(), "status": "permanent_error",
                              "exit_code": None, "usage": {}}
                raw = result.pop("stdout")
                error = result.pop("stderr")
                (attempt_dir / "response.md").write_bytes(raw)
                (attempt_dir / "stderr.txt").write_bytes(error)
                readable = _readable(raw) is not None
                attempt = {**result, "number": number, "started_at": started, "finished_at": now(),
                           "elapsed_seconds": round(time.monotonic() - tick, 6),
                           "response_path": str((attempt_dir / "response.md").relative_to(dest)),
                           "response_sha256": digest_bytes(raw), "stderr_sha256": digest_bytes(error),
                           "readable_text": readable,
                           "projected_request_sha256": record["projected_request_sha256"]}
                write_json(attempt_dir / "record.json", attempt)
                record["attempts"].append(attempt)
                meta["transport_attempts"] += 1
                meta["candidate_calls"] += origin == "command"
                meta["known_total_tokens"] += result["usage"].get("total_tokens", 0)
                if "total_tokens" not in result["usage"]:
                    meta["token_usage_complete"] = False
                    if token_limit is not None:
                        stopped = True
                        meta["budget_stop_reason"] = "usage_unavailable_for_total_token_budget"
                elif token_limit is not None and prior_usage["known_total_tokens"] + meta["known_total_tokens"] >= token_limit:
                    stopped = True
                    meta["budget_stop_reason"] = "total_token_budget_exhausted"
                meta["total_tokens"] = meta["known_total_tokens"] if meta["token_usage_complete"] else None
                if readable:
                    record.update(status="responded", locked_attempt=number,
                                  response_path=attempt["response_path"], response_sha256=attempt["response_sha256"])
                    break
                if result["status"] == "budget_exhausted":
                    stopped = True
                if stopped or number == 2 or result["status"] not in {"transient_error", "timeout"}:
                    record.update(status="execution_error", reason=result["status"])
                    break
                if wait:
                    time.sleep(wait)
            if record["status"] == "not_run" and record["started"]:
                record["status"] = "execution_error"
        parent = materials.get(slot.get("parent_slot"))
        material = compose_material(slot, _raw(dest, record), parent)
        _save_material(dest, slot, material)
        record["material_sha256"] = material[0]["material_sha256"]
        write_json(folder / "record.json", record)
        meta["slot_record_sha256"][sid] = digest_bytes((folder / "record.json").read_bytes())
        records[sid], materials[sid] = record, material
        write_json(dest / "run.json", meta)
    meta.update(status="budget_exhausted" if stopped else "completed", completed_at=now())
    for sid, record in records.items():
        if record["attempts"] and record["evidence_id"] not in meta["budget_evidence"]:
            descriptor = _budget_descriptor(dest, _slot_path(sid) + "/record.json")
            meta["budget_evidence"][record["evidence_id"]] = descriptor
    cumulative = _budget_totals(meta["budget_evidence"])
    meta.update(cumulative_transport_attempts=cumulative["transport_attempts"],
                cumulative_known_total_tokens=cumulative["known_total_tokens"],
                cumulative_token_usage_complete=cumulative["token_usage_complete"],
                cumulative_total_tokens=cumulative["known_total_tokens"] if cumulative["token_usage_complete"] else None)
    meta["execution_failures"] = sum(r["status"] in {"execution_error", "blocked"} for r in records.values())
    meta["unrun_slots"] = [sid for sid, r in records.items() if not r["started"] and sid not in meta["reused_from"]]
    write_json(dest / "run.json", meta)
    return meta


def inspect_reliability_run(root):
    """Recompute all response, projection, history and material links from bytes."""
    root = Path(root).resolve()
    meta = read_json(root / "run.json")
    if meta.get("schema") != "math-gauge.reliability-run/v1":
        raise ValueError("Unsupported reliability run")
    plan_raw = safe_file(root, "plan.json").read_bytes()
    plan = validate_plan(json.loads(plan_raw))
    if (digest_bytes(plan_raw) != meta.get("plan_file_sha256")
            or plan["plan_sha256"] != meta.get("plan_sha256")
            or plan["runner_sha256"] != meta.get("runner_sha256")
            or meta.get("parser_version") != PARSER_VERSION):
        raise ValueError("Frozen reliability plan or parser identity changed")
    manifest_hash = identity({k: meta[k] for k in (
        "plan_sha256", "execution_targets", "selected_slot_ids", "reused_from",
        "command", "timeout_seconds", "origin", "context_transport", "prior_budget_evidence", "budget_scope")})
    if manifest_hash != meta.get("execution_manifest_sha256"):
        raise ValueError("Frozen execution manifest changed")
    if identity(meta.get("execution_contract")) != meta.get("execution_contract_sha256"):
        raise ValueError("Frozen adapter execution contract changed")
    for eid, descriptor in meta.get("budget_evidence", {}).items():
        if _budget_descriptor(root, descriptor["record_path"]) != descriptor or descriptor["evidence_id"] != eid:
            raise ValueError("Frozen cumulative budget evidence changed")
    for eid, descriptor in meta.get("prior_budget_evidence", {}).items():
        if meta.get("budget_evidence", {}).get(eid) != descriptor:
            raise ValueError("Inherited budget evidence disappeared")
    if meta.get("completed_at") is not None:
        cumulative = _budget_totals(meta.get("budget_evidence", {}))
        if (meta.get("cumulative_transport_attempts") != cumulative["transport_attempts"]
                or meta.get("cumulative_known_total_tokens") != cumulative["known_total_tokens"]
                or meta.get("cumulative_token_usage_complete") != cumulative["token_usage_complete"]):
            raise ValueError("Cumulative budget accounting changed")
    prompts = _validate_schedule(plan)
    expected = select_slots(plan, meta.get("execution_targets"))
    if meta.get("selected_slot_ids") != [s["slot_id"] for s in expected]:
        raise ValueError("Frozen execution projection changed")
    runtime = _runtime(plan)
    requests = {}
    for case in plan["case_index"]:
        cid = case["case_id"]
        binding = meta["inputs"][cid]
        for kind in ("reference", "rubric"):
            descriptor = binding.get(kind, {})
            if digest_bytes(safe_file(root, descriptor.get("path", "")).read_bytes()) != descriptor.get("sha256"):
                raise ValueError("Frozen evaluator reference or rubric changed")
        request = read_json(safe_file(root, binding["request"]))
        if (_request_hash(request) != case["request_sha256"]
                or digest_bytes(candidate_message(request).encode()) != case["candidate_message_sha256"]
                or request.get("case_id") != cid or request.get("case_version") != case["version"]
                or digest_bytes(safe_file(root, binding["contract"]).read_bytes()) != case["group_contract_sha256"]):
            raise ValueError("Frozen candidate projection or review contract changed")
        contract = validate_group_contract(read_json(safe_file(root, binding["contract"])))
        if contract["id"] != cid:
            raise ValueError("Frozen group contract identity changed")
        requests[cid] = request
    records, materials = {}, {}
    for slot in expected:
        sid = slot["slot_id"]
        folder = root / _slot_path(sid)
        record_raw = safe_file(root, _slot_path(sid) + "/record.json").read_bytes()
        record = json.loads(record_raw)
        if (digest_bytes(record_raw) != meta["slot_record_sha256"].get(sid)
                or record.get("slot_id") != sid or record.get("case_id") != slot["case_id"]
                or record.get("parent_slot") != slot.get("parent_slot")):
            raise ValueError("Frozen slot record changed")
        if record.get("evidence_id") != identity({"run_id": record.get("evidence_origin_run_id"), "slot_id": sid}):
            raise ValueError("Original generation evidence identity changed")
        reused = meta.get("reused_from", {}).get(sid)
        if reused is not None:
            if (reused.get("plan_sha256") != plan["plan_sha256"]
                    or reused.get("evidence_id") != record["evidence_id"]
                    or reused.get("slot_record_sha256") != digest_bytes(record_raw)):
                raise ValueError("Reusable dependency provenance changed")
        elif record["evidence_origin_run_id"] != meta["run_id"]:
            raise ValueError("Foreign generation evidence lacks a frozen reuse manifest")
        elif record.get("origin") != meta["origin"]:
            raise ValueError("Original generation kind changed")
        messages = _messages_for(slot, requests, prompts, records, root, runtime)
        if record["history_sha256"] is not None:
            history = read_json(folder / "history.json")
            wanted = [{"role": m["role"], "content_sha256": digest_bytes(m["content"].encode()),
                       "content": m["content"]} for m in messages] if messages is not None else None
            projected = read_json(folder / "projected-request.json")
            parameters = dict(_parameters(runtime), **runtime["budget"].get("case_parameters", {}).get(slot["case_id"], {}))
            if (history != wanted or identity(history) != record["history_sha256"]
                    or projected != {"schema": "math-gauge.conversation/v1", "messages": messages,
                                     "parameters": parameters}
                    or identity(projected) != record["projected_request_sha256"]):
                raise ValueError("Reliability visible history or projected request changed")
        elif record["started"]:
            raise ValueError("Started slot lacks its frozen visible history")
        first_readable = None
        for number, attempt in enumerate(record["attempts"], 1):
            attempt_path = _slot_path(sid) + f"/attempts/{number}"
            if read_json(safe_file(root, attempt_path + "/record.json")) != attempt or attempt["number"] != number:
                raise ValueError("Transport attempt record changed")
            data = safe_file(root, attempt["response_path"]).read_bytes()
            error = safe_file(root, attempt_path + "/stderr.txt").read_bytes()
            if (digest_bytes(data) != attempt["response_sha256"]
                    or digest_bytes(error) != attempt["stderr_sha256"]
                    or (_readable(data) is not None) != attempt["readable_text"]
                    or attempt["projected_request_sha256"] != record["projected_request_sha256"]):
                raise ValueError("Frozen transport output changed")
            if first_readable is not None or number > 2:
                raise ValueError("Transport retried a locked answer or exceeded its bound")
            if number == 2 and record["attempts"][0]["status"] not in {"transient_error", "timeout"}:
                raise ValueError("Transport retried a permanent failure")
            if attempt["readable_text"]:
                first_readable = number
        if first_readable != record["locked_attempt"]:
            raise ValueError("Slot does not lock the first readable transport response")
        if first_readable is not None:
            locked = record["attempts"][first_readable - 1]
            if (record["response_path"] != locked["response_path"]
                    or record["response_sha256"] != locked["response_sha256"]
                    or record["status"] != "responded"):
                raise ValueError("Locked slot response changed")
        material = compose_material(slot, _raw(root, record), materials.get(slot.get("parent_slot")))
        saved = read_json(folder / "material.json")
        if material[0] != saved or saved["material_sha256"] != record["material_sha256"]:
            raise ValueError("Reliability material chain changed")
        for name, data in (("material-body.md", material[1]), ("keep-rationale.md", material[2])):
            path = folder / name
            if (data is not None and (not path.is_file() or path.read_bytes() != data)) or (data is None and path.exists()):
                raise ValueError("Reconstructed material bytes changed")
        records[sid] = dict(record, material=saved)
        materials[sid] = material
    meta = dict(meta, plan=plan)
    if meta.get("completed_at") is not None:
        wanted_budget = set(meta.get("prior_budget_evidence", {})) | {
            r["evidence_id"] for r in records.values() if r["attempts"]}
        if set(meta.get("budget_evidence", {})) != wanted_budget:
            raise ValueError("Cumulative budget ledger omitted original generation evidence")
        local = [r for sid, r in records.items() if sid not in meta.get("reused_from", {})]
        if sum(len(r["attempts"]) for r in local) != meta.get("transport_attempts"):
            raise ValueError("Current-run transport accounting changed")
    return meta, records


# Keep execution usable without importing the review owner or any review data.
def reliability_review_templates(root):
    from .reliability_review import reliability_review_templates as implementation
    return implementation(root)


def apply_reliability_reviews(root, entries, *, revise=False, expected_snapshot=None):
    from .reliability_review import apply_reliability_reviews as implementation
    return implementation(root, entries, revise=revise, expected_snapshot=expected_snapshot)


def reliability_score_inputs(root, *, snapshot=None):
    from .reliability_review import reliability_score_inputs as implementation
    return implementation(root, snapshot=snapshot)
