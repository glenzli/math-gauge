"""Ordered native open-research turns, with evaluator-only execution evidence."""

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
from urllib.parse import unquote, urlsplit
import uuid

from . import taste_v130 as flow


PLAN_SCHEMA = "math-gauge.independent-research-batch-plan/v1"
EXECUTION_SCHEMA = "math-gauge.independent-research-execution/v1"
BATCH_SCHEMA = "math-gauge.independent-research-execution-summary/v1"
NATIVE_ORIGIN = "codex-app-server"
PARALLEL_DISPATCH_SCHEMA = "math-gauge.independent-research-parallel-dispatch/v1"
PERMISSION_PROFILE = "independent-research-local"
ROUNDS = flow.ROUNDS
BUDGETS = {"native_seconds": None, "native_output_tokens": None,
           "broker_seconds_per_round": 2700, "controller_seconds_per_round": 2700,
           "outer_seconds_per_round": 2760}


def _require(condition, message):
    if not condition:
        raise ValueError(message)


def utc():
    return datetime.now(timezone.utc).isoformat()


def sha256(raw):
    return hashlib.sha256(raw).hexdigest()


def json_bytes(value):
    return (json.dumps(value, ensure_ascii=False, allow_nan=False) + "\n").encode()


def write_bytes(path, raw):
    with path.open("xb") as stream:
        stream.write(raw)


def write_json(path, value):
    write_bytes(path, json_bytes(value))


def descriptor(root, path):
    raw = path.read_bytes()
    return {"path": path.relative_to(root).as_posix(), "bytes": len(raw),
            "sha256": sha256(raw)}


def _read(root, ref, name=None):
    if name is not None:
        _require(ref.get("path") == name, f"Unexpected execution artifact: {name}")
    return flow._read(root, ref)


def load_plan(plan_path, public_root, *, fixture=False):
    """Verify the authorized private queue against the exact retained inputs."""
    path = flow._safe_absolute(plan_path)
    plan = json.loads(path.read_bytes())
    _require(plan.get("schema") == PLAN_SCHEMA and plan.get("edition") == flow.EDITION
             and plan.get("status") == "authorized-preparation-not-started"
             and plan.get("rounds") == list(ROUNDS) and plan.get("candidate_model_calls") == 0,
             "Invalid independent-research plan")
    reg_ref = plan["registration"]
    registration = flow._contained(path.parent, reg_ref["path"])
    _require(sha256(registration.read_bytes()) == reg_ref["sha256"], "Registration changed")
    flow.load_case(registration)
    baseline = flow._contained(public_root, plan["baseline"]["path"])
    _require(plan["baseline"]["edition"] == "1.2.0" and
             sha256(baseline.read_bytes()) == plan["baseline"]["sha256"], "Baseline changed")
    _require(all(plan["budgets"].get(k) == v for k, v in BUDGETS.items()
                 if k != "broker_seconds_per_round")
             and plan["budgets"].get("broker_seconds_per_round", 2700) == 2700
             and plan["budgets"]["outer_grace_is_answer_time"] is False,
             "Unexpected research round budgets")
    required_conditions = {"commit_before_candidate_dispatch": True,
                           "preflight_before_candidate_dispatch": True,
                           "fresh_native_session": True, "same_session_three_rounds": True,
                           "local_tools": True, "tool_network": False,
                           "external_materials": False, "extra_feedback": False,
                           "fourth_round": False, "seal_first_normal_final_before_next_round": True,
                           "automatic_quality_retry": False, "unconfirmed_failure_retry": False}
    _require(all(plan["conditions"].get(k) is v for k, v in required_conditions.items()),
             "Unexpected independent-research operating conditions")
    cohort = plan["cohort"]
    _require(isinstance(cohort, list) and cohort
             and plan["maximum_initial_math_dispatches"] == len(cohort) * len(ROUNDS)
             and len({row["id"] for row in cohort}) == len(cohort)
             and len({(row["model"], row["effort"]) for row in cohort}) == len(cohort),
             "Expected a unique, ordered candidate cohort")
    if not fixture:
        _require(len(cohort) == 10, "Native queue must contain the ten authorized configurations")
    for row in cohort:
        _require(re.fullmatch(r"[a-z0-9][a-z0-9.-]{1,63}", row["id"])
                 and row["status"] == "not-started" and row["effort"] in {"max", "xhigh"},
                 "Invalid candidate configuration")
        source = row["prior_selected_source"]
        record_raw = flow._contained(public_root, source["path"]).read_bytes()
        _require(sha256(record_raw) == source["sha256"], "Prior selected record changed")
        model = json.loads(record_raw)["model"]
        exact = (model.get("requested_model"), model.get("requested_reasoning_effort"))
        legacy = model.get("requested_label", "").split(" ", 1)[0]
        _require(exact == (row["model"], row["effort"]) or
                 (exact == (None, None) and legacy == row["model"] + "/" + row["effort"]),
                 "Requested model or effort lacks a retained source binding")
    return plan, registration


def prepare(plan_path, public_root, destination, *, fixture=False):
    plan, registration = load_plan(plan_path, public_root, fixture=fixture)
    destination = flow._safe_absolute(destination)
    for root in (Path(public_root).resolve(), flow._source_tree(registration)):
        _require(not (destination.is_relative_to(root) or root.is_relative_to(destination)),
                 "Place execution evidence and candidate work outside all source trees")
    destination.mkdir(mode=0o700)
    for name in ("control", "workspaces", "runtime"):
        (destination / name).mkdir(mode=0o700)
    write_bytes(destination / "control/plan.json", Path(plan_path).read_bytes())
    write_bytes(destination / "control/registration.json", registration.read_bytes())
    write_json(destination / "control/prepared.json", {
        "schema": "math-gauge.independent-research-preparation/v1",
        "plan_path": str(flow._safe_absolute(plan_path)), "registration_path": str(registration),
        "public_root": str(public_root), "created_at": utc(), "fixture_only": fixture,
        "plan_sha256": sha256((destination / "control/plan.json").read_bytes()),
        "budgets": BUDGETS, "candidate_dispatches": 0,
    })
    return destination


def prepared(run_root):
    root = flow._safe_absolute(run_root)
    data = json.loads((root / "control/prepared.json").read_bytes())
    plan, registration = load_plan(data["plan_path"], Path(data["public_root"]),
                                   fixture=data["fixture_only"])
    raw = (root / "control/plan.json").read_bytes()
    _require(sha256(raw) == data["plan_sha256"] and raw == Path(data["plan_path"]).read_bytes(),
             "Prepared plan changed")
    _require((root / "control/registration.json").read_bytes() == registration.read_bytes(),
             "Prepared registration changed")
    _require(data["budgets"] == BUDGETS, "Prepared budgets changed")
    return root, data, plan, registration


def _r1_materials(registration, work):
    materials = []
    for ref in registration["packet"]:
        raw = flow._read(work, ref)
        if ref["path"] == "packet/body.md":
            materials.insert(0, {"type": "text", "text": raw.decode("utf-8"), "text_elements": []})
        else:
            materials.append({"type": "localImage", "path": str(work / ref["path"])})
    return materials


def turn_request(request_id, thread_id, model, effort, prompt, materials=()):
    return {"id": request_id, "method": "turn/start", "params": {
        "threadId": thread_id, "model": model, "effort": effort,
        "input": [{"type": "text", "text": prompt, "text_elements": []}, *materials],
    }}


def thread_identity(response, model, effort, work, *, request_id=2):
    result = response["result"]
    thread = result["thread"]
    _require(response["id"] == request_id and result["model"] == model and
             result["reasoningEffort"] == effort and result["modelProvider"] == "openai"
             and result["approvalPolicy"] == "never" and result["cwd"] == str(work)
             and result["activePermissionProfile"]["id"] == PERMISSION_PROFILE
             and result.get("instructionSources") == []
             and thread["ephemeral"] is True and thread["path"] is None and thread["turns"] == [],
             "Native thread did not confirm the frozen fresh model and permission settings")
    return str(uuid.UUID(thread["id"]))


def parse_turn(request, lines, *, cutoff):
    """Read the first terminal and first explicit final from exact native events."""
    thread = request["params"]["threadId"]
    turn, terminal, first, first_index, violation = None, None, None, None, None
    usage = []
    active = set()
    for index, line in enumerate(lines):
        message = json.loads(line)
        _require(isinstance(message, dict), "Invalid app-server message")
        method, params = message.get("method"), message.get("params", {})
        if message.get("id") == request["id"] and method is None:
            if "error" in message:
                violation = "native-dispatch-rejected"
                break
            new = message["result"]["turn"]["id"]
            _require(turn is None or turn == new, "Turn acknowledgement changed identity")
            turn = new
        if method and "id" in message:
            violation = "unexpected-server-request"
            break
        if params.get("threadId") != thread:
            continue
        if method == "turn/started":
            new = params["turn"]["id"]
            _require(turn is None or new == turn, "Unexpected concurrent turn")
            turn = new
        if turn is None:
            continue
        if method == "turn/completed" and params["turn"]["id"] == turn:
            terminal = params["turn"]["status"]
            _require(terminal in {"completed", "failed", "interrupted"}, "Invalid native terminal")
            if terminal == "completed" and params["turn"].get("error") is not None:
                violation = "contradictory-native-terminal"
            break
        if params.get("turnId") != turn:
            continue
        if method == "model/rerouted":
            violation = "model-rerouted"
            break
        if method == "thread/tokenUsage/updated":
            usage.append(params["tokenUsage"])
        if method not in {"item/started", "item/completed"}:
            continue
        item = params["item"]
        kind = item["type"]
        if kind not in {"userMessage", "agentMessage", "reasoning", "plan", "contextCompaction",
                        "commandExecution", "fileChange", "imageView"}:
            violation = "unexpected-native-tool-or-item"
            break
        if kind in {"commandExecution", "fileChange", "imageView"}:
            if method == "item/started":
                active.add(item["id"])
            else:
                active.discard(item["id"])
        if (method == "item/completed" and kind == "agentMessage"
                and item.get("phase") == "final_answer" and item.get("text", "").strip()):
            if first is None:
                first, first_index = item["text"], index
    result = {"turn_id": turn, "terminal": terminal, "usage_events": usage,
              "final_event_index": first_index, "violation": violation,
              "active_tool_items": sorted(active)}
    if cutoff == "native-terminal" and terminal == "completed" and first and not (violation or active):
        return {**result, "delivery": "normal-final", "final": first.encode()}
    delivery = "delivery-failed" if cutoff == "deadline" and turn and not violation else "unresolved"
    return {**result, "delivery": delivery, "final": None}


def _stamp(value):
    timestamp = datetime.fromisoformat(value)
    _require(timestamp.tzinfo is not None, "Execution time must be timezone-aware")
    return timestamp


def _attachment_paths(text, work):
    """Find only linked or explicitly delivered local Markdown paths."""
    refs = re.compile(r"\]\((?:<([^>\n]+)>|([^\s)]+))(?:\s+\"[^\"\n]*\")?\)|`([^`\n]+\.md)`", re.I)
    delivery = re.compile(r"交付|提交|附件|稿件|手稿|全文|正文|写入|见|deliver|manuscript|attached|saved|written|see\b", re.I)
    local = {}
    for match in refs.finditer(text):
        target = next(group for group in match.groups() if group is not None)
        if match.group(3):
            before = text[:match.start()].rsplit("\n", 1)[-1][-120:]
            after = text[match.end():].split("\n", 1)[0][:120]
            if not delivery.search(before + after):
                continue
        parts = urlsplit(target)
        name = unquote(parts.path)
        if parts.scheme not in {"", "file"} or not name.lower().endswith(".md"):
            continue
        path = Path(name)
        if (parts.netloc or ".." in path.parts or any(c in name for c in ("\\", "\0"))
                or (path.is_absolute() and not path.is_relative_to(work))):
            local[(target, None)] = None
            continue
        rel = path.relative_to(work).as_posix() if path.is_absolute() else path.as_posix()
        if rel.split("/", 1)[0] not in {"packet", "rounds"} and rel != "rules.md":
            local[(target, rel)] = None
    return list(local)


def _collect_attachments(text, work):
    files, errors, seen = [], [], set()
    for target, name in _attachment_paths(text, work):
        if name is None or name in {f"answer-{rid}.md" for rid in ROUNDS}:
            errors.append({"target": target, "path": name, "status": "out-of-scope"})
            continue
        if name in seen:
            continue
        seen.add(name)
        try:
            path = flow._contained(work, name)
        except ValueError:
            errors.append({"target": target, "path": name, "status": "unsafe-path"})
            continue
        if not path.is_file():
            errors.append({"target": target, "path": name, "status": "missing-regular-file"})
            continue
        files.append(descriptor(work, path))
    return files, errors


def execute_one(
    root, prepared_data, plan, registration, model, transport_factory, *,
    register_thread, preflight_ref=None, fixture=False, parallel_dispatch=None,
):
    """Run one configuration through the same three-round collection boundary."""
    _require(prepared_data["fixture_only"] is fixture, "Fixture and native plans must stay separate")
    _require(fixture or preflight_ref is not None, "Native execution needs verified preflight")
    _require(model in plan["cohort"], "Model must belong to the frozen cohort")
    registration_data = json.loads((root / "control/registration.json").read_bytes())
    origin = "fixture" if fixture else NATIVE_ORIGIN
    model_id = model["id"]
    control = root / "control" / model_id
    control.mkdir(mode=0o700)
    state, work = control / "state", root / "workspaces" / model_id
    context = uuid.uuid4().hex
    prompt = flow.reveal(registration, state, work, "R1", context)
    rounds, thread, outcome = [], None, "not-started"
    try:
        with transport_factory(model, control, work) as transport:
            thread = transport.start()
            _require(isinstance(thread, str) and thread, "Expected a fresh native thread")
            register_thread(thread)
            previous = None
            for index, rid in enumerate(ROUNDS):
                if index:
                    prompt = flow.reveal(registration, state, work, rid, context)
                request = turn_request(100 + index, thread, model["model"], model["effort"],
                                       prompt.read_bytes().decode("utf-8"),
                                       _r1_materials(registration_data, work) if index == 0 else ())
                request_path = control / f"{rid}.request.ndjson"
                write_bytes(request_path, json_bytes(request))
                capture = transport.turn(request, rid)
                events_path = control / f"{rid}.native.ndjson"
                write_bytes(events_path, b"".join(capture["lines"]))
                result = parse_turn(request, capture["lines"], cutoff=capture["cutoff"])
                final, delivery = result.pop("final"), result["delivery"]
                answer, attachments, attachment_errors = None, [], []
                if final is not None:
                    attachments, attachment_errors = _collect_attachments(final.decode(), work)
                    answer = work / f"answer-{rid}.md"
                    write_bytes(answer, final)
                boundary_kind = {"normal-final": "first-normal-final", "delivery-failed": "deadline"}.get(
                    delivery, "native-terminal" if result["terminal"] else "unavailable")
                times = capture["received_at"]
                boundary = times[result["final_event_index"]] if final is not None else capture["boundary_at"]
                obs = control / f"{rid}.operator.json"
                write_json(obs, {"schema": "math-gauge.research-round-observation/v1", "round": rid,
                    "context_id": context, "request_id": f"{thread}/{request['id']}",
                    "kind": "fixture" if fixture else "operator-attestation", "delivery": delivery,
                    "first_normal_final": True if final is not None else None,
                    "boundary": {"kind": boundary_kind, "at": boundary},
                    "native_terminal": result["terminal"], "raw": descriptor(work, answer) if answer else None,
                    "delivered_files": attachments})
                flow.seal_final(registration, state, work, rid, context, answer, obs)
                seal = descriptor(root, state / f"{rid}.seal.json")
                rounds.append({**result, "round": rid, "request": descriptor(root, request_path),
                    "wire_events": descriptor(root, events_path), "seal": seal,
                    "observation": descriptor(root, state / f"{rid}.observation.json"),
                    "attachment_diagnostics": attachment_errors,
                    "previous_seal_sha256": previous, "sent_at": capture["sent_at"],
                    "received_at": times, "boundary_at": capture["boundary_at"],
                    "sealed_at": utc(), "cutoff": capture["cutoff"], "pid_evidence": capture["pids"]})
                previous = seal["sha256"]
                outcome = "normal-finals" if index == 2 and final is not None else delivery
                if delivery != "normal-final":
                    break
    except (OSError, ValueError, RuntimeError, KeyError, TypeError, TimeoutError) as error:
        outcome = "unresolved" if thread is not None else "not-started"
        write_json(control / "controller-error.json", {"class": type(error).__name__, "error": str(error)})
    manifest = control / "execution.json"
    artifacts = {name: descriptor(root, control / name) for name in (
        "app-server.stdin.ndjson", "app-server.stdout.ndjson", "app-server.stderr.txt", "process-exit.json")
        if (control / name).is_file()}
    summary = {"schema": EXECUTION_SCHEMA, "origin": origin,
        "model_id": model_id, "requested_model": model["model"], "requested_effort": model["effort"],
        "observed_backend_sku": None, "observed_backend_reasoning_effort": None,
        "context_id": context, "native_context_id": thread, "state": state.relative_to(root).as_posix(),
        "registration_sha256": plan["registration"]["sha256"], "plan_sha256": prepared_data["plan_sha256"],
        "preflight": preflight_ref, "budgets": BUDGETS, "rounds": rounds, "outcome": outcome,
        "artifacts": artifacts,
        "app_server": descriptor(root, control / "app-server.json") if (control / "app-server.json").exists() else None,
        "provider_request_count": None, "finished_at": utc()}
    if parallel_dispatch is not None:
        summary["parallel_dispatch"] = parallel_dispatch
    write_json(manifest, summary)
    return {"model_id": model_id, "outcome": outcome, "execution": descriptor(root, manifest)}


def write_batch_summary(root, prepared_data, plan, rows, *, fixture=False):
    """Merge collected evidence once, in the source plan's order."""
    by_model = {row["model_id"]: row for row in rows}
    expected = [model["id"] for model in plan["cohort"]]
    _require(len(by_model) == len(rows) and set(by_model) <= set(expected),
             "Batch rows must belong to unique frozen configurations")
    summary = {
        "schema": BATCH_SCHEMA, "origin": "fixture" if fixture else NATIVE_ORIGIN,
        "plan_sha256": prepared_data["plan_sha256"],
        "registration_sha256": plan["registration"]["sha256"],
        "cohort": [by_model.get(model_id, {"model_id": model_id, "outcome": "not-started", "execution": None})
                   for model_id in expected],
        "finished_at": utc(),
    }
    write_json(root / "batch-summary.json", summary)
    return summary


def execute_queue(run_root, transport_factory, *, preflight_ref=None, fixture=False):
    """Process each model serially. The transport never sees evaluator paths or feedback."""
    root, prepared_data, plan, registration = prepared(run_root)
    rows, seen_threads = [], set()

    def register_thread(thread):
        _require(thread not in seen_threads, "Expected a fresh, unique native thread")
        seen_threads.add(thread)

    for model in plan["cohort"]:
        row = execute_one(root, prepared_data, plan, registration, model, transport_factory,
                          register_thread=register_thread, preflight_ref=preflight_ref, fixture=fixture)
        rows.append(row)
        if row["outcome"] in {"unresolved", "not-started"}:
            break
    return write_batch_summary(root, prepared_data, plan, rows, fixture=fixture)


def validate_execution(run_root: Path, execution_ref: dict, plan: dict, *, allow_fixture=False) -> dict:
    """Verify a settled run against the frozen private plan and raw wire events."""
    root = flow._safe_absolute(run_root)
    plan_bytes = (root / "control/plan.json").read_bytes()
    _require(json.loads(plan_bytes) == plan, "Execution uses a different plan")
    data = json.loads(_read(root, execution_ref))
    row = next((v for v in plan["cohort"] if v["id"] == data["model_id"]), None)
    _require(row is not None and data["schema"] == EXECUTION_SCHEMA and data["budgets"] == BUDGETS
             and data["registration_sha256"] == plan["registration"]["sha256"]
             and data["plan_sha256"] == sha256(plan_bytes)
             and data["requested_model"] == row["model"] and data["requested_effort"] == row["effort"],
             "Execution identity differs from frozen candidate configuration")
    model_id, thread = row["id"], data["native_context_id"]
    control = f"control/{model_id}"
    _require(execution_ref["path"] == f"{control}/execution.json" and data["state"] == f"{control}/state"
             and isinstance(thread, str) and bool(thread), "Invalid execution or context path")
    fixture = data["origin"] == "fixture" and allow_fixture
    if not fixture:
        _require(data["origin"] == NATIVE_ORIGIN, "Fixture or unknown origin cannot be adopted")
        preflight = json.loads(_read(root, data["preflight"], "control/preflight.json"))
        _require(preflight["status"] == "passed" and preflight["plan_sha256"] == data["plan_sha256"],
                 "Execution lacks a passed native preflight")
        parallel_ref = data.get("parallel_dispatch")
        if parallel_ref is not None:
            dispatch = json.loads(_read(root, parallel_ref, "control/parallel-dispatch-freeze.json"))
            _require(dispatch["schema"] == PARALLEL_DISPATCH_SCHEMA
                     and dispatch["source_plan_sha256"] == data["plan_sha256"]
                     and dispatch["preflight"] == data["preflight"]
                     and model_id in dispatch["remaining_priority"]
                     and _stamp(dispatch["frozen_at"]) <= _stamp(data["rounds"][0]["sent_at"]),
                     "Parallel execution lacks its separate, earlier dispatch freeze")
        server = json.loads(_read(root, data["app_server"], f"{control}/app-server.json"))
        _require(server["thread_id"] == thread and server["configured_model"] == row["model"]
                 and server["configured_effort"] == row["effort"] and server["parent_pid"] > 0,
                 "Execution lacks matching native thread startup evidence")
        original = json.loads(_read(root, server["thread_start_response"], f"{control}/thread-start.ndjson"))
        _require(thread_identity(original, row["model"], row["effort"], root / "workspaces" / model_id) == thread,
                 "Native thread response does not match the retained execution")
        native_proof = json.loads(_read(root, server["parent_pid_check"], f"{control}/native-parent-pid.json"))
        tool_proof = json.loads(_read(root, server["tool_probe"], f"{control}/native-tool-probe.ndjson"))["result"]
        _require(native_proof["passed"] is True and native_proof["pid"] == server["parent_pid"]
                  and tool_proof["exitCode"] == 0 and json.loads(tool_proof["stdout"])["passed"] is True,
                  "Native process policy evidence is incomplete")
        artifacts = data["artifacts"]
        stdout = _read(root, artifacts["app-server.stdout.ndjson"], f"{control}/app-server.stdout.ndjson")
        stdin = _read(root, artifacts["app-server.stdin.ndjson"], f"{control}/app-server.stdin.ndjson")
        _read(root, artifacts["app-server.stderr.txt"], f"{control}/app-server.stderr.txt")
        ended = json.loads(_read(root, artifacts["process-exit.json"], f"{control}/process-exit.json"))
        _require(ended["pid"] == server["parent_pid"], "Native exit refers to another process")
        dispatches = [line for line in stdin.splitlines(keepends=True) if json.loads(line).get("method") == "turn/start"]
    rounds = data["rounds"]
    _require(data["outcome"] in {"normal-finals", "delivery-failed"} and
             0 < len(rounds) <= len(ROUNDS), "Execution is unresolved or unstarted")
    state = flow._contained(root, data["state"])
    seals = flow._seals(state, data["registration_sha256"])
    session = json.loads((state / "session.json").read_bytes())
    _require(len(seals) == len(rounds) and session["context_id"] == data["context_id"],
             "Execution differs from sealed context")
    registration_raw = (root / "control/registration.json").read_bytes()
    _require(sha256(registration_raw) == data["registration_sha256"], "Execution registration content changed")
    registration_data = json.loads(registration_raw)
    work = flow._contained(root, f"workspaces/{model_id}")
    previous, last_sealed, seen_turns = None, None, set()
    offset = 0
    for index, entry in enumerate(rounds):
        rid = ROUNDS[index]
        _require(entry["round"] == rid and entry["previous_seal_sha256"] == previous,
                 "Execution skipped a round or seal")
        request_raw = _read(root, entry["request"], f"{control}/{rid}.request.ndjson")
        request = json.loads(request_raw)
        events_raw = _read(root, entry["wire_events"], f"{control}/{rid}.native.ndjson")
        events = events_raw.splitlines(keepends=True)
        if not fixture:
            location = stdout.find(events_raw, offset)
            _require(len(dispatches) == len(rounds) and dispatches[index] == request_raw and
                     location >= offset and entry["pid_evidence"]["parent"] == server["parent_pid"],
                     "The selected round bytes do not come from the original native transport")
            offset = location + len(events_raw)
        obs = json.loads(_read(root, entry["observation"], f"{data['state']}/{rid}.observation.json"))
        _read(root, entry["seal"], f"{data['state']}/{rid}.seal.json")
        text = request["params"]["input"][0]["text"]
        materials = _r1_materials(registration_data, work) if index == 0 else ()
        _require(request == turn_request(100 + index, thread, row["model"], row["effort"], text, materials)
                 and sha256(text.encode()) == seals[rid]["prompt_sha256"], "Native prompt or turn changed")
        replay = parse_turn(request, events, cutoff=entry["cutoff"])
        final = replay.pop("final")
        _require(all(entry.get(k) == v for k, v in replay.items())
                 and replay["turn_id"] not in seen_turns
                 and obs["request_id"] == f"{thread}/{request['id']}"
                 and obs["kind"] == ("fixture" if fixture else "operator-attestation")
                 and obs["delivery"] == seals[rid]["delivery"] == replay["delivery"]
                 and obs["native_terminal"] == replay["terminal"], "Native delivery differs from sealed outcome")
        seen_turns.add(replay["turn_id"])
        sent, boundary, sealed = map(_stamp, (entry["sent_at"], entry["boundary_at"], entry["sealed_at"]))
        times = list(map(_stamp, entry["received_at"]))
        # Native wire order is preserved above. UTC receipt times are wall-clock observations.
        _require(len(times) == len(events) and sent <= boundary <= sealed
                 and all(sent <= at <= boundary for at in times)
                 and (last_sealed is None or last_sealed <= sent), "Turn timestamps violate freeze order")
        if final is not None:
            _require((state / f"{rid}.md").read_bytes() == final and
                     obs["boundary"]["at"] == entry["received_at"][entry["final_event_index"]],
                     "Sealed final differs from the native first final")
            mentioned = _attachment_paths(final.decode(), work)
            files, diagnostics = obs["delivered_files"], entry["attachment_diagnostics"]
            names = {ref["path"] for ref in files}
            _require(all((d["target"], d["path"]) in mentioned and d["path"] not in names
                         and d["status"] in {"out-of-scope", "unsafe-path", "missing-regular-file"}
                         for d in diagnostics)
                     and names | {d["path"] for d in diagnostics} == {path for _, path in mentioned}
                     and seals[rid]["files"] == [dict(ref, path=f"{rid}.files/{ref['path']}") for ref in files],
                     "Explicit final manuscripts do not match the sealed originals")
        else:
            _require(index == len(rounds) - 1 and entry["delivery"] == "delivery-failed",
                     "Round without a normal final must stop the trajectory")
        previous, last_sealed = entry["seal"]["sha256"], sealed
    _require((data["outcome"] == "normal-finals" and len(rounds) == len(ROUNDS)
              and all(entry["delivery"] == "normal-final" for entry in rounds))
             or (data["outcome"] == "delivery-failed" and rounds[-1]["delivery"] == "delivery-failed"),
             "Execution summary misstates the trajectory")
    return data
