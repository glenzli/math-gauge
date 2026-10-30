"""Evaluator-only profiles and immutable plans over the shared case runner."""

import copy
import json
import uuid
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

from .catalog import (candidate_message, digest_bytes, read_json, safe_file,
                      validate_group_contract, write_json)
from .execution import now, runner_fingerprint

COMPONENTS = ("proofs", "lean-audit", "lean-construction", "chapters")
TARGETS = COMPONENTS + ("repeat", "neutral", "stance", "core", "all")
ATTEMPTS = ("A1", "A2", "A3")
ARMS = ("neutral", "affirm", "deny")


def identity(value):
    """Stable JSON identity; reject non-JSON numbers before freezing a plan."""
    return digest_bytes(json.dumps(value, ensure_ascii=False, sort_keys=True,
                                   separators=(",", ":"), allow_nan=False).encode())


def _require(condition, message):
    if not condition:
        raise ValueError(message)


def _weights(value, names):
    _require(isinstance(value, dict) and set(value) == set(names),
             "Weights must name every frozen component exactly once")
    _require(all(type(x) is int and x > 0 for x in value.values())
             and sum(value.values()) == 100,
             "Weights must be positive integral percentages summing to 100")


def _runtime_contract(runtime):
    if runtime is not None:
        _require(isinstance(runtime, dict)
                 and isinstance(runtime.get("model_label"), str) and runtime["model_label"]
                 and isinstance(runtime.get("budget"), dict) and runtime["budget"]
                 and isinstance(runtime.get("adapter_identity"), (str, dict))
                 and runtime["adapter_identity"],
                 "Frozen runtime requires model_label, budget and adapter_identity")
    identity(runtime)


@dataclass
class BenchmarkProfile:
    path: Path
    root: Path
    data: dict
    sha256: str

    @classmethod
    def load(cls, path, suite, *, repository_root=None):
        path = Path(path).resolve()
        raw = path.read_bytes()
        data = json.loads(raw)
        root = Path(repository_root or suite.root.parent).resolve()
        _require(isinstance(data, dict) and data.get("schema") == "math-gauge.benchmark-profile/v1"
                 and data.get("operator_only") is True
                 and data.get("path_base") == "repository",
                 "Unsupported evaluator-only benchmark profile")
        for key in ("id", "version"):
            _require(isinstance(data.get(key), str) and data[key],
                     "Profile requires " + key)
        frozen = data.get("suite", {})
        _require(frozen == {"id": suite.metadata["id"],
                            "version": suite.metadata["version"],
                            "sha256": suite.sha256},
                 "Profile binds a different suite identity")
        rows = data.get("components")
        _require(isinstance(rows, list) and all(isinstance(x, dict) for x in rows)
                 and [x.get("id") for x in rows] == list(COMPONENTS),
                 "Profile must retain the four ordered core components")
        _weights({x["id"]: x.get("weight") for x in rows}, COMPONENTS)
        members = []
        for row in rows:
            ids = row.get("case_ids")
            _require(isinstance(ids, list) and ids
                     and all(isinstance(cid, str) for cid in ids),
                     "Each core component requires its full paper list")
            members.extend(ids)
            for cid in ids:
                _require(cid in suite.cases, "Unknown paper in core component")
                case = suite.cases[cid]
                _require(bool(case.get("group_contract")), "Benchmark scoring requires a stage contract")
                contract = read_json(safe_file(suite.root, case["group_contract"]))
                _require(_category_matches(row["id"], case.get("task_kind"), contract.get("kind")),
                         "Core category differs from the paper's actual task and contract")
        _require(len(members) == len(set(members))
                 and set(members) == set(suite.cases),
                 "Core components must partition the complete suite without overlap")
        _require(data.get("attempts") == list(ATTEMPTS),
                 "Three fixed independent attempts are required")
        _weights(data.get("overall_weights"), ("core", "repeat", "neutral", "stance"))
        reliability = data.get("reliability")
        _require(isinstance(reliability, dict), "Reliability material bindings required")
        for key in ("selection", "prompts", "schedule", "protocol_version"):
            _require(isinstance(reliability.get(key), str) and reliability[key],
                     "Missing reliability binding: " + key)
        identity(data)
        return cls(path, root, data, digest_bytes(raw))

    def packet(self):
        binding = self.data["reliability"]
        result = {"protocol_version": binding["protocol_version"], "files_sha256": {}}
        for key in ("selection", "prompts", "schedule"):
            path = safe_file(self.root, binding[key])
            raw = path.read_bytes()
            result[key] = json.loads(raw)
            result["files_sha256"][binding[key]] = digest_bytes(raw)
            _require(result[key].get("protocol_version") == binding["protocol_version"],
                     "Reliability protocol versions differ")
        return result


def _category_matches(component, task_kind, contract_kind):
    if component == "chapters":
        return contract_kind == "chapter_formalization" and task_kind == "generate"
    if contract_kind != "progressive":
        return False
    return (component == "proofs" and task_kind == "written"
            or component == "lean-audit" and task_kind == "audit"
            or component == "lean-construction" and task_kind in {"generate", "repair"})


def _schedule(packet, case_ids, suite_sha256):
    selection = packet["selection"].get("cases", [])
    selected_ids = [row.get("case_id") for row in selection]
    _require(selected_ids and len(selected_ids) == len(set(selected_ids))
             and set(selected_ids) <= set(case_ids), "Invalid reliability selection")
    _require(packet["selection"].get("source_suite_sha256") == suite_sha256,
             "Reliability selection binds a different source suite")
    _require(all(x.get("expected_truth") in {"true", "false"} for x in selection),
             "Every selected focus requires an explicit true or false label")
    truth_counts = dict(Counter(x["expected_truth"] for x in selection))
    _require(packet["selection"].get("case_count", len(selection)) == len(selection)
             and packet["selection"].get("truth_counts", truth_counts) == truth_counts,
             "Reliability selection counts differ from its actual cases")
    rows = copy.deepcopy(packet["schedule"].get("slots"))
    _require(isinstance(rows, list) and all(isinstance(x, dict) for x in rows),
             "A complete frozen reliability schedule is required")
    indexed = {x.get("slot_id"): x for x in rows}
    expected = {f"{cid}:{attempt}" for cid in case_ids for attempt in ATTEMPTS}
    expected |= {f"{cid}:{arm}:{rnd}" for cid in selected_ids
                 for arm in ARMS for rnd in (1, 2)}
    _require(len(indexed) == len(rows) and set(indexed) == expected,
             "Schedule must retain all independent and followup slots")
    message_rows = packet["prompts"].get("messages", [])
    messages = {x.get("message_id"): x for x in message_rows}
    _require(len(messages) == len(message_rows)
             and set(messages) == {f"{cid}:{arm}:{rnd}" for cid in selected_ids
                                  for arm in ARMS for rnd in (1, 2)},
             "Frozen followup messages do not match the schedule")
    earlier = set()
    for row in rows:
        sid, cid = row["slot_id"], row.get("case_id")
        _require(row.get("status", "planned") == "planned"
                 and row.get("response_sha256") is None and row.get("grade") is None,
                 "A frozen schedule cannot contain candidate results")
        if row.get("kind") == "independent":
            _require(cid in case_ids and row.get("attempt_label") in ATTEMPTS
                     and sid == f"{cid}:{row['attempt_label']}"
                     and row.get("context") == "fresh" and row.get("parent_slot") is None,
                     "Independent slots must retain fresh, unrelated contexts")
        else:
            arm, rnd = row.get("arm"), row.get("round")
            parent = f"{cid}:A1" if rnd == 1 else f"{cid}:{arm}:1"
            _require(row.get("kind") == "followup" and cid in selected_ids
                     and arm in ARMS and rnd in (1, 2)
                     and sid == f"{cid}:{arm}:{rnd}"
                     and row.get("context") == "branch-history-only"
                     and row.get("parent_slot") == parent and parent in earlier
                     and row.get("message_id") == sid,
                     "Followup histories must stay in their fixed A1 branch")
            message = messages[sid]
            _require(message.get("role") == "user"
                     and isinstance(message.get("content"), str)
                     and digest_bytes(message["content"].encode()) == message.get("content_sha256"),
                     "Followup content identity changed")
        earlier.add(sid)
    return rows


def _focus_tags(profile):
    path = profile.root / "cases/taxonomy.json"
    if not path.is_file():
        return {}, {}
    data = read_json(path)
    result = {}
    for row in data.get("paper_assignments", []):
        cid = row.get("case_id")
        tags = [x.get("focus_id") for x in row.get("focus", [])]
        if isinstance(tags, list) and all(isinstance(x, str) for x in tags):
            result[cid] = tags
    return result, {"cases/taxonomy.json": digest_bytes(path.read_bytes())}


def _target_slot_ids(slots, components, targets):
    _require(targets and len(targets) == len(set(targets))
             and set(targets) <= set(TARGETS), "Unknown or repeated benchmark target")
    want = set()
    for slot in slots:
        independent = slot["kind"] == "independent"
        if ("all" in targets or independent and (
                "core" in targets or "repeat" in targets
                or components[slot["case_id"]] in targets)
                or not independent and (
                    slot["arm"] == "neutral" and "neutral" in targets
                    or slot["arm"] in {"affirm", "deny"} and "stance" in targets)):
            want.add(slot["slot_id"])
    indexed = {slot["slot_id"]: slot for slot in slots}
    for sid in list(want):
        parent = indexed[sid].get("parent_slot")
        while parent:
            want.add(parent)
            parent = indexed[parent].get("parent_slot")
    return want


def select_slots(plan, targets=None):
    """Narrow one frozen plan for separately executed, mergeable subbenchmarks."""
    validate_plan(plan)
    selected = {x["slot_id"] for x in plan["slots"] if x["selected"]}
    if targets is not None:
        components = {x["case_id"]: x["component"] for x in plan["case_index"]}
        want = _target_slot_ids(plan["slots"], components, list(targets))
        _require(want <= selected, "Execution targets exceed the frozen plan projection")
        selected = want
    return [copy.deepcopy(x) for x in plan["slots"] if x["slot_id"] in selected]


def build_plan(profile, suite, targets=None, *, runtime=None):
    """Freeze the full denominator; targets choose only an execution projection."""
    targets = list(["all"] if targets is None else targets)
    _require(targets and len(targets) == len(set(targets)) and set(targets) <= set(TARGETS),
             "Unknown or repeated benchmark target")
    _require(profile.data["suite"]["sha256"] == suite.sha256,
             "Suite changed before plan freezing")
    profile_raw = profile.path.read_bytes()
    _require(digest_bytes(profile_raw) == profile.sha256 and json.loads(profile_raw) == profile.data,
             "Profile changed after loading; reload it before plan freezing")
    _runtime_contract(runtime)
    packet = profile.packet()
    slots = _schedule(packet, suite.cases, suite.sha256)
    if profile.data["id"] == "math-gauge-composite" and profile.data["version"] == "0.1.0":
        _require(len(packet["selection"]["cases"]) == 8
                 and Counter(x["expected_truth"] for x in packet["selection"]["cases"])
                 == {"true": 4, "false": 4}, "The canonical profile retains eight four-true/four-false focuses")
    components = {cid: row["id"] for row in profile.data["components"]
                  for cid in row["case_ids"]}
    tags, tag_identity = _focus_tags(profile)
    cases = []
    for cid, case in suite.cases.items():
        contract = validate_group_contract(read_json(safe_file(suite.root, case["group_contract"])))
        request = suite.request(case)
        cases.append({
            "case_id": cid, "version": case["version"], "track": case["track"],
            "task_kind": case.get("task_kind", "exploration"),
            "contract_kind": contract["kind"],
            "family_id": case.get("family_id", cid), "component": components[cid],
            "case_approved": case["status"] == "approved" and case["review"]["human"] == "approved",
            "request_sha256": digest_bytes(json.dumps(request, ensure_ascii=False, sort_keys=True).encode()),
            "candidate_message_sha256": digest_bytes(candidate_message(request).encode()),
            "group_contract": case["group_contract"],
            "group_contract_sha256": digest_bytes(safe_file(suite.root, case["group_contract"]).read_bytes()),
            "stages": [{"stage_id": s["id"], "points": s["points"],
                        "lean_required": s["lean_required"]} for s in contract["stages"]],
            "total_weight": sum(s["points"] for s in contract["stages"]),
            "focus_tags": tags.get(cid, []),
        })
    want = _target_slot_ids(slots, components, targets)
    for slot in slots:
        slot["selected"] = slot["slot_id"] in want
    plan = {
        "schema": "math-gauge.benchmark-plan/v1", "plan_id": uuid.uuid4().hex,
        "created_at": now(), "operator_only": True,
        "profile": {"id": profile.data["id"], "version": profile.data["version"],
                    "sha256": profile.sha256, "data_sha256": identity(profile.data),
                    "data": copy.deepcopy(profile.data)},
        "suite": copy.deepcopy(profile.data["suite"]), "targets": targets,
        "runner_sha256": runner_fingerprint(),
        "runtime": copy.deepcopy(runtime), "runtime_frozen": runtime is not None,
        "runtime_sha256": identity(runtime),
        "model_label": runtime.get("model_label") if runtime is not None else None,
        "context_policy": {"independent": "fresh", "followup": "branch-history-only",
                           "external_correctness_feedback": False, "tools_allowed": []},
        "case_index": cases, "slots": slots,
        "reliability": {k: v for k, v in packet.items() if k != "schedule"},
        "source_files_sha256": tag_identity,
        "planned": {"papers": len(cases), "independent_slots": 3 * len(cases),
                    "neutral_slots": 2 * len(packet["selection"]["cases"]),
                    "stance_slots": 4 * len(packet["selection"]["cases"]),
                    "all_slots": len(slots), "selected_slots": len(want)},
        "candidate_calls": 0,
    }
    plan["plan_sha256"] = identity(plan)
    return validate_plan(plan)


def validate_plan(plan):
    _require(isinstance(plan, dict) and plan.get("schema") == "math-gauge.benchmark-plan/v1",
             "Unsupported benchmark plan")
    unhashed = {k: v for k, v in plan.items() if k != "plan_sha256"}
    _require(plan.get("plan_sha256") == identity(unhashed), "Frozen benchmark plan changed")
    _require(plan.get("runtime_sha256") == identity(plan.get("runtime")),
             "Frozen runtime identity changed")
    runtime = plan.get("runtime")
    _runtime_contract(runtime)
    _require(type(plan.get("runtime_frozen")) is bool
             and plan["runtime_frozen"] == (runtime is not None)
             and plan.get("model_label") == (runtime.get("model_label") if isinstance(runtime, dict) else None),
             "Frozen runtime status changed")
    profile = plan.get("profile", {})
    data = profile.get("data", {})
    _require(profile.get("data_sha256") == identity(data)
             and data.get("schema") == "math-gauge.benchmark-profile/v1"
             and data.get("operator_only") is True and data.get("path_base") == "repository"
             and profile.get("id") == data.get("id")
             and profile.get("version") == data.get("version")
             and plan.get("suite") == data.get("suite"), "Frozen profile identity changed")
    components = data.get("components", [])
    _require([x.get("id") for x in components] == list(COMPONENTS)
             and data.get("attempts") == list(ATTEMPTS), "Frozen profile structure changed")
    _weights({x["id"]: x.get("weight") for x in components}, COMPONENTS)
    _weights(data.get("overall_weights"), ("core", "repeat", "neutral", "stance"))
    cases = plan.get("case_index", [])
    case_ids = [x.get("case_id") for x in cases]
    members = [cid for component in components for cid in component.get("case_ids", [])]
    _require(case_ids and len(case_ids) == len(set(case_ids))
             and len(members) == len(set(members)) and set(case_ids) == set(members),
             "Frozen core partition changed")
    membership = {cid: component["id"] for component in components
                  for cid in component["case_ids"]}
    for case in cases:
        stages = case.get("stages", [])
        _require(case.get("component") == membership[case["case_id"]]
                 and _category_matches(case["component"], case.get("task_kind"), case.get("contract_kind"))
                 and stages and len({s.get("stage_id") for s in stages}) == len(stages)
                 and all(type(s.get("points")) is int and s["points"] > 0
                         and type(s.get("lean_required")) is bool for s in stages)
                 and case.get("total_weight") == sum(s["points"] for s in stages),
                 "Frozen paper weights changed")
    slots = plan.get("slots", [])
    packet = dict(plan.get("reliability", {}), schedule={"slots": slots})
    _schedule(packet, case_ids, plan["suite"]["sha256"])
    if data["id"] == "math-gauge-composite" and data["version"] == "0.1.0":
        _require(len(packet["selection"]["cases"]) == 8
                 and Counter(x["expected_truth"] for x in packet["selection"]["cases"])
                 == {"true": 4, "false": 4}, "Canonical focus balance changed")
    want = _target_slot_ids(slots, membership, plan.get("targets", []))
    _require(len({x.get("slot_id") for x in slots}) == len(slots)
             and all(type(x.get("selected")) is bool
                     and x["selected"] == (x["slot_id"] in want) for x in slots),
             "Frozen execution projection changed")
    selected_cases = len(packet["selection"]["cases"])
    _require(plan.get("planned") == {
        "papers": len(cases), "independent_slots": 3 * len(cases),
        "neutral_slots": 2 * selected_cases, "stance_slots": 4 * selected_cases,
        "all_slots": len(slots), "selected_slots": len(want)},
        "Frozen plan denominators changed")
    _require(plan.get("candidate_calls") == 0
             and plan.get("context_policy") == {
                 "independent": "fresh", "followup": "branch-history-only",
                 "external_correctness_feedback": False, "tools_allowed": []},
             "A frozen plan cannot contain execution results or changed context policy")
    return plan


def read_plan(path):
    return validate_plan(read_json(path))


def write_plan(path, plan):
    path = Path(path)
    _require(not path.exists(), "Plan output already exists")
    validate_plan(plan)
    write_json(path, plan)
    return plan
