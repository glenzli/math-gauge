"""Evaluator-only profiles and immutable plans over the shared case runner."""

import copy
import json
import uuid
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

from .catalog import (assessment_units, candidate_message, digest_bytes, read_json, relative_name, safe_file,
                      validate_group_contract, write_json)
from .execution import now, runner_fingerprint
from .execution_policy import execution_context, validate_context_policy

COMPONENTS = ("proofs", "lean-audit", "lean-construction", "chapters")
EXTENDED_COMPONENTS = COMPONENTS + ("exploration",)
TARGETS = EXTENDED_COMPONENTS + ("repeat", "neutral", "stance", "core", "all")
ATTEMPTS = ("A1", "A2", "A3")
ARMS = ("neutral", "affirm", "deny")
PROFILE_SCHEMAS = {"math-gauge.benchmark-profile/v1", "math-gauge.benchmark-profile/v2",
                   "math-gauge.benchmark-profile/v3"}
COMPACT_PANEL = ("MG-GR002", "MG-GR014", "MG-GF101", "MG-GF107", "MG-GF104", "MG-GF106")


def identity(value):
    """Stable JSON identity; reject non-JSON numbers before freezing a plan."""
    return digest_bytes(json.dumps(value, ensure_ascii=False, sort_keys=True,
                                   separators=(",", ":"), allow_nan=False).encode())


def _require(condition, message):
    if not condition:
        raise ValueError(message)


def _weights(value, names, *, allow_zero=False):
    _require(isinstance(value, dict) and set(value) == set(names),
             "Weights must name every frozen component exactly once")
    _require(all(type(x) is int and (x >= 0 if allow_zero else x > 0) for x in value.values())
             and sum(value.values()) == 100,
             "Weights must be positive integral percentages summing to 100")


def component_ids(data):
    rows = data.get("components")
    _require(isinstance(rows, list) and rows and all(isinstance(x, dict) for x in rows),
             "Profile requires explicit ordered components")
    ids = [row.get("id") for row in rows]
    if data.get("schema") == "math-gauge.benchmark-profile/v3":
        _require(ids == [cid for cid in EXTENDED_COMPONENTS if cid in ids],
                 "Invalid or repeated v3 core components")
    else:
        _require(ids == list(COMPONENTS), "Profile must retain the four ordered core components")
    return tuple(ids)


def profile_targets(data):
    return component_ids(data) + ("repeat", "neutral", "stance", "core", "all")


def _runtime_contract(runtime):
    if runtime is not None:
        _require(isinstance(runtime, dict)
                 and isinstance(runtime.get("model_label"), str) and runtime["model_label"]
                 and isinstance(runtime.get("budget"), dict) and runtime["budget"]
                 and isinstance(runtime.get("adapter_identity"), (str, dict))
                 and runtime["adapter_identity"],
                 "Frozen runtime requires model_label, budget and adapter_identity")
    identity(runtime)


def independent_attempts(data, case_ids):
    """Read a frozen arrangement; historical profiles retain all three attempts."""
    ids = list(case_ids)
    if data.get("schema") == "math-gauge.benchmark-profile/v1":
        _require(data.get("attempts") == list(ATTEMPTS),
                 "Three fixed independent attempts are required")
        return {cid: list(ATTEMPTS) for cid in ids}
    _require(data.get("schema") in {"math-gauge.benchmark-profile/v2", "math-gauge.benchmark-profile/v3"},
             "Unsupported benchmark attempt arrangement")
    attempts = data.get("attempt_schedule")
    _require(isinstance(attempts, dict) and set(attempts) == set(ids)
             and all(value in (["A1"], list(ATTEMPTS)) for value in attempts.values()),
             "Every paper needs an explicit A1 or A1/A2/A3 arrangement")
    return copy.deepcopy(attempts)


def scoring_policy(data, case_ids):
    """Bind metric membership to the profile, never to observed successful answers."""
    ids = list(case_ids)
    attempts = independent_attempts(data, ids)
    if data["schema"] == "math-gauge.benchmark-profile/v1":
        return {"core_attempt_labels": list(ATTEMPTS), "repeat_case_ids": ids,
                "repeat_attempt_labels": list(ATTEMPTS)}
    policy = data.get("score_policy")
    _require(isinstance(policy, dict) and set(policy) == {
        "core_attempt_labels", "repeat_case_ids", "repeat_attempt_labels"}
        and policy["core_attempt_labels"] == ["A1"]
        and policy["repeat_attempt_labels"] == list(ATTEMPTS),
        "Compact scoring requires A1 core and three-attempt repetition")
    repeated = policy["repeat_case_ids"]
    _require(isinstance(repeated, list) and (repeated or data["schema"] == "math-gauge.benchmark-profile/v3")
             and all(isinstance(cid, str) for cid in repeated)
             and len(repeated) == len(set(repeated))
             and set(repeated) == {cid for cid in ids if attempts[cid] == list(ATTEMPTS)},
             "Repeat membership must match the frozen three-attempt papers")
    return copy.deepcopy(policy)


def _compact_panel(data, packet, case_ids, policy):
    if data["id"] != "math-gauge-composite" or data["version"] != "0.2.0":
        return
    selected = packet["selection"]["cases"]
    _require(data["schema"] == "math-gauge.benchmark-profile/v2" and len(case_ids) == 32
             and [x["case_id"] for x in selected] == list(COMPACT_PANEL)
             and policy["repeat_case_ids"] == list(COMPACT_PANEL)
             and Counter(x["expected_truth"] for x in selected) == {"true": 3, "false": 3}
             and Counter(x["selection_category"] for x in selected)
             == {"written": 2, "audit": 2, "repair": 1, "generate": 1},
             "The compact profile retains 32 papers and its balanced six-paper panel")


def case_approval_sources(suite):
    """Read approval status from its actual manifest, not an in-memory flag."""
    result = {}
    for cid, loaded in suite.cases.items():
        name = suite.case_manifest(cid)
        raw = suite.case_file(cid, name).read_bytes()
        value = json.loads(raw)
        _require(value["id"] == cid, "Case approval source identity changed")
        source = {"manifest": name, "manifest_sha256": digest_bytes(raw),
                  "status": value["status"], "human_review": value["review"]["human"]}
        _require(source["status"] == loaded["status"]
                 and source["human_review"] == loaded["review"]["human"]
                 and value["version"] == loaded["version"],
                 "Case approval source changed after suite loading")
        result[cid] = source
    _require(set(result) == set(suite.cases), "Case approval source inventory changed")
    return result


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
        default_root = (path.parent.parent if data.get("schema") == "math-gauge.benchmark-profile/v3"
                        and path.parent.name == "protocol" else suite.root.parent)
        root = Path(repository_root or default_root).resolve()
        _require(isinstance(data, dict) and data.get("schema") in PROFILE_SCHEMAS
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
        components = component_ids(data)
        _weights({x["id"]: x.get("weight") for x in rows}, components)
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
                contract = read_json(suite.case_file(case, case["group_contract"]))
                _require(_category_matches(row["id"], case.get("task_kind"), contract.get("kind")),
                         "Core category differs from the paper's actual task and contract")
        _require(len(members) == len(set(members))
                 and set(members) == set(suite.cases),
                 "Core components must partition the complete suite without overlap")
        scoring_policy(data, suite.cases)
        _weights(data.get("overall_weights"), ("core", "repeat", "neutral", "stance"),
                 allow_zero=data["schema"] == "math-gauge.benchmark-profile/v3")
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
    if component == "exploration":
        return contract_kind == "research_exploration" and task_kind in {"written", "exploration"}
    if component == "chapters":
        return contract_kind == "chapter_formalization" and task_kind == "generate"
    if contract_kind != "progressive":
        return False
    return (component == "proofs" and task_kind == "written"
            or component == "lean-audit" and task_kind == "audit"
            or component == "lean-construction" and task_kind in {"generate", "repair"})


def _schedule(packet, case_ids, suite_sha256, attempts=None):
    selection = packet["selection"].get("cases", [])
    selected_ids = [row.get("case_id") for row in selection]
    _require(len(selected_ids) == len(set(selected_ids))
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
    attempts = attempts or {cid: ATTEMPTS for cid in case_ids}
    expected = {f"{cid}:{attempt}" for cid in case_ids for attempt in attempts[cid]}
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


def _target_slot_ids(slots, components, targets, policy=None):
    _require(targets and len(targets) == len(set(targets))
             and set(targets) <= set(TARGETS), "Unknown or repeated benchmark target")
    want = set()
    policy = policy or {"core_attempt_labels": ATTEMPTS,
                        "repeat_case_ids": list(components), "repeat_attempt_labels": ATTEMPTS}
    for slot in slots:
        independent = slot["kind"] == "independent"
        if ("all" in targets or independent and (
                slot["attempt_label"] in policy["core_attempt_labels"] and (
                    "core" in targets or components[slot["case_id"]] in targets)
                or "repeat" in targets and slot["case_id"] in policy["repeat_case_ids"]
                    and slot["attempt_label"] in policy["repeat_attempt_labels"])
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
        _require(set(targets) <= set(profile_targets(plan["profile"]["data"])),
                 "Unknown benchmark target for the frozen profile")
        components = {x["case_id"]: x["component"] for x in plan["case_index"]}
        want = _target_slot_ids(plan["slots"], components, list(targets),
                                scoring_policy(plan["profile"]["data"], components))
        _require(want <= selected, "Execution targets exceed the frozen plan projection")
        selected = want
    return [copy.deepcopy(x) for x in plan["slots"] if x["slot_id"] in selected]


def build_plan(profile, suite, targets=None, *, runtime=None):
    """Freeze the full denominator; targets choose only an execution projection."""
    targets = list(["all"] if targets is None else targets)
    _require(targets and len(targets) == len(set(targets)) and set(targets) <= set(profile_targets(profile.data)),
             "Unknown or repeated benchmark target")
    _require(profile.data["suite"]["sha256"] == suite.sha256,
             "Suite changed before plan freezing")
    profile_raw = profile.path.read_bytes()
    _require(digest_bytes(profile_raw) == profile.sha256 and json.loads(profile_raw) == profile.data,
             "Profile changed after loading; reload it before plan freezing")
    _runtime_contract(runtime)
    packet = profile.packet()
    attempts = independent_attempts(profile.data, suite.cases)
    policy = scoring_policy(profile.data, suite.cases)
    slots = _schedule(packet, suite.cases, suite.sha256, attempts)
    if profile.data["id"] == "math-gauge-composite" and profile.data["version"] == "0.1.0":
        _require(len(packet["selection"]["cases"]) == 8
                 and Counter(x["expected_truth"] for x in packet["selection"]["cases"])
                 == {"true": 4, "false": 4}, "The canonical profile retains eight four-true/four-false focuses")
    _compact_panel(profile.data, packet, suite.cases, policy)
    components = {cid: row["id"] for row in profile.data["components"]
                  for cid in row["case_ids"]}
    tags, tag_identity = _focus_tags(profile)
    approvals = case_approval_sources(suite)
    cases = []
    for cid, case in suite.cases.items():
        contract = validate_group_contract(read_json(suite.case_file(case, case["group_contract"])))
        request = suite.request(case)
        cases.append({
            "case_id": cid, "version": case["version"], "track": case["track"],
            "task_kind": case.get("task_kind", "exploration"),
            "contract_kind": contract["kind"],
            "family_id": case.get("family_id", cid), "component": components[cid],
            "case_approved": case["status"] == "approved" and case["review"]["human"] == "approved",
            "case_approval_source": approvals[cid],
            "request_sha256": digest_bytes(json.dumps(request, ensure_ascii=False, sort_keys=True).encode()),
            "candidate_message_sha256": digest_bytes(candidate_message(request).encode()),
            "group_contract": case["group_contract"],
            "group_contract_sha256": digest_bytes(suite.case_file(case, case["group_contract"]).read_bytes()),
            "stages": [{"stage_id": s["id"], "points": s["points"],
                        "lean_required": s["lean_required"]} for s in assessment_units(contract)],
            "total_weight": sum(s["points"] for s in assessment_units(contract)),
            "focus_tags": tags.get(cid, []),
        })
        if contract["kind"] == "research_exploration":
            cases[-1]["assessment_unit"] = "review_dimension"
        if suite.members:
            cases[-1]["source_suite"] = suite.source_binding(case)
        if suite.source_suite(case).metadata["visibility"] == "private":
            cases[-1]["source_visibility"] = "private"
    want = _target_slot_ids(slots, components, targets, policy)
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
        "context_policy": execution_context(runtime),
        "case_index": cases, "slots": slots,
        "reliability": {k: v for k, v in packet.items() if k != "schedule"},
        "source_files_sha256": tag_identity,
        "planned": {"papers": len(cases), "independent_slots": sum(map(len, attempts.values())),
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
             and data.get("schema") in PROFILE_SCHEMAS
             and data.get("operator_only") is True and data.get("path_base") == "repository"
             and profile.get("id") == data.get("id")
             and profile.get("version") == data.get("version")
             and plan.get("suite") == data.get("suite"), "Frozen profile identity changed")
    components = data.get("components", [])
    ids = component_ids(data)
    _weights({x["id"]: x.get("weight") for x in components}, ids)
    _weights(data.get("overall_weights"), ("core", "repeat", "neutral", "stance"),
             allow_zero=data["schema"] == "math-gauge.benchmark-profile/v3")
    cases = plan.get("case_index", [])
    case_ids = [x.get("case_id") for x in cases]
    members = [cid for component in components for cid in component.get("case_ids", [])]
    _require(case_ids and len(case_ids) == len(set(case_ids))
             and len(members) == len(set(members)) and set(case_ids) == set(members),
             "Frozen core partition changed")
    membership = {cid: component["id"] for component in components
                  for cid in component["case_ids"]}
    attempts = independent_attempts(data, case_ids)
    policy = scoring_policy(data, case_ids)
    for case in cases:
        _require(type(case.get("case_approved")) is bool, "Frozen case approval must be explicit")
        approval = case.get("case_approval_source")
        if approval is not None:
            _require(isinstance(approval, dict) and set(approval) == {
                "manifest", "manifest_sha256", "status", "human_review"},
                "Frozen case approval source is incomplete")
            relative_name(approval["manifest"])
            digest = approval["manifest_sha256"]
            _require(isinstance(digest, str) and len(digest) == 64
                     and all(c in "0123456789abcdef" for c in digest)
                     and approval["status"] in {"draft", "approved", "retired"}
                     and approval["human_review"] in {"pending", "approved", "rejected"}
                     and case["case_approved"] == (approval["status"] == "approved"
                                                   and approval["human_review"] == "approved"),
                     "Frozen case approval contradicts its original source")
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
    _schedule(packet, case_ids, plan["suite"]["sha256"], attempts)
    if data["id"] == "math-gauge-composite" and data["version"] == "0.1.0":
        _require(len(packet["selection"]["cases"]) == 8
                 and Counter(x["expected_truth"] for x in packet["selection"]["cases"])
                 == {"true": 4, "false": 4}, "Canonical focus balance changed")
    _compact_panel(data, packet, case_ids, policy)
    want = _target_slot_ids(slots, membership, plan.get("targets", []), policy)
    _require(len({x.get("slot_id") for x in slots}) == len(slots)
             and all(type(x.get("selected")) is bool
                     and x["selected"] == (x["slot_id"] in want) for x in slots),
             "Frozen execution projection changed")
    selected_cases = len(packet["selection"]["cases"])
    _require(plan.get("planned") == {
        "papers": len(cases), "independent_slots": sum(map(len, attempts.values())),
        "neutral_slots": 2 * selected_cases, "stance_slots": 4 * selected_cases,
        "all_slots": len(slots), "selected_slots": len(want)},
        "Frozen plan denominators changed")
    validate_context_policy(plan.get("context_policy"))
    _require(plan.get("candidate_calls") == 0
             and plan.get("context_policy") == execution_context(runtime),
             "A frozen plan cannot contain execution results or changed context policy")
    from .eligibility import validate_execution_requirements
    validate_execution_requirements(plan)
    return plan


def read_plan(path):
    return validate_plan(read_json(path))


def write_plan(path, plan):
    path = Path(path)
    _require(not path.exists(), "Plan output already exists")
    validate_plan(plan)
    write_json(path, plan)
    return plan
