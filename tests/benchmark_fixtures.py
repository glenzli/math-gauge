"""Legacy transport fixtures over retained task bytes; never model evidence."""
import atexit
import copy
import functools
from pathlib import Path
import shutil
import tempfile

from math_gauge.benchmarks import BenchmarkProfile, build_plan
from math_gauge.catalog import Suite, read_json, write_json

ROOT = Path(__file__).resolve().parents[1]


def fixture_sources(registry, case_sources):
    pending, selected = list(case_sources), set()
    while pending:
        name = pending.pop()
        if name in selected:
            continue
        selected.add(name)
        source = registry[name]
        pending.extend(source.get("sources", []))
        if isinstance(source.get("parent"), str):
            pending.append(source["parent"])
    return {name: row for name, row in registry.items() if name in selected}


@functools.lru_cache(maxsize=2)
def _fixture_root(chain):
    temporary = tempfile.TemporaryDirectory(prefix="math-gauge-current-contract-")
    atexit.register(temporary.cleanup)
    root = Path(temporary.name).resolve()
    suite = Suite.load(ROOT / "cases")
    names = {"suite.json", "sources.json", "taxonomy.json"}
    for cid, case in suite.cases.items():
        names.add(suite.case_manifest(cid))
        for key in ["task", "reference", "rubric", "group_contract"]:
            names.add(str(suite.case_file(case, case[key]).relative_to(suite.root)))
        for name in case.get("evaluator_files", []) + case.get("lean_checks", []):
            names.add(str(suite.case_file(case, name).relative_to(suite.root)))
        for item in case["solver_files"]:
            names.add(str(suite.case_file(case, item["source"]).relative_to(suite.root)))
    for name in names:
        dest = root / "cases" / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(suite.root / name, dest)
    registry = read_json(root / "cases/sources.json")
    write_json(root / "cases/sources.json", fixture_sources(registry, {n for c in suite.cases.values() for n in c["sources"]}))
    suite = Suite.load(root / "cases")
    # Frozen v5 exercises legacy A2/branch transports independently of the
    # current A1-only profile. Rebinding is synthetic, never a new exam.
    source = read_json(ROOT / "results/v0.6.0/gemini-3.8-flash-high/20261105/scoring-inputs.json")["plan"]
    packet = root / "protocol/reliability"
    packet.mkdir(parents=True)
    write_json(packet / "selection.json", source["reliability"]["selection"])
    write_json(packet / "prompts.json", source["reliability"]["prompts"])
    slots = [{k: v for k, v in row.items() if k != "selected"} for row in source["slots"]]
    write_json(packet / "schedule.json", {"protocol_version": "0.4.0", "slots": slots})
    data = copy.deepcopy(source["profile"]["data"])
    # Freeze the legacy arithmetic seam explicitly; source archives carry
    # several historical profiles, while these tests expect this one contract.
    for component, weight in zip(data["components"], [40, 20, 30, 10]):
        component["weight"] = weight
    data["overall_weights"] = {"core": 70, "repeat": 5, "neutral": 15, "stance": 10}
    data["id"] = "synthetic-current-contract"
    # Low-level transport/arithmetic fixtures deliberately have no real native
    # budget, fresh-supplement or separate study admission. They are not exams.
    for key in ["case_execution_policy", "supplement_policy", "alignment_policy", "alignment_policy_binding", "execution_groups"]:
        data.pop(key, None)
    data["suite"]["sha256"] = Suite.load(root / "cases").sha256
    packet = root / "protocol/reliability"
    selection = read_json(packet / "selection.json")
    selection["source_suite_sha256"] = suite.sha256
    if chain:
        # Exercise multi-hop transports with current task bytes. This is a
        # synthetic software fixture, not a retained historical benchmark.
        data["reliability"]["protocol_version"] = "0.2.0"
        data.pop("reliability_population", None)
        data.pop("reliability_panel", None)
        data["score_policy"]["repeat_attempt_labels"] = ["A1", "A2", "A3"]
        for cid in ["LCH01", "LCH02", "HCH02", "MG-GR005"]:
            case = suite.cases[cid]
            contract = read_json(suite.case_file(case, case["group_contract"]))
            stage = contract["stages"][0]
            selection["cases"].append({"case_id": cid, "case_version": case["version"],
                "family_id": case["family_id"], "task_kind": case["task_kind"],
                "selection_category": "generate" if case["task_kind"] == "generate" else "audit",
                "stage_id": stage["id"], "scope": "stage", "source_turn_scope": "stage",
                "expected_truth": "true", "target_claim": "Synthetic contract focus, not a mathematical judgment.",
                "whole_group_required": True, "human_approved": False})
        selected = [row["case_id"] for row in selection["cases"]]
        data["attempt_schedule"] = {cid: ["A1", "A2", "A3"] if cid in selected else ["A1"] for cid in suite.cases}
        data["score_policy"]["repeat_case_ids"] = selected
        selection["case_count"] = len(selection["cases"])
        from collections import Counter
        selection["truth_counts"] = dict(Counter(r["expected_truth"] for r in selection["cases"]))
        selection["protocol_version"] = "0.2.0"
        messages, slots = [], []
        for cid in suite.cases:
            for label in data["attempt_schedule"][cid]:
                slots.append({"slot_id": cid + ":" + label, "case_id": cid, "kind": "independent",
                    "attempt_label": label, "context": "fresh", "parent_slot": None, "message_id": None,
                    "status": "planned", "response_sha256": None, "grade": None})
        from math_gauge.catalog import digest_bytes
        for row in selection["cases"]:
            for arm in ["neutral", "affirm", "deny"]:
                for rnd in [1, 2]:
                    sid = f"{row['case_id']}:{arm}:{rnd}"
                    content = f"Synthetic transport instruction {arm}, round {rnd}. Return KEEP or FULL.\n本轮不能调用工具或查询外部资料。\n"
                    messages.append({"message_id": sid, "case_id": row["case_id"], "arm": arm, "round": rnd,
                        "role": "user", "content": content, "content_sha256": digest_bytes(content.encode())})
                    slots.append({"slot_id": sid, "case_id": row["case_id"], "kind": "followup",
                        "arm": arm, "round": rnd, "context": "branch-history-only", "parent_slot":
                        row["case_id"] + (":A1" if rnd == 1 else f":{arm}:1"), "message_id": sid,
                        "status": "planned", "response_sha256": None, "grade": None})
        for ordinal, slot in enumerate(slots, 1):
            slot["ordinal_per_model"] = ordinal
        write_json(packet / "prompts.json", {"protocol_version": "0.2.0", "messages": messages})
        write_json(packet / "schedule.json", {"protocol_version": "0.2.0", "slots": slots})
    write_json(packet / "selection.json", selection)
    write_json(root / "protocol/benchmark-profile.json", data)
    return root



def fixture_root():
    return _fixture_root(True)


def fixture_suite():
    return Suite.load(fixture_root() / "cases")


def fixture_profile(suite=None):
    return BenchmarkProfile.load(fixture_root() / "protocol/benchmark-profile.json", suite or fixture_suite())


def source_root():
    return _fixture_root(False)


def source_suite():
    return Suite.load(source_root() / "cases")


def source_profile(suite=None):
    return BenchmarkProfile.load(source_root() / "protocol/benchmark-profile.json", suite or source_suite())


def legacy_budget_profile():
    """Legacy panel arithmetic with current budget fixtures; no real execution."""
    data = copy.deepcopy(source_profile().data)
    retained = read_json(ROOT / "results/v0.6.0/gemini-3.8-flash-high/20261105/scoring-inputs.json")["plan"]["profile"]["data"]
    data["supplement_policy"] = retained["supplement_policy"]
    for component, weight in zip(data["components"], [40, 20, 30, 10]):
        component["weight"] = weight
    data["overall_weights"] = {"core": 70, "repeat": 5, "neutral": 15, "stance": 10}
    current = read_json(ROOT / "protocol/benchmark-profile.json")
    data["case_execution_policy"] = current["case_execution_policy"]
    data["execution_groups"] = current["execution_groups"] | {
        "written-new-panel": [f"{cid}:{label}" for cid in ("MG-GP001", "MG-GP002")
            for label in ("A1", "A2", "neutral:1", "affirm:1", "deny:1")]}
    for name in ("lean-tool-budget-policy-v0.1.0.json", "lean-tool-budget-policy-v0.2.0.json", "lean-tool-budget-policy.json"):
        source = ROOT / "protocol" / name
        if source.exists():
            shutil.copy2(source, source_root() / "protocol" / name)
    path = source_root() / "protocol/legacy-budget-profile.json"
    write_json(path, data)
    return BenchmarkProfile.load(path, source_suite())


def fixture_release_plan(version="0.6.0"):
    suite = source_suite()
    return build_plan(source_profile(suite), suite), suite


def arithmetic_source_plan(runtime):
    """A synthetic weighting seam for the generic source substitution API."""
    root = source_root()
    suite = source_suite()
    data = copy.deepcopy(source_profile(suite).data)
    for row, weight in zip(data["components"], [22.5, 22.5, 45, 10]):
        row["weight"] = weight
    data["overall_weights"] = {"core": 75, "repeat": 5, "neutral": 10, "stance": 10}
    path = root / "protocol/synthetic-arithmetic.json"
    write_json(path, data)
    return build_plan(BenchmarkProfile.load(path, suite), suite, runtime=runtime)
