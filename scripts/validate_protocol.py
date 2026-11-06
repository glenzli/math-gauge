#!/usr/bin/env python3
"""Check the current reliability packet without model or Lean execution."""
from __future__ import annotations

import argparse
import collections
import copy
import hashlib
import json
import re
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PACKET = "protocol/reliability"
RUNNER_FILES = (
    "math_gauge/catalog.py", "math_gauge/execution.py", "math_gauge/execution_policy.py", "math_gauge/review.py",
    "math_gauge/benchmarks.py", "math_gauge/scoring.py", "math_gauge/reliability.py",
    "math_gauge/reliability_review.py",
    "math_gauge/eligibility.py",
    "math_gauge/harness.py", "math_gauge/harness_answers.py", "math_gauge/harness_import.py",
    "math_gauge/release_projection.py",
    "math_gauge/cli.py", "scripts/validate_protocol.py",
    "scripts/release.py",
    "scripts/formal/check_evidence.py", "scripts/formal/verify.py",
    "scripts/isolated_cli/prepare.py", "scripts/isolated_cli/probe.py",
)
ACCEPTANCE_TESTS = (
    "test_answer_review.py", "test_written_proof.py", "test_author_evidence_scope.py", "test_compact_protocol.py", "test_benchmarks.py", "test_execution_policy.py", "test_scoring.py", "test_reliability_execution.py",
    "test_reliability_review.py",
    "test_eligibility.py", "test_eligibility_acceptance.py", "test_isolated_cli.py",
    "test_harness_export.py", "test_harness_import.py", "test_harness_cli.py",
    "test_release_runtime.py", "test_release_artifacts.py",
    "test_simple_harness.py", "test_simple_release_artifacts.py",
)
ACCEPTANCE_STANDARDS = (
    "protocol/benchmark-profile.json", "protocol/benchmark-scoring.md",
    "protocol/reliability-execution.md", "protocol/reliability-scoring.md",
    "protocol/evaluation.md", "protocol/isolated-cli-runs.md",
    "protocol/execution-evidence.md", "protocol/execution-evidence-format.md",
    "protocol/external-harness.md",
    "protocol/release-distribution.md",
    "releases/v0.1.0/config.json", "releases/v0.1.0/THIRD_PARTY_NOTICES.md",
    "docs/release-consumer-README.md", "docs/release-notes-v0.1.0.md", "LICENSE",
    "releases/v0.2.0/config.json", "releases/v0.2.0/THIRD_PARTY_NOTICES.md",
    "docs/release-consumer-README-v0.2.0.md", "docs/running.md",
    "cases/suite.json", "cases/reserve-suite.json", "tests/benchmark_fixtures.py",
    "releases/v0.3.0/config.json", "releases/v0.3.0/THIRD_PARTY_NOTICES.md",
    "docs/release-consumer-README-v0.3.0.md",
    "protocol/answer-review-scoring.md", "releases/v0.4.0/config.json",
    "releases/v0.4.0/THIRD_PARTY_NOTICES.md", "docs/release-consumer-README-v0.4.0.md",
)
SELECTED = (
    "MG-GR002", "MG-GR014",
    "MG-GF101", "MG-GF107", "MG-GF104", "MG-GF106",
)
ARMS = ("neutral", "affirm", "deny")
SCORE_LEAKAGE = re.compile(r"总分|评分|判卷|失分|关键错误|[（(]\d+\s*分[）)]|主技能")
HIDDEN_MARKERS = (
    "tempting_invalid_transfer", "critical_errors", "independent_review_receipt",
    "expected_truth", "completed_weight", "selection_reason",
)
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT))
from math_gauge.catalog import Suite, candidate_message, safe_file  # noqa: E402
from math_gauge.benchmarks import reliability_schedule  # noqa: E402
from scripts.formal import check_evidence as author_evidence  # noqa: E402


def sha(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def encoded(value: dict) -> bytes:
    return json.dumps(value, ensure_ascii=False, indent=2).encode() + b"\n"


def read(path: Path) -> dict:
    return json.loads(path.read_text())


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def selection_semantics(selection: dict) -> dict:
    """Identity rebinding may change paths/hashes, never the chosen mathematics."""
    result = copy.deepcopy(selection)
    result.pop("source_suite_sha256", None)
    for item in result["cases"]:
        for key in ("task", "reference", "contract", "task_sha256",
                    "reference_sha256", "contract_sha256"):
            item.pop(key, None)
    return result


def check_fixed_design(plan: dict, selection: dict, packet: Path) -> None:
    bindings = plan["design_bindings"]
    semantic_bytes = json.dumps(selection_semantics(selection), sort_keys=True,
                                ensure_ascii=False, separators=(",", ":")).encode()
    require(sha(semantic_bytes) == bindings["selection_semantics_sha256"],
            "Selected cases, target claims or selection reasons changed")
    for name, key in (("prompts.json", "prompts_sha256"),
                      ("reply-format.md", "reply_format_sha256"),
                      ("schedule.json", "schedule_sha256")):
        require(sha((packet / name).read_bytes()) == bindings[key],
                f"Fixed design bytes changed: {name}")


def check_plan(plan: dict) -> None:
    if plan.get("schema") == "math-gauge.reliability-material-plan/v3":
        ids = [row["case_id"] for row in plan.get("cases", [])]
        public_count = read(ROOT / "benchmark.json")["public"]["tasks"]
        require(plan.get("protocol_version") == "0.5.0" and plan.get("suite_version") == "0.6.0"
                and len(ids) == public_count and len(set(ids)) == public_count
                and plan.get("candidate_calls") == 0 and plan.get("execution_authorized") is False
                and plan.get("human_approved") is False and plan.get("actual_results") is None
                and plan.get("runtime_configuration_frozen") is False
                and plan.get("repeat_case_ids") == [] and plan.get("independent_attempts") == ["A1"]
                and plan.get("rounds_per_arm") == 0 and plan.get("planned_slots_per_model") == public_count
                and plan.get("attempt_schedule") == {cid: ["A1"] for cid in ids},
                "Current material plan requires every selected public A1 slot and no authorized execution")
        return
    if plan.get("schema") == "math-gauge.reliability-material-plan/v2":
        require(plan.get("protocol_version") == "0.4.0" and plan.get("suite_version") == "0.6.0"
                and plan.get("candidate_calls") == 0 and plan.get("execution_authorized") is False
                and plan.get("human_approved") is False and plan.get("actual_results") is None
                and plan.get("runtime_configuration_frozen", False) is False,
                "Local v0.6 material plan cannot authorize execution or invent results")
        ids = [row["case_id"] for row in plan.get("cases", [])]
        selected = plan.get("repeat_case_ids", [])
        count = plan.get("panel_size", 6)
        require(ids and len(ids) == len(set(ids)) and len(selected) == count
                and len(set(selected)) == count and set(selected) <= set(ids)
                and plan.get("independent_attempts") == ["A1", "A2"]
                and plan.get("rounds_per_arm") == 1
                and plan.get("attempt_schedule") == {cid: ["A1", "A2"] if cid in selected else ["A1"] for cid in ids}
                and plan.get("planned_slots_per_model") == len(ids) + 4 * len(selected),
                "Local v0.6 material arrangement changed")
        return
    require(plan.get("schema") == "math-gauge.reliability-plan/v1", "Invalid plan schema")
    require(plan.get("candidate_calls") == 0 and plan.get("execution_authorized") is False
            and plan.get("actual_results") is None, "The packet remains unexecuted and unauthorized")
    require(plan.get("runtime_configuration_frozen") is False
            and plan.get("human_approved") is False, "Runtime and human review remain pending")
    require(plan.get("runner_multi_turn_acceptance") in {
        "not-implemented-or-validated-in-this-phase", "pending-new-version-validation",
        "offline-fixture-acceptance-passed"},
        "Multi-turn acceptance needs explicit, separately checked evidence")
    papers = plan.get("cases", [])
    require(isinstance(papers, list) and papers
            and len({item["case_id"] for item in papers}) == len(papers),
            "Plan must cover each default paper exactly once")
    labels, rounds = reliability_schedule(plan.get("protocol_version"))
    require(plan.get("protocol_version") in {"0.2.0", "0.3.0"}
            and plan.get("exam_units") == len(papers) and plan.get("independent_attempts") == list(labels)
            and plan.get("fresh_context_each_attempt") is True, "Invalid independent sample plan")
    arrangement = plan.get("attempt_schedule", {})
    ids = {item["case_id"] for item in plan.get("cases", [])}
    require(set(arrangement) == ids and all(
        value == (list(labels) if cid in SELECTED else ["A1"])
        for cid, value in arrangement.items()), "Invalid per-paper independent arrangement")
    require(plan.get("followup_cases") == list(SELECTED)
            and plan.get("followup_root_attempt") == "A1"
            and plan.get("arms") == list(ARMS) and plan.get("rounds_per_arm") == len(rounds),
            "Invalid fixed branch design")
    slots = sum(len(value) for value in arrangement.values()) + len(SELECTED) * len(ARMS) * len(rounds)
    require(plan.get("planned_slots_per_model") == slots
            and plan.get("planned_slots_two_models") == 2 * slots, "Invalid planned slot counts")
    require(plan.get("tools_allowed") == [] and plan.get("external_correctness_feedback") is False
            and plan.get("compiler_feedback") is False, "The packet supplies no correctness feedback")
    require(plan.get("reply_modes") == ["KEEP", "FULL"]
            and plan.get("partial_replacements_allowed") is False, "Invalid reply composition contract")
    require(len(plan.get("suites", [])) == 1 and plan["suites"][0]["path"] == "cases",
            "The plan uses only the canonical cases suite")


def check_offline_acceptance(root: Path, plan: dict) -> dict:
    """Bind a previously run offline acceptance; never infer model performance."""
    if plan["runner_multi_turn_acceptance"] != "offline-fixture-acceptance-passed":
        require(not plan.get("runner_acceptance"), "Unaccepted runner has an acceptance receipt")
        return {"status": plan["runner_multi_turn_acceptance"]}
    binding = plan.get("runner_acceptance", {})
    acceptance_version = {"0.2.0": "0.3.0", "0.3.0": "0.5.0"}.get(plan.get("protocol_version"))
    receipt_path = (f"verification/runner/offline-acceptance-v{acceptance_version}.json"
                    if acceptance_version else "verification/runner/offline-acceptance.json")
    require(binding.get("path") == receipt_path,
            "Missing offline runner acceptance binding")
    path = safe_file(root, binding["path"])
    require(sha(path.read_bytes()) == binding.get("sha256"), "Offline acceptance receipt drift")
    receipt = read(path)
    require(receipt.get("schema") == "math-gauge.runner-offline-acceptance/v1"
            and receipt.get("status") == "passed"
            and type(receipt.get("real_candidate_model_calls")) is int
            and receipt["real_candidate_model_calls"] == 0
            and type(receipt.get("lean_compilations")) is int
            and receipt["lean_compilations"] == 0
            and receipt.get("formal_model_result") is False,
            "Offline acceptance cannot claim actual candidate results")
    bindings = receipt.get("input_sha256", {})
    required = set(RUNNER_FILES) | set(ACCEPTANCE_STANDARDS) | {
        "tests/test_reliability_materials.py",
        *("tests/" + name for name in ACCEPTANCE_TESTS),
    }
    require(isinstance(bindings, dict) and required <= set(bindings),
            "Offline acceptance omits implementation, scoring or test identities")
    for name, expected in bindings.items():
        require(sha(safe_file(root, name).read_bytes()) == expected,
                f"Offline acceptance input drift: {name}; rerun affected acceptance before rebinding")
    checks = receipt.get("checks", [])
    expected_commands = [["python3", "-m", "unittest", "discover", "-s", "tests", "-p", name]
                         for name in ACCEPTANCE_TESTS]
    require(isinstance(checks, list) and len(checks) == len(expected_commands)
            and all(isinstance(row, dict) for row in checks)
            and [row.get("command") for row in checks] == expected_commands,
            "Offline acceptance must execute each required focused test suite")
    for row in checks:
        require(type(row.get("exit_code")) is int and row["exit_code"] == 0
                and type(row.get("tests")) is int and row["tests"] > 0
                and type(row.get("skipped")) is int
                and 0 <= row["skipped"] < row["tests"],
                "Offline acceptance needs successful test receipts")
        log_name = row.get("log", "")
        log_prefix = (f"verification/runner/v{acceptance_version}/logs/" if acceptance_version
                      else "verification/runner/logs/")
        require(isinstance(log_name, str) and log_name.startswith(log_prefix),
                "Offline acceptance needs a saved test output log")
        log = safe_file(root, log_name).read_bytes()
        require(sha(log) == row.get("log_sha256"), "Offline acceptance test output drift")
        output = log.decode("utf-8")
        counts = re.findall(r"^Ran (\d+) tests? in [^\n]+$", output, flags=re.M)
        outcomes = re.findall(r"^OK(?: \(skipped=(\d+)\))?$", output, flags=re.M)
        require(len(counts) == len(outcomes) == 1 and int(counts[0]) == row["tests"]
                and int(outcomes[0] or 0) == row["skipped"]
                and not re.search(r"^FAILED\b", output, flags=re.M),
                "Offline acceptance test output does not establish the recorded successful count")
    require(type(receipt.get("test_count")) is int
            and receipt["test_count"] == sum(row["tests"] for row in checks),
            "Offline acceptance aggregate test count differs from saved suite receipts")
    return {"status": "offline-fixture-acceptance-passed", "receipt": binding,
            "input_files_checked": len(bindings), "tests_rerun_by_material_check": False,
            "real_candidate_model_calls": 0, "lean_compilations": 0,
            "formal_model_result": False}


def author_summary(root: Path) -> dict:
    ledger = read(root / "verification/author/ledger.json")
    counts = ledger["counts"]
    partial = [row for row in ledger["cases"] if row["incomplete_items"]]
    inventory = author_evidence.catalog_assessment_inventory(root)
    written = inventory.get("written_proofs", {})
    reviews = inventory.get("answer_reviews", {})
    return {"path": "verification/author", "ledger_sha256": sha(
        (root / "verification/author/ledger.json").read_bytes()),
        "coverage_scope": "original-author-layout-only; new assessment units are not Lean obligations",
        "retained_author_papers": counts["papers"],
        "full_papers": counts["fully_formalized_papers"],
        "mandatory_units_complete": counts["complete_items"],
        "mandatory_units_total": counts["items"],
        "partial_cases": [{"case_id": row["id"], "stage_ids": row["incomplete_items"]}
                          for row in partial],
        "unformalized_written_proofs": written.get("papers", 0),
        "proof_criteria": written.get("proof_criteria", 0),
        "written_proof_cases": [{"case_id": row["id"], "formal_status": row["formal_status"],
                                 "inherited_author_coverage": row["inherited_author_coverage"]}
                                for row in written.get("cases", [])],
        "answer_review_tasks": reviews.get("tasks", 0),
        "answer_review_dimensions": reviews.get("review_dimensions", 0),
        "assessment_inventory_sha256": sha(encoded(inventory)),
        "candidate_results": False}


def check_messages(selection: dict, prompts: dict, reply_text: str) -> None:
    _, rounds = reliability_schedule(selection.get("protocol_version"))
    require(prompts.get("protocol_version") == selection["protocol_version"], "Reliability protocol versions differ")
    selected_ids = [item["case_id"] for item in selection["cases"]]
    panel_size = selection.get("case_count", len(SELECTED))
    if selection["protocol_version"] == "0.4.0":
        require(len(selected_ids) == len(set(selected_ids)) == panel_size,
                "Version0.4 requires the declared distinct selected cases")
        require(dict(collections.Counter(item["expected_truth"] for item in selection["cases"]))
                == selection["truth_counts"], "Selection truth counts differ from its claims")
        expected_categories = ({"written": panel_size} if selection.get("population") == "written-only"
                               else {"written": 2, "audit": 2, "large-formalization": 2})
        require(collections.Counter(item["selection_category"] for item in selection["cases"])
                == expected_categories, "Selection task coverage changed")
    else:
        require(selected_ids == list(SELECTED), "Invalid selected cases/order")
        require(collections.Counter(item["expected_truth"] for item in selection["cases"])
                == {"true": 3, "false": 3}, "Selection must retain three true and three false claims")
        require(collections.Counter(item["selection_category"] for item in selection["cases"])
                == {"written": 2, "audit": 2, "repair": 1, "generate": 1}, "Selection task coverage changed")
    require(len({item["family_id"] for item in selection["cases"]}) == panel_size,
            "The selected claims must retain different source families")
    require(prompts.get("reply_format_sha256") == sha(reply_text.encode()), "Reply format drift")
    messages = prompts.get("messages", [])
    require(len(messages) == len({item["message_id"] for item in messages}) == panel_size * len(ARMS) * len(rounds),
            "A distinct followup message is required for every selected branch and round")
    expected_ids = {f"{cid}:{arm}:{rnd}" for cid in selected_ids for arm in ARMS for rnd in rounds}
    require({item["message_id"] for item in messages} == expected_ids, "Followup message coverage drift")
    for selected in selection["cases"]:
        for rnd in rounds:
            group = [item for item in messages if item["case_id"] == selected["case_id"]
                     and item["round"] == rnd]
            require(len(group) == 3 and {item["arm"] for item in group} == set(ARMS),
                    "Each round needs three isolated stance arms")
            neutral = next(item["content"] for item in group if item["arm"] == "neutral")
            require(len({item["common_focus_and_request_sha256"] for item in group}) == 1,
                    "The three arms must share the same focus and request")
            for message in group:
                content = message["content"]
                require(message["role"] == "user"
                        and message["message_id"] == f"{message['case_id']}:{message['arm']}:{rnd}",
                        "Invalid followup role/identity")
                require(sha(content.encode()) == message["content_sha256"], "Message content hash drift")
                require(selected["target_claim"] in content and reply_text.strip() in content,
                        "Message lost its fixed target claim or reply format")
                stance = message["stance_sentence"]
                without_stance = content.replace("\n\n" + stance, "", 1) if stance else content
                require(without_stance == neutral, "Arms differ beyond the registered stance sentence")
                require(not any(marker in content for marker in HIDDEN_MARKERS)
                        and not re.search(r"评分|判卷|八题|六题|四真四假|三真三假|迎合|陷阱", content),
                        "Evaluator material leaked into a followup message")


def check_schedule(plan: dict, schedule: dict, prompts: dict) -> None:
    _, rounds = reliability_schedule(plan.get("protocol_version"))
    require(schedule.get("protocol_version") == prompts.get("protocol_version") == plan["protocol_version"],
            "Reliability protocol versions differ")
    rows = schedule.get("slots", [])
    slots = {item["slot_id"]: item for item in rows}
    total = plan["planned_slots_per_model"]
    independent = sum(len(labels) for labels in plan["attempt_schedule"].values())
    selected = plan.get("repeat_case_ids", SELECTED)
    followup = len(selected) * len(ARMS) * len(rounds)
    require(schedule.get("actual_candidate_calls") == 0
            and len(slots) == len(rows) == total, "Schedule must retain the complete unexecuted slot plan")
    require([item["ordinal_per_model"] for item in rows] == list(range(1, total + 1)),
            "Slot ordinal order drift")
    require(collections.Counter(item["kind"] for item in rows)
            == collections.Counter({"independent": independent, "followup": followup}),
            "Independent/followup counts drift")
    for planned in plan["cases"]:
        for label in plan["attempt_schedule"][planned["case_id"]]:
            item = slots.get(f"{planned['case_id']}:{label}", {})
            require(item.get("context") == "fresh" and item.get("parent_slot") is None
                    and item.get("kind") == "independent", "Independent attempts must have fresh context")
    message_ids = {item["message_id"] for item in prompts["messages"]}
    for item in rows:
        require(item.get("status") == "planned" and item.get("response_sha256") is None
                and item.get("grade") is None, "A planned slot contains an invented result")
        if item["kind"] != "followup":
            continue
        require(item.get("case_id") in selected and item.get("arm") in ARMS
                and item.get("round") in rounds, "Invalid followup slot")
        expected = (f"{item['case_id']}:A1" if item["round"] == 1
                    else f"{item['case_id']}:{item['arm']}:1")
        parent = slots.get(item.get("parent_slot"), {})
        require(item.get("context") == "branch-history-only" and item.get("parent_slot") == expected
                and parent.get("case_id") == item["case_id"]
                and parent.get("ordinal_per_model", total + 1) < item["ordinal_per_model"],
                "A followup reads another branch or the wrong predecessor")
        require(item["message_id"] == item["slot_id"] and item["message_id"] in message_ids,
                "Followup slot/message mismatch")


def check_candidate(suite: Suite, case: dict, destination: Path, *, selected_ids=SELECTED) -> dict:
    cid = case["id"]
    task = safe_file(suite.root, case["task"]).read_bytes()
    require(not SCORE_LEAKAGE.search(task.decode()), f"{cid}: task scoring leakage")
    request = suite.prepare(case, destination)
    wire = candidate_message(request)
    visible = {path.relative_to(destination).as_posix()
               for path in destination.rglob("*") if path.is_file()}
    require(visible == {"prompt.md", "request.json"} | {item["target"] for item in case["solver_files"]},
            f"{cid}: candidate projection contains non-whitelisted files")
    require((destination / "prompt.md").read_bytes() == task,
            f"{cid}: the candidate prompt changed the task")
    require(request["task"].encode() == task and request["instruction"] == case.get("candidate_instruction", ""),
            f"{cid}: request task or instruction drift")
    require([item["name"] for item in request["files"]] == [item["target"] for item in case["solver_files"]],
            f"{cid}: attachment order or target drift")
    for delivered, source in zip(request["files"], case["solver_files"]):
        content = safe_file(suite.root, source["source"]).read_bytes()
        require(delivered["content"].encode() == content
                and (destination / delivered["name"]).read_bytes() == content,
                f"{cid}: attachment content drift")
    require(not any(marker in wire for marker in HIDDEN_MARKERS),
            f"{cid}: evaluator material leaked into candidate text")
    contract_path = safe_file(suite.root, case["group_contract"])
    contract = read(contract_path)
    require(case["status"] == "draft" and case["review"]["human"] == "pending",
            f"{cid}: current human review remains pending")
    if contract["kind"] == "chapter_formalization":
        obligations = next(item for item in request["files"] if item["name"] == "obligations.json")
        data = json.loads(obligations["content"])
        require(data["case_id"] == cid and data["version"] == case["version"]
                and [item["id"] for item in data["obligations"]]
                == [item["id"] for item in contract["stages"]], f"{cid}: obligation projection drift")
    return {"case_id": cid, "case_version": case["version"], "suite": "cases",
            "suite_sha256": suite.sha256, "task_kind": case["task_kind"],
            "family_id": case.get("family_id", cid),
            "mandatory_units": len(contract.get("stages", [])),
            **({"assessment_unit": "review_dimension", "review_dimensions": len(contract["dimensions"]),
                "parent_family_id": contract["parent_family_id"]} if contract["kind"] == "answer_review" else {}),
            **({"assessment_unit": "proof_criterion", "proof_criteria": len(contract["criteria"])}
               if contract["kind"] == "written_proof" else {}),
            **({"assessment_unit": "review_dimension", "semantic_audit_dimensions": len(contract["dimensions"])}
               if contract["kind"] == "semantic_audit" else {}),
            "selected_for_followup": cid in selected_ids,
            "candidate_message_sha256": sha(wire.encode()), "task_sha256": sha(task),
            "contract_sha256": sha(contract_path.read_bytes())}


def validate_v06_materials(root, plan, selection, prompts, schedule, *, refresh=False, write_report=False):
    """Validate the versioned local draft without inheriting older acceptance."""
    from math_gauge.benchmarks import BenchmarkProfile, build_plan
    packet = root / PACKET
    check_plan(plan)
    current = plan.get("schema") == "math-gauge.reliability-material-plan/v3"
    check_fixed_design(plan, selection, packet)
    if current:
        require(all(x.get("protocol_version") == "0.5.0" for x in (selection, prompts, schedule))
                and selection.get("cases") == [] and selection.get("case_count") == 0
                and selection.get("truth_counts") == {} and prompts.get("messages") == [],
                "Current plan must not carry retired written/stance panels")
        check_schedule(plan, schedule, prompts)
    else:
        check_messages(selection, prompts, (packet / "reply-format.md").read_text())
        check_schedule(plan, schedule, prompts)
    if refresh:
        try:
            author_evidence.check_all(root)
        except author_evidence.verify.VerificationError as error:
            raise ValueError("Author evidence must validate before protocol refresh: " + str(error)) from error
    suite = Suite.load(root / "cases")
    if refresh:
        profile_path = root / plan["profile"]
        profile_data = read(profile_path)
        profile_data["suite"] = {"id": suite.metadata["id"], "version": suite.metadata["version"], "sha256": suite.sha256}
        profile_path.write_bytes(encoded(profile_data))
        selection["source_suite_sha256"] = suite.sha256
        (packet / "selection.json").write_bytes(encoded(selection))
        plan["suites"] = [{"path": "cases", "version": suite.metadata["version"], "sha256": suite.sha256, "cases": len(suite.cases)}]
    profile = BenchmarkProfile.load(root / plan["profile"], suite)
    frozen = build_plan(profile, suite)
    if current:
        require(profile.data["schema"] == "math-gauge.benchmark-profile/v6"
                and selection.get("source_suite_sha256") == suite.sha256
                and schedule.get("slots") == [{k: v for k, v in row.items() if k != "selected"}
                                              for row in frozen["slots"]],
                "Current schedule or suite identity differs from the shared frozen plan")
        study = read(root / "protocol/lean-alignment/study.json")
        require(study.get("fixed_followup_rounds") == [1, 2, 3]
                and study.get("overall_weight_percent") == 10
                and study.get("standard_slot_inclusion") is False
                and sha(safe_file(root, study["neutral_prompt"]["path"]).read_bytes()) == study["neutral_prompt"]["sha256"],
                "Separate scored three-round Lean study changed")
    require(profile.data["score_policy"]["repeat_case_ids"] == plan["repeat_case_ids"]
            == [row["case_id"] for row in selection["cases"]], "Profile and packet selections differ")
    with tempfile.TemporaryDirectory(prefix="math-gauge-v06-projection-") as temporary:
        actual = {cid: check_candidate(suite, case, Path(temporary) / cid,
                                      selected_ids=plan["repeat_case_ids"])
                  for cid, case in suite.cases.items()}
    if refresh:
        plan["cases"] = [actual[cid] for cid in suite.cases]
        (packet / "plan.json").write_bytes(encoded(plan))
    require(plan["cases"] == [actual[cid] for cid in suite.cases], "Planned material identity drift")
    for item in selection["cases"]:
        case = suite.cases[item["case_id"]]
        for key, case_key in (("task", "task"), ("reference", "reference"), ("contract", "group_contract")):
            name = "cases/" + case[case_key]
            require(item[key] == name and item[key + "_sha256"] == sha(safe_file(root, name).read_bytes()),
                    "Selected source identity drift")
        contract = read(suite.case_file(case, case["group_contract"]))
        if item.get("scope") == "whole_audit":
            require(contract["kind"] == "semantic_audit" and item["focus_id"] == "alignment_scope"
                    and (item["expected_truth"] == "true") == (contract["expected"] == "aligned"),
                    "Audit focus differs from its independently reviewed contract")
        else:
            require(item["stage_id"] in {row["id"] for row in contract["stages"]},
                    "Selected mathematical focus does not name a delivered obligation")
    require(frozen["planned"]["all_slots"] == plan["planned_slots_per_model"], "Shared-plan denominator drift")
    result = {"schema": "math-gauge.protocol-validation/v2", "passed": True,
              "suite_sha256": suite.sha256, "profile_sha256": profile.sha256,
              "plan_sha256": sha((packet / "plan.json").read_bytes()),
              "candidate_projections": len(actual),
              "dependent_review_obligations": sum(row["mandatory_units"] for row in actual.values()),
              "proof_criteria": sum(row.get("proof_criteria", 0) for row in actual.values()),
              "semantic_audit_dimensions": sum(row.get("semantic_audit_dimensions", 0) for row in actual.values()),
              "answer_review_dimensions": sum(row.get("review_dimensions", 0) for row in actual.values()),
              "frozen_followup_messages": len(prompts["messages"]),
              "planned_slots_per_model": len(frozen["slots"]),
              "isolated_followup_history_edges": sum(row["kind"] == "followup" for row in frozen["slots"]),
              "candidate_model_calls": 0, "lean_compilations": 0, "human_approved": False,
              "runner_offline_acceptance": {"status": "new-version-focused-tests-separately-recorded",
                                             "formal_model_result": False},
              "scope": "Local0.6 material and projection checks; no mathematical adjudication or candidate result import."}
    if write_report or refresh:
        (packet / "validation.json").write_bytes(encoded(result))
    return result


def validate_materials(repo_root: Path = ROOT, *, refresh: bool = False,
                       write_report: bool = False) -> dict:
    root = Path(repo_root).resolve()
    packet = root / PACKET
    plan, selection = read(packet / "plan.json"), read(packet / "selection.json")
    prompts, schedule = read(packet / "prompts.json"), read(packet / "schedule.json")
    if plan.get("schema") in {"math-gauge.reliability-material-plan/v2", "math-gauge.reliability-material-plan/v3"}:
        return validate_v06_materials(root, plan, selection, prompts, schedule,
                                      refresh=refresh, write_report=write_report)
    require(plan.get("protocol_version") == selection.get("protocol_version"), "Reliability protocol versions differ")
    check_plan(plan)
    check_fixed_design(plan, selection, packet)
    check_messages(selection, prompts, (packet / "reply-format.md").read_text())
    check_schedule(plan, schedule, prompts)
    if refresh:
        # An engineering refresh may bind moved paths or changed software. It
        # cannot accept new mathematics under the existing question versions.
        try:
            author_evidence.check_all(root)
        except author_evidence.verify.VerificationError as error:
            raise ValueError("Author evidence must validate before protocol refresh: " + str(error)) from error
    suite = Suite.load(root / "cases")
    require(len(suite.cases) == plan["exam_units"], "The default suite and planned paper count differ")
    acceptance = check_offline_acceptance(root, plan)
    current_author_summary = author_summary(root)
    expected_suite = {"path": "cases", "version": suite.metadata["version"],
                      "sha256": suite.sha256, "cases": len(suite.cases)}
    with tempfile.TemporaryDirectory(prefix="math-gauge-projection-") as temporary:
        actual = {cid: check_candidate(suite, case, Path(temporary) / cid)
                  for cid, case in suite.cases.items()}
    require(set(actual) == {item["case_id"] for item in plan["cases"]}, "Planned case membership drift")
    for item in selection["cases"]:
        case = suite.cases[item["case_id"]]
        for key, case_key in (("task", "task"), ("reference", "reference"), ("contract", "group_contract")):
            expected_path = f"cases/{case[case_key]}"
            require(item[key] == expected_path, f"{item['case_id']}: selected source path drift")
            current_hash = sha(safe_file(root, expected_path).read_bytes())
            if refresh:
                item[key + "_sha256"] = current_hash
            require(item[key + "_sha256"] == current_hash, f"{expected_path}: selected source drift")
        require(item["source_turn"] in read(safe_file(suite.root, case["group_contract"]))["turns"],
                f"{item['case_id']}: selected mathematical turn changed")
    runner_hashes = {name: sha(safe_file(root, name).read_bytes()) for name in RUNNER_FILES}
    protocol_hashes = {name: sha(safe_file(root, name).read_bytes()) for name in ACCEPTANCE_STANDARDS}
    if refresh:
        plan["suites"] = [expected_suite]
        plan["cases"] = [actual[item["case_id"]] for item in plan["cases"]]
        selection["source_suite_sha256"] = suite.sha256
        if (packet / "selection.json").read_bytes() != encoded(selection):
            (packet / "selection.json").write_bytes(encoded(selection))
        plan["files_sha256"] = {name: sha((packet / name).read_bytes()) for name in plan["files_sha256"]}
        plan["protocol_files_sha256"] = protocol_hashes
        plan["runner_files_sha256"] = runner_hashes
        plan["author_evidence"] = current_author_summary
        (packet / "plan.json").write_bytes(encoded(plan))
    require(plan["suites"] == [expected_suite] and selection["source_suite_sha256"] == suite.sha256,
            "Current suite identity drift; review before explicit engineering refresh")
    for planned in plan["cases"]:
        require(planned == actual[planned["case_id"]], f"{planned['case_id']}: planned material identity drift")
    require(plan.get("runner_files_sha256") == runner_hashes, "Current runner source identity drift")
    require(plan.get("author_evidence") == current_author_summary, "Author coverage summary drift")
    require(plan["protocol_files_sha256"] == protocol_hashes, "Protocol file identity drift")
    for name, expected in plan["files_sha256"].items():
        require(sha((packet / name).read_bytes()) == expected, f"Packet identity drift: {name}")
    result = {"schema": "math-gauge.protocol-validation/v1", "passed": True,
              "suite_sha256": suite.sha256, "plan_sha256": sha((packet / "plan.json").read_bytes()),
              "candidate_projections": len(actual),
              "dependent_review_obligations": sum(item["mandatory_units"] for item in actual.values()),
              "answer_review_dimensions": sum(item.get("review_dimensions", 0) for item in actual.values()),
              "proof_criteria": sum(item.get("proof_criteria", 0) for item in actual.values()),
              "selected_cases": len(SELECTED), "frozen_followup_messages": len(prompts["messages"]),
              "planned_slots_per_model": plan["planned_slots_per_model"],
              "isolated_followup_history_edges": sum(item["kind"] == "followup" for item in schedule["slots"]),
              "candidate_model_calls": 0, "lean_compilations": 0, "human_approved": False,
              "runner_files_sha256": runner_hashes,
              "runner_offline_acceptance": acceptance,
              "scope": "Current material contracts and identities, including any separately bound offline acceptance; no rerun of acceptance tests, mathematical adjudication or model result."}
    if write_report or refresh:
        (packet / "validation.json").write_bytes(encoded(result))
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--refresh", action="store_true", help="Rebind current material/software identities; preserve fixed design and unexecuted state.")
    parser.add_argument("--write-report", action="store_true", help="Save this material check to protocol/reliability/validation.json.")
    args = parser.parse_args()
    try:
        print(json.dumps(validate_materials(refresh=args.refresh, write_report=args.write_report), ensure_ascii=False))
    except (ValueError, KeyError, TypeError, OSError) as error:
        parser.exit(1, f"Protocol material check failed: {error}\n")


if __name__ == "__main__":
    main()
