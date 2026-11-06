#!/usr/bin/env python3
"""Adopt user-selected theorem-extension cases and exact A1 evidence.

Private mappings and source material are supplied by the companion repository.
This command never invokes a model and never copies a runner implementation.
"""

import argparse
import copy
import hashlib
import json
import os
import shutil
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from math_gauge.catalog import Suite, candidate_message, assessment_weights
from math_gauge.records import descriptor
from math_gauge.theorem_extension import validate_policy


def load(path):
    return json.loads(Path(path).read_bytes())


def write(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2, allow_nan=False) + "\n")


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def copy_exact(source, target):
    source, target = Path(source), Path(target)
    if source.is_symlink() or not source.is_file():
        raise ValueError("Only exact regular source files may be adopted")
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.exists() and target.read_bytes() != source.read_bytes():
        raise ValueError("Existing original evidence differs; never overwrite it")
    if not target.exists():
        shutil.copyfile(source, target)


def import_cases(private_root, config):
    source = private_root / config["candidate_root"]
    original = load(source / "protocol/plan.json")
    originals = {row["id"]: row for row in original["cases"]}
    policy = validate_policy(load(ROOT / "protocol/theorem-extension-policy.json"))
    for row in config["cases"]:
        cid, old = row["case_id"], originals[row["pilot_case_id"]]
        root = ROOT if row["visibility"] == "public" else private_root
        folder = root / "cases/theorem-extension" / cid
        folder.mkdir(parents=True, exist_ok=True)
        material = source / old["source_directory"]
        copy_exact(source / old["a1_prompt"], folder / "task.md")
        copy_exact(material / "02_中文参考.md", folder / "reference.md")
        copy_exact(next(material.glob("03*")), folder / "source-rubric.md")
        criteria = []
        for ident, title, evidence in zip(
                ("local-refinement", "substantive-extension", "complete-structure"),
                ("有效局部细化或更高成果", "实质额外定理或更高成果", "完整结构性成果"), row["level_evidence"]):
            criteria.append({"id": ident, "title": title, "points": 1,
                "required_evidence": [evidence, "只审核原样题面下A1实际交付的有效结果；认可同等价值替代路线。"],
                "critical_errors": ["以未证明猜测、等价改写或未交付推论冒充额外成果。",
                                    "把参考的特定路线设为唯一标准，或用研究邀请后结果回填A1。"]})
        contract = {"schema": "math-gauge.group-contract/v2", "id": cid,
            "version": "0.1.0", "kind": "written_proof", "assessment_unit": "proof_criterion",
            "criteria": criteria, "research_assessment": {"policy_version": "0.1.0",
                "basis": "A1-only; three cumulative levels; baseline B recorded separately",
                "partial": "(R - baseline_penalty[B])/3; penalties B0=2, B1=1, B2=0; no per-case floor",
                "strict": "B=2 and R=3", "post_observation": True}}
        write(folder / "contract.json", contract)
        write(folder / "research-policy.json", policy)
        write(folder / "rubric.json", {"schema": "math-gauge.rubric/v1", "expected": "true",
            "required_evidence": ["B按原题完整性0/1/2独立记录。",
                "R按source-rubric.md的开放判准0/1/2/3，三个累计判准各1分；再单独扣除B0的2分或B1的1分，B2不扣。净研究分为(R−扣分)/3，可为负分。",
                "Strict要求原目标正确且A1实际完成完整结构性拓展；接受同等数学价值的替代结构。"],
            "critical_errors": ["将没有额外拓展称为原题数学失败。", "使用任何邀请后答复或跨轮并集计分。"],
            "aggregation": "Research tiers and baseline-error deductions are separate. Correct baseline without extension scores0; wrong baseline without extension scores negatively; only the full benchmark is floored at0.",
            "review_contract": cid + "/contract.json", "human_review": "pending"})
        source_id = "user-selected-theorem-extension-" + cid.lower()
        write(folder / "case.json", {"schema": "math-gauge.case/v1", "id": cid,
            "version": "0.1.0", "title": old["title"], "track": "determinate", "task_kind": "written",
            "family_id": cid, "visibility": row["visibility"], "status": "draft", "language": "zh-CN",
            "path_base": "case", "task": "task.md", "candidate_instruction": "", "solver_files": [],
            "reference": "reference.md", "rubric": "rubric.json", "group_contract": "contract.json",
            "sources": [source_id], "review": {"mathematical": "ai-reviewed; open research criteria; post-observation",
                "human": "pending", "formalization": {"status": "not_performed", "author_coverage_inherited": False}},
            "lean_checks": [], "evaluator_files": ["source-rubric.md", "research-policy.json", "provenance.json", "review.json"]})
        write(folder / "provenance.json", {"case_id": cid, "source": "User-supplied candidate package v5",
            "source_task_sha256": old["a1_sha256"], "source_reference_sha256": digest(folder / "reference.md"),
            "source_rubric_sha256": digest(folder / "source-rubric.md"), "repository_visibility": row["visibility"],
            "selection": "Explicit user selection after Terra A1 pilot; two higher A1 cases public, three companion cases private",
            "source_public_availability": "unverified; classical background is not a hidden-holdout claim",
            "post_observation": True, "human_review": "pending", "formal_comparison_eligible": False})
        write(folder / "review.json", {"case_id": cid, "status": "ai-mathematical-material-review-complete",
            "reference": "reference.md", "criteria": "source-rubric.md", "baseline_truth": "true",
            "human_review": "pending", "lean_verification": "not_performed",
            "required_flow": "one independent A1; no research invitation", "post_observation_selection": True})
        sources = load(root / "cases/sources.json")
        sources[source_id] = {"title": old["title"] + " · 用户提供材料", "visibility": row["visibility"],
            "access": "User supplied and explicitly selected for this repository component",
            "original_external_availability": "unverified", "human_review": "pending"}
        write(root / "cases/sources.json", sources)
        suite = load(root / "cases/suite.json")
        suite["title"] = ("Math Gauge: written proof, Lean, answer review and theorem extension"
                          if row["visibility"] == "public" else
                          "Math Gauge: private written arguments and theorem extension")
        manifest = f"theorem-extension/{cid}/case.json"
        if manifest not in suite["cases"]:
            suite["cases"].append(manifest)
        write(root / "cases/suite.json", suite)
    public, private = Suite.load(ROOT / "cases"), Suite.load(private_root / "cases")
    for row in config["cases"]:
        suite = public if row["visibility"] == "public" else private
        actual = candidate_message(suite.request(suite.cases[row["case_id"]])).encode()
        if hashlib.sha256(actual).hexdigest() != originals[row["pilot_case_id"]]["a1_sha256"]:
            raise ValueError("The adopted candidate projection changed the actual A1 prompt")
    return public, private


def retain_answers(private_root, config, public_suite, private_suite):
    source = private_root / config["candidate_root"]
    suites = {"public": public_suite, "private": private_suite}
    cases = []
    for row in config["cases"]:
        suite, cid = suites[row["visibility"]], row["case_id"]
        case = suite.cases[cid]
        contract = load(suite.case_file(case, case["group_contract"]))
        cases.append({"case_id": cid, "family_id": cid, "component": "theorem-extension",
            "contract_kind": "written_proof", "task_kind": "written", "source_visibility": row["visibility"],
            "version": "0.1.0", "total_weight": 3, **assessment_weights(contract),
            "task_sha256": digest(suite.case_file(case, case["task"])),
            "contract_sha256": digest(suite.case_file(case, case["group_contract"]))})
    for model in load(ROOT / "benchmark.json")["selected_result_models"]:
        rel = Path("results/v0.6.0") / model / "20261105"
        private, public = private_root / rel, ROOT / rel
        old_inputs = load(private / "scoring-inputs.json")
        data = {"schema": "math-gauge.theorem-extension-inputs/v1", "benchmark_version": "0.6.0",
            "model_label": old_inputs["model_label"], "attempt_labels": ["A1"],
            "policy": load(ROOT / "protocol/theorem-extension-policy.json"),
            "research_invitation_included": False, "case_index": cases, "slots": [],
            "human_review": "pending", "formal_comparison_eligible": False,
            "adoption": "Post-observation source-bound reuse, no new model calls by adoption",
            "prior_environment_diagnostics": {"dispatches": 15 if model == config["model"] else 0,
                "final_answers": 0, "reason": "workspace routing discovery failed" if model == config["model"] else "not_run",
                "repaired_batch": "proxy-fixed-1" if model == config["model"] else None}}
        public_rows = []
        for row in config["cases"]:
            cid, pilot = row["case_id"], row["pilot_case_id"]
            retained = {"slot_id": cid + ":A1", "case_id": cid, "attempt_label": "A1",
                "status": "not_run", "baseline_B": None, "research_R": None,
                "response": None, "review": None}
            if model == config["model"]:
                original = source / "answers-proxy-fixed-1" / pilot / "A1"
                target = private / "theorem-extension" / cid
                copy_exact(original / "answer.md", target / "A1/answer.md")
                copy_exact(source / "reviews" / (pilot + "-A1.json"), target / "source-review.json")
                review = load(target / "source-review.json")
                introduction = (target / "A1/answer.md").read_text().split("\n", 1)[0]
                for name in ("input/task.md", "output/events.ndjson", "output/stderr.txt", "runtime/execution.json",
                             "runtime/plan.json", "runtime/outer.sb", "runtime/open-probe.json",
                             "runtime/parent-pid-check.json", "runtime/worker-pid-check.json"):
                    copy_exact(original / "attempt-1" / name, target / "native" / name)
                retained.update(status="response_received_execution_unverified", baseline_B=review["B"],
                    research_R=review["R"], response=descriptor(private, target / "A1/answer.md"),
                    review=descriptor(private, target / "source-review.json"),
                    source_prompt_sha256=cases[len(data["slots"])]["task_sha256"],
                    original_input=descriptor(private, target / "native/input/task.md"),
                    execution=descriptor(private, target / "native/runtime/execution.json"),
                    artifacts=[descriptor(private, p) for p in sorted((target / "native").rglob("*")) if p.is_file()],
                    self_assessment={"origin": "original_excerpt", "explicit_100_percent": "not_stated",
                        "excerpt": introduction, "utf8_start": 0, "utf8_end": len(introduction.encode()),
                        "separate_completeness_report": "not_requested_not_stated",
                        "summary": review["self_assessment"]},
                    source_batch="proxy-fixed-1", source_attempt=1,
                    original_alias=pilot, invited_answer_used=False)
                if row["visibility"] == "public":
                    destination = public / "theorem-extension" / cid
                    for item in ("A1/answer.md", "source-review.json", "native/runtime/execution.json"):
                        copy_exact(target / item, destination / item)
                    public_rows.append({"case_id": cid, "attempt_label": "A1", "baseline_B": review["B"],
                        "research_R": review["R"], "response": descriptor(public, destination / "A1/answer.md"),
                        "review": descriptor(public, destination / "source-review.json")})
            data["slots"].append(retained)
        write(private / "theorem-extension-inputs.json", data)
        private_record, public_record = load(private / "record.json"), load(public / "record.json")
        private_record["theorem_extension_inputs"] = descriptor(private, private / "theorem-extension-inputs.json")
        projection = {"schema": "math-gauge.theorem-extension-public-evidence/v1",
            "benchmark_version": "0.6.0", "attempt_labels": ["A1"], "research_invitation_included": False,
            "public_cases": 2, "private_cases": 3, "records": public_rows,
            "combined_source_sha256": digest(private / "theorem-extension-inputs.json"),
            "human_review": "pending", "formal_comparison_eligible": False}
        write(public / "theorem-extension-evidence.json", projection)
        public_record["theorem_extension_evidence"] = descriptor(public, public / "theorem-extension-evidence.json")
        write(private / "record.json", private_record)
        write(public / "record.json", public_record)


def configure_current(private_root, config, public, private):
    """Refresh current projections; frozen historical inputs are not rewritten."""
    extension = validate_policy(load(ROOT / "protocol/theorem-extension-policy.json"))
    policy = load(ROOT / "protocol/scoring-policy.json")
    policy["version"] = "0.6.0"
    policy["theorem_extension"] = extension
    leaf = next(c for c in policy["subcategories"] if c["id"] == "theorem-extension")
    leaf.update(source_components=["theorem-extension"], public_tasks=2, private_tasks=3,
                families=5, status="active")
    policy["scope"].update(public_tasks=22, private_tasks=6, tasks=28, parent_families=24,
                           initial_slots=28, public_initial_slots=22)
    write(ROOT / "protocol/scoring-policy.json", policy)
    profile = load(ROOT / "protocol/benchmark-profile.json")
    profile["suite"]["sha256"] = public.sha256
    profile["assessment_policy"] = policy
    ids = [row["case_id"] for row in config["cases"] if row["visibility"] == "public"]
    profile["components"] = [row for row in profile["components"] if row["id"] != "theorem-extension"]
    profile["components"].append({"id": "theorem-extension", "title": "命题拓展", "case_ids": ids,
                                  "weight": 10, "aggregation": "family"})
    execution = profile["case_execution_policy"]
    for cid in ids:
        execution["case_tracks"][cid] = "math-gauge.no-tools/v1"
        if cid not in execution["retain_source_runtime_case_ids"]:
            execution["retain_source_runtime_case_ids"].append(cid)
        profile["attempt_schedule"][cid] = ["A1"]
    write(ROOT / "protocol/benchmark-profile.json", profile)
    edition = load(ROOT / "benchmark.json")
    edition["public"].update(suite_sha256=public.sha256, tasks=22, standard_slots=22)
    edition["private"].update(suite_sha256=private.sha256, tasks=6, standard_slots=6)
    edition["combined"].update(tasks=28, standard_slots=28)
    edition["profile"]["sha256"] = digest(ROOT / edition["profile"]["path"])
    edition["scoring_policy"].update(version="0.6.0", sha256=digest(ROOT / "protocol/scoring-policy.json"))
    edition["score_capacity"].update(active=80, under_construction=20)
    edition["theorem_extension_policy"] = {"path": "protocol/theorem-extension-policy.json", "version": "0.1.0",
                                           "sha256": digest(ROOT / "protocol/theorem-extension-policy.json")}
    for key, filename in (("result_record_contract", "protocol/result-record.md"),
                          ("result_record_schema", "protocol/result-record.schema.json")):
        edition[key]["sha256"] = digest(ROOT / filename)
    write(ROOT / "benchmark.json", edition)
    release_path = ROOT / "releases/v0.6.0/config.json"
    release = load(release_path)
    release.update(case_count=len(public.cases), slot_count=len(public.cases))
    write(release_path, release)
    private_edition = load(private_root / "benchmark.json")
    private_edition.update(benchmark_version="0.6.0", case_count=6, standard_slots=6,
                           combined_standard_slots=28, scoring_method_version="0.6.0")
    private_edition.pop("version", None)
    private_edition.pop("tasks", None)
    private_edition["theorem_extension"] = {"public_cases": 2, "private_cases": 3,
        "formal_attempts": ["A1"], "research_invitation": False, "scoring_method": "0.6.0"}
    private_edition["suite_sha256"] = private.sha256
    private_edition["score_capacity"].update(active=80, under_construction=20)
    private_edition["case_selection"]["source"] = "shared20-public/3-private legacy selection plus2-public/3-private theorem extension"
    write(private_root / "benchmark.json", private_edition)

    from scripts import catalog
    taxonomy = load(ROOT / "cases/taxonomy.json")
    for suite in taxonomy["source_suites"]:
        suite.update(suite_sha256=public.sha256, paper_count=len(public.cases))
    _, sources = catalog.load_sources(ROOT, taxonomy)
    taxonomy["scope"].update(paper_count=len(sources),
        written_proof_papers=sum(s["contract"]["kind"] == "written_proof" for s in sources.values()),
        proof_criteria=sum(len(s["contract"].get("criteria", [])) for s in sources.values()))
    taxonomy["paper_assignments"] = [a for a in taxonomy["paper_assignments"] if a["case_id"] not in ids]
    for cid in ids:
        source = sources[cid]
        focus_ids = ["F06", "F01", "F04"] if cid == ids[0] else ["F06", "F07", "F04"]
        taxonomy["paper_assignments"].append({"case_id": cid, "version": "0.1.0",
            "source_bindings": source["source_bindings"],
            "focus": [{"focus_id": fid, "role": "primary" if i == 0 else "secondary",
                "evidence": [{"criterion_id": "complete-structure",
                    "note": "只按首答实际交付核验构造与结构、适用条件和严格结论；接受有效替代路线。",
                    "contract_pointer": "/criteria/2/required_evidence",
                    "task_locator": {"path": source["paths"]["task"], "line": 1,
                                      "applies_to": "whole-paper"}}]} for i, fid in enumerate(focus_ids)],
            "classification_review": {"status": "ai-reviewed", "human": "pending"}})
    write(ROOT / "cases/taxonomy.json", taxonomy)
    index, document = catalog.build(ROOT)
    write(ROOT / "cases/catalog.json", index)
    (ROOT / "cases/by-focus.md").write_text(document)
    (ROOT / "cases/README.md").write_text(catalog.render_index(index))

    packet = ROOT / "protocol/reliability"
    selection = load(packet / "selection.json")
    selection["source_suite_sha256"] = public.sha256
    write(packet / "selection.json", selection)
    schedule = load(packet / "schedule.json")
    for cid in ids:
        if not any(row["case_id"] == cid for row in schedule["slots"]):
            schedule["slots"].append({"ordinal_per_model": len(schedule["slots"]) + 1,
                "slot_id": cid + ":A1", "case_id": cid, "kind": "independent", "attempt_label": "A1",
                "context": "fresh", "parent_slot": None, "message_id": None,
                "status": "planned", "response_sha256": None, "grade": None})
    write(packet / "schedule.json", schedule)
    plan = load(packet / "plan.json")
    plan["planned_slots_per_model"] = 22
    plan["assessment_method_version"] = "0.6.0"
    plan["attempt_schedule"] = {cid: ["A1"] for cid in public.cases}
    from scripts.validate_protocol import check_candidate
    with tempfile.TemporaryDirectory(prefix="math-gauge-adoption-projection-") as temporary:
        plan["cases"] = [check_candidate(public, case, Path(temporary) / cid,
                                          selected_ids=plan["repeat_case_ids"])
                         for cid, case in public.cases.items()]
    for item in plan.get("suites", []):
        if "sha256" in item:
            item["sha256"] = public.sha256
        if "suite_sha256" in item:
            item["suite_sha256"] = public.sha256
        if "paper_count" in item:
            item["paper_count"] = 22
        if isinstance(item.get("cases"), int):
            item["cases"] = 22
    plan["design_bindings"]["schedule_sha256"] = digest(packet / "schedule.json")
    write(packet / "plan.json", plan)
    configure_combined(private_root, profile, public, private)


def configure_combined(private_root, public_profile, public, private):
    """Keep the companion's current profile bound to the complete A1 pool."""
    from math_gauge.benchmarks import BenchmarkProfile, build_plan
    protocol = private_root / "protocol"
    composition = {"schema": "math-gauge.suite-composition/v1", "id": "math-gauge-combined",
        "version": "0.6.0", "suites": [{"path": os.path.relpath(s.root, protocol),
            "id": s.metadata["id"], "version": s.metadata["version"], "sha256": s.sha256}
            for s in (public, private)]}
    write(protocol / "suite-composition.json", composition)
    suite = Suite.load(protocol / "suite-composition.json")
    profile = copy.deepcopy(public_profile)
    profile["id"] = "math-gauge-assessment-combined"
    profile["suite"] = {"id": suite.metadata["id"], "version": suite.metadata["version"], "sha256": suite.sha256}
    for cid, case in private.cases.items():
        component = "theorem-extension" if private.case_manifest(cid).startswith("theorem-extension/") else "proofs"
        next(c for c in profile["components"] if c["id"] == component)["case_ids"].append(cid)
        profile["attempt_schedule"][cid] = ["A1"]
        profile["case_execution_policy"]["case_tracks"][cid] = "math-gauge.no-tools/v1"
        profile["case_execution_policy"]["retain_source_runtime_case_ids"].append(cid)
    for name in ("lean-tool-budget-policy.json", "scoring-policy.json", "strict-scoring-policy.json"):
        (protocol / name).write_bytes((ROOT / "protocol" / name).read_bytes())
    packet = protocol / "reliability"
    packet.mkdir(exist_ok=True)
    selection = load(ROOT / "protocol/reliability/selection.json")
    selection["source_suite_sha256"] = suite.sha256
    write(packet / "selection.json", selection)
    write(packet / "prompts.json", load(ROOT / "protocol/reliability/prompts.json"))
    schedule = load(ROOT / "protocol/reliability/schedule.json")
    for cid in private.cases:
        schedule["slots"].append({"ordinal_per_model": len(schedule["slots"]) + 1,
            "slot_id": cid + ":A1", "case_id": cid, "kind": "independent", "attempt_label": "A1",
            "context": "fresh", "parent_slot": None, "message_id": None,
            "status": "planned", "response_sha256": None, "grade": None})
    write(packet / "schedule.json", schedule)
    write(protocol / "benchmark-profile.json", profile)
    loaded = BenchmarkProfile.load(protocol / "benchmark-profile.json", suite)
    plan = build_plan(loaded, suite)
    if len(plan["slots"]) != 28 or any(row["attempt_label"] != "A1" for row in plan["slots"]):
        raise ValueError("The current combined profile must contain28 independent A1 slots only")
    edition = load(private_root / "benchmark.json")
    edition["composition"] = {"path": "protocol/suite-composition.json", "suite_sha256": suite.sha256,
                               "tasks": 28, "sha256": digest(protocol / "suite-composition.json")}
    edition["profile"] = {"path": "protocol/benchmark-profile.json",
                          "sha256": digest(protocol / "benchmark-profile.json"), "scope": "combined"}
    write(private_root / "benchmark.json", edition)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--private-root", type=Path, required=True)
    parser.add_argument("--configuration", type=Path, required=True)
    args = parser.parse_args()
    private_root = args.private_root.resolve()
    config = load(args.configuration)
    public, private = import_cases(private_root, config)
    configure_current(private_root, config, public, private)
    retain_answers(private_root, config, public, private)
    print(json.dumps({"public_cases": len(public.cases), "private_cases": len(private.cases),
                      "new_model_calls": 0, "research_invitation_in_scoring": False}))


if __name__ == "__main__":
    main()
