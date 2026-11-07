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
                "human": "pending", "formalization": {"status": "not-performed", "author_coverage_inherited": False,
                    "inherited_parent_evidence": False}},
            "lean_checks": [], "evaluator_files": ["source-rubric.md", "research-policy.json", "provenance.json", "review.json"]})
        write(folder / "provenance.json", {"case_id": cid, "source": "User-supplied candidate package v5",
            "source_task_sha256": old["a1_sha256"], "source_reference_sha256": digest(folder / "reference.md"),
            "source_rubric_sha256": digest(folder / "source-rubric.md"), "repository_visibility": row["visibility"],
            "selection": "Explicit user selection after Terra A1 pilot; two higher A1 cases public, three companion cases private",
            "source_public_availability": "unverified; classical background is not a hidden-holdout claim",
            "post_observation": True, "human_review": "pending", "formal_comparison_eligible": False})
        write(folder / "review.json", {"case_id": cid, "status": "ai-mathematical-material-review-complete",
            "reference": "reference.md", "criteria": "source-rubric.md", "baseline_truth": "true",
            "human_review": "pending", "human": "pending",
            "mathematical": "AI-reviewed mathematical materials; open research criteria; post-observation; human review pending",
            "formalization": {"status": "not-performed", "author_coverage_inherited": False,
                "inherited_parent_evidence": False},
            "lean_verification": "not_performed",
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
            "version": case["version"], "total_weight": 3, **assessment_weights(contract),
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
            "public_cases": len(data["policy"]["public_case_ids"]),
            "private_cases": data["policy"]["private_cases"],
            "research_policy_version": data["policy"]["version"], "records": public_rows,
            "combined_source_sha256": digest(private / "theorem-extension-inputs.json"),
            "human_review": "pending", "formal_comparison_eligible": False}
        write(public / "theorem-extension-evidence.json", projection)
        public_record["theorem_extension_evidence"] = descriptor(public, public / "theorem-extension-evidence.json")
        write(private / "record.json", private_record)
        write(public / "record.json", public_record)


from scripts.current_assessment import configure_current, configure_combined


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--private-root", type=Path, required=True)
    parser.add_argument("--configuration", type=Path, required=True)
    args = parser.parse_args()
    private_root = args.private_root.resolve()
    config = load(args.configuration)
    selected = validate_policy(load(ROOT / "protocol/theorem-extension-policy.json"))
    if len(config["cases"]) != selected["families"]:
        raise ValueError("This initial source importer cannot replace an expanded component with an older selection; adopt additional evidence incrementally")
    public, private = import_cases(private_root, config)
    configure_current(private_root, config, public, private)
    retain_answers(private_root, config, public, private)
    print(json.dumps({"public_cases": len(public.cases), "private_cases": len(private.cases),
                      "new_model_calls": 0, "research_invitation_in_scoring": False}))


if __name__ == "__main__":
    main()
