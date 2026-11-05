#!/usr/bin/env python3
"""Generate the current case catalog and operator-only navigation.

Taxonomy owns editorial classification; case contracts own mathematical requirements.
This command only reads case material and emits catalog/navigation projections.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TAXONOMY = "cases/taxonomy.json"
CATALOG = "cases/catalog.json"
DOCUMENT = "cases/by-focus.md"
INDEX = "cases/README.md"
OUTPUTS = (CATALOG, DOCUMENT, INDEX)
FOCUS_IDS = tuple(f"F{n:02}" for n in range(1, 10))
SUITES = (("default", "cases/suite.json"),)
SUITE_ROOTS = tuple(manifest for _, manifest in SUITES)
CATEGORIES = (
    ("proofs", "书面证明、反例与构造"),
    ("lean-audit", "Lean 语义审计"),
    ("lean-formalization", "大Lean形式化梯度"),
    ("answer-review", "真实答卷审阅"),
)
FOCUS_FILES = {TAXONOMY, *OUTPUTS, "scripts/catalog.py"}
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT))
from math_gauge.catalog import Suite  # noqa: E402


def json_text(data: dict) -> str:
    return json.dumps(data, ensure_ascii=False, indent=2) + "\n"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def local_file(root: Path, name: str) -> Path:
    require(isinstance(name, str) and bool(name), "Invalid local path")
    relative = Path(name)
    require(
        not relative.is_absolute() and ".." not in relative.parts,
        f"Unsafe local path: {name}",
    )
    result = (root / relative).resolve()
    require(result.is_relative_to(root), f"Path escapes repository: {name}")
    require(result.is_file(), f"Missing source file: {name}")
    return result


def stage_headings(task: Path) -> dict:
    found = {}
    for number, line in enumerate(task.read_text().splitlines(), 1):
        match = re.match(r"##\s+(S\d+)(?:\s|\u3000)", line)
        if match:
            require(match[1] not in found, f"Duplicate task stage: {match[1]}")
            found[match[1]] = {"line": number, "heading": line}
    return found


def task_goals(task: Path) -> dict:
    return {f"goal{match[1]}": number
            for number, line in enumerate(task.read_text().splitlines(), 1)
            if (match := re.match(r"^(\d+)\.\s", line))}


def assessment_label(entry: dict) -> tuple[int, str]:
    if entry["kind"] == "written_proof":
        return entry["proof_criterion_count"], "评审判准"
    if entry["kind"] in {"answer_review", "semantic_audit"}:
        return entry["review_dimension_count"], "审阅维度"
    return entry["stage_count"], "义务" if entry["kind"] == "chapter_formalization" else "阶段"


def validate_assignment(assignment: dict, source: dict) -> None:
    cid = source["case"]["id"]
    case, contract = source["case"], source["contract"]
    require(assignment.get("version") == case["version"], f"{cid}: version drift")
    require(
        assignment.get("source_bindings") == source["source_bindings"],
        f"{cid}: source drift; review the classification before rebinding it",
    )
    review = assignment.get("classification_review", {})
    require(review.get("human") == "pending", f"{cid}: human review must stay pending")
    require(
        isinstance(review.get("status"), str) and review["status"].startswith("ai-"),
        f"{cid}: classification must identify its AI review status",
    )
    tags = assignment.get("focus", [])
    require(isinstance(tags, list) and 3 <= len(tags) <= 5, f"{cid}: need 3-5 tags")
    require(
        sum(tag.get("role") == "primary" for tag in tags) == 1
        and tags[0].get("role") == "primary"
        and all(tag.get("role") == "secondary" for tag in tags[1:]),
        f"{cid}: exactly one leading primary and 2-4 secondary tags required",
    )
    ids = [tag.get("focus_id") for tag in tags]
    require(len(ids) == len(set(ids)), f"{cid}: duplicate focus tag")
    require(all(fid in FOCUS_IDS for fid in ids), f"{cid}: unknown focus tag")
    is_review = contract["kind"] in {"answer_review", "semantic_audit"}
    is_written = contract["kind"] == "written_proof"
    unit_key = "criterion_id" if is_written else "dimension_id" if is_review else "stage_id"
    collection = "criteria" if is_written else "dimensions" if is_review else "stages"
    units = contract[collection]
    stages = {stage["id"]: (i, stage) for i, stage in enumerate(units)}
    for tag in tags:
        evidence = tag.get("evidence", [])
        require(isinstance(evidence, list) and evidence, f"{cid}: tag lacks evidence")
        seen = set()
        for item in evidence:
            sid = item.get(unit_key)
            require(sid in stages and sid not in seen, f"{cid}: invalid evidence ID {sid}")
            seen.add(sid)
            number, stage = stages[sid]
            if tag["focus_id"] == "F09":
                require(
                    stage.get("lean_required") is True,
                    f"{cid}/{sid}: F09 evidence does not require candidate Lean",
                )
            note = item.get("note")
            require(
                isinstance(note, str) and 0 < len(note.strip()) <= 400,
                f"{cid}/{sid}: a brief evidence note is required",
            )
            require(
                item.get("contract_pointer") == f"/{collection}/{number}/required_evidence",
                f"{cid}/{sid}: incorrect contract pointer",
            )
            locator = item.get("task_locator", {})
            require(locator.get("path") == source["paths"]["task"], f"{cid}: task drift")
            if is_written:
                applies_to = locator.get("applies_to")
                goals = source.get("goals", {})
                require(
                    applies_to == "whole-paper" and locator.get("line") == 1
                    or applies_to in goals and locator.get("line") == goals[applies_to],
                    f"{cid}/{sid}: written-proof final-goal locator drift",
                )
            elif is_review:
                require(
                    locator.get("applies_to") == ("whole-semantic-audit" if contract["kind"] == "semantic_audit" else "whole-answer-review") and locator.get("line") == 1,
                    f"{cid}/{sid}: answer-review locator drift",
                )
            elif contract["kind"] == "progressive":
                require(
                    sid in source["headings"]
                    and {key: locator.get(key) for key in ("line", "heading")}
                    == source["headings"][sid],
                    f"{cid}/{sid}: task heading locator drift",
                )
            else:
                require(
                    item.get("obligations_locator")
                    == {"path": source["obligations_path"], "id": sid}
                    and item.get("source_anchor") == stage["source_anchor"],
                    f"{cid}/{sid}: obligation locator drift",
                )
                require(
                    locator.get("applies_to") == "whole-paper-delivery"
                    and locator.get("line") == 3,
                    f"{cid}/{sid}: whole-paper task locator drift",
                )


def load_sources(root: Path, taxonomy: dict) -> tuple[list, dict]:
    declared = taxonomy.get("source_suites", [])
    suites = [(membership, manifest, Suite.load(root / manifest))
              for membership, manifest in SUITES]
    summaries = [{"root": "cases", "manifest": manifest, "membership": membership,
                  "id": suite.metadata["id"], "version": suite.metadata["version"],
                  "suite_sha256": suite.sha256, "paper_count": len(suite.cases)}
                 for membership, manifest, suite in suites]
    require(declared == summaries, "cases: suite drift; review before rebinding")
    sources = {}
    for membership, suite_manifest, suite in suites:
        for manifest in suite.metadata["cases"]:
            case_path = f"cases/{manifest}"
            raw = json.loads(local_file(root, case_path).read_text())
            cid = raw["id"]
            case = suite.cases[cid]  # Shared runner resolves case-relative manifests.
            category = Path(manifest).parent.parent.name
            require(category in {item[0] for item in CATEGORIES}, f"{cid}: unknown category")
            canonical_path = Path(category) / cid / "case.json"
            allowed_paths = {canonical_path}
            if membership == "reserve":
                allowed_paths.add(Path("reserve") / canonical_path)
            require(Path(manifest) in allowed_paths, f"{cid}: suite membership and directory differ")
            require(raw.get("path_base") == "case", f"{cid}: case-relative paths required")
            paths = {"case": case_path, "task": f"cases/{case['task']}",
                     "contract": f"cases/{case['group_contract']}"}
            contract = json.loads(local_file(root, paths["contract"]).read_text())
            source = {"case": case, "contract": contract, "paths": paths,
                      "category": category, "suite_root": "cases", "suite_sha256": suite.sha256,
                      "membership": membership, "suite_manifest": suite_manifest,
                      "source_bindings": {name: digest(local_file(root, name)) for name in paths.values()},
                      "headings": stage_headings(local_file(root, paths["task"])),
                      "goals": task_goals(local_file(root, paths["task"]))}
            if contract["kind"] == "chapter_formalization":
                source["obligations_path"] = str(Path(case_path).parent / "candidate/obligations.json")
                path = local_file(root, source["obligations_path"])
                obligations = json.loads(path.read_text())
                public_ids = [item["id"] for item in obligations["obligations"]]
                contract_ids = [item["id"] for item in contract["stages"]]
                require(obligations["case_id"] == cid and obligations["version"] == case["version"]
                        and len(public_ids) == len(set(public_ids)) and set(public_ids) == set(contract_ids),
                        f"{cid}: public obligation coverage drift")
                source["source_bindings"][source["obligations_path"]] = digest(path)
            inputs = {paths["task"]} | {f"cases/{item['source']}" for item in case["solver_files"]}
            require(not inputs & FOCUS_FILES, f"{cid}: focus data entered candidate inputs")
            request = suite.request(case)
            encoded = json.dumps(request, sort_keys=True, ensure_ascii=False, separators=(",", ":")).encode()
            source["candidate_projection_sha256"] = hashlib.sha256(encoded).hexdigest()
            sources[cid] = source
    return summaries, sources


def render_document(catalog: dict, taxonomy: dict) -> str:
    def link(label: str, target: str) -> str:
        return f"[{label}]({os.path.relpath(target, 'cases')})"

    counts = catalog["counts"]
    lines = [
        "# 按考察重点选卷",
        "",
        f"本目录覆盖当前{counts['papers']}份相关任务：{counts['mathematical_papers']}份数学卷与{counts['answer_review_tasks']}份真实答卷审阅。默认任务关联{counts['default_parent_families']}个母题家族。当前数学任务含{counts['default_obligations']}项阶段或章节义务。另有{counts.get('proof_criteria', 0)}项书面证明评审判准。阶段、义务、评审判准及审阅维度均不能当作独立试题。",
        "",
        "分类是AI审查建议；源题全部仍为 **draft / human pending**。本目录不产生模型调用、数学裁定或新增判卷要求，也不证明作者或候选Lean覆盖。完整要求以唯一题面和合同为准。",
        "",
        "每份任务恰有1个主重点和2–4个次重点。主重点构成互斥阅读索引；多标签层可以重叠，数量不能相加。数学任务的证据指向实际阶段、义务或最终目标的评审判准，审阅任务指向审阅维度，不能据此增加证明路线或Lean交付义务。这些标签没有另行冻结子分数，不重复加权。",
        "",
        "中性自查、支持/怀疑立场和重复轮次属于执行维度，见[可靠性执行协议](../protocol/reliability-execution.md)。数学主题和任务类型是其他交叉索引。",
        "",
        "本页仅供出题侧，不能附入候选输入；候选材料继续由共享runner按每题显式投影生成。",
        "",
        "| 考察重点 | 主重点任务数 | 含该标签任务数 |",
        "| --- | ---: | ---: |",
    ]
    for definition in taxonomy["definitions"]:
        fid = definition["id"]
        count = catalog["focus_counts"][fid]
        lines.append(
            f"| {fid} {definition['label']} | {count['primary_papers']} | "
            f"{count['all_tagged_papers']} |"
        )
    for definition in taxonomy["definitions"]:
        fid = definition["id"]
        lines += ["", f"## {fid} {definition['label']}", "", definition["includes"], "", definition["boundary"]]
        for role, label in (("primary", "主重点"), ("secondary", "次重点")):
            selected = [
                (entry, tag)
                for entry in catalog["entries"]
                for tag in entry["focus"]
                if tag["focus_id"] == fid and tag["role"] == role
            ]
            lines += ["", f"### {label} · {len(selected)}份（完整题库）", "", "| 任务 | 成员 | 版本与规模 | 实际阶段、义务、评审判准或审阅维度证据 |", "| --- | --- | --- | --- |"]
            for entry, tag in selected:
                count, unit = assessment_label(entry)
                evidence = "；".join(
                    f"**{item.get('criterion_id', item.get('dimension_id', item.get('stage_id')))}**：{item['note'].rstrip('。')}"
                    for item in tag["evidence"]
                ) + "。"
                title = link(f"{entry['case_id']} · {entry['title']}", entry["paths"]["task"])
                contract = link("合同", entry["paths"]["contract"])
                lines.append(
                    f"| {title} · {contract} | {'默认' if entry['membership'] == 'default' else '后备'} | {entry['version']} · "
                    f"{count}{unit} | {evidence} |"
                )
    lines += [
        "",
        "证据短句仅描述实际需求。F07不强制合同参考图的唯一路线；有效短证、合并声明、独立重证和替代证明仍按原合同接受。",
        "",
        "[分类源](taxonomy.json) · [机器目录与源散列](catalog.json) · [全部试卷](README.md)",
        "",
    ]
    return "\n".join(lines)


def render_index(catalog: dict) -> str:
    counts = catalog["counts"]
    suite_version = next(item["version"] for item in catalog["suites"] if item["membership"] == "default")
    lines = ["# 当前试卷", "",
             f"{suite_version}默认题集 `cases/suite.json` 含{counts['default_papers']}份相关任务，关联{counts['default_parent_families']}个母题家族。完整题库含{counts['mathematical_papers']}份数学卷与{counts['answer_review_tasks']}份真实答卷审阅，共{counts['default_obligations'] + counts['reserve_obligations']}项阶段或章节义务，另有{counts.get('proof_criteria', 0)}项书面证明评审判准。相关任务、判准及审阅维度不构成独立数学家族。", "",
             "材料具参考、判准、来源及AI审核记录，题目与当前答卷仍为 **human pending**。已有数学答卷及8份候选审阅答卷；AR纳入、评分与统一重评属于观察结果后的方法变更，详见[审阅说明](../docs/answer-review.md)与[当前结果](../docs/results.md)。已发布资产保持原样。", "",
             "题面与附件由共享runner按 `case.json` 显式投影；本目录、分类、参考、评分和审核记录均为出题侧材料。参考与既有历史继续公开以供透明复核，不进入 solver 题包，也不构成未公开留出集。", "",
             "[按考察重点选卷](by-focus.md) · [机器目录](catalog.json) · [分类定义与逐项依据](taxonomy.json) · [来源](../SOURCES.md) · [验证状态](../docs/verification.md)"]
    for category in catalog["categories"]:
        lines += ["", f"## {category['label']} · {category['default_count']}份", "",
                  "| 试卷 | 任务 | 必答规模 | 完整材料 |", "| --- | --- | ---: | --- |"]
        for entry in catalog["entries"]:
            if entry["category"] != category["id"] or entry["membership"] != "default":
                continue
            paths = entry["paths"]
            task = os.path.relpath(paths["task"], "cases")
            folder = os.path.relpath(str(Path(paths["case"]).parent), "cases")
            count, unit = assessment_label(entry)
            contract_link = os.path.relpath(paths["contract"], "cases")
            extra = (f" · [作者Lean]({folder}/formal/COVERAGE.md)"
                     if entry["source_review"].get("formalization", {}).get("evidence") else "")
            review_name = "review.json" if (ROOT / paths["case"]).parent.joinpath("review.json").is_file() else "integration-review.json"
            lines.append(f"| [{entry['case_id']} · {entry['title']}]({task}) | "
                         f"{entry['task_kind']} | "
                         f"{count}{unit} | [合同]({contract_link}) · "
                         f"[参考]({folder}/reference.md) · [评分]({folder}/rubric.json) · "
                         f"[题包复核]({folder}/{review_name}){extra} |")
    lines += ["", "旧题和备选题通过Git历史恢复。审阅可用独立清单answer-review-suite.json选择。",
              "", "所有路径和候选输入散列由 `python3 scripts/catalog.py` 从当前合同生成；`--check`只读核验。", ""]
    return "\n".join(lines)


def build(root: Path = ROOT, *, taxonomy_data: dict | None = None) -> tuple[dict, str]:
    root = root.resolve()
    raw = local_file(root, TAXONOMY).read_bytes()
    taxonomy = json.loads(raw) if taxonomy_data is None else taxonomy_data
    if taxonomy_data is not None:
        raw = json_text(taxonomy).encode()
    require(taxonomy.get("schema") == "math-gauge.focus-taxonomy/v1", "Invalid taxonomy schema")
    require(taxonomy.get("operator_only") is True, "Focus taxonomy must be operator-only")
    require(
        [definition.get("id") for definition in taxonomy.get("definitions", [])]
        == list(FOCUS_IDS),
        "Exactly nine ordered focus definitions required",
    )
    for definition in taxonomy["definitions"]:
        require(
            all(isinstance(definition.get(key), str) and definition[key].strip()
                for key in ("label", "includes", "boundary")),
            f"{definition['id']}: incomplete definition",
        )
    suites, sources = load_sources(root, taxonomy)
    assignments = taxonomy.get("paper_assignments", [])
    ids = [item.get("case_id") for item in assignments]
    require(len(ids) == len(set(ids)) == len(sources) and set(ids) == set(sources),
            "Assignments must cover every selected mathematical paper and answer review exactly once")
    entries = []
    for assignment in sorted(assignments, key=lambda item: item["case_id"]):
        cid = assignment["case_id"]
        source = sources[cid]
        validate_assignment(assignment, source)
        case, contract = source["case"], source["contract"]
        entries.append({
            "case_id": cid, "version": case["version"], "title": case["title"],
            "family_id": case.get("family_id") or contract.get("parent_family_id") or cid,
            "kind": contract["kind"],
            "category": source["category"],
            "task_kind": case["task_kind"],
            "sample_unit": "one-complete-answer-review; parent-correlated" if contract["kind"] == "answer_review" else "one-full-paper",
            "parent_family_id": contract.get("parent_family_id", cid),
            "stage_count": len(contract.get("stages", [])),
            "stage_ids": [stage["id"] for stage in contract.get("stages", [])],
            "review_dimension_count": len(contract.get("dimensions", [])),
            "review_dimension_ids": [item["id"] for item in contract.get("dimensions", [])],
            **({"proof_criterion_count": len(contract["criteria"]),
                "proof_criterion_ids": [item["id"] for item in contract["criteria"]]}
               if contract["kind"] == "written_proof" else {}),
            "suite_root": source["suite_root"], "suite_sha256": source["suite_sha256"],
            "suite_manifest": source["suite_manifest"], "membership": source["membership"],
            "paths": source["paths"], "original_sha256": source["source_bindings"],
            "candidate_projection_sha256": source["candidate_projection_sha256"],
            "status": case["status"], "source_review": case["review"],
            "focus": assignment["focus"],
            "classification_review": assignment["classification_review"],
        })
    progressive = [entry for entry in entries if entry["kind"] == "progressive"]
    chapters = [entry for entry in entries if entry["kind"] == "chapter_formalization"]
    answer_reviews = [entry for entry in entries if entry["kind"] == "answer_review"]
    semantic_audits = [entry for entry in entries if entry["kind"] == "semantic_audit"]
    written_proofs = [entry for entry in entries if entry["kind"] == "written_proof"]
    by_id = {entry["case_id"]: entry for entry in entries}
    def parent_family(entry):
        family = entry["parent_family_id"] if entry["kind"] == "answer_review" else entry["family_id"]
        return by_id[family]["family_id"] if family in by_id else family

    scope = {
        "id": "complete-case-bank", "paper_count": len(entries),
        "progressive_papers": len(progressive),
        "progressive_stages": sum(entry["stage_count"] for entry in progressive),
        "chapter_papers": len(chapters),
        "chapter_obligations": {entry["case_id"]: entry["stage_count"] for entry in chapters},
        "answer_review_tasks": len(answer_reviews),
        "answer_review_dimensions": sum(entry["review_dimension_count"] for entry in answer_reviews),
        **({"semantic_audit_tasks": len(semantic_audits),
            "semantic_audit_dimensions": sum(entry["review_dimension_count"] for entry in semantic_audits)} if semantic_audits else {}),
        "sample_unit": "one full mathematical paper or complete answer review; parent-correlated",
    }
    if written_proofs:
        scope.update(written_proof_papers=len(written_proofs),
                     proof_criteria=sum(entry["proof_criterion_count"] for entry in written_proofs))
    require(taxonomy.get("scope") == scope, "Declared mathematical/review task scope/counts drift")
    primary = Counter(entry["focus"][0]["focus_id"] for entry in entries)
    tagged = Counter(tag["focus_id"] for entry in entries for tag in entry["focus"])
    catalog = {
        "schema": "math-gauge.case-catalog/v1", "version": taxonomy["version"],
        "catalog_status": "ai-classification-suggestions; source-human-review-separate",
        "snapshot_status": "final-catalog-snapshot",
        "operator_only": True, "path_base": "repository root",
        "sample_unit": "one full mathematical paper or complete answer review; parent-correlated",
        "candidate_input_policy": taxonomy["candidate_input_policy"],
        "taxonomy": TAXONOMY, "taxonomy_sha256": hashlib.sha256(raw).hexdigest(),
        "scope": scope,
        "counts": {
            "papers": len(entries),
            "default_papers": sum(entry["membership"] == "default" for entry in entries),
            "reserve_papers": sum(entry["membership"] == "reserve" for entry in entries),
            "mathematical_papers": len(entries) - len(answer_reviews),
            "answer_review_tasks": len(answer_reviews),
            **({"semantic_audit_tasks": len(semantic_audits),
                "semantic_audit_dimensions": scope["semantic_audit_dimensions"]} if semantic_audits else {}),
            "default_parent_families": len({parent_family(entry) for entry in entries
                                            if entry["membership"] == "default"}),
            **({"written_proof_papers": len(written_proofs), "proof_criteria": scope["proof_criteria"]}
               if written_proofs else {}),
            "default_obligations": sum(e["stage_count"] for e in entries if e["membership"] == "default"),
            "reserve_obligations": sum(e["stage_count"] for e in entries if e["membership"] == "reserve"),
            "progressive_stages": scope["progressive_stages"],
            "chapter_obligations": sum(scope["chapter_obligations"].values()),
            "source_human_approved": sum(entry["source_review"]["human"] == "approved" for entry in entries),
            "model_calls_by_indexer": 0,
        },
        "suites": [dict(item, cases=sorted(cid for cid, source in sources.items()
                                         if source["membership"] == item["membership"])) for item in suites],
        "categories": [{"id": cid, "label": label, "suite": "cases",
                        "count": sum(entry["category"] == cid for entry in entries),
                        "default_count": sum(entry["category"] == cid and entry["membership"] == "default" for entry in entries),
                        "reserve_count": sum(entry["category"] == cid and entry["membership"] == "reserve" for entry in entries),
                        "case_ids": [entry["case_id"] for entry in entries if entry["category"] == cid]}
                       for cid, label in CATEGORIES],
        "focus_counts": {fid: {"primary_papers": primary[fid], "all_tagged_papers": tagged[fid]} for fid in FOCUS_IDS},
        "entries": entries,
        "excluded_execution_axes": taxonomy["excluded_execution_axes"],
        "limitations": [
            "Focus annotations do not change mathematical requirements, truth labels or scoring.",
            "Dependent stages, obligations and source-related variants are not independent trials.",
            "AI classification, mathematical review, Lean compilation and human approval are separate evidence.",
            "No model result, author Lean coverage or experimental discrimination is inferred by this index.",
        ],
    }
    require(sum(item["count"] for item in catalog["categories"]) == len(entries)
            and all(item["paper_count"] == sum(entry["membership"] == item["membership"]
                                              for entry in entries) for item in suites),
            "Category or suite membership counts drift")
    document = render_document(catalog, taxonomy)
    generated = {(root / name).resolve() for name in OUTPUTS}
    for target in re.findall(r"\]\(([^)]+)\)", document):
        destination = (root / "cases" / target).resolve()
        require("://" not in target and destination.is_relative_to(root)
                and (destination.is_file() or destination in generated),
                f"Broken focus index link: {target}")
    return catalog, document


def refresh(root: Path = ROOT, *, check: bool = False) -> dict:
    catalog, document = build(root)
    outputs = {CATALOG: json_text(catalog), DOCUMENT: document, INDEX: render_index(catalog)}
    if check:
        for name, expected in outputs.items():
            require(local_file(root, name).read_text() == expected, f"Stale focus output: {name}")
    else:
        for name, value in outputs.items():
            (root / name).write_text(value)
    return {"status": "passed", "mode": "check" if check else "refresh",
            "catalog": CATALOG, "catalog_sha256": digest(root / CATALOG),
            "counts": catalog["counts"], "scope": catalog["scope"],
            "model_calls": 0}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Read-only source, evidence and deterministic output check.")
    args = parser.parse_args()
    try:
        print(json.dumps(refresh(check=args.check), ensure_ascii=False))
    except (ValueError, KeyError, TypeError) as error:
        parser.exit(1, f"Case catalog check failed: {error}\n")


if __name__ == "__main__":
    main()
