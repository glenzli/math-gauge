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
SUITE_ROOTS = ("cases",)
CATEGORIES = (
    ("proofs", "书面证明、反例与构造", 29),
    ("lean-audit", "Lean 语义审计", 6),
    ("lean-construction", "Lean 生成与修复", 6),
    ("chapters", "整章形式化", 2),
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
    stages = {stage["id"]: (i, stage) for i, stage in enumerate(contract["stages"])}
    for tag in tags:
        evidence = tag.get("evidence", [])
        require(isinstance(evidence, list) and evidence, f"{cid}: tag lacks evidence")
        seen = set()
        for item in evidence:
            sid = item.get("stage_id")
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
                item.get("contract_pointer") == f"/stages/{number}/required_evidence",
                f"{cid}/{sid}: incorrect contract pointer",
            )
            locator = item.get("task_locator", {})
            require(locator.get("path") == source["paths"]["task"], f"{cid}: task drift")
            if contract["kind"] == "progressive":
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
    require([item.get("root") for item in declared] == list(SUITE_ROOTS),
            "The catalog must use the single canonical cases suite")
    suite = Suite.load(root / "cases")
    summary = {"root": "cases", "id": suite.metadata["id"],
               "version": suite.metadata["version"], "suite_sha256": suite.sha256,
               "paper_count": len(suite.cases)}
    require(declared == [summary], "cases: suite drift; review before rebinding")
    sources = {}
    for manifest in suite.metadata["cases"]:
        case_path = f"cases/{manifest}"
        raw = json.loads(local_file(root, case_path).read_text())
        cid = raw["id"]
        case = suite.cases[cid]  # Shared runner resolves case-relative manifests.
        category = Path(manifest).parts[0]
        require(category in {item[0] for item in CATEGORIES}, f"{cid}: unknown category")
        require(raw.get("path_base") == "case", f"{cid}: case-relative paths required")
        paths = {"case": case_path, "task": f"cases/{case['task']}",
                 "contract": f"cases/{case['group_contract']}"}
        contract = json.loads(local_file(root, paths["contract"]).read_text())
        source = {"case": case, "contract": contract, "paths": paths,
                  "category": category, "suite_root": "cases", "suite_sha256": suite.sha256,
                  "source_bindings": {name: digest(local_file(root, name)) for name in paths.values()},
                  "headings": stage_headings(local_file(root, paths["task"]))}
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
    return [summary], sources


def render_document(catalog: dict, taxonomy: dict) -> str:
    def link(label: str, target: str) -> str:
        return f"[{label}]({os.path.relpath(target, 'cases')})"

    lines = [
        "# 按考察重点选卷",
        "",
        "本目录覆盖当前43份试卷：41份递进题组含246阶段，另2份整章试卷各含34/92项义务。每份完整试卷是一个样本，阶段与义务不能当作独立试题。",
        "",
        "分类是AI审查建议；源题全部仍为 **draft / human pending**。本目录不产生模型调用、数学裁定或新增判卷要求，也不证明作者或候选Lean覆盖。完整要求以唯一题面和合同为准。",
        "",
        "每卷恰有1个主重点和2–4个次重点。主重点构成互斥阅读索引；多标签层可以重叠，卷数不能相加。按重点统计仍以完整试卷为分母，保留未运行、未决和环境失败。",
        "",
        "中性自查、支持/怀疑立场和重复轮次属于执行维度，见[可靠性执行协议](../protocol/reliability-execution.md)。数学主题和任务类型是其他交叉索引。",
        "",
        "本页仅供出题侧，不能附入候选输入；候选材料继续由共享runner按每题显式投影生成。",
        "",
        "| 考察重点 | 主重点卷数 | 含该标签卷数 |",
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
            lines += ["", f"### {label} · {len(selected)}卷", "", "| 试卷 | 版本与规模 | 实际阶段或义务证据 |", "| --- | --- | --- |"]
            for entry, tag in selected:
                unit = "义务" if entry["kind"] == "chapter_formalization" else "阶段"
                evidence = "；".join(
                    f"**{item['stage_id']}**：{item['note'].rstrip('。')}"
                    for item in tag["evidence"]
                ) + "。"
                title = link(f"{entry['case_id']} · {entry['title']}", entry["paths"]["task"])
                contract = link("合同", entry["paths"]["contract"])
                lines.append(
                    f"| {title} · {contract} | {entry['version']} · "
                    f"{entry['stage_count']}{unit} | {evidence} |"
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
    lines = ["# 当前试卷", "",
             "唯一题集为 `cases/suite.json`，共43份完整试卷。每组或每章是一份相关样本；246阶段与126项章节义务合计372项审核义务，不能记作372道独立题。", "",
             "材料已具数学参考、逐项判准、来源及AI审核记录；全部为 **draft / human pending**。`draft` 是待人工审定的生命周期状态。当前没有候选模型答卷或通过率。", "",
             "题面与附件由共享runner按 `case.json` 显式投影；本目录、分类、参考、评分和审核记录均为出题侧材料。", "",
             "[按考察重点选卷](by-focus.md) · [机器目录](catalog.json) · [分类定义与逐项依据](taxonomy.json) · [来源](../SOURCES.md) · [验证状态](../docs/verification.md)"]
    for category in catalog["categories"]:
        lines += ["", f"## {category['label']} · {category['count']}份", "",
                  "| 试卷 | 任务 | 必答规模 | 完整材料 |", "| --- | --- | ---: | --- |"]
        for entry in catalog["entries"]:
            if entry["category"] != category["id"]:
                continue
            paths = entry["paths"]
            task = os.path.relpath(paths["task"], "cases")
            folder = os.path.relpath(str(Path(paths["case"]).parent), "cases")
            unit = "义务" if entry["kind"] == "chapter_formalization" else "阶段"
            lines.append(f"| [{entry['case_id']} · {entry['title']}]({task}) | {entry['task_kind']} | "
                         f"{entry['stage_count']}{unit} | [合同]({folder}/contract.json) · "
                         f"[参考]({folder}/reference.md) · [评分]({folder}/rubric.json) · "
                         f"[题包复核]({folder}/review.json) · [作者Lean]({folder}/formal/COVERAGE.md) |")
    lines += ["", "所有路径和候选输入散列由 `python3 scripts/catalog.py` 从当前合同生成；`--check` 只读核验。", ""]
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
    require(len(ids) == len(set(ids)) == 43 and set(ids) == set(sources), "Assignments must cover exactly the 43 current papers once")
    entries = []
    for assignment in sorted(assignments, key=lambda item: item["case_id"]):
        cid = assignment["case_id"]
        source = sources[cid]
        validate_assignment(assignment, source)
        case, contract = source["case"], source["contract"]
        entries.append({
            "case_id": cid, "version": case["version"], "title": case["title"],
            "family_id": case["family_id"], "kind": contract["kind"],
            "category": source["category"],
            "task_kind": case["task_kind"], "sample_unit": "one-full-paper",
            "stage_count": len(contract["stages"]),
            "stage_ids": [stage["id"] for stage in contract["stages"]],
            "suite_root": source["suite_root"], "suite_sha256": source["suite_sha256"],
            "paths": source["paths"], "original_sha256": source["source_bindings"],
            "candidate_projection_sha256": source["candidate_projection_sha256"],
            "status": case["status"], "source_review": case["review"],
            "focus": assignment["focus"],
            "classification_review": assignment["classification_review"],
        })
    progressive = [entry for entry in entries if entry["kind"] == "progressive"]
    chapters = [entry for entry in entries if entry["kind"] == "chapter_formalization"]
    scope = {
        "id": "current-benchmark", "paper_count": len(entries),
        "progressive_papers": len(progressive),
        "progressive_stages": sum(entry["stage_count"] for entry in progressive),
        "chapter_papers": len(chapters),
        "chapter_obligations": {entry["case_id"]: entry["stage_count"] for entry in chapters},
        "sample_unit": "one full paper",
    }
    require(taxonomy.get("scope") == scope, "Declared 43-paper scope/counts drift")
    primary = Counter(entry["focus"][0]["focus_id"] for entry in entries)
    tagged = Counter(tag["focus_id"] for entry in entries for tag in entry["focus"])
    catalog = {
        "schema": "math-gauge.case-catalog/v1", "version": taxonomy["version"],
        "catalog_status": "ai-classification-suggestions; source-human-review-separate",
        "snapshot_status": "final-catalog-snapshot",
        "operator_only": True, "path_base": "repository root", "sample_unit": "one full paper",
        "candidate_input_policy": taxonomy["candidate_input_policy"],
        "taxonomy": TAXONOMY, "taxonomy_sha256": hashlib.sha256(raw).hexdigest(),
        "scope": scope,
        "counts": {
            "papers": len(entries), "progressive_stages": scope["progressive_stages"],
            "chapter_obligations": sum(scope["chapter_obligations"].values()),
            "source_human_approved": sum(entry["source_review"]["human"] == "approved" for entry in entries),
            "model_calls_by_indexer": 0,
        },
        "suites": [dict(item, cases=sorted(sources)) for item in suites],
        "categories": [{"id": cid, "label": label, "suite": "cases",
                        "count": sum(entry["category"] == cid for entry in entries),
                        "case_ids": [entry["case_id"] for entry in entries if entry["category"] == cid]}
                       for cid, label, expected in CATEGORIES],
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
    require([item["count"] for item in catalog["categories"]] == [item[2] for item in CATEGORIES],
            "Category counts drift")
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
