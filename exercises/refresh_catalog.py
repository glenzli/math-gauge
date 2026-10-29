#!/usr/bin/env python3
"""Build operator-facing exercise indexes from existing, uniquely owned cases.

This is a documentation/evidence indexer. It neither prepares candidate prompts,
executes models, scores responses, edits cases, nor implements a second runner.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
HERE = ROOT / "exercises"
QUAL = ROOT / "results/full-comparison-20261030/qualification"
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT))
from math_gauge.catalog import Suite


def read(path: Path):
    return json.loads(path.read_text())


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rel(path: Path) -> str:
    return path.resolve().relative_to(ROOT).as_posix()


def link(label: str, path: str, document: Path) -> str:
    target = os.path.relpath(ROOT / path, document.parent)
    return f"[{label}]({target})"


def dump(path: Path, data) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n")


def resolve_evidence(value: str, suite: Path, case_dir: Path) -> Path | None:
    for base in [ROOT, suite, case_dir]:
        p = (base / value).resolve()
        if p.is_file() and p.is_relative_to(ROOT):
            return p
    return None


def check_index() -> dict:
    """Read-only identity and link check; safe after a runtime plan is frozen."""
    catalog_path = HERE / "catalog.json"
    catalog = read(catalog_path)
    qual = ROOT / catalog.get("qualification_root", rel(QUAL))
    gate = read(qual / "gate.json")
    entries = catalog["case_entries"]
    ids = [e["id"] for e in entries]
    assert len(ids) == 41 and len(set(ids)) == 41
    assert set(ids) == {x for s in catalog["suites"] for x in s["cases"]}
    assert set(ids) == {x for s in catalog["sections"] for x in s["cases"]}
    assert gate["catalog_sha256"] == digest(catalog_path)
    suite_hashes = {s["root"]: Suite.load(ROOT / s["root"]).sha256 for s in catalog["suites"]}
    assert all(s["suite_sha256"] == suite_hashes[s["root"]] for s in catalog["suites"])
    files = {}
    for e in entries:
        assert e["id"] == e["case_id"]
        assert e["mathematical_review"]["human"] == "pending"
        assert e["suite_sha256"] == suite_hashes[e["suite_root"]]
        for name, expected in e["original_sha256"].items():
            actual = digest(ROOT / name)
            if actual != expected:
                raise ValueError(f"Catalog source drift: {e['id']} {name}")
            files[name] = expected
    links = 0
    for p in list(HERE.rglob("*.md")) + list(qual.glob("*.md")):
        for target in re.findall(r"\]\(([^)]+)\)", p.read_text()):
            if "://" in target or target.startswith("#"):
                continue
            if not (p.parent / target.split("#")[0]).exists():
                raise ValueError(f"Missing index link: {rel(p)} {target}")
            links += 1
    return {"catalog_sha256": digest(catalog_path), "source_files_checked": len(files),
            "local_links_checked": links, "current_cases": len(entries), "chapters": len(catalog["sections"]),
            "status": "passed", "snapshot_status": catalog["snapshot_status"]}


def main() -> None:
    global QUAL
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--final", action="store_true", help="Record a closed catalog snapshot; does not authorize model execution.")
    ap.add_argument("--check", action="store_true", help="Read-only check of the current frozen index; does not regenerate it.")
    ap.add_argument("--qualification-dir", type=Path, help="New repository-relative qualification destination; preserves earlier frozen qualification records.")
    args = ap.parse_args()
    if args.check:
        print(json.dumps(check_index(), ensure_ascii=False))
        return
    if args.qualification_dir is not None:
        QUAL = (ROOT / args.qualification_dir).resolve()
        if not QUAL.is_relative_to(ROOT) or QUAL == ROOT:
            raise ValueError("Qualification directory must be inside the repository")
        if QUAL.exists() and any(QUAL.iterdir()):
            raise ValueError("Explicit new qualification directory must be empty; preserve existing evidence")
    elif (HERE / "catalog.json").exists():
        QUAL = ROOT / read(HERE / "catalog.json").get("qualification_root", rel(QUAL))
    structure_path = HERE / "structure.json"
    structure = read(structure_path)
    sections = {s["id"]: s for s in structure["sections"]}
    assigned = [c for s in sections.values() for c in s["cases"]]
    if len(assigned) != len(set(assigned)):
        raise ValueError("A case appears in multiple primary chapters")
    section_of = {c: s["id"] for s in sections.values() for c in s["cases"]}
    now = datetime.now(timezone.utc).isoformat()
    suites, entries, issues, notes = [], [], [], []
    for suite_root in structure["current_suites"]:
        sp = ROOT / suite_root
        shared_suite = Suite.load(sp)
        sj = read(sp / "suite.json")
        sources_path = sp / "sources.json"
        registry = read(sources_path)
        ids = []
        alignment_status = read(sp / "reviews/status.json") if "lean-alignment" in suite_root else None
        proof_status = read(sp / "reviews/status.json") if "public-proof-extractions" in suite_root else None
        for cp in sj["cases"]:
            case_path = sp / cp
            c = read(case_path)
            cid = c["id"]
            ids.append(cid)
            if cid not in section_of:
                raise ValueError(f"No primary chapter for {cid}")
            d = case_path.parent
            original = {}

            def bind(p: Path) -> None:
                if p.is_file():
                    original[rel(p)] = digest(p)

            bind(case_path)
            bind(sp / "suite.json")
            bind(sources_path)
            paths = {k: rel(sp / c[k]) for k in ("task", "reference", "rubric")}
            for p in paths.values():
                bind(ROOT / p)
            for name in ("review.json", "design.json", "design.md", "source-notes.md", "source-evidence.json", "source-record.json", "sources.fragment.json", "round2-review.json", "external/provenance.json", "formal/vendor/PROVENANCE.json", "formal/external-dependency-audit.json", "formal/external-library-review.json", "formal/PORTING.md"):
                bind(d / name)
            review_path = d / "review.json"
            review = read(review_path)
            records = []
            proof_case = None
            semantic_record = None
            for r in review.get("independent_reviews", []):
                value = r.get("report", r.get("evidence"))
                if value:
                    p = resolve_evidence(value, sp, d)
                    if p:
                        records.append(p)
                        bind(p)
                        expected = r.get("report_sha256", r.get("evidence_sha256"))
                        if expected and digest(p) != expected:
                            issues.append(f"{cid}: independent review record hash mismatch {value}")
                    else:
                        issues.append(f"{cid}: missing independent evidence {value}")
                for supporting in r.get("supporting_reports", []):
                    p = resolve_evidence(supporting["report"], sp, d)
                    if p:
                        bind(p)
                        records.append(p)
                        expected = supporting.get("sha256")
                        if expected and digest(p) != expected:
                            issues.append(f"{cid}: supporting review record hash mismatch {supporting['report']}")
            if alignment_status:
                st = next(x for x in alignment_status["cases"] if x["case_id"] == cid)
                rp = sp / st["mathematical_review"]["record"]
                records.append(rp)
                bind(rp)
                for field, name, hash_key in [(st["mathematical_review"], "record", "record_sha256"), (st["formal"], "report", "report_sha256")]:
                    p = sp / field[name]
                    bind(p)
                    if digest(p) != field[hash_key]:
                        issues.append(f"{cid}: status evidence hash mismatch {name}")
                bind(sp / "reviews/status.json")
            elif cid.startswith("MG-P"):
                proof_case = next(x for x in proof_status["cases"] if x["case_id"] == cid)
                rp = sp / proof_case["independent_ai"]["report"]
                records.append(rp)
                bind(rp)
                bind(sp / "reviews/status.json")
                if digest(rp) != proof_case["independent_ai"]["sha256"]:
                    issues.append(f"{cid}: independent mathematical review hash mismatch")
                if (d / "round2-review.json").exists():
                    records.append(d / "round2-review.json")
                if proof_case.get("round2_review"):
                    r2 = proof_case["round2_review"]
                    if digest(sp / r2["report"]) != r2["sha256"]:
                        issues.append(f"{cid}: round2 review hash mismatch")
                fc = proof_case.get("formal_coverage", {})
                if fc.get("independent_semantic_review"):
                    semantic_record = sp / fc["independent_semantic_review"]
                    records.append(semantic_record)
                    bind(semantic_record)
                    if digest(semantic_record) != fc["independent_semantic_review_sha256"]:
                        issues.append(f"{cid}: independent semantic review hash mismatch")
            elif not records and review.get("mathematical") == "ai-independent-review-passed" and review.get("reviewer_agent"):
                # R020 records the independent review directly, not as a list.
                records.append(review_path)
            # Follow review closure records as well as initial reviews. An
            # author's updated summary alone cannot refresh a stale review.
            text = "\n".join(p.read_text() for p in records if p.is_file())
            core_bound = {k: digest(ROOT / paths[k]) in text for k in ("task", "reference", "rubric")}
            if not records or not all(core_bound.values()):
                issues.append(f"{cid}: missing independent review or core input hash binding")
            human = c.get("review", {}).get("human", review.get("human", "pending"))
            if human != "pending":
                issues.append(f"{cid}: human status changed; inspect before using index")
            formal = d / "formal"
            manifest_path = formal / "manifest.json"
            manifest = read(manifest_path)
            bind(manifest_path)
            for name, expected in manifest["frozen_inputs"].items():
                p = d / name
                if digest(p) != expected:
                    issues.append(f"{cid}: frozen input mismatch {name}")
            for item in manifest["modules"] + [manifest["audit"], manifest["coverage"]]:
                p = formal / item["source"]
                bind(p)
                if digest(p) != item["sha256"]:
                    issues.append(f"{cid}: formal source mismatch {item['source']}")
            full = cid not in ("MG-P001", "MG-P003") or manifest.get("semantic_status", "").startswith("full-task-kernel-verified")
            if proof_case and proof_case.get("formal_coverage"):
                full = proof_case["formal_coverage"]["full_task"]
            gaps = []
            if cid == "MG-P001" and not full:
                gaps = ["整数约化同调与可缩性的双向局部判据尚未连接到当前有限复形对象。", "单纯/奇异同调比较及有限增广整数链复形的决策正确性尚未完成。"]
            elif cid == "MG-P003":
                gaps = ["完整有限对应与转移预层、明示几何输入 G1–G3 及大/小位点比较尚未集成。", "任意有限点集上典范层化单位为同构的完整终点尚未声明和证明。"]
            if alignment_status:
                evidence = sp / st["formal"]["report"]
            elif proof_case and proof_case.get("formal_coverage"):
                evidence = sp / proof_case["formal_coverage"]["report"]
            elif (formal / "verification-report.json").exists():
                evidence = formal / "verification-report.json"
            else:
                evidence = formal / "verification-summary.json"
            ev = read(evidence)
            bind(evidence)
            if proof_case and proof_case.get("formal_coverage"):
                fc = proof_case["formal_coverage"]
                if digest(evidence) != fc["report_sha256"] or digest(manifest_path) != fc["manifest_sha256"]:
                    issues.append(f"{cid}: final proof status evidence binding mismatch")
            report_matches = ev.get("manifest_sha256") == digest(manifest_path)
            reuse_path = None
            if not report_matches and (formal / "current-formal.json").exists():
                current = read(formal / "current-formal.json")
                if current.get("evidence_reuse_receipt"):
                    reuse_path = formal / current["evidence_reuse_receipt"]
                    reuse = read(reuse_path)
                    bind(reuse_path)
                    compiled = {x["module"]: x["source_sha256"] for x in ev["modules"] + [ev["audit"]["command"]]}
                    unchanged_sources = all(compiled.get(x["module"]) == x["sha256"] for x in manifest["modules"] + [manifest["audit"]])
                    report_matches = (
                        unchanged_sources and reuse["status"] == "passed"
                        and digest(reuse_path) == current["evidence_reuse_receipt_sha256"]
                        and reuse["old_manifest_sha256"] == ev["manifest_sha256"]
                        and reuse["new_manifest_sha256"] == digest(manifest_path)
                        and reuse["original_compilation_report_sha256"] == digest(evidence)
                        and current["source_manifest_sha256"] == digest(manifest_path)
                    )
            if ev.get("status") != "passed" or not report_matches:
                issues.append(f"{cid}: formal report does not match current manifest")
            bind(formal / "current-formal.json")
            for name in ("GAPS.md", "LIBRARY-GAPS.md"):
                bind(formal / name)
            solver_files = []
            for f in c.get("solver_files", []):
                p = sp / f["source"]
                bind(p)
                solver_files.append({"source": rel(p), "target": f["target"], "sha256": digest(p)})
            src_records = []
            for sid in c["sources"]:
                if sid not in registry:
                    issues.append(f"{cid}: missing source {sid}")
                    continue
                src_records.append({"id": sid, "registry": rel(sources_path), "record": registry[sid]})
            task_kind = c.get("task_kind", "written")
            entries.append({
                "id": cid, "case_id": cid, "version": c["version"], "title": c["title"],
                "suite_root": suite_root, "case_path": rel(case_path),
                "suite_version": sj["version"], "suite_sha256": shared_suite.sha256,
                "suite_manifest_sha256": digest(sp / "suite.json"), "status": c["status"],
                "family_id": c.get("family_id", "exercise-" + cid.lower()),
                "family_id_origin": "source-case" if c.get("family_id") else "catalog-stable-single-case-id",
                "section": section_of[cid], "task_kind": task_kind, "track": c["track"],
                "domain": c.get("domain", sections[section_of[cid]]["title"]),
                "paths": paths, "solver_files": solver_files, "sources": src_records,
                "mathematical_review": {
                    "status": "independent-ai-review-passed", "human": human,
                    "reference_present": (ROOT / paths["reference"]).is_file(),
                    "reference_scope": "Complete application relative to precisely cited published geometric inputs; those background theorems are not reproved from foundations." if cid == "MG-P003" else "Complete reference proof or legal counterexample for the original task; valid alternative routes are accepted.",
                    "records": list(dict.fromkeys(rel(p) for p in records)),
                    "core_input_hashes_bound": core_bound,
                    "evidence_reuse": "Existing mathematical reviews; this catalog run checks inventory and identities, not a new mathematical proof review."
                },
                "author_lean_coverage": "full-main-task" if full else "partial-main-task",
                "lean_coverage": {
                    "status": "full-main-task" if full else "partial-main-task", "full_main_task": full,
                    "scope": "Author reference and intentionally matched/mismatched input artifacts" if c["track"] == "alignment" else "Author proof of original main targets or complete legal refutation; optional reference branches may differ.",
                    "coverage": rel(formal / "COVERAGE.md"), "manifest": rel(manifest_path),
                    "evidence": rel(evidence), "compile_status": ev["status"],
                    "independent_semantic_review": rel(semantic_record) if semantic_record else None,
                    "evidence_reuse_receipt": rel(reuse_path) if reuse_path else None,
                    "current_report_binding": "matched" if report_matches else "pending-source-closure",
                    "toolchain": manifest["lean_toolchain"], "mathlib_revision": manifest["mathlib_revision"],
                    "verification_profile": manifest.get("verification_profile", "lean-4.29.1-mathlib"),
                    "tauceti_revision": manifest.get("tauceti_revision"),
                    "source_module_count": len(manifest["modules"]), "remaining_main_task_gaps": gaps,
                    "candidate_result": False
                },
                "qualification": {"eligible_for_full_comparison": True, "human_approved": False,
                    "basis": "完整数学参考、非作者 AI 数学审核及当前输入身份；Lean 覆盖另列，不以部分覆盖静默排除文字题。"},
                "original_sha256": dict(sorted(original.items()))
            })
        suites.append({"root": suite_root, "id": sj["id"], "version": sj["version"], "suite_sha256": shared_suite.sha256,
                       "suite_manifest_sha256": digest(sp / "suite.json"), "cases": ids})
    byid = {e["id"]: e for e in entries}
    if set(assigned) != set(byid) or len(entries) != 41:
        raise ValueError("Current scope must have exactly the 41 uniquely assigned cases")
    task_hashes = [e["original_sha256"][e["paths"]["task"]] for e in entries]
    if len(set(task_hashes)) != len(entries):
        issues.append("Duplicate current task bytes; inspect semantic/variant identity")
    archival = []
    for root in structure["historical_suites"]:
        sp = ROOT / root
        sj = read(sp / "suite.json")
        for p in sj["cases"]:
            c = read(sp / p)
            current = c["id"] if root.startswith("archive/research-v0.2") else None
            archival.append({"id": c["id"], "version": c["version"], "title": c["title"], "suite_root": root,
                "case_path": rel(sp / p), "task": rel(sp / c["task"]),
                "task_sha256": digest(sp / c["task"]), "status": "superseded" if current else "retired-suite",
                "current_case": current, "same_task_bytes": digest(sp / c["task"]) == digest(ROOT / byid[current]["paths"]["task"]) if current else None,
                "count_in_current_comparison": False})
    predecessor = dict(structure["unregistered_predecessor"])
    predecessor["same_task_bytes"] = digest(ROOT / predecessor["path"] / "task.md") == digest(ROOT / byid[predecessor["current_case"]]["paths"]["task"])
    predecessor["count_in_current_comparison"] = False
    notes.extend([
        "All current cases remain draft / human pending; eligibility for this comparison is not publication or human approval.",
        "The six alignment family pairs must use separate candidate sessions and stay together for any train/test source split.",
        "P002 and F107/F108 share a public source mechanism but ask different mathematics; preserve their cross-source relation when splitting data."
    ])
    proof_root = ROOT / "drafts/public-proof-extractions-20261029"
    if "not-formalized" in (proof_root / "reviews/status.json").read_text():
        notes.append("Public-proof-extractions first-round status retains historical not-formalized wording; use current manifests, coverage ledgers and later review records.")
    if not (proof_root / "MG-P001/round2-review.json").exists():
        notes.append("P001 COVERAGE links ../round2-review.json, absent at this snapshot; the unchanged original mathematics has a separate independent review. The absent link is not evidence.")
    counts = {"current_exercises": len(entries), "written": sum(e["task_kind"] == "written" for e in entries),
              "alignment": sum(e["track"] == "alignment" for e in entries), "full_main_task_lean": sum(e["lean_coverage"]["full_main_task"] for e in entries),
        "partial_main_task_lean": sum(not e["lean_coverage"]["full_main_task"] for e in entries),
              "human_approved": 0, "historical_suite_records": len(archival),
              "primary_case_families": len({e["family_id"] for e in entries}),
              "alignment_families": len({e["family_id"] for e in entries if e["track"] == "alignment"}),
              "task_kinds": dict(Counter(e["task_kind"] for e in entries)),
              "sections": dict(Counter(e["section"] for e in entries))}
    full_count = counts["full_main_task_lean"]
    partial_ids = [e["id"] for e in entries if not e["lean_coverage"]["full_main_task"]]
    partial_text = "、".join(partial_ids)
    catalog = {"schema": "math-gauge.exercise-catalog/v1", "title": structure["title"], "generated_utc": now,
        "snapshot_status": "final-catalog-snapshot" if args.final else "provisional-awaiting-source-closure",
        "path_base": "repository root", "qualification_root": rel(QUAL), "operator_only": True, "candidate_input_policy": "Use the shared runner's exact per-case projection; never send this catalog, chapter indexes, references, sources or labels to candidates.",
        "structure_sha256": digest(structure_path), "counts": counts, "suites": suites,
        "sections": structure["sections"], "related_families": structure["related_families"],
        "case_entries": entries, "historical_entries": archival, "unregistered_predecessor": predecessor, "limitations": notes}
    pending = [x for x in issues if x.startswith("MG-P001:")]
    fatal = [x for x in issues if x not in pending]
    if fatal or (args.final and issues):
        raise ValueError("Catalog qualification failed:\n" + "\n".join(issues))
    catalog["pending_source_identity_checks"] = pending
    dump(HERE / "catalog.json", catalog)
    kind_labels = {"written": "数学论证", "audit": "Lean 对齐判定", "generate": "Lean 生成", "repair": "Lean 修复"}
    for sid, section in sections.items():
        p = HERE / "chapters" / (sid + ".md")
        lines = ["# " + section["title"], "", section["introduction"], "", "每道题都链接原始题面；版本和任务类型用于选题。完整作答要求以题面为准。", "", "| 题号与题目 | 版本 | 任务类型 |", "| --- | --- | --- |"]
        for cid in section["cases"]:
            e = byid[cid]
            lines.append(f"| {link(cid + ' · ' + e['title'], e['paths']['task'], p)} | {e['version']} | {kind_labels[e['task_kind']]} |")
        lines += ["", "[返回总目录](../README.md) · [按任务类型选题](../task-types.md) · [出题与审核材料](../instructor-guide.md)", ""]
        p.write_text("\n".join(lines))
    p = HERE / "README.md"
    lines = ["# Math Gauge 习题集", "", "现行习题共 **41 题**，按七个数学主题编排：29 道数学论证题，以及六个母题的 12 道 Lean 对齐任务。题号和原始文件路径保持不变，各章节直接链接唯一题面。", "", "数学论证题要求完成题面中的证明、反例、构造或分类；Lean 对齐任务分为判定、生成和修复。不要从题号、题目来源或历史结果猜测结论。", "", "## 按数学主题阅读", "", "| 章节 | 题数 | 内容 |", "| --- | ---: | --- |"]
    for s in sections.values():
        lines.append(f"| [{s['title']}](chapters/{s['id']}.md) | {len(s['cases'])} | {'、'.join(s['cases'])} |")
    lines += ["", "## 使用这套习题", "", "- [按任务类型选题](task-types.md)：数学论证、Lean 判定、Lean 生成和 Lean 修复。", "- [出题与审核材料](instructor-guide.md)：参考解、来源、独立审核及 Lean 覆盖账本，仅供出题侧使用。", "- [版本与历史对应](history.md)：旧版、退役题集和初始草稿单独保留，不重复计入 41 题。", "- " + link("正式试跑验收清单", rel(QUAL / "README.md"), p) + "：完整数学参考与独立审核为出题门槛，Lean 证据另列。", "- [机器目录](catalog.json)：精确版本、suite 根路径、母题、来源和文件散列。", "", f"当前全部题目仍为 **draft / human pending**。首轮整体对比覆盖全部 41 题；版本修订后的单题补测另行记录。其中 {full_count} 题的原始主目标已有完整作者 Lean 证据，{partial_text} 保留完整数学题面并明确列出尚未完成的形式化。该 {full_count} 题子集只作分层统计，不替代整体成绩。", "", "本目录是阅读和出题索引。实际模型输入必须由原有共享 runner 按每题显式投影生成；本目录、参考解、评分、来源、历史结果和作者形式化均不得附入候选输入。", "", "索引重建：在仓库根目录运行 `python3 exercises/refresh_catalog.py`；所有源工件完成并核对后使用 `--final` 固定新快照。重建目录不启动模型，也不改变原题或人工状态。冻结后可用 `python3 exercises/refresh_catalog.py --check` 只读核对，不改变目录散列。", ""]
    p.write_text("\n".join(lines))
    p = HERE / "task-types.md"
    lines = ["# 按任务类型选题", "", "任务类型与数学章节是两个交叉索引。这里不显示判定题的正确标签，也不预告数学论证题的结论。", ""]
    for kind in ("written", "audit", "generate", "repair"):
        subset = [e for e in entries if e["task_kind"] == kind]
        lines += [f"## {kind_labels[kind]} · {len(subset)} 题", ""]
        if kind == "written":
            lines += ["按原题要求给出完整数学论证；候选无需提交 Lean。", ""]
        elif kind == "audit":
            lines += ["结合原文与提供的完整 Lean 依赖，判断语义对应并指出关键依据；编译成功本身不决定对齐。", ""]
        else:
            lines += ["最终回答按题面要求交付带文件名的完整 Lean 代码块及覆盖说明；冻结答卷中的源码才是候选交付物。", ""]
        for e in subset:
            lines.append("- " + link(e["id"] + " · " + e["title"], e["paths"]["task"], p))
        lines.append("")
    lines += ["同母题的两个 Lean 任务必须在独立会话中运行，不能把一个版本的答卷带给另一个版本。", "", "[返回总目录](README.md)", ""]
    p.write_text("\n".join(lines))
    p = HERE / "instructor-guide.md"
    lines = ["# 出题与审核材料", "", "本页仅供出题侧。参考、rubric、来源、审核和形式化是不同证据；它们均不进入候选投影。有效的替代证明、短证明和标准定理应用按原题与评分标准接受。", "", "所有 41 题具有完整数学参考及非作者 AI 数学审核。P003 的完整参考相对于精确引用的已发表几何输入展开应用，不声称从基础重证这些输入。当前全部人工状态为 pending。", "", "## 逐题材料", "", "| 题目 | 数学参考与评分 | 审核 | 作者 Lean 主目标 |", "| --- | --- | --- | --- |"]
    for e in entries:
        reviews = e["mathematical_review"]["records"]
        coverage = e["lean_coverage"]
        label = "完整" if coverage["full_main_task"] else "部分；见缺口"
        lines.append(f"| {e['id']} · {e['title']} | {link('参考',e['paths']['reference'],p)} · {link('评分',e['paths']['rubric'],p)} | {link('独立 AI 审核',reviews[0],p)} | {link(label,coverage['coverage'],p)} |")
    lines += ["", "## 同源与版本", "", "Lean 六个母题分别为商环理想、初始拓扑、陪集覆盖、序列乘子、有限轨道筛选、扩展值上界；每个母题有两个任务版本。41 份答卷不等于 41 个完全独立的数学样本。统计同时报告整体、任务类型和母题结果。", ""]
    for item in structure["related_families"]:
        lines.append("- " + "、".join(item["cases"]) + "：" + item["relation"])
    lines += ["", "## 形式化边界", "", ("- P001：实际有限复形上的分类、全部实现和有限局部整数矩阵判据均已形式化；当前独立 Lean 4.36/TauCeti profile 的证据取代早期部分覆盖阶段。" if byid["MG-P001"]["lean_coverage"]["full_main_task"] else "- P001：实际有限复形上的同伦分类与全部实现已形式化；整数局部可缩判据及有限链复形决策接口尚未接通。"), "- P003：半局部化、邻域极限与交换图等实质辅助已形式化；完整动机几何输入和典范层化同构终点尚未完成。", "- P002：全部题面目标已有实际环面上的形式化；参考中的部分可选强化未单列定理，不是题目缺口。", "- 其余 38 题：作者主目标的成立结论或完整合法否定反例已有 Lean 证据。判断题故意失配的可见输入也可编译，语义判断来自独立审核。", "", "历史作者稿中的待审或未形式化文字按原始快照保留；本目录索引最新匹配工件的证据，不回写历史状态。", "", "[来源与精确文件身份](catalog.json) · " + link("验收清单", rel(QUAL / "README.md"), p) + " · [返回总目录](README.md)", ""]
    p.write_text("\n".join(lines))
    p = HERE / "history.md"
    lines = ["# 版本与历史对应", "", "现行集合为 41 题。以下 33 条历史 suite 记录和一份未注册前身不作为新增样本加入当前对比；原始记录保留，不回填后续评分或审核状态。", "", "## 研究题 0.2 的替代关系", "", "现行 public suite 为 " + byid["MG-R005"]["suite_version"] + "。R001–R010 的基线为 0.3.0；R005 当前版本为 " + byid["MG-R005"]["version"] + "。R011–R020 为追加的 0.4.0；suite 修订不把未变题面重算为新题。", "", "| 历史题 | 历史版本 | 现行对应 | 题面关系 |", "| --- | --- | --- | --- |"]
    for e in archival:
        if e["current_case"]:
            lines.append(f"| {link(e['id']+' · '+e['title'],e['task'],p)} | {e['version']} | {link(e['current_case'],byid[e['current_case']]['paths']['task'],p)} | {'题面字节相同，证据阶段不同' if e['same_task_bytes'] else '后续修订或重设计，旧版仅供追溯'} |")
    lines += ["", "## 已退役首轮题集", "", "这些是历史基础题与挑战题，不声称每题都由某一道新题一对一替换。保留它们用于历史结果及共享 runner 合同追溯。", "", "| 历史集合 | 题号与题目 | 版本 |", "| --- | --- | --- |"]
    for e in archival:
        if not e["current_case"]:
            lines.append(f"| {e['suite_root'].rsplit('/',1)[-1]} | {link(e['id']+' · '+e['title'],e['task'],p)} | {e['version']} |")
    lines += ["", "## 首轮完整比较与后续修订", "", "首轮 [41 题比较](../results/full-comparison-20261030/comparison.md) 使用当时冻结的 R005 0.3.0，答卷、评分和完整题集快照均已独立归档。现行 R005 0.3.1 明确扩展实值竞争函数与实高度上图约定；[新版单题补测](../results/r005-clarified-v0.3.1-20261030/README.md) 单独记录，不替换首轮分数或增加现行题数。", "", "## 草稿与内部历史", "", "- `drafts/recursive-operator-closure/task.md` 与现行 R001 逐字节相同；它是前身，不另计题。", "- true-goal-six 的 R101–R106 是六道独立现行题，没有被 R011–R020 取代。R103 当前 0.1.1 只修正评分措辞，题面与原 0.1.0 相同；旧资格快照不是额外题目。", "- public-proof-extractions 的 `history/round1`、`history/round2-*` 保存同一 P001–P003 的作者或验证阶段，不另计题。", "- Lean 对齐的 12 题是六个母题的有意任务变体；它们不是历史版本，但必须按母题标注相关性。", "", "[机器对应表](catalog.json) · [返回总目录](README.md)", ""]
    p.write_text("\n".join(lines))
    catalog_sha = digest(HERE / "catalog.json")
    gate = {"schema": "math-gauge.comparison-qualification/v1", "generated_utc": now,
        "snapshot_status": catalog["snapshot_status"], "status": "pending-source-closure" if pending else "passed-inventory-and-inherited-mathematics-evidence",
        "catalog": "exercises/catalog.json", "catalog_sha256": catalog_sha, "counts": counts,
        "case_ids": [e["id"] for e in entries],
        "fully_lean_covered_case_ids": [e["id"] for e in entries if e["lean_coverage"]["full_main_task"]],
        "partially_lean_covered_case_ids": [e["id"] for e in entries if not e["lean_coverage"]["full_main_task"]],
        "checks": {"41_unique_current_cases": True, "one_primary_chapter_per_case": True,
            "all_task_reference_rubric_files_present": True, "all_source_ids_resolve": True,
            "existing_independent_review_and_core_hash_binding": True,
            "current_manifest_source_hashes_match": not any("source mismatch" in x or "input mismatch" in x for x in pending),
            "current_formal_reports_match_manifest": not any("report does not match" in x for x in pending), "all_human_status_pending": True,
            "history_excluded_from_new_sample_count": True, "candidate_models_executed_by_catalog_builder": False},
        "authorization": "This evidence inventory does not unlock runtime or authorize publication; root release controls any model execution.",
        "scope": "No source case, runner, historical review, mathematical reference, rubric or human decision modified.",
        "pending_source_identity_checks": pending, "limitations": notes}
    dump(QUAL / "gate.json", gate)
    p = QUAL / "README.md"
    p.write_text("\n".join([
        "# 习题集 · 出题验收清单", "", f"本快照：`{catalog['snapshot_status']}`。现行范围 **41 题**；机器检查见 [gate.json](gate.json)，唯一选题目录见 {link('catalog.json', 'exercises/catalog.json', p)}。", "",
        "## 已核对的出题门槛", "", "- 41 个唯一现行题号与准确版本，四个 suite 根目录均保留；本清单是当前全库身份检查，实际试验题目范围由各轮冻结记录决定。",
        "- 每题具有完整题面、数学参考、具体评分标准、公开来源记录及非作者 AI 数学审核。既有审核绑定当前题面、参考和评分散列。",
        "- 题目文件不复制、不改写；七个数学章节和任务类型索引均指向原始唯一来源。",
        "- 作者 formal manifest、输入散列及编译报告的身份核对见 gate.json；待刷新项为：" + ("；".join(pending) if pending else "无") + "。本目录工作没有重新执行数学编译。",
        f"- 作者 Lean 主目标完整覆盖 {full_count} 题，{partial_text} 的原题尚有形式化缺口。首轮全部 41 题的比较包含该书面题，并另报 {full_count} 题子集成绩。",
        "- 12 道对齐题有完整作者参考与可编译输入；六个母题每题各两个任务版本。",
        "- 全部 human pending，未把 AI 审核、作者编译或试跑资格当成人工批准。", "",
        "## 运行侧仍须独立落实", "", "- 使用同一个共享 runner，逐题按显式候选投影准备输入；目录和评审材料不进入候选。",
        "- 每模型每题使用独立会话，母题变体不共享答案；冻结模型请求配置、真实响应及退出状态。",
        "- 分开记录请求模型身份、实际回显身份、工具预算、基础设施失败和数学失败，不用旧试跑替代新比较。",
        "- Lean 生成/修复从冻结最终答卷提取完整文件，单独编译并审核语义；不得把作者参考通过当作候选通过。",
        f"- 模型答卷必须另经审核，整体结果同时按数学章节、任务类型、同源母题和 {full_count} 题完整 Lean 子集报告。",
        "- 完成最终源哈希刷新与运行计划绑定后，由根任务显式发布运行放行记录；本清单本身不启动模型。", "",
        "## 本轮证据范围", "", "这次验收是目录、来源解析与既有审核/编译工件身份核对，没有重做全部数学证明审核，也未执行候选模型。P003 的参考相对于明确引用的已发表几何输入完整；背景定理的基础重建不是此次书面题作答要求。", "",
        "早期摘要中的未形式化或未试跑文字可能是冻结作者阶段记录。以对应版本、源码散列和后续记录的明确范围为准，不能从文件名或单一总表推断最新状态。", "",
        link("习题总目录", "exercises/README.md", p) + " · " + link("历史对应", "exercises/history.md", p), ""
    ]))
    validation = check_index()
    dump(QUAL / "index-validation.json", {"schema": "math-gauge.exercise-index-validation/v1",
        "generated_utc": now, **validation, "generator_sha256": digest(Path(__file__)),
        "command": "python3 exercises/refresh_catalog.py" + (" --final" if args.final else "") + (" --qualification-dir " + rel(QUAL) if args.qualification_dir else ""),
        "scope": "Catalog contract, all bound source identities and local Markdown links; no model execution or mathematical recompilation."})
    print(json.dumps({"catalog": rel(HERE / "catalog.json"), "sha256": catalog_sha, "counts": counts, "issues": issues, "validation": validation}, ensure_ascii=False))


if __name__ == "__main__":
    main()
