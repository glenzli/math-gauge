"""Review ownership: bind opinions to exact responses and keep fixture/AI/human evidence distinct."""

from pathlib import Path

from .catalog import digest_bytes, read_json, write_json
from .execution import now


def inspect_run(root):
    root = Path(root)
    meta = read_json(root / "run.json")
    if meta.get("schema") != "math-gauge.run/v1":
        raise ValueError("Unsupported run")
    records = {}
    for case in meta["cases"]:
        cid = case["id"]
        record = read_json(root / cid / "record.json")
        if (
            record["case_id"] != cid
            or digest_bytes((root / cid / "response.md").read_bytes())
            != record["response_sha256"]
        ):
            raise ValueError(f"{cid}: response changed after execution")
        records[cid] = record
    return meta, records


def templates(root):
    meta, records = inspect_run(root)
    return [
        {
            "case_id": c["id"],
            "response_sha256": records[c["id"]]["response_sha256"],
            "reviewer": "",
            "reviewer_kind": "human",
            "decision": "unresolved",
            "assumption_fidelity": "unknown",
            "proof_validity": "unknown",
            "scope_accuracy": "unknown",
            "unnecessary_restriction": False,
            "notes": "",
            "findings": [],
        }
        for c in meta["cases"]
    ]


def apply_reviews(root, entries):
    root = Path(root)
    meta, records = inspect_run(root)
    if not isinstance(entries, list):
        raise ValueError("Review input must be an array")
    existing = (
        read_json(root / "reviews.json") if (root / "reviews.json").exists() else {}
    )
    updated = dict(existing)
    for entry in entries:
        cid = entry["case_id"]
        if (
            cid not in records
            or entry.get("response_sha256") != records[cid]["response_sha256"]
        ):
            raise ValueError(f"{cid}: review does not refer to this response")
        if cid in updated:
            raise ValueError(
                f"{cid}: review already exists; keep original record and use a new run for revisions in v0.1"
            )
        if (
            entry.get("reviewer_kind") not in {"human", "ai", "fixture"}
            or not entry.get("reviewer", "").strip()
        ):
            raise ValueError(f"{cid}: reviewer attribution required")
        if entry.get("decision") not in {"pass", "fail", "partial", "unresolved"}:
            raise ValueError(f"{cid}: invalid decision")
        if entry.get("assumption_fidelity") not in {"clean", "drift", "unknown"}:
            raise ValueError(f"{cid}: invalid assumption assessment")
        if entry.get("proof_validity") not in {"valid", "invalid", "unknown"}:
            raise ValueError(f"{cid}: invalid proof assessment")
        if entry.get("scope_accuracy") not in {"correct", "incorrect", "unknown"}:
            raise ValueError(f"{cid}: invalid scope assessment")
        if type(entry.get("unnecessary_restriction")) is not bool:
            raise ValueError(f"{cid}: restriction assessment required")
        if not isinstance(entry.get("notes"), str) or not entry["notes"].strip():
            raise ValueError(f"{cid}: mathematical review notes required")
        if not isinstance(entry.get("findings"), list) or not all(
            isinstance(f, str) for f in entry["findings"]
        ):
            raise ValueError(f"{cid}: findings must be a string array")
        if entry["decision"] == "pass" and (
            entry["assumption_fidelity"] != "clean"
            or entry["proof_validity"] != "valid"
            or entry["scope_accuracy"] != "correct"
            or entry["unnecessary_restriction"]
            or records[cid]["status"] != "ok"
        ):
            raise ValueError(
                f"{cid}: pass contradicts the evidence axes or execution status"
            )
        updated[cid] = dict(entry, recorded_at=now())
    write_json(root / "reviews.json", updated)
    return updated


def report(root):
    root = Path(root)
    meta, records = inspect_run(root)
    reviews = (
        read_json(root / "reviews.json") if (root / "reviews.json").exists() else {}
    )
    tracks = {}
    for track in ("determinate", "alignment", "exploration"):
        cases = [c for c in meta["cases"] if c["track"] == track]
        reviewed = [(c, reviews[c["id"]]) for c in cases if c["id"] in reviews]
        # Recheck binding even if a user edits the review file directly.
        for c, r in reviewed:
            if r["response_sha256"] != records[c["id"]]["response_sha256"]:
                raise ValueError("Review binding changed")
        eligible = [
            (c, r)
            for c, r in reviewed
            if c["case_approved"]
            and r["reviewer_kind"] == "human"
            and meta["origin"] != "replay"
            and r["decision"] != "unresolved"
        ]
        tracks[track] = {
            "attempted": len(cases),
            "execution_ok": sum(records[c["id"]]["status"] == "ok" for c in cases),
            "reviewed": len(reviewed),
            "pending": len(cases) - len(reviewed),
            "human_reviews": sum(r["reviewer_kind"] == "human" for _, r in reviewed),
            "provisional_reviews": sum(
                r["reviewer_kind"] != "human" for _, r in reviewed
            ),
            "eligible_for_model_comparison": len(eligible),
            "strict_passes": sum(r["decision"] == "pass" for _, r in eligible)
            if track != "exploration"
            else None,
            "assumption_drifts": sum(
                r["assumption_fidelity"] == "drift" for _, r in eligible
            ),
            "unnecessary_restrictions": sum(
                r["unnecessary_restriction"] for _, r in eligible
            ),
            "reviewed_findings": sum(len(r["findings"]) for _, r in eligible)
            if track == "exploration"
            else None,
        }
    result = {
        "schema": "math-gauge.report/v1",
        "run": meta,
        "tracks": tracks,
        "automatically_establishes_mathematical_correctness": False,
        "notice": "Replay、AI/fixture 审核与未人工审定的题目不计为模型比较成绩；开放构造单独记录发现，不生成统一总分。",
    }
    lines = [
        "# Math Gauge 运行报告",
        "",
        result["notice"],
        "",
        f"- 来源：{meta['origin']}",
        f"- 模型/适配器标签：{meta['model_label']}",
        f"- 题集：{meta['suite_id']} {meta['suite_version']}",
        f"- 题集指纹：{meta['suite_sha256']}",
        f"- runner 指纹：{meta['runner_sha256']}",
        "",
        "| 类别 | 尝试 | 执行成功 | 已审/待审 | 可计入模型比较 |",
        "|---|---:|---:|---:|---:|",
    ]
    for t, s in tracks.items():
        lines.append(
            f"| {t} | {s['attempted']} | {s['execution_ok']} | {s['reviewed']}/{s['pending']} | {s['eligible_for_model_comparison']} |"
        )
    lines += [
        "",
        "## 每题证据",
        "",
        "| 题目 | 执行 | 审核来源 | 结论 |",
        "|---|---|---|---|",
    ]
    for c in meta["cases"]:
        cid = c["id"]
        r = reviews.get(cid, {})
        lines.append(
            f"| {cid} | {records[cid]['status']} | {r.get('reviewer_kind', 'pending')} | {r.get('decision', 'pending')} |"
        )
    return result, "\n".join(lines) + "\n"
