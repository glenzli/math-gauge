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


def compare_models(case_index, model_runs, *, execution_receipts, lean_reports=None):
    """Compare frozen single-case runs without turning AI review into human approval.

    case_index is the pre-inference list, including exact request/message hashes.
    Receipt paths are keyed by model label and case id. Execution assessments are
    operator-reviewed evidence, not an automatic claim of isolation by this function.
    Missing runs/reviews remain visible and do not produce a complete-suite rate.
    """
    from .catalog import candidate_message
    from collections import Counter
    import json

    index = {c["case_id"]: c for c in case_index}
    if not index or len(index) != len(case_index):
        raise ValueError("Comparison requires a nonempty unique frozen case index")
    if len(model_runs) != 2:
        raise ValueError("This paired comparison requires exactly two model labels")
    for c in index.values():
        for field in (
            "version",
            "request_sha256",
            "candidate_message_sha256",
            "task_kind",
            "family_id",
            "section",
            "suite_sha256",
            "author_lean_coverage",
        ):
            if not c.get(field):
                raise ValueError(f"{c['case_id']}: missing frozen {field}")
    lean_reports = lean_reports or {}

    def bound_receipt(path, cid, response_hash, request_hash):
        data = read_json(path)
        if (
            data.get("case_id") != cid
            or data.get("response_sha256") != response_hash
            or data.get("request_sha256") != request_hash
        ):
            raise ValueError(f"{cid}: receipt does not bind this request and response")
        return data, digest_bytes(Path(path).read_bytes())

    def summarize(rows):
        resolved = [r for r in rows if r["resolved"]]
        passes = sum(r["strict_pass"] for r in rows)
        complete = len(resolved) == len(rows)
        known_requests = sum(r["request_count"] or 0 for r in rows)
        unknown_requests = sum(r["request_count"] is None for r in rows)
        return {
            "planned": len(rows),
            "started": sum(r["started"] for r in rows),
            "mathematical_requests": known_requests if not unknown_requests else None,
            "known_mathematical_requests": known_requests,
            "unknown_request_counts": unknown_requests,
            "valid_executions": sum(r["valid_execution"] for r in rows),
            "reviewed": sum(r["reviewed"] for r in rows),
            "resolved": len(resolved),
            "pending": len(rows) - len(resolved),
            "strict_passes": passes,
            "outcome_counts": dict(Counter(r["outcome"] for r in rows)),
            "decision_counts": dict(
                Counter(r.get("decision", "not_reviewed") for r in rows)
            ),
            "lean_status_counts": dict(
                Counter(r["lean_status"] for r in rows if "lean_status" in r)
            ),
            "complete": complete,
            "strict_pass_rate": passes / len(rows) if complete and rows else None,
            "strict_pass_rate_on_resolved": passes / len(resolved)
            if resolved
            else None,
        }

    models = {}
    for label, paths in model_runs.items():
        rows = {
            cid: {
                "case_id": cid,
                "started": False,
                "request_count": 0,
                "valid_execution": False,
                "reviewed": False,
                "resolved": False,
                "strict_pass": False,
                "outcome": "not_started",
                "human_comparison_eligible": False,
            }
            for cid in index
        }
        seen = set()
        for directory in paths:
            root = Path(directory)
            meta, records = inspect_run(root)
            if meta.get("origin") != "command":
                raise ValueError("Replay runs cannot enter a model comparison")
            if meta.get("model_label") != label or len(meta["cases"]) != 1:
                raise ValueError("Expected one case per run with the exact model label")
            info = meta["cases"][0]
            cid = info["id"]
            if cid not in index or cid in seen:
                raise ValueError("Unknown or repeated comparison case: " + cid)
            seen.add(cid)
            frozen = index[cid]
            record = records[cid]
            if (
                info["version"] != frozen["version"]
                or meta["suite_sha256"] != frozen["suite_sha256"]
            ):
                raise ValueError(cid + ": version or suite changed")
            request = read_json(root / cid / "solver/request.json")
            request_hash = digest_bytes(
                json.dumps(request, ensure_ascii=False, sort_keys=True).encode()
            )
            message_hash = digest_bytes(candidate_message(request).encode())
            if (
                request_hash != frozen["request_sha256"]
                or request_hash != record["request_sha256"]
                or message_hash != frozen["candidate_message_sha256"]
            ):
                raise ValueError(cid + ": frozen candidate input changed")
            row = rows[cid]
            row.update(
                started=True,
                request_count=None,
                run_dir=str(root),
                execution_status=record["status"],
                response_sha256=record["response_sha256"],
                request_sha256=request_hash,
                candidate_message_sha256=message_hash,
                outcome="execution_not_assessed",
            )
            path = execution_receipts.get(label, {}).get(cid)
            if path is None:
                continue
            receipt, receipt_hash = bound_receipt(
                path, cid, record["response_sha256"], request_hash
            )
            if (
                not meta.get("run_id")
                or receipt.get("run_id") != meta["run_id"]
                or receipt.get("model_label") != label
            ):
                raise ValueError(
                    cid + ": execution receipt belongs to a different model or run"
                )
            count = receipt.get("mathematical_request_count")
            if type(count) is not int or count not in (0, 1):
                raise ValueError(
                    cid + ": single-attempt request count must be zero or one"
                )
            if receipt.get("candidate_message_sha256") != message_hash:
                raise ValueError(cid + ": execution receipt has a different message")
            row.update(
                request_count=count,
                execution_receipt_sha256=receipt_hash,
                valid_execution=receipt.get("valid_for_comparison") is True
                and count == 1,
                outcome=receipt.get("outcome", "execution_not_qualified"),
            )
            if not row["valid_execution"]:
                continue
            if record["status"] == "timeout":
                row.update(resolved=True, outcome="timeout")
                continue
            if record["status"] != "ok":
                continue
            reviews = (
                read_json(root / "reviews.json")
                if (root / "reviews.json").exists()
                else {}
            )
            review = reviews.get(cid)
            if not review:
                row["outcome"] = "awaiting_mathematical_review"
                continue
            if review.get("response_sha256") != record["response_sha256"]:
                raise ValueError(cid + ": mathematical review binding changed")
            if review.get("reviewer_kind") not in ("ai", "human"):
                raise ValueError("Fixture reviews cannot enter a model comparison")
            decision = review.get("decision")
            if decision not in ("pass", "fail", "partial", "unresolved"):
                raise ValueError(cid + ": invalid mathematical review decision")
            if decision == "pass" and (
                review.get("assumption_fidelity") != "clean"
                or review.get("proof_validity") != "valid"
                or review.get("scope_accuracy") != "correct"
                or review.get("unnecessary_restriction") is not False
            ):
                raise ValueError(cid + ": pass contradicts mathematical review axes")
            row.update(
                reviewed=True,
                reviewer_kind=review["reviewer_kind"],
                decision=decision,
                review_sha256=digest_bytes(
                    json.dumps(review, ensure_ascii=False, sort_keys=True).encode()
                ),
                outcome=decision,
                resolved=decision != "unresolved",
                strict_pass=decision == "pass",
            )
            if frozen["task_kind"] in ("generate", "repair"):
                lean_path = lean_reports.get(label, {}).get(cid)
                if lean_path is None:
                    row.update(
                        strict_pass=False,
                        resolved=False,
                        outcome="awaiting_candidate_lean",
                        human_comparison_eligible=False,
                    )
                    continue
                lean, lean_hash = bound_receipt(
                    lean_path, cid, record["response_sha256"], request_hash
                )
                if lean.get("status") not in (
                    "passed",
                    "compile_error",
                    "format_error",
                    "infrastructure_error",
                    "axiom_rejected",
                ):
                    raise ValueError(cid + ": unknown candidate Lean status")
                row.update(lean_status=lean.get("status"), lean_report_sha256=lean_hash)
                if lean.get("status") == "infrastructure_error":
                    row.update(
                        strict_pass=False,
                        resolved=False,
                        outcome="lean_infrastructure_error",
                        human_comparison_eligible=False,
                    )
                elif lean.get("status") != "passed":
                    row.update(
                        strict_pass=False,
                        resolved=(
                            decision in ("fail", "partial")
                            if lean.get("status") == "format_error"
                            else True
                        ),
                        outcome="candidate_lean_" + str(lean.get("status")),
                    )
                if review.get("candidate_lean_report_sha256") not in (None, lean_hash):
                    raise ValueError(
                        cid + ": semantic review binds a different Lean report"
                    )
                if (
                    decision == "pass"
                    and lean.get("status") == "passed"
                    and review.get("candidate_lean_report_sha256") != lean_hash
                ):
                    raise ValueError(
                        cid
                        + ": successful semantic review must bind candidate Lean evidence"
                    )
            row["human_comparison_eligible"] = (
                row["valid_execution"]
                and row["resolved"]
                and decision != "unresolved"
                and info["case_approved"]
                and review["reviewer_kind"] == "human"
            )
        values = list(rows.values())
        groups = {}
        dimensions = (
            "task_kind",
            "section",
            "family_id",
            "author_lean_coverage",
            "audit_expected",
        )
        for dimension in dimensions:
            groups[dimension] = {
                key: summarize(
                    [rows[cid] for cid, c in index.items() if c.get(dimension) == key]
                )
                for key in sorted(
                    {c[dimension] for c in index.values() if c.get(dimension)}
                )
            }
        models[label] = {
            "summary": summarize(values),
            "groups": groups,
            "cases": values,
            "human_comparison_eligible": sum(
                r["human_comparison_eligible"] for r in values
            ),
        }
    labels = list(models)
    paired = []
    lookup = {
        label: {r["case_id"]: r for r in models[label]["cases"]} for label in labels
    }
    for cid in index:
        a, b = [lookup[label][cid] for label in labels]
        comparable = all(r["valid_execution"] and r["resolved"] for r in (a, b))
        key = (
            "both_pass"
            if a["strict_pass"] and b["strict_pass"]
            else "first_only"
            if a["strict_pass"]
            else "second_only"
            if b["strict_pass"]
            else "neither_pass"
        )
        paired.append(
            {
                "case_id": cid,
                "comparable": comparable,
                "result": key if comparable else "pending",
                "outcomes": {labels[0]: a["outcome"], labels[1]: b["outcome"]},
            }
        )

    def summarize_pairs(rows):
        counts = {
            key: sum(r["comparable"] and r["result"] == key for r in rows)
            for key in ("both_pass", "first_only", "second_only", "neither_pass")
        }
        return {
            "planned": len(rows),
            "comparable": sum(r["comparable"] for r in rows),
            "counts": counts,
        }

    paired_groups = {
        dimension: {
            key: summarize_pairs(
                [r for r in paired if index[r["case_id"]].get(dimension) == key]
            )
            for key in sorted(
                {c[dimension] for c in index.values() if c.get(dimension)}
            )
        }
        for dimension in dimensions
    }
    return {
        "schema": "math-gauge.paired-comparison/v1",
        "created_at": now(),
        "review_status": "provisional_until_human_adjudication",
        "planned_cases": len(index),
        "case_index_sha256": digest_bytes(
            json.dumps(case_index, ensure_ascii=False, sort_keys=True).encode()
        ),
        "complete": all(m["summary"]["complete"] for m in models.values()),
        "model_order": labels,
        "models": models,
        "paired": {
            **summarize_pairs(paired),
            "groups": paired_groups,
            "cases": paired,
        },
        "notice": "Single attempts on frozen cases; AI review is provisional. Task families are related variants, not independent samples. Missing or invalid executions do not yield a complete-suite pass rate.",
    }
