"""Review ownership: bind opinions to exact responses and keep fixture/AI/human evidence distinct."""

import json
from pathlib import Path

from .catalog import (candidate_message, digest_bytes, read_json, safe_file,
                      validate_alignment_manifest, validate_group_contract, write_json)
from .execution import extract_candidate_alignment, now, validate_alignment_audit


def _input_identity(root, meta, case, record):
    cid = case["id"]
    is_group = bool(case.get("group_contract") or record.get("group_contract_sha256"))
    # These early external imports predate run IDs and message bindings. Their
    # original archive format may omit the request or bind only raw task bytes.
    # Keep them readable without granting current verified-input eligibility.
    historical_import = (
        not is_group and "run_id" not in meta
        and meta.get("origin") in {"external-agent", "isolated-cli-evidence-import"}
        and all("candidate_message_sha256" not in item for item in (case, record))
    )
    request = None
    try:
        request = read_json(safe_file(root, cid + "/solver/request.json"))
        if not isinstance(request, dict):
            raise ValueError("Request must be an object")
        request_hash = digest_bytes(json.dumps(request, ensure_ascii=False, sort_keys=True).encode())
        if request_hash != record.get("request_sha256"):
            if historical_import and record.get("request_format") == "raw-task-utf8":
                raise ValueError("Legacy raw-task hash does not bind the canonical request JSON")
            raise ValueError("Frozen candidate input changed")
        if (request.get("schema") != "math-gauge.request/v1"
                or request.get("case_id") != cid
                or ("version" in case and request.get("case_version") != case["version"])
                or ("track" in case and request.get("track") != case["track"])):
            raise ValueError("Frozen candidate input identity changed")
        message_hash = digest_bytes(candidate_message(request).encode("utf-8"))
        for descriptor in (case, record):
            # Earlier non-group runs did not store a separate message hash.
            if ((is_group or "candidate_message_sha256" in descriptor)
                    and descriptor.get("candidate_message_sha256") != message_hash):
                raise ValueError("Frozen candidate input message binding changed")
    except (ValueError, OSError, KeyError, TypeError) as error:
        if not historical_import:
            raise ValueError(f"{cid}: candidate input verification failed: {error}") from error
        identity = {"status": "historical/unverifiable", "verified": False,
                    "reason": str(error), "recorded_request_format": record.get("request_format", "canonical-request-json")}
        if (record.get("request_format") == "raw-task-utf8" and isinstance(request, dict)
                and isinstance(request.get("task"), str)):
            identity["raw_task_hash_matches"] = digest_bytes(request["task"].encode("utf-8")) == record.get("request_sha256")
        return identity
    return {"status": "verified", "verified": True,
            "request_sha256": request_hash, "candidate_message_sha256": message_hash}


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
        record = dict(record, input_identity=_input_identity(root, meta, case, record))
        records[cid] = record
        descriptor = case.get("group_contract")
        if descriptor or record.get("group_contract_sha256"):
            if not descriptor or descriptor.get("sha256") != record.get("group_contract_sha256"):
                raise ValueError(f"{cid}: frozen group contract binding changed")
            _group_contract(root, case)
    return meta, records


def _group_contract(root, case):
    descriptor = case.get("group_contract")
    if not descriptor:
        return None
    path = safe_file(root, descriptor["path"])
    if digest_bytes(path.read_bytes()) != descriptor["sha256"]:
        raise ValueError("Frozen group contract changed")
    contract = validate_group_contract(read_json(path))
    if contract.get("id") != case["id"]:
        raise ValueError("Frozen group identity changed")
    return contract


def _stage_template(stage):
    return {"stage_id": stage["id"], "decision": "unresolved",
            "assumption_fidelity": "unknown", "proof_validity": "unknown",
            "scope_accuracy": "unknown", "unnecessary_restriction": False,
            "failure_category": "unresolved", "inherited_from": [],
            "lean_status": "not_run" if stage["lean_required"] else "not_required",
            "declarations": [],
            "notes": ""}


def _validate_review_axes(entry, record):
    """Shared content-review contract, independent of conversation transport."""
    if (entry.get("reviewer_kind") not in {"human", "ai", "fixture"}
            or not isinstance(entry.get("reviewer"), str) or not entry["reviewer"].strip()):
        raise ValueError("Reviewer attribution required")
    if (entry.get("decision") not in {"pass", "fail", "partial", "unresolved"}
            or entry.get("assumption_fidelity") not in {"clean", "drift", "unknown"}
            or entry.get("proof_validity") not in {"valid", "invalid", "unknown"}
            or entry.get("scope_accuracy") not in {"correct", "incorrect", "unknown"}
            or type(entry.get("unnecessary_restriction")) is not bool):
        raise ValueError("Invalid review evidence axes")
    if not isinstance(entry.get("notes"), str) or not entry["notes"].strip():
        raise ValueError("Specific mathematical review notes required")
    if not isinstance(entry.get("findings"), list) or not all(isinstance(f, str) for f in entry["findings"]):
        raise ValueError("Findings must be a string array")
    if entry["decision"] == "pass" and (
        entry["assumption_fidelity"] != "clean" or entry["proof_validity"] != "valid"
        or entry["scope_accuracy"] != "correct" or entry["unnecessary_restriction"]
        or record["status"] != "ok"
    ):
        raise ValueError("Pass contradicts the evidence axes or execution status")


def _validate_group_review(root, case, record, entry, *, response_text=None, lean_evidence=None,
                           additional_obligations=False):
    contract = _group_contract(root, case)
    if contract is None:
        if entry.get("stages"):
            raise ValueError("Stage judgments require a frozen group contract")
        return None
    if entry.get("group_contract_sha256") != case["group_contract"]["sha256"]:
        raise ValueError("Review binds a different group contract")
    rows = entry.get("stages")
    expected = [s["id"] for s in contract["stages"]]
    if not isinstance(rows, list) or not all(isinstance(r, dict) for r in rows) or [r.get("stage_id") for r in rows] != expected:
        raise ValueError("Stage reviews must cover every frozen stage exactly once in order")
    earlier = set()
    lean_pass_needed = False
    completed = 0
    for stage, row in zip(contract["stages"], rows):
        sid = stage["id"]
        if (row.get("decision") not in {"pass", "fail", "partial", "unresolved"}
                or row.get("assumption_fidelity") not in {"clean", "drift", "unknown"}
                or row.get("proof_validity") not in {"valid", "invalid", "unknown"}
                or row.get("scope_accuracy") not in {"correct", "incorrect", "unknown"}
                or type(row.get("unnecessary_restriction")) is not bool):
            raise ValueError(f"{sid}: invalid stage evidence axes")
        if row.get("failure_category") not in {"none", "mathematical", "lean_compilation", "problem_defect", "response_format", "execution", "unresolved"}:
            raise ValueError(f"{sid}: failure category required")
        inherited = row.get("inherited_from")
        if not isinstance(inherited, list) or not all(isinstance(x, str) for x in inherited) or len(inherited) != len(set(inherited)) or not set(inherited) <= earlier:
            raise ValueError(f"{sid}: invalid inherited failure references")
        if any(rows[expected.index(x)]["decision"] == "pass" for x in inherited):
            raise ValueError(f"{sid}: cannot inherit a failure from a passed stage")
        if not isinstance(row.get("notes"), str) or not row["notes"].strip():
            raise ValueError(f"{sid}: specific mathematical review notes required")
        allowed_lean = {"passed", "compile_error", "format_error", "infrastructure_error", "axiom_rejected", "not_run"} if stage["lean_required"] else {"not_required"}
        if row.get("lean_status") not in allowed_lean:
            raise ValueError(f"{sid}: invalid Lean assessment")
        if row["decision"] == "pass":
            if (row["assumption_fidelity"] != "clean" or row["proof_validity"] != "valid"
                    or row["scope_accuracy"] != "correct" or row["unnecessary_restriction"]
                    or row["failure_category"] != "none" or inherited
                    or record["status"] != "ok"
                    or (stage["lean_required"] and row["lean_status"] != "passed")):
                raise ValueError(f"{sid}: stage pass contradicts its evidence")
            completed += stage["points"]
        elif row["failure_category"] == "none":
            raise ValueError(f"{sid}: unresolved or failed stage needs an attribution")
        lean_pass_needed |= stage["lean_required"] and row["lean_status"] == "passed"
        lean_pass_needed |= bool(contract.get("alignment_manifest_required") and row["decision"] == "pass")
        earlier.add(sid)
    if entry["decision"] == "pass" and any(r["decision"] != "pass" for r in rows):
        raise ValueError("Group pass requires every mandatory stage to pass")
    if entry["decision"] == "pass" and (
        entry.get("assumption_fidelity") != "clean" or entry.get("proof_validity") != "valid"
        or entry.get("scope_accuracy") != "correct" or entry.get("unnecessary_restriction") is not False
        or record["status"] != "ok"
    ):
        raise ValueError("Group pass contradicts overall evidence axes")
    if all(r["decision"] == "pass" for r in rows) and entry["decision"] != "pass" and not additional_obligations:
        raise ValueError("All-stage pass must have a matching group decision")
    if lean_pass_needed:
        if lean_evidence is None:
            path = safe_file(root, entry.get("candidate_lean_report", ""))
            receipt = read_json(path)
            report_hash_matches = digest_bytes(path.read_bytes()) == entry.get("candidate_lean_report_sha256")
        else:
            # The reliability owner validates the full original-source artifact
            # and its current material/parent binding before sharing this receipt.
            receipt = lean_evidence
            report_hash_matches = True
        if (not report_hash_matches
                or receipt.get("schema") != "math-gauge.candidate-lean/v1"
                or receipt.get("case_id") != case["id"]
                or receipt.get("response_sha256") != record["response_sha256"]
                or receipt.get("request_sha256") != record["request_sha256"]
                or receipt.get("group_contract_sha256") != case["group_contract"]["sha256"]
                or receipt.get("status") != "passed" or receipt.get("source_repaired") is not False):
            raise ValueError("Stage Lean pass needs bound, unrepaired candidate compilation evidence for this group contract")
        audited = {(d["module"], d["name"]) for d in receipt.get("audit", {}).get("declarations", [])}
        alignment_items = None
        if contract.get("alignment_manifest_required"):
            manifest, span, _ = extract_candidate_alignment(
                response_text if response_text is not None else
                safe_file(root, case['id'] + '/response.md').read_bytes().decode('utf-8'))
            validate_alignment_manifest(manifest, contract)
            if (receipt.get('alignment_manifest') != manifest
                    or receipt.get('alignment_manifest_sha256') != span['sha256']
                    or receipt.get('alignment_source_span') != span
                    or receipt.get('alignment_inventory_validated') is not True):
                raise ValueError("Lean evidence does not bind the candidate's alignment.json")
            validate_alignment_audit(manifest, contract, receipt)
            alignment_items = {x['id']: x for x in manifest['items']}
        for stage, row in zip(contract["stages"], rows):
            if alignment_items is not None and row["decision"] == "pass":
                item = alignment_items[stage['id']]
                if item['status'] != 'complete':
                    raise ValueError(f"{stage['id']}: incomplete candidate obligation cannot pass")
                declared = {(d['file'], d['name']) for d in item['declarations']}
                reviewed = row.get('declarations')
                if (not isinstance(reviewed, list) or not all(
                    isinstance(d, dict) and set(d) == {'file', 'name'}
                    and isinstance(d['file'], str) and isinstance(d['name'], str) for d in reviewed
                ) or {(d['file'], d['name']) for d in reviewed} != declared):
                    raise ValueError(f"{stage['id']}: reviewed declarations differ from candidate alignment")
            if not stage["lean_required"] or row["lean_status"] != "passed":
                continue
            declarations = row.get("declarations")
            if not isinstance(declarations, list) or not declarations:
                raise ValueError(f"{stage['id']}: Lean assessment requires mapped declarations")
            for declaration in declarations:
                if not isinstance(declaration, dict) or set(declaration) != {"file", "name"}:
                    raise ValueError("Mapped declaration requires file and name")
                name = declaration["file"]
                permitted_files = set(receipt.get("files_sha256", {}))
                if stage.get("allow_background_declarations") is True:
                    permitted_files.update(receipt.get("input_files_sha256", {}))
                if (name not in permitted_files or not name.endswith(".lean")
                        or (name[:-5].replace("/", "."), declaration["name"]) not in audited):
                    raise ValueError("Stage declaration was not audited in submitted source")
    return {"stage_count": len(rows), "stage_passes": sum(r["decision"] == "pass" for r in rows),
            "completed_weight": completed, "total_weight": sum(s["points"] for s in contract["stages"]),
            "root_failures": [r["stage_id"] for r in rows if r["decision"] in {"fail", "partial"} and not r["inherited_from"]],
            "problem_defect_flags": [r["stage_id"] for r in rows if r["failure_category"] == "problem_defect"],
            "stages": rows}


def templates(root):
    meta, records = inspect_run(root)
    entries = [
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
    for case, entry in zip(meta["cases"], entries):
        contract = _group_contract(root, case)
        if contract:
            entry.update(group_contract_sha256=case["group_contract"]["sha256"],
                         stages=[_stage_template(s) for s in contract["stages"]])
    return entries


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
        if not records[cid]["input_identity"]["verified"]:
            raise ValueError(f"{cid}: historical candidate input is unverified; archived reviews remain read-only")
        _validate_review_axes(entry, records[cid])
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
        _validate_group_review(root, next(c for c in meta["cases"] if c["id"] == cid), records[cid], entry)
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
    group_diagnostics = {}
    for track in ("determinate", "alignment", "exploration"):
        cases = [c for c in meta["cases"] if c["track"] == track]
        reviewed = [(c, reviews[c["id"]]) for c in cases if c["id"] in reviews]
        # Recheck binding even if a user edits the review file directly.
        for c, r in reviewed:
            if r["response_sha256"] != records[c["id"]]["response_sha256"]:
                raise ValueError("Review binding changed")
            diagnostic = _validate_group_review(root, c, records[c["id"]], r)
            if diagnostic:
                group_diagnostics[c["id"]] = diagnostic
        eligible = [
            (c, r)
            for c, r in reviewed
            if c["case_approved"]
            and r["reviewer_kind"] == "human"
            and meta["origin"] != "replay"
            and r["decision"] != "unresolved"
            and records[c["id"]]["input_identity"]["verified"]
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
        "group_diagnostics": group_diagnostics,
        "input_identity": {cid: record["input_identity"] for cid, record in records.items()},
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
        "| 题目 | 执行 | 输入身份 | 审核来源 | 结论 |",
        "|---|---|---|---|---|",
    ]
    for c in meta["cases"]:
        cid = c["id"]
        r = reviews.get(cid, {})
        lines.append(
            f"| {cid} | {records[cid]['status']} | {records[cid]['input_identity']['status']} | {r.get('reviewer_kind', 'pending')} | {r.get('decision', 'pending')} |"
        )
    unverified = [(cid, record["input_identity"]) for cid, record in records.items()
                  if not record["input_identity"]["verified"]]
    if unverified:
        lines += ["", "以下旧导入记录仅供历史阅读，输入身份未验证，不具备当前模型比较资格："]
        lines += [f"- {cid}: {identity['reason']}（{identity['recorded_request_format']}）"
                  for cid, identity in unverified]
    if group_diagnostics:
        lines += ["", "## 题组诊断", "", "以下是相关阶段的完成情况，不是独立样本通过率。", "",
                  "| 题组 | 完成阶段 | 完成权重 | 独立错误根项 | 题目问题待复核 |",
                  "|---|---:|---:|---|---|"]
        for cid, d in group_diagnostics.items():
            lines.append(f"| {cid} | {d['stage_passes']}/{d['stage_count']} | {d['completed_weight']}/{d['total_weight']} | {', '.join(d['root_failures']) or '—'} | {', '.join(d['problem_defect_flags']) or '—'} |")
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
            diagnostic = _validate_group_review(root, info, record, review)
            if diagnostic:
                row['stage_diagnostics'] = diagnostic
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
