"""Content review of verified multi-turn materials, independent of execution.

Scores are derived from validated stage judgments, never imported numeric
scores. Compilation evidence remains attached to its original source response;
KEEP can reuse unchanged source evidence but always needs a new content review.
"""

import copy
import json
import os
import re
from pathlib import Path

from .benchmarks import identity
from .catalog import digest_bytes, read_json, safe_file, write_json
from .execution import (_candidate_engine, _candidate_imports, _candidate_sources,
                        _override_extraction, extract_candidate_lean, now,
                        verify_candidate_lean)
from .reliability import PARSER_VERSION, _raw, _slot_path, inspect_reliability_run
from .review import _stage_template, _validate_group_review, _validate_review_axes

UNKNOWN_REASONS = {"review_pending", "problem_defect_pending", "infrastructure_error",
                   "execution_error", "not_run", "parent_without_readable_response"}
REASONS = UNKNOWN_REASONS | {"candidate_incomplete", "lean_failure", "format_failure",
                             "mathematical_error"}


def review_binding(meta, record):
    material = record["material"]
    case = next(c for c in meta["plan"]["case_index"] if c["case_id"] == record["case_id"])
    return {"plan_sha256": meta["plan_sha256"], "slot_id": record["slot_id"],
            "evidence_id": record["evidence_id"], "response_sha256": record["response_sha256"],
            "history_sha256": record["history_sha256"],
            "projected_request_sha256": record["projected_request_sha256"],
            "prompt_sha256": record["prompt_sha256"], "parser_version": PARSER_VERSION,
            "parent_slot": material["parent_slot"],
            "parent_response_sha256": material["parent_response_sha256"],
            "parent_material_sha256": material["parent_material_sha256"],
            "material_sha256": material["material_sha256"],
            "body_origin": material["body_origin"], "body_sha256": material["body_sha256"],
            "rationale_sha256": material["rationale_sha256"],
            "request_sha256": case["request_sha256"],
            "group_contract_sha256": case["group_contract_sha256"]}


def _math_template():
    return {"decision": "unresolved", "assumption_fidelity": "unknown",
            "proof_validity": "unknown", "scope_accuracy": "unknown",
            "unnecessary_restriction": False, "reasons": ["review_pending"], "notes": ""}


def reliability_review_templates(root):
    meta, records = inspect_reliability_run(root)
    result = []
    focus = {r["case_id"]: r for r in meta["plan"]["reliability"]["selection"]["cases"]}
    for sid, record in records.items():
        cid = record["case_id"]
        case = next(c for c in meta["plan"]["case_index"] if c["case_id"] == cid)
        contract = read_json(safe_file(root, meta["inputs"][cid]["contract"]))
        entry = {"schema": "math-gauge.reliability-review/v1", "slot_id": sid,
                 "case_id": cid, "binding": review_binding(meta, record),
                 "reviewer": "", "reviewer_kind": "human", "decision": "unresolved",
                 "assumption_fidelity": "unknown", "proof_validity": "unknown",
                 "scope_accuracy": "unknown", "unnecessary_restriction": False,
                 "notes": "", "findings": [], "group_contract_sha256": case["group_contract_sha256"],
                 "stages": [], "format_review": {"decision": "pending", "notes": ""}}
        for stage in contract["stages"]:
            entry["stages"].append(dict(_stage_template(stage), math_review=_math_template()))
        if cid in focus:
            entry["focus_review"] = dict(_math_template(), stage_id=focus[cid]["stage_id"], verdict="undetermined")
        if record["material"]["mode"] == "KEEP":
            entry["keep_rationale_review"] = dict(_math_template(), affects_focus=True,
                                                   affected_stages=[s["id"] for s in contract["stages"]])
        result.append(entry)
    return result


def _math_axis(review):
    if not isinstance(review, dict):
        raise ValueError("Independent mathematical review is required")
    # Share exactly the single-answer evidence axes and review-note rule.
    attributed = dict(review, reviewer="content-axis", reviewer_kind="fixture", findings=[])
    _validate_review_axes(attributed, {"status": "ok"})
    reasons = review.get("reasons")
    if (not isinstance(reasons, list) or len(reasons) != len(set(reasons))
            or not all(isinstance(x, str) and x in REASONS for x in reasons)):
        raise ValueError("Mathematical review requires explicit recognized reasons")
    if "problem_defect_pending" in reasons or "review_pending" in reasons:
        return {"state": "U", "adjudicated": False, "reasons": reasons}
    invalid = (review["proof_validity"] == "invalid" or review["assumption_fidelity"] == "drift"
               or review["scope_accuracy"] == "incorrect" or review["unnecessary_restriction"])
    if review["decision"] == "pass":
        if reasons:
            raise ValueError("Mathematical pass cannot retain unresolved or failure reasons")
        return {"state": "C", "adjudicated": True, "reasons": []}
    if invalid or review["decision"] == "fail":
        if not invalid or "mathematical_error" not in reasons:
            raise ValueError("Mathematical failure requires a specific invalid evidence axis")
        return {"state": "I", "adjudicated": True, "reasons": reasons}
    if review["decision"] == "partial":
        if "candidate_incomplete" not in reasons:
            raise ValueError("Incomplete mathematical review must say candidate_incomplete")
    elif not set(reasons) & UNKNOWN_REASONS:
        raise ValueError("Unresolved mathematical review requires a pending reason")
    return {"state": "U", "adjudicated": not bool(set(reasons) & UNKNOWN_REASONS), "reasons": reasons}


def _combined_math(axes):
    if any(a["state"] == "I" for a in axes):
        return {"state": "I", "adjudicated": True,
                "reasons": sorted({r for a in axes if a["state"] == "I" for r in a["reasons"]})}
    if axes and all(a["state"] == "C" for a in axes):
        return {"state": "C", "adjudicated": True, "reasons": []}
    return {"state": "U", "adjudicated": bool(axes) and all(a["adjudicated"] for a in axes),
            "reasons": sorted({r for a in axes for r in a["reasons"]}) or ["review_pending"]}


def _origin_record(records, record):
    origin = record["material"]["body_origin"]
    if origin is None or origin["slot_id"] not in records:
        raise ValueError("Full original source material is unresolved")
    source = records[origin["slot_id"]]
    if source["response_sha256"] != origin["response_sha256"]:
        raise ValueError("Material origin no longer binds its original assistant response")
    return source


def _source_bundle(root, meta, records, record):
    source = _origin_record(records, record)
    cid = record["case_id"]
    case = next(c for c in meta["plan"]["case_index"] if c["case_id"] == cid)
    return {"response_path": safe_file(root, source["response_path"]),
            "request_path": safe_file(root, meta["inputs"][cid]["request"]),
            "contract_path": safe_file(root, meta["inputs"][cid]["contract"]),
            "record": {"case_id": cid, "response_sha256": source["response_sha256"],
                       "request_sha256": case["request_sha256"],
                       "group_contract_sha256": case["group_contract_sha256"]},
            "binding": review_binding(meta, record)}


def verify_reliability_candidate_lean(root, slot_id, destination, **kwargs):
    """Compile unchanged original source; never create a synthetic response run."""
    meta, records = inspect_reliability_run(root)
    if slot_id not in records:
        raise ValueError("Unknown reliability slot")
    record = records[slot_id]
    bundle = _source_bundle(root, meta, records, record)
    result = verify_candidate_lean(bundle["response_path"].parent, destination,
                                   source_bundle=bundle, **kwargs)
    # Both failures and success keep the current slot identity, while source
    # spans and response hash continue to refer to the actual original node.
    return result


def _artifact_path(directory, value):
    path = Path(value)
    if not path.is_absolute():
        path = Path(directory) / path
    path = path.resolve()
    if not path.is_relative_to(Path(directory).resolve()) or not path.is_file():
        raise ValueError("Candidate Lean artifact path escapes its frozen artifact")
    return path


def _verify_lean_artifact(path, receipt, expected, raw, request, contract):
    """Check saved source, compiler outputs, audit logs and engine identity.

    Hash labels alone are insufficient. A minimal hand-written `passed` receipt
    has no frozen compilation artifact and is rejected, including in fixtures.
    No compiler is invoked here.
    """
    directory = path.parent.resolve()
    if (receipt.get("schema") != "math-gauge.candidate-lean/v1"
            or receipt.get("status") != "passed" or receipt.get("source_repaired") is not False
            or receipt.get("fixture_only") is True
            or receipt.get("case_id") != expected["case_id"]
            or receipt.get("response_sha256") != expected["response_sha256"]
            or receipt.get("request_sha256") != expected["request_sha256"]
            or receipt.get("group_contract_sha256") != expected["group_contract_sha256"]):
        raise ValueError("Lean pass requires a bound unrepaired original-source receipt")
    if (safe_file(directory, "response.md").read_bytes() != raw
            or read_json(safe_file(directory, "request.json")) != request):
        raise ValueError("Candidate Lean receipt does not freeze the original request and response")
    if receipt.get("extraction_override_sha256") is not None:
        override_path = safe_file(directory, "extraction-override.json")
        if digest_bytes(override_path.read_bytes()) != receipt["extraction_override_sha256"]:
            raise ValueError("Candidate Lean extraction evidence changed")
        files = _override_extraction(raw.decode("utf-8"), read_json(override_path))
    else:
        files = extract_candidate_lean(raw.decode("utf-8"))
    submitted = {f["name"]: f["content"] for f in files}
    inputs = {f["name"]: f["content"] for f in request["files"] if f["name"].endswith(".lean")}
    hashes = lambda values: {n: digest_bytes(t.encode()) for n, t in values.items()}
    if (receipt.get("files_sha256") != hashes(submitted)
            or receipt.get("input_files_sha256") != hashes(inputs)
            or receipt.get("source_spans") != [{k: v for k, v in f.items() if k != "content"} for f in files]):
        raise ValueError("Candidate Lean receipt source inventory changed")
    for kind, values in (("submitted", submitted), ("inputs", inputs)):
        actual = {str(p.relative_to(directory / kind)) for p in (directory / kind).rglob("*") if p.is_file()}
        if actual != set(values):
            raise ValueError("Candidate Lean artifact has missing or extra source files")
        for name, content in values.items():
            if safe_file(directory, kind + "/" + name).read_bytes() != content.encode():
                raise ValueError("Candidate Lean source bytes changed after compilation")
    manifest_path = safe_file(directory, "manifest.json")
    manifest_hash = digest_bytes(manifest_path.read_bytes())
    manifest = read_json(manifest_path)
    if (manifest_hash != receipt.get("manifest_sha256") or manifest_hash != receipt.get("artifact_sha256")
            or _artifact_path(directory, receipt.get("manifest", "")) != manifest_path.resolve()
            or any(manifest.get(key) != receipt.get(key) for key in (
                "case_id", "response_sha256", "request_sha256", "group_contract_sha256",
                "files_sha256", "input_files_sha256", "alignment_manifest_sha256", "extraction_override_sha256"))):
        raise ValueError("Candidate Lean compilation manifest changed")
    engine, engine_path = _candidate_engine()
    template = engine_path.with_name("audit-candidate.lean.in")
    engine_identity = {"execution": digest_bytes(Path(__file__).with_name("execution.py").read_bytes()),
                       "dependency_verifier": digest_bytes(engine_path.read_bytes()),
                       "audit_template": digest_bytes(template.read_bytes())}
    if (receipt.get("engine_identity") != engine_identity
            or receipt.get("engine_sha256") != digest_bytes(json.dumps(engine_identity, sort_keys=True).encode())):
        raise ValueError("Candidate Lean engine or audit identity changed")
    sources, _ = _candidate_sources(submitted, inputs, lambda text: _candidate_imports(text, engine["clean_lean"]))
    ordered = [{"name": name, "sha256": digest_bytes(text.encode()),
                "origin": "submitted" if name in submitted else "frozen-input"} for name, text in sources]
    if manifest.get("ordered_sources") != ordered:
        raise ValueError("Candidate Lean complete compilation closure changed")
    modules = receipt.get("modules")
    names = [n[:-5].replace("/", ".") for n, _ in sources]
    if (not isinstance(modules, list) or len(modules) != len(names) + 1
            or [m.get("module") for m in modules[:-1]] != names
            or not re.fullmatch(r"GaugeCandidateAudit_[0-9a-f]+", modules[-1].get("module", ""))):
        raise ValueError("Candidate Lean receipt lacks its complete compiled module inventory")
    audit_source = template.read_text().replace("{{IMPORTS}}", "\n".join("import " + n for n in names)).replace(
        "{{MODULES}}", "#[" + ", ".join(json.dumps(n, ensure_ascii=False) for n in names) + "]")
    if safe_file(directory, "audit.lean").read_bytes() != audit_source.encode():
        raise ValueError("Candidate Lean audit source changed")
    for index, module in enumerate(modules):
        source = sources[index][1].encode() if index < len(sources) else audit_source.encode()
        log = _artifact_path(directory, module.get("log", ""))
        artifact = safe_file(directory, "oleans/" + module["module"].replace(".", "/") + ".olean")
        if (module.get("exit_code") != 0 or module.get("timeout") is not False
                or module.get("source_sha256") != digest_bytes(source)
                or module.get("log_sha256") != digest_bytes(log.read_bytes())
                or module.get("olean_sha256") != digest_bytes(artifact.read_bytes()) or not artifact.stat().st_size):
            raise ValueError("Candidate Lean compile log or object artifact changed")
    audit_log = _artifact_path(directory, modules[-1]["log"]).read_text(encoding="utf-8")
    summaries = [json.loads(x) for x in re.findall(r"CANDIDATE_AUDIT_SUMMARY (\{[^\r\n]*\})", audit_log)]
    declarations = [json.loads(x) for x in re.findall(r"CANDIDATE_DECL (\{[^\r\n]*\})", audit_log)]
    audit = receipt.get("audit", {})
    if (len(summaries) != 1 or summaries[0].get("passed") is not True
            or summaries[0] != audit.get("summary") or declarations != audit.get("declarations")
            or not declarations or len(declarations) != summaries[0].get("declaration_count")
            or len({d["name"] for d in declarations}) != len(declarations)
            or any(d["module"] not in names for d in declarations)
            or set(summaries[0].get("axiom_union", [])) - engine["ALLOWED_AXIOMS"]):
        raise ValueError("Candidate Lean axiom audit does not match the frozen audit log")
    isolation = receipt.get("isolation", {})
    probes = isolation.get("probes", [])
    policy = safe_file(directory, "compiler.sb").read_bytes()
    if (isolation.get("network") != "denied" or isolation.get("process_fork") != "denied"
            or digest_bytes(policy) != isolation.get("policy_sha256") or len(probes) != 3
            or [p.get("expected") for p in probes] != ["allowed", "denied", "denied"]
            or not all(p.get("passed") is True for p in probes)):
        raise ValueError("Candidate Lean lacks successful frozen isolation evidence")
    dependency = receipt.get("dependency", {})
    try:
        if (digest_bytes(Path(dependency["lean"]).read_bytes()) != dependency["lean_sha256"]
                or digest_bytes((Path(dependency["root"]) / "lake-manifest.json").read_bytes()) != dependency["lockfile_sha256"]):
            raise ValueError("Candidate Lean dependency identity changed")
    except (KeyError, OSError) as error:
        raise ValueError("Candidate Lean dependency identity is unavailable") from error
    return receipt


def _lean_evidence(root, meta, records, record, entry, contract):
    path_name = entry.get("candidate_lean_report")
    if not path_name:
        return None
    artifact_root = Path(root)
    source_root = entry.get("candidate_lean_source_run")
    if source_root is not None:
        allowed = {str(Path(v["source_root"]).resolve()) for v in meta.get("reused_from", {}).values()}
        if str(Path(source_root).resolve()) not in allowed:
            raise ValueError("External Lean evidence is not a frozen reusable dependency")
        source_meta, source_records = inspect_reliability_run(source_root)
        if source_meta["plan_sha256"] != meta["plan_sha256"]:
            raise ValueError("External Lean evidence belongs to a different plan")
        artifact_root = Path(source_root)
    path = safe_file(artifact_root, path_name)
    if digest_bytes(path.read_bytes()) != entry.get("candidate_lean_report_sha256"):
        raise ValueError("Candidate Lean report changed")
    receipt = read_json(path)
    binding = receipt.get("reliability_binding")
    source = _origin_record(records, record)
    current_binding = review_binding(meta, record)
    if not isinstance(binding, dict) or any(binding.get(key) != current_binding[key] for key in (
        "plan_sha256", "parser_version", "request_sha256", "group_contract_sha256", "body_origin", "body_sha256")):
        raise ValueError("Candidate Lean report does not bind this material's original source")
    # Reuse is limited to the same original body and complete source project.
    # The current slot still has its own independently checked semantic review.
    if source_root is None:
        origin_binding_record = records.get(binding.get("slot_id"))
    else:
        origin_binding_record = source_records.get(binding.get("slot_id"))
    if origin_binding_record is None:
        raise ValueError("Candidate Lean evidence source slot is unavailable")
    origin_meta = meta if source_root is None else source_meta
    if binding != review_binding(origin_meta, origin_binding_record):
        raise ValueError("Candidate Lean source slot/history/material binding changed")
    bundle = _source_bundle(root, meta, records, record)
    raw = _raw(root, source)
    return _verify_lean_artifact(path, receipt, bundle["record"], raw,
                                 read_json(bundle["request_path"]), contract)


def _validate_entry(root, meta, records, entry):
    if not isinstance(entry, dict) or entry.get("schema") != "math-gauge.reliability-review/v1":
        raise ValueError("Unsupported reliability review")
    sid = entry.get("slot_id")
    if sid not in records:
        raise ValueError("Review references an unexecuted projection slot")
    record = records[sid]
    if entry.get("case_id") != record["case_id"] or entry.get("binding") != review_binding(meta, record):
        raise ValueError("Reliability review raw/history/parent/material binding changed")
    raw = _raw(root, record)
    status = "ok" if raw is not None else "error"
    _validate_review_axes(entry, {"status": status})
    cid = record["case_id"]
    case = next(c for c in meta["plan"]["case_index"] if c["case_id"] == cid)
    contract = read_json(safe_file(root, meta["inputs"][cid]["contract"]))
    descriptor = {"id": cid, "group_contract": {"path": meta["inputs"][cid]["contract"],
                                                "sha256": case["group_contract_sha256"]}}
    source_record = record
    if record["material"]["status"] == "resolved":
        source_record = _origin_record(records, record)
    single_record = {"status": status, "response_sha256": source_record["response_sha256"],
                     "request_sha256": case["request_sha256"]}
    receipt = _lean_evidence(root, meta, records, record, entry, contract)
    if any(s.get("lean_status") == "passed" for s in entry.get("stages", [])) and receipt is None:
        raise ValueError("Lean pass requires actual original-source compilation evidence")
    # Reject unverified Lean passes before the shared validator can use the
    # legacy single-answer minimal-receipt compatibility path.
    if contract.get("alignment_manifest_required") and any(
        s.get("decision") == "pass" for s in entry.get("stages", [])) and receipt is None:
        raise ValueError("Alignment pass requires actual original-source compilation evidence")
    format_review = entry.get("format_review")
    if (not isinstance(format_review, dict) or format_review.get("decision") not in {"valid", "invalid", "pending"}
            or not isinstance(format_review.get("notes"), str) or not format_review["notes"].strip()):
        raise ValueError("Current response format needs attributed review notes")
    material = record["material"]
    if format_review["decision"] == "valid" and material["status"] != "resolved":
        raise ValueError("Unresolved material cannot receive a valid format decision")
    if material["format_status"] == "invalid" and entry["decision"] == "pass":
        raise ValueError("Unresolved or invalid full material cannot strictly pass")
    extra_rationale = (_math_axis(entry.get("keep_rationale_review"))
                       if material["mode"] == "KEEP" else None)
    has_extra_failure = (format_review["decision"] != "valid"
                         or (extra_rationale is not None and extra_rationale["state"] != "C"))
    diagnostic = _validate_group_review(root, descriptor, single_record, entry,
                                        response_text=_raw(root, source_record).decode("utf-8") if raw is not None else "",
                                        lean_evidence=receipt, additional_obligations=has_extra_failure)
    stage_axes = []
    weights = []
    for stage, row in zip(contract["stages"], entry["stages"]):
        axis = _math_axis(row.get("math_review"))
        if any(row.get(k) != row["math_review"].get(k) for k in (
            "assumption_fidelity", "proof_validity", "scope_accuracy", "unnecessary_restriction")):
            raise ValueError("Stage mathematics axes contradict its separate mathematical review")
        if row["failure_category"] == "mathematical" and axis["state"] == "C":
            raise ValueError("Mathematical stage failure contradicts a mathematical pass")
        if row["decision"] == "pass" and axis["state"] != "C":
            raise ValueError("Strict stage pass contradicts its independent mathematics review")
        if row["failure_category"] == "problem_defect":
            axis = {"state": "U", "adjudicated": False, "reasons": ["problem_defect_pending"]}
        stage_axes.append(axis)
        unknown = (row["failure_category"] in {"problem_defect", "execution", "unresolved"}
                   or row["decision"] == "unresolved" or row["lean_status"] == "infrastructure_error"
                   or bool(set(axis["reasons"]) & UNKNOWN_REASONS))
        value = None if unknown else 1 if row["decision"] == "pass" else 0
        weights.append((stage["points"], value))
    rationale_axis = None
    if material["mode"] == "KEEP":
        rationale = entry.get("keep_rationale_review")
        rationale_axis = _math_axis(rationale)
        if (type(rationale.get("affects_focus")) is not bool
                or not isinstance(rationale.get("affected_stages"), list)
                or not set(rationale["affected_stages"]) <= {s["id"] for s in contract["stages"]}):
            raise ValueError("KEEP rationale needs explicit scope of its current claims")
        if rationale_axis["state"] != "C" and entry["decision"] == "pass":
            raise ValueError("KEEP cannot strictly pass without a valid current rationale")
        for index, stage in enumerate(contract["stages"]):
            if stage["id"] in rationale["affected_stages"]:
                stage_axes[index] = _combined_math([stage_axes[index], rationale_axis])
                if rationale_axis["state"] != "C":
                    weights[index] = (weights[index][0], 0 if rationale_axis["adjudicated"] else None)
    elif "keep_rationale_review" in entry:
        raise ValueError("Only KEEP has a current rationale review")
    focus_rows = {r["case_id"]: r for r in meta["plan"]["reliability"]["selection"]["cases"]}
    focus_axis = {"state": "U", "adjudicated": False, "reasons": ["review_pending"]}
    if cid in focus_rows:
        focus = entry.get("focus_review")
        focus_axis = _math_axis(focus)
        if (focus.get("stage_id") != focus_rows[cid]["stage_id"]
                or focus.get("verdict") not in {"true", "false", "undetermined"}):
            raise ValueError("Focus review binds a different frozen target")
        if focus_axis["state"] == "C" and focus["verdict"] != focus_rows[cid]["expected_truth"]:
            raise ValueError("Focus pass contradicts the independently frozen target truth")
        if rationale_axis is not None and entry["keep_rationale_review"]["affects_focus"]:
            focus_axis = _combined_math([focus_axis, rationale_axis])
        focus_stage = next(r for r in entry["stages"] if r["stage_id"] == focus_rows[cid]["stage_id"])
        if focus_stage["failure_category"] == "problem_defect":
            focus_axis = {"state": "U", "adjudicated": False, "reasons": ["problem_defect_pending"]}
        stage_axis = stage_axes[[s["id"] for s in contract["stages"]].index(focus_rows[cid]["stage_id"])]
        if (focus_rows[cid].get("scope", "stage") == "stage"
                and stage_axis["adjudicated"] and focus_axis["adjudicated"]
                and stage_axis["state"] != focus_axis["state"]):
            raise ValueError("Whole-stage focus review contradicts that stage's mathematical judgment")
        if stage_axis["state"] == "C" and focus_axis["state"] == "I":
            raise ValueError("A completed stage cannot contain an incorrect required focus subclaim")
    elif "focus_review" in entry:
        raise ValueError("Unselected case has no frozen focus target")
    total = sum(w for w, _ in weights)
    lower = sum(w for w, v in weights if v == 1) / total
    upper = sum(w for w, v in weights if v != 0) / total
    exact = lower if all(v is not None for _, v in weights) else None
    strict = (False if any(v == 0 for _, v in weights) else
              True if all(v == 1 for _, v in weights) else None)
    if rationale_axis is not None and rationale_axis["state"] != "C":
        strict = False if rationale_axis["adjudicated"] else (False if strict is False else None)
    reasons = sorted({r for axis in stage_axes + ([rationale_axis] if rationale_axis is not None else [])
                      for r in axis["reasons"]})
    reasons.extend("lean_failure" for r in entry["stages"]
                   if r["lean_status"] in {"compile_error", "axiom_rejected"})
    reasons.extend("format_failure" for r in entry["stages"]
                   if r["lean_status"] == "format_error" or r["failure_category"] == "response_format")
    reasons.extend("infrastructure_error" for r in entry["stages"] if r["lean_status"] == "infrastructure_error")
    if format_review["decision"] != "valid":
        reasons.append("format_failure" if format_review["decision"] == "invalid" else "review_pending")
        strict = False if format_review["decision"] == "invalid" else (False if strict is False else None)
    if material["status"] != "resolved":
        # A KEEP without a valid immediate material never silently borrows A1.
        lower, upper, exact = 0, 1, None
        strict = False if format_review["decision"] == "invalid" else None
        if material["mode"] == "KEEP" and focus_axis["state"] == "C":
            focus_axis = {"state": "U", "adjudicated": False, "reasons": ["format_failure"]}
    if entry["decision"] == "pass" and strict is not True:
        raise ValueError("Whole strict pass contradicts its current stage, rationale or format evidence")
    whole_math = _combined_math(stage_axes + ([rationale_axis] if rationale_axis is not None else []))
    global_invalid = (entry["proof_validity"] == "invalid" or entry["assumption_fidelity"] == "drift"
                      or entry["scope_accuracy"] == "incorrect" or entry["unnecessary_restriction"])
    if global_invalid and whole_math["state"] != "I":
        raise ValueError("Whole-answer mathematical failure needs an attributed stage or current rationale failure")
    if strict is True and entry["decision"] != "pass":
        raise ValueError("Computed strict pass contradicts the whole-answer decision")
    if material["status"] != "resolved" and whole_math["state"] == "C":
        whole_math = {"state": "U", "adjudicated": False, "reasons": ["format_failure"]}
    strict_state = "C" if strict is True else "I" if whole_math["state"] == "I" else "U"
    if raw is None:
        if strict is True or whole_math["state"] == "C" or focus_axis["state"] == "C":
            raise ValueError("No-response technical slots cannot acquire a content pass")
        whole_math = focus_axis = {"state": "E", "adjudicated": False,
                                   "reasons": [record.get("reason") or "execution_error"]}
        strict_state, strict = "E", None
        lower, upper, exact = 0, 1, None
    return {"strict_pass": strict,
            "completion": {"lower": lower, "upper": upper, "exact": exact},
            "whole_strict": {"state": strict_state, "adjudicated": strict is not None,
                             "reasons": sorted(set(reasons))},
            "whole_math": whole_math, "focus_math": focus_axis,
            "problem_defect": any(r["failure_category"] == "problem_defect" for r in entry["stages"]),
            "group_diagnostic": diagnostic, "lean_evidence_verified": receipt is not None}


def _load_review_snapshot(root, meta, records, snapshot=None):
    root = Path(root)
    path = root / "reliability-reviews.json"
    if snapshot is not None and (type(snapshot) is not int or snapshot <= 0):
        raise ValueError("Review snapshot must be a positive integer version")
    if not path.exists():
        if snapshot is not None:
            raise ValueError("Requested review snapshot does not exist")
        return {}, None, {"schema": "math-gauge.reliability-review-index/v1",
                          "active_snapshot": None, "snapshots": []}
    index = read_json(path)
    if (not isinstance(index, dict) or index.get("schema") != "math-gauge.reliability-review-index/v1"
            or not isinstance(index.get("snapshots"), list)):
        raise ValueError("Unsupported reliability review snapshot index")
    chosen = snapshot if snapshot is not None else index.get("active_snapshot")
    prior_hash = None
    picked = None
    descriptors = index["snapshots"]
    if index.get("active_snapshot") != len(descriptors) or not descriptors:
        raise ValueError("Active review snapshot index changed")
    for version, descriptor in enumerate(descriptors, 1):
        if descriptor.get("version") != version or descriptor.get("path") != f"review-snapshots/{version:06d}.json":
            raise ValueError("Review snapshot sequence changed")
        raw = safe_file(root, descriptor["path"]).read_bytes()
        value = json.loads(raw)
        if (digest_bytes(raw) != descriptor.get("file_sha256")
                or value.get("schema") != "math-gauge.reliability-review-snapshot/v1"
                or value.get("version") != version or value.get("run_id") != meta["run_id"]
                or value.get("plan_sha256") != meta["plan_sha256"]
                or value.get("previous_snapshot_sha256") != prior_hash
                or value.get("snapshot_sha256") != descriptor.get("snapshot_sha256")
                or value.get("snapshot_sha256") != identity({k: v for k, v in value.items() if k != "snapshot_sha256"})
                or set(value.get("reviews", {})) != set(records)):
            raise ValueError("Append-only review snapshot evidence changed")
        prior_hash = value["snapshot_sha256"]
        if version == chosen:
            picked = value
    if picked is None:
        raise ValueError("Requested review snapshot does not exist")
    reviews = {sid: entry for sid, entry in picked["reviews"].items() if entry is not None}
    for sid, entry in reviews.items():
        if (entry.get("slot_id") != sid
                or entry.get("review_sha256") != identity({k: v for k, v in entry.items() if k != "review_sha256"})):
            raise ValueError("Saved reliability review evidence changed")
        _validate_entry(root, meta, records, entry)
    return reviews, {"version": picked["version"], "sha256": picked["snapshot_sha256"]}, index


def apply_reliability_reviews(root, entries, *, revise=False, expected_snapshot=None):
    meta, records = inspect_reliability_run(root)
    if not isinstance(entries, list):
        raise ValueError("Reliability reviews must be an array")
    root = Path(root)
    path = root / "reliability-reviews.json"
    old, previous, index = _load_review_snapshot(root, meta, records)
    if expected_snapshot is not None and expected_snapshot != (previous["sha256"] if previous else None):
        raise ValueError("Active review snapshot differs from the expected snapshot")
    updated = copy.deepcopy(old)
    seen = set()
    for entry in entries:
        sid = entry.get("slot_id")
        if sid in seen:
            raise ValueError("A snapshot cannot contain duplicate reviews for one slot")
        seen.add(sid)
        if sid in updated and not revise:
            raise ValueError("Review already exists; use explicit revise to append a new snapshot")
        _validate_entry(root, meta, records, entry)
        saved = {k: v for k, v in copy.deepcopy(entry).items() if k not in {
            "review_sha256", "recorded_at", "review_revision", "supersedes_review_sha256"}}
        saved.update(recorded_at=now(), review_revision=old.get(sid, {}).get("review_revision", 0) + 1,
                     supersedes_review_sha256=old[sid]["review_sha256"] if sid in old else None)
        saved["review_sha256"] = identity(saved)
        updated[sid] = saved
    version = len(index["snapshots"]) + 1
    value = {"schema": "math-gauge.reliability-review-snapshot/v1", "version": version,
             "run_id": meta["run_id"], "plan_sha256": meta["plan_sha256"], "created_at": now(),
             "previous_snapshot_sha256": previous["sha256"] if previous else None,
             "revised": bool(revise), "reviews": {sid: updated.get(sid) for sid in records}}
    value["snapshot_sha256"] = identity(value)
    relative = f"review-snapshots/{version:06d}.json"
    destination = root / relative
    if path.exists() and read_json(path) != index:
        raise ValueError("Active review snapshot changed during review; retry with the current snapshot")
    destination.parent.mkdir(parents=True, exist_ok=True)
    try:
        with destination.open("x", encoding="utf-8") as stream:
            stream.write(json.dumps(value, ensure_ascii=False, indent=2) + "\n")
    except FileExistsError as error:
        raise ValueError("Review snapshot output already exists; preserve its original evidence") from error
    index["snapshots"].append({"version": version, "path": relative,
                                "snapshot_sha256": value["snapshot_sha256"],
                                "file_sha256": digest_bytes(destination.read_bytes())})
    index["active_snapshot"] = version
    temporary = path.with_name(".reliability-reviews-" + value["snapshot_sha256"] + ".json")
    write_json(temporary, index)
    os.replace(temporary, path)
    return updated


def reliability_score_inputs(root, *, snapshot=None, audit_snapshot=None):
    """Return only recomputed, fully bound score evidence for aggregation."""
    from .eligibility import verify_execution_eligibility

    meta, records = inspect_reliability_run(root)
    reviews, snapshot_identity, _ = _load_review_snapshot(root, meta, records, snapshot)
    execution_eligibility = verify_execution_eligibility(
        root, meta=meta, records=records, audit_snapshot=audit_snapshot)
    rows = []
    for sid, record in records.items():
        entry = reviews.get(sid)
        if entry is None:
            state = "E" if record["status"] in {"execution_error", "blocked"} else "U"
            reason = record.get("reason") or ("review_pending" if record["started"] else "not_run")
            axis = {"state": state, "adjudicated": False, "reasons": [reason]}
            result = {"strict_pass": None, "completion": {"lower": 0, "upper": 1, "exact": None},
                      "whole_strict": copy.deepcopy(axis), "whole_math": copy.deepcopy(axis),
                      "focus_math": copy.deepcopy(axis), "problem_defect": False}
        else:
            if entry.get("review_sha256") != identity({k: v for k, v in entry.items() if k != "review_sha256"}):
                raise ValueError("Saved reliability review evidence changed")
            result = _validate_entry(root, meta, records, entry)
        origin = record.get("origin", meta["origin"])
        execution = execution_eligibility["slots"][sid]
        rows.append({"slot_id": sid, "case_id": record["case_id"],
                     "started": record["started"], "status": record["status"],
                     "selected": True, "reason": record.get("reason"),
                     "execution_status": record["status"],
                     "model_label": meta["model_label"], "origin": origin,
                     "case_approval_evidence_verified": meta["case_approval_evidence_verified"][record["case_id"]],
                     "case_approval_source": meta["inputs"][record["case_id"]].get("case_approval_source"),
                     "fixture_only": origin in {"fixture", "replay"},
                     "evidence_id": record["evidence_id"],
                     "slot_record_sha256": meta["slot_record_sha256"][sid],
                     "reused_from": meta.get("reused_from", {}).get(sid),
                     "binding": review_binding(meta, record),
                     "response_sha256": record["response_sha256"],
                     "history_sha256": record["history_sha256"],
                     "material_sha256": record["material_sha256"],
                     "reviewer": entry.get("reviewer") if entry else None,
                     "reviewer_kind": entry.get("reviewer_kind") if entry else None,
                     "review_sha256": entry.get("review_sha256") if entry else None,
                     "focus_verdict": entry.get("focus_review", {}).get("verdict") if entry else None,
                     "execution_eligibility": copy.deepcopy(execution),
                     "execution_receipt_sha256": execution.get("receipt_sha256"),
                     "execution_audit_sha256": execution.get("audit_sha256"),
                     "comparison_eligible": execution["eligible"] is True, **result})
    return {"plan": meta["plan"], "model_label": meta["model_label"], "slots": rows,
            "root": str(Path(root).resolve()),
            "run_id": meta["run_id"], "origin": meta["origin"],
            "review_snapshot": snapshot_identity,
            "audit_snapshot": execution_eligibility.get("audit_snapshot"),
            "execution_eligibility": {key: value for key, value in execution_eligibility.items()
                                      if key != "slots"},
            "execution_contract_sha256": meta["execution_contract_sha256"],
            **{key: meta.get(key) for key in ("selected_slot_ids", "candidate_calls", "transport_attempts",
                 "budget_stop_reason", "unrun_slots", "budget_scope", "unseen_plan_fragments_accounted_for",
                 "prior_transport_attempts", "prior_known_total_tokens", "cumulative_transport_attempts",
                 "cumulative_known_total_tokens", "cumulative_total_tokens", "cumulative_token_usage_complete")},
            }
