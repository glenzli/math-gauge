"""Source-bound final records: raw self-assessment evidence and finite trajectories.

This owner collects and validates records. Mathematical aggregation remains in
scoring.py; execution remains in execution.py and the existing harness.
"""

import hashlib
import json
from pathlib import Path, PurePosixPath

SCHEMA = "math-gauge.result-record/v1"
ASSESSMENTS = {"complete", "incomplete", "uncertain", "not_stated", "not_requested", "unresolved"}


def descriptor(root, path):
    root, path = Path(root).resolve(), Path(path).resolve()
    if not path.is_file() or not path.is_relative_to(root):
        raise ValueError("Record evidence must be a local regular file")
    raw = path.read_bytes()
    return {"path": str(path.relative_to(root)), "bytes": len(raw),
            "sha256": hashlib.sha256(raw).hexdigest()}


def evidence_bytes(root, item):
    name = item.get("path")
    if not isinstance(name, str) or "\\" in name:
        raise ValueError("Invalid record evidence path")
    relative = PurePosixPath(name)
    root = Path(root).resolve()
    if relative.is_absolute() or ".." in relative.parts or str(relative) != name:
        raise ValueError("Record evidence path escapes its archive")
    path = root / name
    if any(p.is_symlink() for p in [path, *path.parents] if p != root.parent):
        raise ValueError("Record evidence cannot traverse a symlink")
    if not path.is_file() or not path.resolve().is_relative_to(root):
        raise ValueError("Missing record evidence")
    raw = path.read_bytes()
    if len(raw) != item.get("bytes") or hashlib.sha256(raw).hexdigest() != item.get("sha256"):
        raise ValueError("Record evidence bytes changed")
    return raw


def validate_self_assessment(root, assessment):
    if assessment.get("value") not in ASSESSMENTS:
        raise ValueError("Unknown self-assessment value")
    origin = assessment.get("origin")
    if origin not in {"model_structured", "extracted_from_original", "not_available"}:
        raise ValueError("Unknown self-assessment origin")
    evidence = assessment.get("evidence", [])
    if origin in {"extracted_from_original", "model_structured"} and not evidence:
        raise ValueError("Self-assessment needs original evidence")
    if origin == "not_available" and assessment["value"] in {"complete", "incomplete", "uncertain"}:
        raise ValueError("A model judgment cannot be supplied without original evidence")
    for item in evidence:
        raw = evidence_bytes(root, item["source"])
        if item.get("kind") == "structured_alignment":
            data = json.loads(raw)
            items = data.get("items", [])
            if (len(items) != item.get("total")
                    or len({r.get("id") for r in items}) != len(items)
                    or sum(r.get("status") == "complete" for r in items) != item.get("reported_complete")):
                raise ValueError("Structured self-assessment differs from its original alignment")
            if "response_source" in item or "response_span" in item:
                response = evidence_bytes(root, item["response_source"])
                span = item["response_span"]
                start, end = span.get("start_byte"), span.get("end_byte")
                if (type(start) is not int or type(end) is not int
                        or not 0 <= start < end <= len(response)
                        or response[start:end] != raw
                        or span.get("sha256") != hashlib.sha256(raw).hexdigest()):
                    raise ValueError("Structured self-assessment differs from its original response")
            continue
        start, end = item.get("start_byte"), item.get("end_byte")
        if (type(start) is not int or type(end) is not int or not 0 <= start < end <= len(raw)
                or raw[start:end].decode("utf-8") != item.get("quote")):
            raise ValueError("Self-assessment quotation does not match original bytes")
    if origin == "not_available" and not assessment.get("reason"):
        raise ValueError("Missing self-assessment needs an explicit reason")


def trajectory(rounds, *, planned_rounds):
    """Describe only observed adjudicated states; never infer future convergence."""
    if type(planned_rounds) is not int or planned_rounds < 1 or len(rounds) > planned_rounds:
        raise ValueError("Invalid fixed trajectory denominator")
    values = [r.get("evaluation", {}).get("complete_count") for r in rounds]
    totals = [r.get("evaluation", {}).get("total") for r in rounds]
    verified = [type(v) is int and type(t) is int and t > 0 and v == t for v, t in zip(values, totals)]
    first_verified = next((i + 1 for i, v in enumerate(verified) if v), None)
    first_claimed = next((i + 1 for i, r in enumerate(rounds)
                          if r.get("self_assessment", {}).get("value") == "complete"
                          and r.get("self_assessment", {}).get("scope") == "full_task"), None)
    false_claims = [i + 1 for i, r in enumerate(rounds)
                    if r.get("evaluation", {}).get("false_complete_claim") is True]
    if not rounds or len(rounds) < planned_rounds:
        state = "interrupted"
    elif any(v is None or t is None for v, t in zip(values, totals)):
        state = "unresolved"
    elif verified[-1]:
        state = "verified_complete"
    elif (any(b < a for a, b in zip(values, values[1:]))
          or any(r.get("evaluation", {}).get("regressed", 0) not in (None, 0) for r in rounds)):
        state = "regressed"
    elif len(set(values)) == 1:
        state = "incomplete_stable"
    else:
        state = "incomplete_changed"
    held = 0
    if first_verified:
        for v in verified[first_verified:]:
            if not v:
                break
            held += 1
    return {"planned_rounds": planned_rounds, "recorded_rounds": len(rounds),
            "first_claimed_complete_round": first_claimed,
            "first_verified_complete_round": first_verified,
            "verified_maintenance_rounds_after_first_complete": held,
            "false_complete_claim_rounds": false_claims,
            "last_complete_count": values[-1] if values else None,
            "total": totals[-1] if totals else None, "state": state,
            "selection": "last_prescribed_round; no best-of or union",
            "stop_reason": "fixed_rounds_completed" if len(rounds) == planned_rounds else "missing_or_blocked_rounds"}


def validate_formalization_review(root, inputs, review):
    """Bind each mathematical judgment to the selected sealed files and kernel audit."""
    from .scoring import formalization_substitutions

    formalization_substitutions(inputs, review)
    frozen_cases = {case["case_id"]: case for case in inputs["plan"]["case_index"]}
    for case in review["cases"]:
        contract = evidence_bytes(root, case["case_contract"])
        if hashlib.sha256(contract).hexdigest() != frozen_cases[case["case_id"]]["group_contract_sha256"]:
            raise ValueError("Engineering evidence binds a different mathematical contract")
        if set(case.get("background_inputs", {})) != set(json.loads(contract)["immutable_input_files"]):
            raise ValueError("Engineering background inventory differs from the frozen contract")
        manifest = json.loads(evidence_bytes(root, case["source_manifest"]))
        if manifest.get("tree_sha256") != case.get("source_sha256"):
            raise ValueError("Engineering source differs from its original sealed manifest")
        selected = case.get("source_files", {})
        if set(selected) != set(case["compiled_sources"]):
            raise ValueError("Engineering evidence changed its compiled-file inventory")
        for name, item in selected.items():
            raw = evidence_bytes(root, item)
            actual = hashlib.sha256(raw).hexdigest()
            if (actual != case["compiled_sources"][name]
                    or manifest.get("files", {}).get(name, {}).get("sha256") != actual):
                raise ValueError("Compiled engineering source differs from the sealed original")
        kernel = json.loads(evidence_bytes(root, case["kernel_report"]))
        if (kernel.get("files_sha256") != case["compiled_sources"]
                or kernel.get("source_repaired") is not False):
            raise ValueError("Kernel evidence belongs to different or repaired source")
        audit = kernel.get("audit", {})
        modules = kernel.get("modules", [])
        background = {name[:-5].replace("/", "."): hashlib.sha256(evidence_bytes(root, item)).hexdigest()
                      for name, item in case.get("background_inputs", {}).items()}
        selected_modules = {name[:-5].replace("/", "."): case["compiled_sources"][name] for name in selected}
        compiled_modules = {row.get("module"): row.get("source_sha256") for row in modules}
        if any(compiled_modules.get(name) != digest for name, digest in selected_modules.items()):
            raise ValueError("Kernel module receipts differ from the selected engineering source")
        for module in modules:
            name = module.get("module", "")
            if name.startswith("formal_oet.") and name not in selected_modules:
                if background.get(name) != module.get("source_sha256"):
                    raise ValueError("Kernel audit used a different or unprovided frozen predecessor")
        passed = (bool(modules) and all(row.get("exit_code") == 0 and row.get("timeout") is not True
                                      for row in modules)
                  and audit.get("summary", {}).get("passed") is True
                  and not audit.get("summary", {}).get("unexpected_axioms"))
        if (case.get("kernel_status") == "passed") != passed:
            raise ValueError("Selected engineering kernel status differs from its actual report")
        inventory = {(row.get("module"), row.get("name")) for row in audit.get("declarations", [])}
        for item in case["obligations"]:
            if item["complete"] is True:
                for declaration in item["declarations"]:
                    filename, name = declaration.get("file"), declaration.get("name")
                    if (not isinstance(filename, str) or not filename.endswith(".lean")
                            or not isinstance(name, str)
                            or (filename[:-5].replace("/", "."), name) not in inventory):
                        raise ValueError("Completed obligation names a declaration absent from the kernel audit")
        for item in case.get("review_evidence", []):
            evidence_bytes(root, item)
    return {"cases": len(review["cases"]), "passed": True}


def validate_record(root, *, formalization_root=None):
    root = Path(root).resolve()
    record = json.loads((root / "record.json").read_bytes())
    if record.get("schema") != SCHEMA or record.get("benchmark_version") != "0.6.0":
        raise ValueError("Unsupported formal result record")
    if record.get("retention", {}).get("user_requested") is not True:
        raise ValueError("Formal retention requires an explicit user selection")
    rows = record.get("records", [])
    ids = [r.get("id") for r in rows]
    if len(ids) != len(set(ids)) or any(not isinstance(i, str) or not i for i in ids):
        raise ValueError("Repeated or invalid record IDs")
    known = set(ids)
    indexed = {r["id"]: r for r in rows}
    for row in rows:
        ancestors = {row["id"]}
        parent = row.get("parent_id")
        while parent is not None:
            if parent in ancestors or parent not in indexed:
                raise ValueError("Unknown or cyclic record parent")
            ancestors.add(parent)
            if indexed[parent]["case_id"] != row["case_id"]:
                raise ValueError("Record parent belongs to a different task")
            parent = indexed[parent].get("parent_id")
    for row in rows:
        if row.get("parent_id") is not None and row["parent_id"] not in known:
            raise ValueError("Unknown record parent")
        response = row.get("response")
        if response is not None:
            evidence_bytes(root, response)
            expected = row.get("source", {}).get("response_sha256")
            if expected is not None and expected != response["sha256"]:
                raise ValueError("Raw response differs from its execution source")
        elif not row.get("missing_response_reason"):
            raise ValueError("Missing raw response needs an explicit reason")
        validate_self_assessment(root, row["self_assessment"])
        for item in row.get("artifacts", []):
            evidence_bytes(root, item)
        evaluation = row.get("evaluation", {})
        n, total = evaluation.get("complete_count"), evaluation.get("total")
        if n is not None and (type(n) is not int or type(total) is not int or not 0 <= n <= total):
            raise ValueError("Invalid reviewed obligation counts")
    for item in record.get("evidence", []):
        evidence_bytes(root, item)
    if record.get("formalization_review") is not None:
        location = record.get("formalization_evidence_location", "local")
        if location not in {"local", "public_archive"}:
            raise ValueError("Unknown formalization evidence location")
        if location == "public_archive" and formalization_root is None:
            raise ValueError("Private record requires its explicitly selected public engineering archive")
        source_root = Path(formalization_root).resolve() if location == "public_archive" else root
        review = json.loads(evidence_bytes(source_root, record["formalization_review"]))
        inputs = json.loads((root / "scoring-inputs.json").read_bytes())
        validate_formalization_review(source_root, inputs, review)
        policy_raw = (root / "scoring-policy.json").read_bytes()
        policy = json.loads(policy_raw)
        alignment_path = root / "reviews/alignment.json"
        if not alignment_path.exists():
            alignment_path = root / "alignment-review.json"
        alignment = json.loads(alignment_path.read_bytes())
        if (review.get("policy_sha256") != hashlib.sha256(policy_raw).hexdigest()
                or alignment.get("policy_sha256") != review["policy_sha256"]
                or alignment.get("scoring_version") != policy.get("version")):
            raise ValueError("Engineering and alignment reviews bind different scoring policies")
        for filename in ("result.json", "combined-aggregate.json"):
            if filename == "combined-aggregate.json" and location == "public_archive":
                continue
            result = json.loads((root / filename).read_bytes())
            if (result.get("engineering_review_sha256") != record["formalization_review"]["sha256"]
                    or result.get("scoring_method_version") != policy["version"]):
                raise ValueError("Current result binds a different engineering review or scoring method")
    elif (root / "scoring-policy.json").is_file():
        if json.loads((root / "scoring-policy.json").read_bytes()).get("version") == "0.4.0":
            raise ValueError("Current engineering scoring requires all four source-bound reviews")
    if record.get("human_review") != "pending" or record.get("formal_comparison_eligible") is not False:
        raise ValueError("Record migration cannot promote human or execution qualification")
    return {"record_id": record["record_id"], "records": len(rows),
            "raw_responses": sum(r.get("response") is not None for r in rows),
            "candidate_calls_by_migration": record.get("candidate_calls_by_migration"), "passed": True}
