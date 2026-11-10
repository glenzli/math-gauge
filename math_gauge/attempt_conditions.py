"""Source bindings for parallel first-attempt and admitted-retry archives.

No scoring or execution lives here. Each condition selects complete retained
inputs, engineering and trajectory judgments; it cannot mix the two conditions.
"""
import json


CONDITIONS = {"single_attempt", "nonlogical_retry_3"}
RESEARCH_SOURCES = {"theorem_extension_inputs", "background_check_inputs"}


def load_sources(root, record, condition, *, public_root=None):
    from .records import evidence_bytes
    from .benchmarks import validate_plan
    if record.get("attempt_condition_sources") is None:
        return None
    if condition not in CONDITIONS:
        raise ValueError("Unknown retained attempt condition")
    manifest = json.loads(evidence_bytes(root, record["attempt_condition_sources"]))
    if (manifest.get("schema") != "math-gauge.attempt-condition-sources/v1"
            or manifest.get("selection") != "first_normal_delivery_after_counted_operational_failures"
            or set(manifest.get("conditions", {})) != CONDITIONS
            or manifest.get("human_review") != "pending"
            or manifest.get("formal_comparison_eligible") is not False):
        raise ValueError("Attempt conditions require complete separate source bundles")
    external = record.get("formalization_evidence_location") == "public_archive"
    if external and public_root is None:
        raise ValueError("Private attempt sources need an explicit public engineering archive")
    engineering_root = public_root if external else root
    result = {}
    for key, bundle in manifest["conditions"].items():
        required = {"scoring_inputs", "formalization_review", "alignment_review",
                    "manuscript_completion_inputs", "source_records"}
        if (not required <= set(bundle) or set(bundle) - required - RESEARCH_SOURCES
                or bundle["formalization_review"] is None or bundle["alignment_review"] is None):
            raise ValueError("Attempt condition lost a source component")
        inputs = json.loads(evidence_bytes(root, bundle["scoring_inputs"]))
        validate_plan(inputs["plan"])
        if inputs.get("model_label") != record["model"]["requested_label"]:
            raise ValueError("Attempt condition belongs to another model")
        engineering = json.loads(evidence_bytes(engineering_root, bundle["formalization_review"]))
        alignment = json.loads(evidence_bytes(root, bundle["alignment_review"]))
        source_records = json.loads(evidence_bytes(root, bundle["source_records"]))
        if {r["id"] for r in source_records["records"]} != {r["slot_id"] for r in inputs["slots"]}:
            raise ValueError("Attempt sources changed their fixed A1 inventory")
        for row in source_records["records"]:
            raw = row.get("response")
            if raw is not None:
                evidence_bytes(root, raw)
            scored = next(s for s in inputs["slots"] if s["slot_id"] == row["id"])
            if (scored.get("response_sha256") != (raw or {}).get("sha256")
                    or any(row["evaluation"].get(f) != scored.get(f) for f in ("completion", "strict_pass"))):
                raise ValueError("Attempt sources changed the selected answer or original judgment")
            if external:
                from .claude_code_evidence import validate_delivery, validate_failure
                if raw is not None:
                    if row.get("agy_native_evidence") is not None:
                        from .agy_evidence import validate_delivery as validate_agy_delivery
                        validate_agy_delivery(root, row, evidence_bytes)
                        continue
                    native = row.get("native_delivery")
                    if not isinstance(native, dict) or native.get("response", {}).get("sha256") != raw["sha256"]:
                        raise ValueError("Retry answer lost its original native delivery")
                    validate_delivery(root, native, evidence_bytes)
                else:
                    if row.get("delivery_failure") is not None:
                        from .records import validate_native_delivery_failure
                        validate_native_delivery_failure(root, row)
                    elif (row.get("delivery_status") == "not_run"
                            and scored.get("delivery_status") == "not_run"
                            and row.get("agy_native_evidence") is None
                            and row.get("native_delivery") is None
                            and scored.get("completion", {}).get("exact") is None
                            and scored.get("strict_pass") is None):
                        # An unrun slot has no native failure to validate. Its
                        # fixed denominator and unresolved judgment remain.
                        continue
                    else:
                        try:
                            validate_failure(root, row, evidence_bytes)
                        except KeyError as error:
                            raise ValueError("Missing answer needs an unresolved unrun slot or native failure evidence") from error
        if external:
            manuscript = json.loads(evidence_bytes(root, bundle["manuscript_completion_inputs"]))
        else:
            manuscript = None
            if not isinstance(bundle["manuscript_completion_inputs"], dict) or set(
                    bundle["manuscript_completion_inputs"]) != {"sha256"}:
                raise ValueError("Public attempt manuscript source must remain opaque")
        research = {}
        for name in RESEARCH_SOURCES & set(bundle):
            if external:
                value = json.loads(evidence_bytes(root, bundle[name]))
                if (value.get("model_label") != record["model"]["requested_label"]
                        or any((r.get("response") or {}).get("sha256") != next(
                            (s.get("response_sha256") for s in inputs["slots"] if s["case_id"] == r["case_id"]), None)
                            for r in value.get("slots", []))):
                    raise ValueError("Attempt research source differs from its selected A1 answers")
                research[name] = value
            elif not isinstance(bundle[name], dict) or set(bundle[name]) != {"sha256"}:
                raise ValueError("Public attempt research sources must remain opaque")
        result[key] = dict(bindings=bundle, inputs=inputs, engineering=engineering,
                           alignment=alignment, manuscript=manuscript, records=source_records,
                           **research)
    first = result["single_attempt"]["bindings"]
    if (first["scoring_inputs"]["path"] != "scoring-inputs.json"
            or first["formalization_review"] != record["formalization_review"]
            or external and first["manuscript_completion_inputs"] != record["manuscript_completion_inputs"]):
        raise ValueError("First-attempt source bundle must preserve the original archive")
    for name in RESEARCH_SOURCES:
        if ((name in first) != (name in result["nonlogical_retry_3"]["bindings"])
                or external and name in first and first[name] != record.get(name)):
            raise ValueError("Research attempt sources need paired conditions and an unchanged first source")
    first_inputs, retry_inputs = (result[c]["inputs"] for c in ("single_attempt", "nonlogical_retry_3"))
    if (first_inputs["plan"] != retry_inputs["plan"]
            or [r["slot_id"] for r in first_inputs["slots"]] != [r["slot_id"] for r in retry_inputs["slots"]]):
        raise ValueError("Retry sources cannot change the frozen plan or denominators")
    return result[condition]
