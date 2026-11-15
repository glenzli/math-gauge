#!/usr/bin/env python3
"""Anonymous, display-only attempt counts from a bound native history archive.

This module neither calls candidates nor changes answer selection, judgments or
scores. A lifecycle can end before an API call; it is never an HTTP-call count.
The source paths and lifecycle identities belong only in the private receipt.
"""

import argparse
from collections import Counter, defaultdict
from datetime import datetime
import hashlib
import json
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
PUBLIC_PATH = Path("results/execution-attempts/v0.1.0/current.json")
SCHEMA = "math-gauge.execution-attempt-summary/v1"
VERSION = "0.1.0"
COUNT_KEYS = {
    "lifecycle_records", "effective_attempts", "system_exclusions",
    "normal_finals", "consumed_delivery_failures",
}
EXCLUSION_CLASSES = {
    "source-bound-user-accepted-historical-pure-service-exclusion",
    "source-bound-candidate-TLS-handshake-system-failure",
    "user-confirmed-source-bound-TLS-or-auth-system-failure",
    "proven-controller-only-native-effort-admission-failure",
    "source-bound-candidate-auth-TLS-system-failure",
}
NORMAL = "normal-delivery"
FAILURE = "effective-model-delivery-failure"
HEX = re.compile(r"[a-f0-9]{64}\Z")
MODEL = re.compile(r"[a-z0-9][a-z0-9._-]{0,127}\Z")
RECORD = re.compile(r"[a-z0-9][a-z0-9._-]{0,127}\Z")


def _require(condition, message):
    if not condition:
        raise ValueError(message)


def _keys(value, allowed, label):
    _require(isinstance(value, dict) and set(value) == set(allowed),
             f"Unexpected {label} fields")


def _integer(value):
    return type(value) is int and value >= 0


def _counts(rows):
    return {
        "lifecycle_records": len(rows),
        "effective_attempts": sum(row["effective"] for row in rows),
        "system_exclusions": sum(row["effective"] == 0 for row in rows),
        "normal_finals": sum(row["classification"] == NORMAL for row in rows),
        "consumed_delivery_failures": sum(row["classification"] == FAILURE for row in rows),
    }


def _validate_counts(value, *, planned=False):
    _keys(value, COUNT_KEYS | ({"planned_slots"} if planned else set()), "count")
    _require(all(_integer(number) for number in value.values()), "Counts must be nonnegative integers")
    _require(value["lifecycle_records"] == value["effective_attempts"] + value["system_exclusions"],
             "Lifecycle count does not conserve effective and excluded attempts")
    _require(value["effective_attempts"] == value["normal_finals"] + value["consumed_delivery_failures"],
             "Effective count does not conserve normal and failed attempts")
    if planned:
        _require(value["planned_slots"] <= value["effective_attempts"], "Scored slots exceed effective attempts")
        _require(value["normal_finals"] <= value["planned_slots"], "Multiple normal finals cannot fill one slot")


def validate_public(document):
    """Validate the public allowlist, conservation rules and fixed interpretation."""
    _keys(document, {"schema", "version", "visibility", "unit", "is_score", "scores_modified",
                     "new_candidate_calls", "reviewer_kind", "human_review", "formal_comparison_eligible",
                     "models"}, "document")
    fixed = {"schema": SCHEMA, "version": VERSION, "visibility": "public", "unit": "attempt_lifecycle",
             "is_score": False, "scores_modified": False, "new_candidate_calls": 0,
             "reviewer_kind": "ai", "human_review": "pending", "formal_comparison_eligible": False}
    for key, expected in fixed.items():
        _require(type(document[key]) is type(expected) and document[key] == expected,
                 f"Unexpected public {key}")
    _require(isinstance(document["models"], dict) and document["models"], "No model attempt summaries")
    for model_id, row in document["models"].items():
        _require(isinstance(model_id, str) and MODEL.fullmatch(model_id), "Invalid model identity")
        _keys(row, {"model_id", "record_id", "source_binding", "history_scope", "totals", "phases",
                    "rounds", "segments", "actual_candidate_api_calls", "normal_final_locks_selection",
                    "mathematical_errors_allow_retry"}, "model summary")
        _require(row["model_id"] == model_id and isinstance(row["record_id"], str)
                 and RECORD.fullmatch(row["record_id"]), "Invalid record identity")
        _keys(row["source_binding"], {"public_record_sha256", "private_history_sha256"}, "source binding")
        _require(all(isinstance(v, str) and HEX.fullmatch(v) for v in row["source_binding"].values()),
                 "Source bindings must be opaque SHA256 values")
        _require(row["history_scope"] == "identified_source_epochs", "Unexpected history scope")
        _require(row["actual_candidate_api_calls"] is None, "Lifecycle counts are not API-call counts")
        _require(row["normal_final_locks_selection"] is True and row["mathematical_errors_allow_retry"] is False,
                 "A normal mathematical error never authorizes another attempt")
        totals = row["totals"]
        _keys(totals, COUNT_KEYS | {"planned_slots", "additional_lifecycles", "additional_effective_attempts"},
              "total")
        base = {k: v for k, v in totals.items() if k not in {"additional_lifecycles", "additional_effective_attempts"}}
        _validate_counts(base, planned=True)
        _require(_integer(totals["additional_lifecycles"]) and _integer(totals["additional_effective_attempts"]),
                 "Additional attempt counts must be nonnegative integers")
        _require(totals["additional_lifecycles"] == totals["lifecycle_records"] - totals["planned_slots"]
                 and totals["additional_effective_attempts"] == totals["effective_attempts"] - totals["planned_slots"],
                 "Additional attempt counts do not retain the fixed slot baseline")
        _keys(row["phases"], {"A1", "selfcheck"}, "phase")
        for counts in row["phases"].values():
            _validate_counts(counts, planned=True)
        for key in COUNT_KEYS | {"planned_slots"}:
            _require(sum(v[key] for v in row["phases"].values()) == totals[key], "Phases do not partition totals")
        _keys(row["rounds"], {"R1", "R2", "R3"}, "round")
        for counts in row["rounds"].values():
            _validate_counts(counts, planned=True)
            _require(counts["planned_slots"] == 1, "Each fixed selfcheck round has one slot")
        for key in COUNT_KEYS | {"planned_slots"}:
            _require(sum(v[key] for v in row["rounds"].values()) == row["phases"]["selfcheck"][key],
                     "Rounds do not partition the selfcheck trajectory")
        _keys(row["segments"], {"historical", "resumed"}, "segment")
        for counts in row["segments"].values():
            _validate_counts(counts)
        for key in COUNT_KEYS:
            _require(sum(v[key] for v in row["segments"].values()) == totals[key], "Segments do not partition totals")
    return document


def load_public(root):
    """Return the optional anonymous projection; absence is not a zero count."""
    path = Path(root) / PUBLIC_PATH
    return validate_public(json.loads(path.read_bytes())) if path.is_file() else None


def _descriptor(path, data):
    return {"path": str(Path(path).resolve()), "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def build_from_sources(history_path, public_record_path, *, historical_epochs):
    """Recompute counts and return (public document, private source receipt).

    ``historical_epochs`` selects exact evaluator-side epoch roots. It is never
    copied into the public document. Every retained lifecycle must belong to one
    known epoch, and a normally delivered slot cannot have a later attempt.
    """
    history_bytes = Path(history_path).read_bytes()
    record_bytes = Path(public_record_path).read_bytes()
    history = json.loads(history_bytes)
    record = json.loads(record_bytes)
    _require(history.get("schema") == "math-gauge.complete-physical-request-retention/v1", "Unknown history contract")
    _require(record.get("schema") == "math-gauge.result-record/v1", "Unknown public record contract")
    _require(history.get("model_id") == record.get("model_id"), "History and public model differ")
    _require(history.get("source_benchmark_version") == record.get("benchmark_version"), "Source editions differ")
    _require(history.get("ready_for_record_binding") is True and history.get("original_bytes_rewritten") is False,
             "History is not a retained source-bound archive")
    _require(history.get("new_candidate_calls") == 0
             and type(history.get("new_mathematical_judgments")) in {int, bool}
             and history["new_mathematical_judgments"] == 0,
             "History preparation may not call candidates or add judgments")
    _require(record.get("human_review") == "pending" and record.get("formal_comparison_eligible") is False,
             "This projection preserves AI-review and human-pending status")
    execution = record["execution_summary"]
    history_sha = hashlib.sha256(history_bytes).hexdigest()
    _require(execution.get("physical_history_sha256") == history_sha, "History bytes differ from the public record binding")
    _require(history.get("summary", {}).get("actual_cloud_candidate_call_count") is None
             and execution.get("physical_model_requests") is None,
             "Do not replace unknown API counts with lifecycle counts")
    epochs = history.get("source_epoch_roots_scanned")
    _require(isinstance(epochs, list) and epochs and all(isinstance(v, str) and v for v in epochs)
             and len(epochs) == len(set(epochs)), "Invalid source epoch inventory")
    historical_epochs = list(historical_epochs)
    _require(historical_epochs and len(historical_epochs) == len(set(historical_epochs))
             and set(historical_epochs) < set(epochs), "Historical and resumed epochs must be exact, nonempty disjoint sets")
    rows, identities, per_slot = [], set(), defaultdict(list)
    original_rows = history.get("physical_lifecycle_records")
    _require(isinstance(original_rows, list) and original_rows, "No retained lifecycle inventory")
    for source in original_rows:
        identity, case_id, phase = source.get("original_attempt_root"), source.get("case_id"), source.get("phase")
        _require(isinstance(identity, str) and identity and identity not in identities, "Duplicate or missing lifecycle identity")
        identities.add(identity)
        matches = [epoch for epoch in epochs if identity.startswith(epoch.rstrip("/") + "/")]
        _require(len(matches) == 1, "Epochs must partition all lifecycle identities without overlap")
        _require(isinstance(case_id, str) and case_id and phase in {"A1", "R1", "R2", "R3"}, "Unknown scored slot")
        effective, classification = source.get("reported_effective_consumption"), source.get("source_classification")
        _require(type(effective) is int and effective in {0, 1}, "Unknown source-bound effective consumption")
        _require(classification in ({NORMAL, FAILURE} | EXCLUSION_CLASSES)
                 and effective == int(classification in {NORMAL, FAILURE}), "Classification and effective consumption disagree")
        entry = source.get("primary_source_entry", {})
        _require(source.get("closed_result_present") is True, "A retained lifecycle is not closed")
        _require(entry.get("case_id") == case_id, "Lifecycle and source case identities differ")
        _require(entry.get("normal_complete_delivery") is (classification == NORMAL), "Normal-final evidence disagrees")
        if classification == NORMAL:
            _require(entry.get("normal_final_locks_selection_regardless_of_mathematical_quality") is True,
                     "Normal final must lock selection regardless of mathematics")
        started = entry.get("native_started_utc")
        try:
            timestamp = datetime.fromisoformat(started.replace("Z", "+00:00"))
            _require(timestamp.utcoffset() is not None, "Missing source timezone")
        except (AttributeError, TypeError, ValueError) as exc:
            raise ValueError("Missing original lifecycle timestamp") from exc
        row = {"identity": identity, "case_id": case_id, "phase": phase, "effective": effective,
               "classification": classification, "segment": "historical" if matches[0] in historical_epochs else "resumed",
               "started": timestamp}
        rows.append(row)
        per_slot[(case_id, phase)].append(row)
    for slot_rows in per_slot.values():
        ordered = sorted(slot_rows, key=lambda r: r["started"])
        normal_positions = [i for i, row in enumerate(ordered) if row["classification"] == NORMAL]
        _require(not normal_positions or normal_positions == [len(ordered) - 1],
                 "A first normal final locks selection; mathematical errors cannot justify retries")
        _require(sum(row["effective"] for row in ordered) <= 3, "A slot exceeds three effective attempts")
    initials = [row for row in rows if row["phase"] == "A1"]
    rounds = [row for row in rows if row["phase"] != "A1"]
    initial_ids = {row["case_id"] for row in initials}
    round_ids = {row["case_id"] for row in rounds}
    _require(len(round_ids) == 1 and round_ids <= initial_ids and {row["phase"] for row in rounds} == {"R1", "R2", "R3"},
             "Fixed rounds must continue one retained A1 parent")
    _require(execution.get("planned_initial_tasks") == len(initial_ids)
             and execution.get("prescribed_selfcheck_rounds") == 3, "Fixed scoring denominator differs")
    totals = _counts(rows)
    summary = history["summary"]
    expected_summary = {"retained_lifecycle_records": totals["lifecycle_records"],
                        "closed_result_records": totals["lifecycle_records"],
                        "source_reported_effective_attempts": totals["effective_attempts"],
                        "effective_attempts_after_source_bound_correction": totals["effective_attempts"],
                        "source_reported_nonconsumed_lifecycles": totals["system_exclusions"],
                        "observed_normal_native_finals": totals["normal_finals"],
                        "source_classification_counts": dict(Counter(row["classification"] for row in rows)),
                        "fixed_round_lifecycles": len(rounds),
                        "fixed_round_source_effective_attempts": sum(row["effective"] for row in rounds)}
    parent_rows = [row for row in initials if row["case_id"] in round_ids]
    expected_summary.update(C003_lifecycles=len(parent_rows),
                            C003_source_effective_attempts=sum(row["effective"] for row in parent_rows))
    for key, value in expected_summary.items():
        _require(summary.get(key) == value, f"History summary differs from recomputed {key}")
        _require(execution.get("request_history_counts", {}).get(key) == value,
                 f"Public record summary differs from recomputed {key}")
    _require(execution.get("delivered_initial_tasks") == _counts(initials)["normal_finals"]
             and execution.get("delivered_selfcheck_rounds") == _counts(rounds)["normal_finals"],
             "Normal delivery counts differ from the public record")
    planned = len(initial_ids) + 3
    totals.update(planned_slots=planned, additional_lifecycles=len(rows) - planned,
                  additional_effective_attempts=totals["effective_attempts"] - planned)
    model = {"model_id": record["model_id"], "record_id": record["record_id"],
             "source_binding": {"public_record_sha256": hashlib.sha256(record_bytes).hexdigest(),
                                "private_history_sha256": history_sha},
             "history_scope": "identified_source_epochs", "totals": totals,
             "phases": {"A1": dict(_counts(initials), planned_slots=len(initial_ids)),
                        "selfcheck": dict(_counts(rounds), planned_slots=3)},
             "rounds": {phase: dict(_counts([row for row in rounds if row["phase"] == phase]), planned_slots=1)
                        for phase in ("R1", "R2", "R3")},
             "segments": {segment: _counts([row for row in rows if row["segment"] == segment])
                          for segment in ("historical", "resumed")},
             "actual_candidate_api_calls": None, "normal_final_locks_selection": True,
             "mathematical_errors_allow_retry": False}
    document = {"schema": SCHEMA, "version": VERSION, "visibility": "public", "unit": "attempt_lifecycle",
                "is_score": False, "scores_modified": False, "new_candidate_calls": 0,
                "reviewer_kind": "ai", "human_review": "pending", "formal_comparison_eligible": False,
                "models": {record["model_id"]: model}}
    validate_public(document)
    binding = {"schema": "math-gauge.execution-attempt-source-binding/v1", "visibility": "private",
               "new_candidate_calls": 0, "scores_modified": False,
               "source_history": _descriptor(history_path, history_bytes),
               "source_public_record": _descriptor(public_record_path, record_bytes),
               "historical_epochs": historical_epochs, "resumed_epochs": [e for e in epochs if e not in historical_epochs],
               "validated_summary_fields": sorted(expected_summary),
               "lifecycle_partition": [{k: v for k, v in row.items() if k != "started"} for row in rows],
               "public_document_sha256": hashlib.sha256(_json_bytes(document)).hexdigest()}
    return document, binding


def _json_bytes(document):
    return (json.dumps(document, ensure_ascii=False, indent=2) + "\n").encode()


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--history", type=Path, required=True)
    parser.add_argument("--record", type=Path, required=True)
    parser.add_argument("--historical-epoch", action="append", required=True)
    parser.add_argument("--output", type=Path, default=ROOT / PUBLIC_PATH)
    parser.add_argument("--private-binding", type=Path, required=True)
    args = parser.parse_args(argv)
    _require(not args.private_binding.resolve().is_relative_to(ROOT)
             and args.private_binding.resolve() != args.output.resolve(),
             "The private source receipt must stay outside the public repository")
    document, binding = build_from_sources(args.history, args.record, historical_epochs=args.historical_epoch)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.private_binding.parent.mkdir(parents=True, exist_ok=True)
    args.private_binding.write_bytes(_json_bytes(binding))
    args.output.write_bytes(_json_bytes(document))
    print(json.dumps({"written": str(args.output), "models": list(document["models"]),
                      "private_binding_written": True, "new_candidate_calls": 0}))


if __name__ == "__main__":
    main()
