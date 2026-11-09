"""Optional, source-bound answer timings; never a source of mathematical credit.

The supplement deliberately points outwards to immutable answer records. Adding
it cannot change an answer record, a grading input, or a score-policy identity.
"""
import ast
import hashlib
import json
import math
import re
import statistics
from datetime import datetime
from pathlib import Path

from .records import evidence_bytes

SCHEMA = "math-gauge.answer-timings/v1"
METHODS = {
    "native_terminal_wall", "execution_elapsed", "historical_reported_elapsed",
    "coordinator_observed_wall", "operator_reported_elapsed",
}
DELIVERIES = {"delivered", "delivery_failed", "not_run", "unresolved"}


def descriptor(path, root):
    path, root = Path(path), Path(root)
    raw = path.read_bytes()
    return {"path": path.relative_to(root).as_posix(), "bytes": len(raw),
            "sha256": hashlib.sha256(raw).hexdigest()}


def _require(condition, message):
    if not condition:
        raise ValueError(message)


def _sha(value):
    return isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value) is not None


def _seconds(value):
    return type(value) in (int, float) and math.isfinite(value) and value >= 0


def _stamp(value):
    _require(isinstance(value, str), "timing timestamp must be a string")
    parsed = datetime.fromisoformat(value.replace("Z", "+00:00"))
    _require(parsed.tzinfo is not None, "timing timestamp needs an explicit timezone")
    return parsed


def _pointer(value, pointer):
    _require(isinstance(pointer, str) and pointer.startswith("/"), "timing source needs a JSON pointer")
    for token in pointer[1:].split("/"):
        token = token.replace("~1", "/").replace("~0", "~")
        try:
            value = value[int(token)] if isinstance(value, list) else value[token]
        except (KeyError, IndexError, TypeError, ValueError) as error:
            raise ValueError("timing source pointer does not resolve") from error
    return value


def _contains(container, expected):
    if container == expected:
        return True
    values = container.values() if isinstance(container, dict) else container if isinstance(container, list) else ()
    return any(_contains(value, expected) for value in values if isinstance(value, (dict, list)))


def _source(root, item):
    value = json.loads(evidence_bytes(root, item))
    if value.get("schema") == "math-gauge.historical-timing-extract/v1":
        _require(value.get("extraction_only") is True and value.get("runtime_independently_verified") is False,
                 "historical extracts cannot create independent runtime certification")
        excerpt = value.get("original_excerpt")
        _require(isinstance(excerpt, str) and len(excerpt) <= 2_000_000,
                 "historical timing needs a bounded original output excerpt")
        try:
            original = json.loads(excerpt)
        except ValueError:
            try:
                original = ast.literal_eval(excerpt)
            except (ValueError, SyntaxError, TypeError, RecursionError) as error:
                raise ValueError("historical timing excerpt is not literal source data") from error
        _require(_contains(original, value.get("timing")), "timing extraction differs from its retained literal excerpt")
        _require(_sha(value.get("original_event_sha256")) and _sha(value.get("original_session_sha256")),
                 "historical timing must retain its original event/session identities")
    return value


def _bound_seconds(root, binding, method):
    """Resolve one measurement, including attempt clocks outside selected rows."""
    if binding.get("kind") == "elapsed_field":
        _require(binding.get("pointer", "").split("/")[-1] in {"elapsed_seconds", "native_elapsed_seconds", "duration_seconds"},
                 "a configured limit or other numeric field is not observed elapsed time")
        _require(method != "native_terminal_wall", "native terminal timing needs its actual timestamp pair")
        source = _source(root, binding["source"])
        seconds = _pointer(source, binding["pointer"])
        _require(_seconds(seconds), "elapsed field is not an actual finite duration")
        return seconds, None, None
    if binding.get("kind") == "timestamp_difference":
        start = _pointer(_source(root, binding["start"]["source"]), binding["start"]["pointer"])
        end = _pointer(_source(root, binding["end"]["source"]), binding["end"]["pointer"])
        return (_stamp(end) - _stamp(start)).total_seconds(), start, end
    raise ValueError("known timing needs an exact elapsed field or timestamp pair")


def summary(rows):
    """Describe delivered, timed answers; failed/unrun slots never become zeros."""
    values = [row["seconds"] for row in rows
              if row["delivery_status"] == "delivered" and row["availability"] == "known"]
    delivered = sum(row["delivery_status"] == "delivered" for row in rows)
    return {
        "planned": len(rows), "delivered": delivered, "timed_delivered": len(values),
        "untimed_delivered": delivered - len(values),
        "timed_slots": sum(row["availability"] == "known" for row in rows),
        "delivery_failed": sum(row["delivery_status"] == "delivery_failed" for row in rows),
        "timed_failures": sum(row["delivery_status"] == "delivery_failed" and row["availability"] == "known" for row in rows),
        "not_run": sum(row["delivery_status"] == "not_run" for row in rows),
        "unresolved": sum(row["delivery_status"] == "unresolved" for row in rows),
        "timed_unresolved": sum(row["delivery_status"] == "unresolved" and row["availability"] == "known" for row in rows),
        "minimum_seconds": round(min(values), 6) if values else None,
        "median_seconds": round(statistics.median(values), 6) if values else None,
        "mean_seconds": round(statistics.mean(values), 6) if values else None,
        "maximum_seconds": round(max(values), 6) if values else None,
        "sum_seconds": round(sum(values), 6) if values else None,
        "methods": {method: sum(row["method"] == method and row["availability"] == "known"
                                and row["delivery_status"] == "delivered" for row in rows)
                    for method in sorted(METHODS)
                    if any(row["method"] == method and row["availability"] == "known"
                           and row["delivery_status"] == "delivered" for row in rows)},
    }


def summaries(rows):
    return {"initial_answers": summary([row for row in rows if row["phase"] == "A1"]),
            "selfcheck_rounds": summary([row for row in rows if row["phase"] != "A1"])}


def validate_private(document, root, expected_answers):
    _require(document.get("schema") == SCHEMA and document.get("version") == "0.1.0"
             and document.get("visibility") == "private", "unsupported private timing supplement")
    _require(document.get("new_candidate_calls") == 0 and document.get("scores_modified") is False,
             "timing collection must not generate answers or mathematical scores")
    rows = document.get("rows")
    _require(isinstance(rows, list) and len({row.get("id") for row in rows}) == len(rows),
             "timing rows need unique identities")
    _require({row["id"] for row in rows} == set(expected_answers), "timing supplement changed the selected slots")
    for row in rows:
        _require(row.get("answer_sha256") == expected_answers[row["id"]], "timing belongs to a different selected answer")
        _require(row.get("phase") in {"A1", "R1", "R2", "R3"}
                 and row.get("delivery_status") in DELIVERIES, "unknown timing phase/delivery status")
        _require(row.get("availability") in {"known", "unknown"}, "unknown timing availability")
        _require(isinstance(row.get("note"), str) and bool(row["note"].strip()), "timing row needs a source/coverage note")
        for item in row.get("evidence", []):
            evidence_bytes(root, item)
        if row["availability"] == "unknown":
            _require(row.get("seconds") is None and row.get("method") is None and row.get("time_binding") is None,
                     "missing timing cannot be replaced with zero or a configured budget")
            continue
        _require(row["delivery_status"] != "not_run", "unrun slot cannot have observed elapsed time")
        _require(_seconds(row.get("seconds")) and row.get("method") in METHODS,
                 "known timing needs a finite measured duration and named boundary")
        seconds, start, end = _bound_seconds(root, row.get("time_binding", {}), row["method"])
        if start is not None:
            _require(row.get("started_at") == start and row.get("ended_at") == end,
                     "retained timing timestamps differ from the source")
        _require(_seconds(seconds) and abs(seconds - row["seconds"]) < 0.000002,
                 "elapsed time differs from retained source bytes")
    for attempt in document.get("physical_attempt_timings", []):
        _require(attempt.get("slot_id") in expected_answers, "attempt timing changed the selected slots")
        _require(_seconds(attempt.get("seconds")) and attempt.get("method") in METHODS,
                 "attempt needs a finite observed duration and named boundary")
        for item in attempt.get("evidence", []):
            evidence_bytes(root, item)
        seconds, _, _ = _bound_seconds(root, attempt.get("time_binding", {}), attempt["method"])
        _require(_seconds(seconds) and abs(seconds - attempt["seconds"]) < 0.000002,
                 "attempt elapsed time differs from retained source bytes")
    _require(document.get("summary") == summaries(rows), "timing summary differs from its selected source rows")
    return document


def project_public(document, public_case_ids, *, record, public_tasks, private_sha256):
    allowed = set(public_case_ids)
    fields = ("id", "case_id", "phase", "answer_sha256", "delivery_status", "availability",
              "seconds", "method", "quality", "started_at", "ended_at", "note")
    # Public notes are written separately; raw evidence paths/context stay private.
    rows = []
    for original in document["rows"]:
        if original["case_id"] not in allowed:
            continue
        row = {key: original[key] for key in fields if key in original}
        row["note"] = original["public_note"]
        row["source_sha256"] = sorted({item["sha256"] for item in original.get("evidence", [])})
        rows.append(row)
    return {"schema": SCHEMA, "version": "0.1.0", "visibility": "public-projection",
            "benchmark_version": document["benchmark_version"], "model_id": document["model_id"],
            "record_id": document["record_id"], "record": record, "public_tasks": public_tasks,
            "private_timing_sha256": private_sha256, "public_case_ids": sorted(allowed),
            "rows": rows, "summary": document["summary"], "summary_scope": "combined-selected-answers",
            "new_candidate_calls": 0, "scores_modified": False,
            "interpretation": document["interpretation"]}


def record_context(public_root, private_root):
    public_root, private_root = Path(public_root), Path(private_root)
    name = "record.json" if (public_root / "record.json").exists() else "native-observation.json"
    public_record = json.loads((public_root / name).read_bytes())
    private_record = json.loads((private_root / name).read_bytes())
    score_path = private_record.get("assessment_results", {}).get("nonlogical_retry_3", {}).get("path", "partial-retry-result.json")
    report = json.loads((private_root / score_path).read_bytes())
    expected = {row["case_id"] + ":A1": row.get("response_sha256") for row in report["tasks"]}
    for number in range(1, 4):
        candidates = [row for row in public_record.get("records", []) if row.get("id") in
                      {f"MG-C003:R{number}", f"MG-C003:alignment:{number}"}]
        candidates += [row for row in public_record.get("selfcheck_rounds", []) if row["round"] == number]
        response = candidates[0].get("response") if candidates else None
        expected[f"MG-C003:R{number}"] = response["sha256"] if response else None
    public_tasks = json.loads((public_root / "public-task-scores.json").read_bytes())
    _require(len(expected) == 42, "current timing inventory requires39 initial answers and3 fixed rounds")
    return {"name": name, "public_record": public_record, "private_record": private_record,
            "report_path": score_path, "report": report, "expected": expected,
            "public_case_ids": public_tasks["public_case_ids"]}


def check_pair(public_root, private_root):
    public_root, private_root = Path(public_root), Path(private_root)
    context = record_context(public_root, private_root)
    private_path = private_root / "answer-timings.json"
    document = json.loads(private_path.read_bytes())
    evidence_bytes(private_root, document["record"])
    evidence_bytes(private_root, document["assessment_result"])
    _require(document["record"]["path"] == context["name"]
             and document["assessment_result"]["path"] == context["report_path"], "timing supplement binds another record/report")
    validate_private(document, private_root, context["expected"])
    projected = project_public(document, context["public_case_ids"],
        record=descriptor(public_root / context["name"], public_root),
        public_tasks=descriptor(public_root / "public-task-scores.json", public_root),
        private_sha256=hashlib.sha256(private_path.read_bytes()).hexdigest())
    actual = json.loads((public_root / "answer-timings.json").read_bytes())
    _require(actual == projected, "public timing projection differs from private source evidence")
    return document
