"""Descriptive cost evidence, selected-attempt arithmetic and public projection.

This owner never executes a candidate or changes a mathematical judgment. Native
receipts, incomplete observations and imputed totals remain distinct.
"""
from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path

SCHEMA = "math-gauge.cost-reference/v1"
VERSION = "0.1.0"
PUBLIC_SCHEMA = "math-gauge.cost-reference-public/v1"
ARCHIVE_SCHEMA = "math-gauge.cost-evidence-archive/v1"
SUPPLEMENT_REFERENCE_SCHEMA = "math-gauge.cost-supplement-reference/v1"
SELECTIONS = {"retained_final", "last_retained_failure", "fixed_round", "not_run", "unresolved"}
STATES = {"complete", "partial", "missing", "not_run"}
ESTIMATED_MODELS = {"terra-6.1-max", "gemini-3.8-flash-high", "kimi-3.1-pro-max", "glm-5.3-max"}


def _require(condition, message):
    if not condition:
        raise ValueError(message)


def _number(value):
    return type(value) in (int, float) and math.isfinite(value) and value >= 0


def normalize_usage(usage, convention):
    """Normalize provider counters without charging cache or reasoning twice."""
    required = ("input_tokens", "output_tokens", "cached_input_tokens", "cache_write_input_tokens")
    _require(all(type(usage.get(key)) is int and usage[key] >= 0 for key in required),
             "Cost usage needs explicit nonnegative input/output/cache/write counts")
    inp, out, cache, write = (usage[key] for key in required)
    _require(convention in {"input_includes_cache", "input_excludes_cache"}, "Unknown token convention")
    plain = inp - cache - write if convention == "input_includes_cache" else inp
    _require(plain >= 0, "Cache exceeds inclusive input")
    reasoning = usage.get("reasoning_output_tokens")
    _require(reasoning is None or type(reasoning) is int and 0 <= reasoning <= out,
             "Reasoning must be an output subset or unknown")
    return {"uncached_input_tokens": plain, "cached_input_tokens": cache,
            "cache_write_input_tokens": write, "output_tokens": out,
            "reasoning_output_tokens": reasoning, "total_tokens": plain + cache + write + out}


def unit_cost(unit, prices):
    tokens = normalize_usage(unit["usage"], unit["convention"])
    if unit.get("reported_list_cost_usd") is not None:
        value = unit["reported_list_cost_usd"]
        _require(_number(value) and unit.get("reported_cost_basis") == "list",
                 "Only an explicitly native list price may bypass repricing")
        return float(value), tokens
    price = prices.get(unit.get("price_id"))
    _require(price is not None, "Missing cost reference tariff")
    rates = price["rates_per_million"]
    value = 0.0
    for token, leg in (("uncached_input_tokens", "input"), ("cached_input_tokens", "cached_input"),
                       ("cache_write_input_tokens", "cache_write"), ("output_tokens", "output")):
        count = tokens[token]
        if not count:
            continue
        rate = rates.get(leg)
        _require(_number(rate), "Missing applicable cost leg")
        value += count * rate / 1_000_000
    return value, tokens


def source_descriptor(path, root):
    path, root = Path(path), Path(root)
    raw = path.read_bytes()
    return {"path": path.relative_to(root).as_posix(), "bytes": len(raw),
            "sha256": hashlib.sha256(raw).hexdigest()}


def verify_source(root, descriptor):
    root = Path(root).resolve()
    rel = Path(descriptor.get("path", ""))
    _require(not rel.is_absolute() and ".." not in rel.parts and rel.parts,
             "Cost source must remain inside its evidence root")
    path = root / rel
    _require(not path.is_symlink() and path.is_file() and path.resolve().is_relative_to(root),
             "Cost evidence must be a regular in-root file")
    raw = path.read_bytes()
    _require(len(raw) == descriptor.get("bytes") and hashlib.sha256(raw).hexdigest() == descriptor.get("sha256"),
             "Cost source bytes changed")


def validate_evidence_archive(document, *, root):
    """Verify the optional lossless path map and its single-copy source objects."""
    descriptor = document.get("evidence_archive")
    if descriptor is None:
        return None
    verify_source(root, descriptor)
    manifest = json.loads((Path(root) / descriptor["path"]).read_text())
    _require(manifest.get("schema") == ARCHIVE_SCHEMA and manifest.get("version") == VERSION,
             "Unknown cost evidence archive schema")
    objects = {}
    for item in manifest["objects"]:
        sha = item["sha256"]
        _require(isinstance(sha, str) and len(sha) == 64 and
                 item["path"] == f"evidence/sha256/{sha}" and sha not in objects,
                 "Cost archive objects must have unique content-addressed paths")
        verify_source(root, item)
        objects[sha] = item
    paths = {}
    original_bytes = 0
    for item in manifest["files"]:
        rel = Path(item["original_path"])
        _require(not rel.is_absolute() and ".." not in rel.parts and rel.parts and
                 item["original_path"] not in paths,
                 "Cost archive original paths must be unique relative paths")
        sha = item["sha256"]
        _require(sha in objects, "Cost archive logical file has no retained object")
        paths[item["original_path"]] = sha
        original_bytes += objects[sha]["bytes"]
    inventory = manifest["source_inventory"]
    _require(objects.get(inventory.get("sha256")) == inventory and
             paths.get("costs.json") == inventory.get("sha256"),
             "Cost archive must retain its exact original inventory")
    stats = {"original_files": len(paths), "original_bytes": original_bytes,
             "unique_objects": len(objects), "unique_bytes": sum(x["bytes"] for x in objects.values())}
    _require(manifest.get("preserved") == stats, "Cost archive preservation totals differ")
    for model in document["models"]:
        sources = [source for slot in model["slots"] for source in slot.get("sources", [])]
        for field in ("estimate", "cost_resolution"):
            sources.extend((model.get(field) or {}).get("sources", []))
        _require(all(objects.get(item.get("sha256")) == item for item in sources),
                 "Current cost source is outside its retained archive objects")
    return stats


def resolved_reference_cost(model, known, *, root=None):
    """Apply a source-bound cost scope without inventing native usage."""
    resolution = model["cost_resolution"]
    _require(resolution.get("model_id") == model["model_id"] and
             resolution.get("record_id") == model["record_id"],
             "Cost resolution belongs to a different selected record")
    _require(resolution.get("basis") and resolution.get("sources"),
             "Cost resolution needs its declared scope and confirmation evidence")
    _require(model.get("estimate") is None, "A resolved cost cannot also be imputed")
    if root is not None:
        for descriptor in resolution["sources"]:
            verify_source(root, descriptor)
    if resolution.get("kind") == "reported_terminal_usage":
        _require(model.get("pricing_basis") == "reported_native_usage_reference",
                 "Reported usage needs an explicit reference-cost basis")
        pending = {slot["id"]: slot for slot in model["slots"] if slot["state"] == "partial"}
        bindings = resolution.get("receipts", [])
        _require(pending and not any(slot["state"] == "missing" for slot in model["slots"]) and
                 len(bindings) == len(pending) and {row["slot_id"] for row in bindings} == set(pending),
                 "Reported usage resolution cannot close missing attempts or unrelated slots")
        for binding in bindings:
            slot = pending[binding["slot_id"]]
            _require(len(slot["units"]) == 1, "Reported usage needs one final cumulative receipt")
            unit = slot["units"][0]
            _require(binding.get("attempt_identity_sha256") == slot["attempt_identity_sha256"] and
                     binding.get("unit_identity_sha256") == unit["identity_sha256"] and
                     binding.get("usage") == unit["usage"],
                     "Reported usage resolution differs from the retained native receipt")
            if root is not None:
                extracts = [json.loads((Path(root) / item["path"]).read_text()) for item in slot["sources"]]
                _require(any(item.get("native_final_usage_present") is True for item in extracts),
                         "Reported usage resolution requires a native final cumulative receipt")
        return known
    _require(resolution.get("kind") == "test_date_zero_charge", "Unknown cost resolution")
    _require(model["model_id"] == "dot-underlying-model-20261108" and model["record_id"] == "20261108" and
             resolution.get("test_date") == "2026-11-08" and model.get("pricing_basis") == "test_date_zero_charge",
             "A zero-charge observation is bound to the selected Dot test date")
    _require(_number(resolution.get("total_usd")) and resolution["total_usd"] == 0 and known == 0,
             "A confirmed zero charge cannot replace a recorded positive cost")
    return 0.0


def summarize_model(model, prices, *, root=None, expected_answers=None):
    slots = model["slots"]
    ids = [slot["id"] for slot in slots]
    _require(len(ids) == 42 and len(set(ids)) == 42, "Cost inventory requires 39 initial slots plus 3 rounds")
    _require(sum(slot.endswith(":A1") for slot in ids) == 39 and
             all(f"MG-C003:R{i}" in ids for i in range(1, 4)), "Cost slots do not match the fixed suite")
    if expected_answers is not None:
        _require(set(ids) == set(expected_answers), "Cost inventory differs from selected answers")
    seen = set()
    known = 0.0
    tokens = {key: 0 for key in ("uncached_input_tokens", "cached_input_tokens", "cache_write_input_tokens",
                               "output_tokens", "total_tokens")}
    coverage = {state: 0 for state in STATES}
    for slot in slots:
        state, selection = slot["state"], slot["selection"]
        _require(state in STATES and selection in SELECTIONS, "Invalid cost observation status")
        coverage[state] += 1
        _require(selection != "unresolved" or state == "missing", "An unresolved attempt cannot supply cost")
        _require((state == "not_run") == (selection == "not_run"), "Non-execution needs explicit selection")
        if expected_answers is not None and expected_answers[slot["id"]] is not None:
            _require(slot.get("answer_sha256") == expected_answers[slot["id"]], "Cost is attached to a different answer")
        _require(state not in {"missing", "not_run"} or not slot.get("units"), "Unknown or unrun slots cannot invent counters")
        _require(state != "complete" or slot.get("units"), "A completed cost observation needs original usage")
        if state in {"complete", "partial"}:
            attempt = slot.get("attempt_identity_sha256")
            _require(isinstance(attempt, str) and len(attempt) == 64,
                     "A cost slot must bind one retained outer attempt")
        if root is not None:
            _require(slot.get("sources"), "Every cost slot needs retained selection/source evidence")
            for descriptor in slot["sources"]:
                verify_source(root, descriptor)
        for unit in slot.get("units", []):
            _require(unit.get("attempt_identity_sha256") == slot["attempt_identity_sha256"],
                     "Other retries cannot be combined into a retained slot")
            identity = unit["identity_sha256"]
            _require(isinstance(identity, str) and len(identity) == 64 and identity not in seen,
                     "A native cost unit cannot be duplicated across slots")
            seen.add(identity)
            value, normalized = unit_cost(unit, prices)
            known += value
            for key in tokens:
                tokens[key] += normalized[key]
    complete = coverage["missing"] == coverage["partial"] == 0
    status = "observed" if complete else "partial"
    total = known if complete else None
    if not seen and not complete:
        status = "unavailable"
    interval = None
    estimate = model.get("estimate")
    if estimate is not None:
        _require(model["model_id"] in ESTIMATED_MODELS,
                 "Imputation requires an explicitly selected model")
        total = estimate["total_usd"]
        lo, hi = estimate["range_usd"]
        _require(all(_number(v) for v in (total, lo, hi)) and known <= lo <= total <= hi,
                 "Invalid or below-observed cost estimate")
        _require(estimate.get("basis") and estimate.get("sources"), "An estimate requires calibration evidence")
        if root is not None:
            for descriptor in estimate["sources"]:
                verify_source(root, descriptor)
        status, interval = "estimated", [float(lo), float(hi)]
    if model.get("cost_resolution") is not None:
        total = resolved_reference_cost(model, known, root=root)
        status = "observed"
    return {"model_id": model["model_id"], "record_id": model["record_id"], "status": status,
            "record_sha256": model.get("public_record_binding", {}).get("sha256"),
            "total_usd": total, "known_usd": known, "estimate_range_usd": interval,
            "coverage": {"planned": 42, **coverage}, "tokens": tokens,
            "pricing_basis": model.get("pricing_basis", "standard_api_reference")}


def validate_private(document, *, root=None, expected_answers=None):
    _require(document.get("schema") == SCHEMA and document.get("version") == VERSION,
             "Unknown cost reference schema")
    _require(document.get("selection_rule") == "one_retained_attempt_per_slot" and
             document.get("other_retries_included") is False, "Wrong cost attempt selection")
    if root is not None:
        validate_evidence_archive(document, root=root)
    prices = {price["id"]: price for price in document["prices"]}
    _require(len(prices) == len(document["prices"]), "Duplicate cost tariff")
    ids = [model["model_id"] for model in document["models"]]
    _require(len(ids) == len(set(ids)), "Duplicate model cost inventory")
    return [summarize_model(model, prices, root=root,
            expected_answers=None if expected_answers is None else expected_answers[model["model_id"]])
            for model in document["models"]]


def project_public(document, *, source_sha256, root=None, expected_answers=None, benchmark_version=None):
    rows = validate_private(document, root=root, expected_answers=expected_answers)
    # No slot IDs, source paths, native identities, token details or private breakdowns leave this owner.
    source_version = document.get("benchmark_version", "0.6.0")
    active_version = source_version if benchmark_version is None else benchmark_version
    projection = {"schema": PUBLIC_SCHEMA, "version": VERSION, "benchmark_version": active_version,
            "as_of": document["as_of"], "currency": "USD", "selection_rule": document["selection_rule"],
            "other_retries_included": False, "private_source_sha256": source_sha256,
            "prices": [{key: p[key] for key in ("id", "label", "source_url")} for p in document["prices"]],
            "models": [{key: row[key] for key in ("model_id", "record_id", "record_sha256", "status", "total_usd", "known_usd",
                       "estimate_range_usd", "coverage", "pricing_basis")} for row in rows]}
    if active_version != source_version:
        projection["source_benchmark_version"] = source_version
    return projection


def pareto_frontier(rows, *, axis="cost"):
    """Return measured nondominated points for the selected resource axis."""
    _require(axis in {"cost", "time"}, "Unknown frontier axis")
    key = "total_usd" if axis == "cost" else "seconds"
    usable = [row for row in rows if (axis == "time" or row.get("status") == "observed")
              and row.get("score_complete") is True
              and _number(row.get(key)) and _number(row.get("score"))]
    return [row["model_id"] for row in sorted(usable, key=lambda row: (row[key], -row["score"], row["model_id"]))
            if not any(other[key] <= row[key] and other["score"] >= row["score"] and
                       (other[key] < row[key] or other["score"] > row["score"]) for other in usable)]
