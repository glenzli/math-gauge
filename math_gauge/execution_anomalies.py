"""Source-bound operational observations, independent of mathematical scores.

The unit is one physical candidate run. Categories may overlap; their union is
counted once. A recovered service error remains observable, whereas a normal
continuation boundary, subscription allowance or voluntary cancellation alone
does not establish an anomaly. Causal reviews and supplemental native findings
change attributable counts without rewriting the original six source flags.
"""
import copy
import hashlib
import json
import re
from datetime import datetime
from pathlib import Path

from .evidence_retention import read_bytes


SCHEMA = "math-gauge.execution-anomalies/v1"
VERSION = "0.3.0"
VERSIONS = {"0.1.0", "0.2.0", VERSION}
# Original source judgments stay in their six categories. The current public
# observation groups them without rewriting the retained reviews.
CATEGORIES = (
    "timeout", "service_stream_connection", "http_429",
    "output_or_context_limit", "harness_environment", "other",
)
PUBLIC_CATEGORIES = {
    "server_errors": ("service_stream_connection", "http_429"),
    "context": ("output_or_context_limit",),
    "runner": ("timeout", "harness_environment", "other"),
}
COUNTED_SCOPES = {"benchmark", "legacy_benchmark", "diagnostic_case"}
EXCLUDED_SCOPES = {"control", "prototype", "invited_study", "preparation", "open", "after_cutoff", "out_of_scope"}
COVERAGES = {"complete", "partial", "unknown", "qualitative_only"}
_CAUSAL_DECISIONS = {"count": True, "exclude": False, "unresolved": None}


def _require(value, message):
    if not value:
        raise ValueError(message)


def _sha(value):
    return isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value) is not None


def _stamp(value):
    parsed = datetime.fromisoformat(value.replace("Z", "+00:00"))
    _require(parsed.tzinfo is not None, "Operational timestamps need an explicit timezone")
    return parsed


def verify_sources(document, roots):
    """Verify retained originals through the same cold reader as other evidence."""
    checked = {}
    for source in document["sources"].values():
        _require(source["root"] in roots, "Operational source root is unavailable")
        root = Path(roots[source["root"]]).resolve()
        relative = Path(source["path"])
        _require(not relative.is_absolute() and ".." not in relative.parts,
                 "Operational source must stay inside its declared repository")
        path = root / relative
        _require(path.resolve().is_relative_to(root) and not path.is_symlink(),
                 "Operational source escapes its repository")
        if path not in checked:
            raw = read_bytes(path)
            checked[path] = len(raw), hashlib.sha256(raw).hexdigest()
        _require(checked[path] == (source["bytes"], source["sha256"]),
                 "Operational source bytes changed")


def validate_private(document):
    _require(document.get("schema") == SCHEMA and document.get("version") in VERSIONS
             and document.get("visibility") == "private" and document.get("is_score") is False,
             "Invalid operational observation contract")
    _require(document.get("unit") == "physical_candidate_run", "Operational counting unit changed")
    cutoff = _stamp(document["cutoff_utc"])
    groups = document["groups"]
    _require(isinstance(groups, list) and len({g["id"] for g in groups}) == len(groups),
             "Operational groups must be unique")
    group_ids = {g["id"] for g in groups}
    sources = document["sources"]
    _require(isinstance(sources, dict), "Operational sources need an explicit registry")
    for key, source in sources.items():
        _require(_sha(key) and _sha(source.get("sha256"))
                 and type(source.get("bytes")) is int and source["bytes"] >= 0,
                 "Operational sources need exact byte descriptors")
    for group in groups:
        _require(group.get("coverage") in COVERAGES and type(group.get("history_complete")) is bool,
                 "Operational coverage must be explicit")
        _require(all(isinstance(group.get(k), str) and group[k] for k in
                     ("id", "model_id", "model_label", "harness_label")), "Incomplete operational group")
        _require(set(group.get("sources", [])).issubset(sources), "Group source is not retained")
        exclusions = group.get("category_exclusions", {})
        _require(isinstance(exclusions, dict) and set(exclusions).issubset(_categories(document["version"])),
                 "Unknown operational category exclusion")
        for review in exclusions.values():
            _require(isinstance(review.get("reason"), str) and review["reason"]
                     and review.get("evidence") and set(review["evidence"]).issubset(sources),
                     "An operational category exclusion needs retained review evidence")
        if group["history_complete"]:
            _require(group["coverage"] == "complete", "Partial history cannot establish exact totals")
    for row in document["runs"]:
        _require(_sha(row.get("identity_sha256")) and row.get("group_id") in group_ids,
                 "Operational run needs a bound identity and group")
        _require(row.get("scope") in COUNTED_SCOPES | EXCLUDED_SCOPES, "Unknown operational scope")
        _require(row.get("disposition") in {"normal_final", "failed", "quota_exhausted", "cancelled", "unknown"},
                 "Unknown operational disposition")
        _require(isinstance(row.get("sources"), list) and row["sources"]
                 and set(row["sources"]).issubset(sources), "A run needs retained source evidence")
        if row.get("observed_at") is not None and row["scope"] in COUNTED_SCOPES:
            _require(_stamp(row["observed_at"]) <= cutoff, "Run evidence is later than the frozen cutoff")
        flags = row["flags"]
        _require(set(flags) == set(CATEGORIES), "Every operational category needs a known or unknown judgment")
        for kind, finding in flags.items():
            _require(finding.get("observed") is None or type(finding["observed"]) is bool,
                     "Operational flags must be true, false or unknown")
            if finding["observed"] is True:
                _require(finding.get("evidence") and set(finding["evidence"]).issubset(sources)
                         and isinstance(finding.get("reason"), str) and finding["reason"],
                         "An anomaly requires source-bound review evidence")
        for field, decisions in (("causal_review", _CAUSAL_DECISIONS),
                                 ("native_findings", {"count", "unresolved"})):
            if field not in row:
                continue
            label = field.replace("_", " ")
            _require(document["version"] == "0.3.0", f"Operational {label} requires version 0.3.0")
            reviews = row[field]
            _require(isinstance(reviews, dict) and set(reviews).issubset(CATEGORIES),
                     f"Unknown operational {label} category")
            for kind, review in reviews.items():
                if field == "causal_review":
                    _require(flags[kind]["observed"] is True,
                             "Operational causal review requires an originally observed anomaly")
                _require(isinstance(review, dict) and set(review) == {"decision", "reason", "evidence"}
                         and isinstance(review.get("decision"), str)
                         and review["decision"] in decisions,
                         f"Invalid operational {label} decision or fields")
                _require(isinstance(review.get("reason"), str) and review["reason"].strip()
                         and isinstance(review.get("evidence"), list) and review["evidence"]
                         and all(isinstance(key, str) and key in sources for key in review["evidence"]),
                         f"An operational {label} needs retained review evidence and a reason")
    return document


def deduplicate_runs(runs):
    """Aliases of one native run cannot multiply errors or normal submissions."""
    unique = {}
    for original in runs:
        row = copy.deepcopy(original)
        identity = row["identity_sha256"]
        if identity not in unique:
            unique[identity] = row
            continue
        kept = unique[identity]
        _require(all(kept[key] == row[key] for key in ("group_id", "scope", "disposition")),
                 "Duplicate operational identities disagree about their source or scope")
        kept["sources"] = sorted(set(kept["sources"]) | set(row["sources"]))
        for category in CATEGORIES:
            previous, incoming = kept["flags"][category], row["flags"][category]
            a, b = previous["observed"], incoming["observed"]
            _require(a is None or b is None or a == b,
                     "Duplicate operational reviews conflict; resolve the original evidence first")
            if a is None:
                kept["flags"][category] = incoming
            elif a is True:
                previous["evidence"] = sorted(set(previous["evidence"]) | set(incoming.get("evidence", [])))
        for field in ("causal_review", "native_findings"):
            reviews = kept.get(field, {})
            for category, incoming in row.get(field, {}).items():
                previous = reviews.get(category)
                if previous is None:
                    reviews[category] = incoming
                else:
                    label = "causal reviews" if field == "causal_review" else "native findings"
                    _require(previous["decision"] == incoming["decision"],
                             f"Duplicate operational {label} conflict; resolve the original evidence first")
                    previous["evidence"] = sorted(set(previous["evidence"]) | set(incoming["evidence"]))
            if reviews:
                kept[field] = reviews
    return list(unique.values())


def _metric(value, exact):
    return {"known": value, "exact": value if exact else None}


def _categories(version):
    return {key: (key,) for key in CATEGORIES} if version == "0.1.0" else PUBLIC_CATEGORIES


def _counted_scopes(version):
    return COUNTED_SCOPES if version == "0.1.0" else COUNTED_SCOPES - {"diagnostic_case"}


def _observed(row, kinds):
    reviews = row.get("causal_review", {})
    values = [_CAUSAL_DECISIONS[reviews[kind]["decision"]] if kind in reviews
              else row["flags"][kind]["observed"] for kind in kinds]
    native = row.get("native_findings", {})
    values.extend(_CAUSAL_DECISIONS[native[kind]["decision"]] for kind in kinds if kind in native)
    return True if True in values else None if None in values else False


def project_public(document, *, private_sha256):
    """Allowlist aggregates only; no task ids, paths, excerpts or native ids."""
    validate_private(document)
    _require(_sha(private_sha256), "Public operational report needs its private source hash")
    unique = deduplicate_runs(document["runs"])
    categories = _categories(document["version"])
    counted_scopes = _counted_scopes(document["version"])
    rows = []
    for group in document["groups"]:
        retained = [r for r in unique if r["group_id"] == group["id"]]
        measured = [r for r in retained if r["scope"] in counted_scopes]
        exact_history = group["history_complete"] and bool(measured)
        exclusions = group.get("category_exclusions", {})
        counts = {}
        for kind, source_kinds in categories.items():
            if kind in exclusions:
                counts[kind] = _metric(0, False)
                continue
            observed = sum(_observed(r, source_kinds) is True for r in measured)
            counts[kind] = _metric(observed, exact_history and all(
                _observed(r, source_kinds) is not None for r in measured))
        included = tuple(k for category, kinds in categories.items() if category not in exclusions for k in kinds)
        affected = sum(_observed(r, included) is True for r in measured)
        union_known = all(_observed(r, included) is not None for r in measured)
        rows.append({
            "id": group["id"], "model_id": group["model_id"], "model_label": group["model_label"],
            "harness_label": group["harness_label"], "route": group.get("route", ""),
            "coverage": group["coverage"], "history_complete": exact_history,
            "reviewed_runs": len(measured), "anomalous_runs": _metric(affected, exact_history and union_known),
            "categories": counts,
            "quota_exhausted_runs": sum(r["disposition"] == "quota_exhausted" for r in measured),
            "cancelled_runs": sum(r["disposition"] == "cancelled" for r in measured),
            "excluded_runs": len(retained) - len(measured),
        })
    return {"schema": SCHEMA, "version": document["version"], "visibility": "public", "is_score": False,
            "unit": document["unit"], "as_of": document["as_of"], "cutoff_utc": document["cutoff_utc"],
            "source_review_sha256": private_sha256, "categories": list(categories), "rows": rows}


def validate_public(document):
    _require(set(document) == {"schema", "version", "visibility", "is_score", "unit", "as_of",
                              "cutoff_utc", "source_review_sha256", "categories", "rows"},
             "Public operational observation contains nonaggregate fields")
    _require(document.get("schema") == SCHEMA and document.get("version") in VERSIONS
             and document.get("visibility") == "public" and document.get("is_score") is False,
             "Invalid public operational observation")
    categories = _categories(document["version"])
    _require(document.get("unit") == "physical_candidate_run"
             and document.get("categories") == list(categories) and _sha(document.get("source_review_sha256")),
             "Public operational counting contract changed")
    _stamp(document["cutoff_utc"])
    rows = document["rows"]
    _require(len({r["id"] for r in rows}) == len(rows), "Duplicate public operational group")
    for row in rows:
        _require(set(row) == {"id", "model_id", "model_label", "harness_label", "route", "coverage",
                              "history_complete", "reviewed_runs", "anomalous_runs", "categories",
                              "quota_exhausted_runs", "cancelled_runs", "excluded_runs"},
                 "Public operational row contains private or unrecognized fields")
        _require(row["coverage"] in COVERAGES and type(row["history_complete"]) is bool,
                 "Public operational coverage is invalid")
        _require(type(row["reviewed_runs"]) is int and row["reviewed_runs"] >= 0
                 and set(row["categories"]) == set(categories), "Invalid public operational counts")
        _require(not row["history_complete"] or row["coverage"] == "complete",
                 "Public operational history completeness conflicts with coverage")
        _require(row["history_complete"] or all(m["exact"] is None for m in
                 [row["anomalous_runs"], *row["categories"].values()]),
                 "Partial operational history cannot establish exact totals")
        for metric in [row["anomalous_runs"], *row["categories"].values()]:
            _require(set(metric) == {"known", "exact"} and type(metric["known"]) is int
                     and 0 <= metric["known"] <= row["reviewed_runs"]
                     and (metric["exact"] is None or type(metric["exact"]) is int
                          and metric["exact"] == metric["known"]),
                     "Operational count cannot exceed its reviewed runs or fabricate precision")
        _require(row["anomalous_runs"]["known"] >= max(
            m["known"] for m in row["categories"].values()), "Anomaly union cannot be smaller than a category")
        for field in ("quota_exhausted_runs", "cancelled_runs", "excluded_runs"):
            _require(type(row[field]) is int and row[field] >= 0, "Invalid operational exclusion count")
        _require(row["quota_exhausted_runs"] <= row["reviewed_runs"]
                 and row["cancelled_runs"] <= row["reviewed_runs"], "Disposition counts exceed reviewed runs")
    return document


def load_public(root):
    for version in (VERSION, "0.2.0", "0.1.0"):
        path = Path(root) / f"results/execution-anomalies/v{version}/current.json"
        if path.is_file():
            return validate_public(json.loads(path.read_bytes()))
    return None
