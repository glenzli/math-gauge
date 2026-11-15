#!/usr/bin/env python3
"""Combine reviewed operational inventories; never invoke a candidate model."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from math_gauge.execution_anomalies import (
    deduplicate_runs, project_public, validate_private, validate_public, verify_sources,
)


def merge(parts):
    if not parts:
        raise ValueError("At least one reviewed operational inventory is required")
    document = {key: parts[0][key] for key in
                ("schema", "version", "visibility", "is_score", "unit", "as_of", "cutoff_utc")}
    document.update(groups=[], sources={}, runs=[], reviewer_kind="ai", human_review="pending")
    groups = {}
    for part in parts:
        validate_private(part)
        if any(part[key] != document[key] for key in
               ("schema", "version", "visibility", "unit", "as_of", "cutoff_utc")):
            raise ValueError("Operational inventory snapshots or contracts differ")
        for key, source in part["sources"].items():
            previous = document["sources"].get(key)
            if previous and (previous["bytes"], previous["sha256"]) != (source["bytes"], source["sha256"]):
                raise ValueError("Operational source identities conflict")
            document["sources"].setdefault(key, source)
        for group in part["groups"]:
            if group["id"] in groups and groups[group["id"]] != group:
                raise ValueError("Operational group identity is ambiguous")
            if group["id"] not in groups:
                groups[group["id"]] = group
                document["groups"].append(group)
        document["runs"].extend(part["runs"])
    document["runs"] = deduplicate_runs(document["runs"])
    validate_private(document)
    return document


def encode(value):
    return (json.dumps(value, ensure_ascii=False, indent=2, allow_nan=False) + "\n").encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--part", type=Path, action="append", required=True)
    parser.add_argument("--public-root", type=Path, default=ROOT)
    parser.add_argument("--private-root", type=Path, default=ROOT.parent / "math-gauge-private")
    parser.add_argument("--private-out", type=Path, required=True)
    parser.add_argument("--public-out", type=Path, required=True)
    args = parser.parse_args()
    parts = [json.loads(path.read_bytes()) for path in args.part]
    document = merge(parts)
    verify_sources(document, {"public": args.public_root, "private": args.private_root})
    raw = encode(document)
    public = project_public(document, private_sha256=hashlib.sha256(raw).hexdigest())
    validate_public(public)
    # Resolve and validate every input before either output becomes selectable.
    for path, content in ((args.private_out, raw), (args.public_out, encode(public))):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)
    print(json.dumps({"status": "passed", "groups": len(document["groups"]),
                      "reviewed_source_runs": len(document["runs"]), "sources": len(document["sources"]),
                      "source_review_sha256": public["source_review_sha256"], "candidate_calls": 0}))


if __name__ == "__main__":
    main()
