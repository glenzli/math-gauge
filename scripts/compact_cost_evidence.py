#!/usr/bin/env python3
"""Copy one selected cost snapshot into a lossless, single-copy evidence archive.

This migration never deletes its input, contacts a model, changes a counter or
selects an attempt. Superseded snapshots can be removed after the caller has
verified this output and secured the original tree in Git history.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from math_gauge.costs import (ARCHIVE_SCHEMA, SUPPLEMENT_REFERENCE_SCHEMA, VERSION, project_public,
                              source_descriptor, validate_private, verify_source)


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n")


def selected_sources(model):
    for slot in model["slots"]:
        yield slot
    for field in ("estimate", "cost_resolution"):
        if model.get(field) is not None:
            yield model[field]


def inventory_semantics(document):
    """Only evidence locations may differ; all other frozen fields must match."""
    value = copy.deepcopy(document)
    value.pop("evidence_archive", None)
    for model in value["models"]:
        for owner in selected_sources(model):
            for source in owner.get("sources", []):
                source.pop("path", None)
    return value


def compact_snapshot(source, output, *, source_git_revision, public_root=None):
    source, output = Path(source).resolve(), Path(output).resolve()
    public_root = Path(public_root or Path(__file__).resolve().parents[1]).resolve()
    active_version = json.loads((public_root / "benchmark.json").read_text())["version"]
    if output.exists() or output.is_relative_to(source) or source.is_relative_to(output):
        raise ValueError("Use a new output directory outside the original snapshot")
    original = json.loads((source / "costs.json").read_text())
    if original.get("evidence_archive") is not None:
        raise ValueError("This snapshot already has a canonical evidence archive")
    before = validate_private(original, root=source)
    files = {}
    objects = {}
    for path in sorted(source.rglob("*")):
        if path.is_symlink():
            raise ValueError("Cost snapshot must not contain symbolic links")
        if not path.is_file():
            continue
        data = path.read_bytes()
        sha = hashlib.sha256(data).hexdigest()
        files[path.relative_to(source).as_posix()] = sha
        objects.setdefault(sha, data)
    output.mkdir(parents=True)
    descriptors = {}
    for sha, data in sorted(objects.items()):
        path = output / "evidence" / "sha256" / sha
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
        descriptors[sha] = source_descriptor(path, output)

    def retained(descriptor, relative_root):
        verify_source(relative_root, descriptor)
        path = (relative_root / descriptor["path"]).resolve()
        logical = path.relative_to(source).as_posix()
        return copy.deepcopy(descriptors[files[logical]])

    def relocate(model, relative_root):
        for owner in selected_sources(model):
            if "sources" in owner:
                owner["sources"] = [retained(item, relative_root) for item in owner["sources"]]

    manifest = {"schema": ARCHIVE_SCHEMA, "version": VERSION,
        "source_git_revision": source_git_revision,
        "source_snapshot": source.name,
        "source_inventory": descriptors[files["costs.json"]],
        "preserved": {"original_files": len(files), "original_bytes": sum(len(objects[sha]) for sha in files.values()),
                      "unique_objects": len(objects), "unique_bytes": sum(len(data) for data in objects.values())},
        "objects": list(descriptors.values()),
        "files": [{"original_path": name, "sha256": sha} for name, sha in files.items()]}
    manifest_path = output / "evidence-archive.json"
    write_json(manifest_path, manifest)
    current = copy.deepcopy(original)
    for model in current["models"]:
        relocate(model, source)
    current["evidence_archive"] = source_descriptor(manifest_path, output)
    if inventory_semantics(current) != inventory_semantics(original):
        raise ValueError("Canonicalization changed frozen cost inventory fields")
    after = validate_private(current, root=output)
    if before != after:
        raise ValueError("Canonicalization changed model cost or token summaries")
    write_json(output / "costs.json", current)
    current_descriptor = source_descriptor(output / "costs.json", output)
    public = project_public(current, source_sha256=current_descriptor["sha256"], root=output,
                            benchmark_version=active_version)
    old_public = project_public(original, source_sha256=current_descriptor["sha256"], benchmark_version=active_version)
    if public != old_public:
        raise ValueError("Canonicalization changed public model cost fields")
    write_json(output / "public.json", public)

    recipe_path = source / "reproduction-inputs.json"
    if recipe_path.is_file():
        recipe = json.loads(recipe_path.read_text())
        supplements = []
        for descriptor in recipe["supplements"]:
            verify_source(source, descriptor)
            path = source / descriptor["path"]
            model = json.loads(path.read_text())
            model_id = model["model_id"]
            if Path(model_id).name != model_id:
                raise ValueError("Supplement model identity must be a filename component")
            relocated = copy.deepcopy(model)
            relocate(relocated, path.parent)
            adopted = next(item for item in current["models"] if item["model_id"] == model_id)
            for field in ("slots", "estimate", "cost_resolution", "pricing_basis"):
                if relocated.get(field) != adopted.get(field):
                    raise ValueError("Reproduction supplement differs from the adopted model inventory")
            destination = output / f"supplement-{model_id}.json"
            write_json(destination, {"schema": SUPPLEMENT_REFERENCE_SCHEMA, "version": VERSION,
                "model_id": model_id, "record_id": model["record_id"], "inventory": current_descriptor})
            supplements.append(source_descriptor(destination, output))
        recipe["supplements"] = supplements
        recipe["extra_prices"] = [retained(item, source) for item in recipe.get("extra_prices", [])]
        recipe["collector_sha256"] = hashlib.sha256((public_root / recipe["public_collector"]).read_bytes()).hexdigest()
        recipe["cost_owner_sha256"] = hashlib.sha256((public_root / recipe["public_cost_owner"]).read_bytes()).hexdigest()
        recipe["evidence_archive"] = current["evidence_archive"]
        write_json(output / "reproduction-inputs.json", recipe)

    verification = {"schema": "math-gauge.cost-archive-verification/v1", "version": VERSION,
        "benchmark_version": active_version, "source_benchmark_version": original.get("benchmark_version", "0.6.0"),
        "source_git_revision": source_git_revision,
        "source_inventory": manifest["source_inventory"], "current_inventory": current_descriptor,
        "evidence_archive": current["evidence_archive"], "preserved": manifest["preserved"],
        "all_original_files_recoverable": True,
        "all_nonlocation_inventory_fields_unchanged": True,
        "all_model_token_cost_coverage_summaries_unchanged": True,
        "all_public_cost_fields_unchanged": True, "raw_model_records_unchanged": True,
        "new_candidate_calls": 0}
    write_json(output / "archive-verification.json", verification)
    return verification


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--source-git-revision", required=True)
    parser.add_argument("--public-root", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    result = compact_snapshot(args.source, args.output, source_git_revision=args.source_git_revision,
                              public_root=args.public_root)
    print(json.dumps({"output": str(args.output), "preserved": result["preserved"],
                      "costs_sha256": result["current_inventory"]["sha256"]}, ensure_ascii=False))


if __name__ == "__main__":
    main()
