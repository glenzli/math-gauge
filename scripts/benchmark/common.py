"""Operator-side identities and frozen-plan gates; no model request code."""

import hashlib
import importlib.util
import json
import sys
from datetime import datetime, timezone
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO))
sys.dont_write_bytecode = True
from math_gauge.catalog import Suite, candidate_message
from math_gauge.execution import runner_fingerprint

_spec = importlib.util.spec_from_file_location(
    "isolated_cli_prepare", REPO / "scripts/isolated_cli/prepare.py"
)
helper = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(helper)


def now():
    return datetime.now(timezone.utc).isoformat()


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def text_digest(value):
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def load(path):
    return json.loads(Path(path).read_text())


def save(path, value, *, exclusive=False):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("x" if exclusive else "w", encoding="utf-8") as stream:
        json.dump(value, stream, ensure_ascii=False, indent=2)
        stream.write("\n")


def code_identity():
    paths = sorted((REPO / "scripts/benchmark").glob("*.py"))
    paths += [REPO / "scripts/isolated_cli/prepare.py", REPO / "scripts/isolated_cli/probe.py"]
    return {str(p.relative_to(REPO)): digest(p) for p in paths}


def catalog_suites(catalog_path):
    catalog = load(catalog_path)
    if catalog.get("schema") != "math-gauge.case-catalog/v1":
        raise ValueError("Unsupported case catalog")
    result = []
    seen = set()
    for row in catalog["suites"]:
        root = (REPO / row["root"]).resolve()
        if not root.is_relative_to(REPO):
            raise ValueError("Suite root escaped repository")
        suite = Suite.load(root)
        if suite.sha256 != row["suite_sha256"]:
            raise ValueError("Catalog suite has changed: " + row["root"])
        for case in suite.select(row["cases"]):
            if case["id"] in seen:
                raise ValueError("Duplicate case across catalog suites")
            seen.add(case["id"])
        result.append((row, suite))
    entries = catalog.get("entries", [])
    entry_ids = [entry["case_id"] for entry in entries]
    categories = catalog.get("categories", [])
    category_ids = [cid for category in categories for cid in category["case_ids"]]
    if (not seen or len(entry_ids) != len(set(entry_ids)) or set(entry_ids) != seen
            or len(category_ids) != len(set(category_ids)) or set(category_ids) != seen):
        raise ValueError("Catalog entries and categories must cover every selected case exactly once")
    return catalog, result


def verify_release(runtime, release_path):
    runtime = Path(runtime)
    freeze_path = runtime / "freeze.json"
    freeze, release = load(freeze_path), load(release_path)
    if not (
        release.get("schema") == "math-gauge.comparison-release/v1"
        and release.get("allow_mathematical_requests") is True
        and release.get("released_by") == "/root"
        and release.get("freeze_sha256") == digest(freeze_path)
        and release.get("catalog_sha256") == freeze["catalog_sha256"]
        and release.get("model_order") == ["terra", "gemini"]
    ):
        raise ValueError("Explicit root release does not bind this frozen comparison")
    if digest(freeze["catalog_path"]) != freeze["catalog_sha256"]:
        raise ValueError("Frozen catalog changed")
    if code_identity() != freeze["code_identity"] or runner_fingerprint() != freeze["runner_sha256"]:
        raise ValueError("Frozen runtime or shared runner changed")
    for item in freeze["preflight_bindings"] + freeze.get("session_bindings", []):
        if digest(item["path"]) != item["sha256"]:
            raise ValueError("Frozen preflight artifact changed")
    for snapshot in freeze["suite_snapshots"]:
        if Suite.load(snapshot["root"]).sha256 != snapshot["suite_sha256"]:
            raise ValueError("Frozen suite snapshot changed")
    return freeze
