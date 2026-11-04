"""Historical configuration fixtures over unchanged public case bytes, never model data."""

import atexit
import functools
import hashlib
from pathlib import Path
import shutil
import tempfile

from math_gauge.benchmarks import BenchmarkProfile, build_plan, identity
from math_gauge.catalog import Suite, read_json, write_json

ROOT = Path(__file__).resolve().parents[1]
HISTORY = ROOT / "protocol/history/v0.2.0"

# These original credit records were part of the frozen registry even though
# no case cites them directly. Preserve them while excluding later additions.
LEGACY_CREDITS = {"openai-torus-formal-reuse", "vilin-topology-formal-reuse",
                  "tauceti-topology-formal-reuse"}


def legacy_sources(registry, case_sources):
    """Project the original source graph without importing unrelated new cases."""
    pending = [*case_sources, *LEGACY_CREDITS]
    selected = set()
    while pending:
        name = pending.pop()
        if name in selected:
            continue
        selected.add(name)
        source = registry[name]
        pending.extend(source.get("sources", []))
        if isinstance(source.get("parent"), str):
            pending.append(source["parent"])
    # Preserve the original registry order and bytes under write_json.
    return {name: source for name, source in registry.items() if name in selected}


@functools.lru_cache(maxsize=1)
def legacy_root():
    temporary = tempfile.TemporaryDirectory(prefix="math-gauge-legacy-config-fixture-")
    atexit.register(temporary.cleanup)
    root = Path(temporary.name).resolve()
    cases = root / "cases"
    cases.mkdir()
    shutil.copy2(HISTORY / "suite.json", cases / "suite.json")
    shutil.copy2(HISTORY / "taxonomy.json", cases / "taxonomy.json")
    relocations = read_json(ROOT / "cases/reserve/relocations.json")["case_paths"]

    def current_source(name):
        recorded = "cases/" + name
        for row in relocations:
            if recorded == row["previous"] or recorded.startswith(row["previous"] + "/"):
                return ROOT / (row["current"] + recorded[len(row["previous"]):])
        return ROOT / recorded

    names, case_sources = set(), set()
    for manifest in read_json(HISTORY / "suite.json")["cases"]:
        # Restore the exact historical logical names; only physical storage moved.
        # The source manifests remain case-relative and byte-identical.
        raw = read_json(current_source(manifest))
        case_sources.update(raw["sources"])
        prefix = Path(manifest).parent
        case = dict(raw)
        if raw.get("path_base") == "case":
            for key in ("task", "reference", "rubric", "group_contract"):
                if case.get(key):
                    case[key] = str(prefix / case[key])
            case["solver_files"] = [dict(item, source=str(prefix / item["source"]))
                                    for item in case["solver_files"]]
            for key in ("evaluator_files", "lean_checks"):
                case[key] = [str(prefix / name) for name in case.get(key, [])]
        names.update([manifest, case["task"], case["reference"], case["rubric"],
                      *case.get("evaluator_files", []), *case["lean_checks"]])
        if case.get("group_contract"):
            names.add(case["group_contract"])
        names.update(item["source"] for item in case["solver_files"])
    for name in names:
        target = cases / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(current_source(name), target)
    write_json(cases / "sources.json",
               legacy_sources(read_json(ROOT / "cases/sources.json"), case_sources))
    protocol = root / "protocol"
    protocol.mkdir()
    shutil.copy2(HISTORY / "benchmark-profile.json", protocol / "benchmark-profile.json")
    shutil.copytree(HISTORY / "reliability", protocol / "reliability")
    return root


def legacy_suite():
    return Suite.load(legacy_root() / "cases")


def legacy_profile(suite=None):
    return BenchmarkProfile.load(legacy_root() / "protocol/benchmark-profile.json", suite or legacy_suite())


def legacy_release_plan(version="0.1.0"):
    suite = legacy_suite()
    plan = build_plan(legacy_profile(suite), suite)
    config = read_json(ROOT / f"releases/v{version}/config.json")
    plan.update(plan_id=config["plan_id"], created_at=config["created_at"])
    plan["plan_sha256"] = identity({key: value for key, value in plan.items() if key != "plan_sha256"})
    return plan, suite


@functools.lru_cache(maxsize=1)
def compact_release_root():
    """Keep published v0.4 content isolated while exercising the current runner."""
    snapshot = read_json(ROOT / "tests/fixtures/compact-v0.4.0-source.json")
    temporary = tempfile.TemporaryDirectory(prefix="math-gauge-v040-source-fixture-")
    atexit.register(temporary.cleanup)
    root = Path(temporary.name).resolve()
    for name, item in snapshot["files"].items():
        raw = item["content"].encode("utf-8")
        if hashlib.sha256(raw).hexdigest() != item["sha256"]:
            raise ValueError("Historical release fixture bytes changed: " + name)
        target = root / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(raw)
    for manifest in read_json(root / "cases/suite.json")["cases"]:
        directory = Path(manifest).parent
        shutil.copytree(ROOT / "cases" / directory, root / "cases" / directory)
    shutil.copy2(legacy_root() / "cases/sources.json", root / "cases/sources.json")
    for name, expected in snapshot["unchanged_asset_sha256"].items():
        source = ROOT / name
        if hashlib.sha256(source.read_bytes()).hexdigest() != expected:
            raise ValueError("Published release asset changed: " + name)
        target = root / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)
    # The fixture is a local preview of historical inputs with today's software,
    # never a claim to reproduce the published release's clean source commit.
    for source in (ROOT / "math_gauge").glob("*.py"):
        target = root / "math_gauge" / source.name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)
    (root / "scripts").mkdir()
    shutil.copy2(ROOT / "scripts/release.py", root / "scripts/release.py")
    return root


@functools.lru_cache(maxsize=1)
def v05_root():
    """Read the exact archived v0.5 profile over its unchanged original cases."""
    temporary = tempfile.TemporaryDirectory(prefix="math-gauge-v050-config-fixture-")
    atexit.register(temporary.cleanup)
    root = Path(temporary.name).resolve()
    history = ROOT / "protocol/history/v0.5.0"
    cases = root / "cases"
    cases.mkdir()
    for name in ("suite.json", "reserve-suite.json", "sources.json", "taxonomy.json", "catalog.json"):
        shutil.copy2(history / name, cases / name)
    for name in ("suite.json", "reserve-suite.json"):
        for manifest in read_json(history / name)["cases"]:
            directory = Path(manifest).parent
            shutil.copytree(ROOT / "cases" / directory, cases / directory)
    protocol = root / "protocol"
    protocol.mkdir()
    shutil.copy2(history / "benchmark-profile.json", protocol / "benchmark-profile.json")
    shutil.copytree(history / "reliability", protocol / "reliability")
    return root


def v05_suite():
    return Suite.load(v05_root() / "cases")


def v05_profile(suite=None):
    return BenchmarkProfile.load(v05_root() / "protocol/benchmark-profile.json", suite or v05_suite())
