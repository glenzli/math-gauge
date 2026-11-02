"""Historical configuration fixtures over unchanged public case bytes, never model data."""

import atexit
import functools
from pathlib import Path
import shutil
import tempfile

from math_gauge.benchmarks import BenchmarkProfile, build_plan, identity
from math_gauge.catalog import Suite, read_json

ROOT = Path(__file__).resolve().parents[1]
HISTORY = ROOT / "protocol/history/v0.2.0"


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

    names = {"sources.json"}
    for manifest in read_json(HISTORY / "suite.json")["cases"]:
        # Restore the exact historical logical names; only physical storage moved.
        # The source manifests remain case-relative and byte-identical.
        raw = read_json(current_source(manifest))
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
