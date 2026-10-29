"""Recompute saved judgments offline with the archived shared comparison code.

This relocates paths in memory; it never edits evidence, submits a model request,
regrades mathematics, or reruns Lean. Use only after the final evidence archive
and the final comparison.json have been written.
"""

import argparse
import hashlib
import importlib
import importlib.util
import json
import os
from pathlib import Path
import sys


def load(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def safe_child(root, relative):
    root, relative = Path(root).resolve(), Path(relative)
    if relative.is_absolute() or ".." in relative.parts:
        raise ValueError("Unsafe evidence path: " + str(relative))
    result = root / relative
    if any((root / Path(*relative.parts[:n])).is_symlink()
           for n in range(1, len(relative.parts) + 1)):
        raise ValueError("Evidence must not use symlinks: " + str(result))
    if not result.resolve().is_relative_to(root):
        raise ValueError("Evidence path escaped root")
    return result


def verified_archive(archive):
    manifest = load(archive / "manifest.json")
    if manifest.get("schema") != "math-gauge.final-execution-archive/v1" or manifest.get("queue_terminal") is not True:
        raise ValueError("A final execution archive is required")
    names = set()
    for row in manifest["files"]:
        if row["path"] in names:
            raise ValueError("Repeated archive manifest entry")
        names.add(row["path"])
        source = safe_child(archive, row["path"])
        if not source.is_file() or digest(source) != row["sha256"]:
            raise ValueError("Archive hash mismatch: " + row["path"])
    for required in ("runtime/freeze.json", "runtime/root-release.json",
                     "runtime/model-runs.json", "runtime/queue-final.json"):
        if required not in names:
            raise ValueError("Archive missing required evidence: " + required)
    release = load(archive / "runtime/root-release.json")
    if release.get("freeze_sha256") != digest(archive / "runtime/freeze.json"):
        raise ValueError("Release does not bind the archived freeze")
    for source in (archive / "source-code/math_gauge").rglob("*.py"):
        if str(source.relative_to(archive)) not in names:
            raise ValueError("Unmanifested shared code: " + str(source))
    return manifest, names


def relocate(path, old_root, archive, names, *, directory=False):
    try:
        relative = Path(path).relative_to(old_root)
    except ValueError as error:
        raise ValueError("Indexed path is outside the original evidence root") from error
    result = safe_child(archive, relative)
    required = str(relative / "run.json") if directory else str(relative)
    if required not in names:
        raise ValueError("Indexed evidence is not in the archive: " + required)
    return str(result)


def relocate_lean(mapping, answers):
    reports, evidence = {}, []
    for label, cases in mapping.items():
        reports[label] = {}
        for cid, original in cases.items():
            parts = Path(original).parts
            if len(parts) < 4 or parts[-4] != "answers" or parts[-2:] != ("lean", "report.json"):
                raise ValueError("Unexpected archived Lean report path")
            relative = Path(*parts[-3:])
            report = safe_child(answers, relative)
            declaration = safe_child(answers, Path(parts[-3]) / "archive-manifest.json")
            matches = [row for row in load(declaration)
                       if tuple(Path(row["archived"]).parts[-4:]) == tuple(parts[-4:])]
            if len(matches) != 1 or digest(report) != matches[0]["sha256"]:
                raise ValueError("Candidate Lean report archive binding changed: " + cid)
            reports[label][cid] = str(report)
            evidence.append({"model_label": label, "case_id": cid,
                             "report": str(relative), "sha256": digest(report)})
    return reports, evidence


def install_offline_guard(old_root, archive, names):
    old_root = os.path.normpath(str(old_root))
    archive = os.path.normpath(str(archive))
    allowed = {str(Path(archive) / name) for name in names} | {str(Path(archive) / "manifest.json")}

    def guard(event, args):
        if event in {"subprocess.Popen", "os.system", "os.exec", "os.posix_spawn",
                     "socket.connect", "socket.connect_ex", "socket.getaddrinfo"}:
            raise RuntimeError("Offline recomputation forbids processes and network access")
        if event == "open" and isinstance(args[0], (str, bytes, os.PathLike)):
            path = os.path.abspath(os.fsdecode(args[0]))
            if path == old_root or path.startswith(old_root + os.sep):
                raise RuntimeError("Offline recomputation tried to read the old temporary root")
            if path.startswith(archive + os.sep) and path not in allowed:
                # Importlib probes a bytecode cache before reading the verified
                # source, even when bytecode writes are disabled. Never use it.
                if path.endswith(".pyc"):
                    raise FileNotFoundError(path)
                raise RuntimeError("Offline recomputation tried to open unmanifested archive evidence: " + path)

    sys.addaudithook(guard)


def archived_comparator(archive, expected_fingerprint):
    package = archive / "source-code/math_gauge"
    alias = "_math_gauge_archived_comparison"
    if alias in sys.modules:
        raise ValueError("Use a fresh Python process for each offline recomputation")
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location(alias, package / "__init__.py",
                                                submodule_search_locations=[str(package)])
    module = importlib.util.module_from_spec(spec)
    sys.modules[alias] = module
    spec.loader.exec_module(module)
    execution = importlib.import_module(alias + ".execution")
    if execution.runner_fingerprint() != expected_fingerprint:
        raise ValueError("Archived shared runner differs from the pre-inference freeze")
    review = importlib.import_module(alias + ".review")
    if Path(review.__file__).resolve() != (package / "review.py").resolve():
        raise ValueError("Comparison code was loaded outside the archive")
    return review.compare_models


def normalized(report):
    data = json.loads(json.dumps(report))
    data.pop("created_at", None)
    for model in data["models"].values():
        for case in model["cases"]:
            case.pop("run_dir", None)
    return data


def replay(archive, results, reference, lean_map, output):
    archive, results, output = archive.resolve(), results.resolve(), output.resolve()
    if output.exists() or output.is_relative_to(archive) or output.is_relative_to(results / "answers"):
        raise ValueError("Output must be a new directory outside original evidence")
    manifest, names = verified_archive(archive)
    old_root = Path(manifest["source_root"])
    if archive.is_relative_to(old_root):
        raise ValueError("Archive must survive removal of the original temporary root")
    install_offline_guard(old_root, archive, names)
    freeze = load(archive / "runtime/freeze.json")
    run_index = load(archive / "runtime/model-runs.json")
    model_runs = {label: [relocate(path, old_root, archive, names, directory=True)
                          for path in paths] for label, paths in run_index["model_runs"].items()}
    receipts = {label: {cid: relocate(path, old_root, archive, names) for cid, path in cases.items()}
                for label, cases in run_index["execution_receipts"].items()}
    lean, lean_evidence = relocate_lean(load(lean_map), results / "answers")
    compare = archived_comparator(archive, freeze["runner_sha256"])
    report = compare(freeze["cases"], model_runs, execution_receipts=receipts, lean_reports=lean)
    baseline = load(reference)
    normalized_report, normalized_baseline = normalized(report), normalized(baseline)
    checks = {
        "summary": {label: report["models"][label]["summary"] for label in report["model_order"]}
                   == {label: baseline["models"][label]["summary"] for label in baseline["model_order"]},
        "groups": {label: report["models"][label]["groups"] for label in report["model_order"]}
                  == {label: baseline["models"][label]["groups"] for label in baseline["model_order"]},
        "paired": report["paired"] == baseline["paired"],
        "cases_without_run_dir": {label: normalized_report["models"][label]["cases"] for label in report["model_order"]}
                                 == {label: normalized_baseline["models"][label]["cases"] for label in baseline["model_order"]},
        "full_report_without_created_at_and_run_dir": normalized_report == normalized_baseline,
    }
    verification = {"schema": "math-gauge.offline-comparison-check/v1", "matched": all(checks.values()),
                    "checks": checks, "archive_manifest_sha256": digest(archive / "manifest.json"),
                    "freeze_sha256": digest(archive / "runtime/freeze.json"),
                    "shared_runner_sha256": freeze["runner_sha256"], "reference_sha256": digest(reference),
                    "lean_map_sha256": digest(lean_map), "lean_reports": lean_evidence,
                    "ignored_fields": ["created_at", "models.*.cases.*.run_dir"],
                    "model_requests": 0, "lean_recompiled": False, "mathematics_regraded": False,
                    "original_evidence_modified": False, "old_temporary_root_open_blocked": True,
                    "subprocess_and_network_blocked": True}
    output.mkdir(parents=True)
    for name, data in [("comparison.json", report), ("verification.json", verification)]:
        with (output / name).open("x", encoding="utf-8") as stream:
            json.dump(data, stream, ensure_ascii=False, indent=2)
            stream.write("\n")
    return verification


def main():
    base = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path, default=base / "runtime/evidence-final")
    parser.add_argument("--results", type=Path, default=base)
    parser.add_argument("--reference", type=Path)
    parser.add_argument("--lean-map", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = replay(args.archive, args.results, args.reference or args.results / "comparison.json",
                    args.lean_map or args.results / "reviews/lean-report-map.json", args.output)
    print(json.dumps({"matched": result["matched"], "checks": result["checks"], "output": str(args.output)}))
    raise SystemExit(0 if result["matched"] else 1)


if __name__ == "__main__":
    main()
