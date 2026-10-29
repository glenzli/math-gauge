"""Offline supplemental comparison using only the byte-verified archive."""
import argparse
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
from replay_comparison import (archived_comparator, digest, install_offline_guard,
                               load, normalized, relocate, verified_archive)


def replay(archive, output):
    archive, output = Path(archive).resolve(), Path(output).resolve()
    if output.exists() or output.is_relative_to(archive):
        raise ValueError("Use a new output directory outside archived evidence")
    manifest, names = verified_archive(archive)
    if manifest.get("experiment") != "r005-clarified-supplement":
        raise ValueError("Not a single-case supplement archive")
    old_root = Path(manifest["source_root"])
    if archive.is_relative_to(old_root) or output.is_relative_to(old_root):
        raise ValueError("Archive and replay output must survive deletion of the old root")
    required = {"scoring/comparison.json", "scoring/review-manifest.json",
                "tools/supplement_replay.py", "tools/replay_comparison.py"}
    if not required.issubset(names):
        raise ValueError("Missing supplemental scoring or offline tools")
    install_offline_guard(old_root, archive, names)
    freeze = load(archive / "runtime/freeze.json")
    index = load(archive / "runtime/model-runs.json")
    if any(x["task_kind"] != "written" for x in freeze["cases"]):
        raise ValueError("This supplement has no candidate Lean obligations")
    runs = {label: [relocate(p, old_root, archive, names, directory=True) for p in paths]
            for label, paths in index["model_runs"].items()}
    receipts = {label: {cid: relocate(p, old_root, archive, names) for cid, p in rows.items()}
                for label, rows in index["execution_receipts"].items()}
    compare = archived_comparator(archive, freeze["runner_sha256"])
    report = compare(freeze["cases"], runs, execution_receipts=receipts, lean_reports={})
    baseline = load(archive / "scoring/comparison.json")
    a, b = normalized(report), normalized(baseline)
    checks = {
        "summary": {k:v["summary"] for k,v in a["models"].items()} == {k:v["summary"] for k,v in b["models"].items()},
        "groups": {k:v["groups"] for k,v in a["models"].items()} == {k:v["groups"] for k,v in b["models"].items()},
        "paired": a["paired"] == b["paired"],
        "cases_without_run_dir": {k:v["cases"] for k,v in a["models"].items()} == {k:v["cases"] for k,v in b["models"].items()},
        "full_report_without_created_at_and_run_dir": a == b,
    }
    verification = {"schema":"math-gauge.offline-comparison-check/v1", "experiment":manifest["experiment"],
        "matched":all(checks.values()), "checks":checks,
        "archive_manifest_sha256":digest(archive/"manifest.json"),
        "freeze_sha256":digest(archive/"runtime/freeze.json"),
        "shared_runner_sha256":freeze["runner_sha256"],
        "reference_sha256":digest(archive/"scoring/comparison.json"),
        "planned_cases":len(freeze["cases"]), "planned_runs":len(freeze["cases"])*len(freeze["model_order"]),
        "ignored_fields":["created_at","models.*.cases.*.run_dir"], "model_requests":0,
        "lean_recompiled":False, "mathematics_regraded":False, "original_evidence_modified":False,
        "old_temporary_root_open_blocked":True, "subprocess_and_network_blocked":True}
    output.mkdir(parents=True)
    for name, data in (("comparison.json",report),("verification.json",verification)):
        with (output/name).open("x",encoding="utf-8") as stream:
            json.dump(data,stream,indent=2,ensure_ascii=False);stream.write("\n")
    return verification


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive",type=Path,required=True)
    parser.add_argument("--output",type=Path,required=True)
    args=parser.parse_args()
    result=replay(args.archive,args.output)
    print(json.dumps({"matched":result["matched"],"checks":result["checks"],"model_requests":0}))
    return 0 if result["matched"] else 1


if __name__ == "__main__":raise SystemExit(main())
