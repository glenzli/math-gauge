"""Thin two-slot scheduler over math_gauge.execution.run, with frozen snapshots."""

import argparse
import concurrent.futures
import json
import shutil
import sys
import threading
from pathlib import Path

from common import REPO, Suite, candidate_message, catalog_suites, code_identity, digest, load, now, runner_fingerprint, save, text_digest, verify_release
from isolation import open_probe, prepare_session
from preflight import DEFAULT_ROOT, network_probe
from math_gauge.execution import run as runner_run


def snapshot_suite(suite, destination):
    """Copy exactly the existing Suite fingerprint's declared files."""
    names = {"suite.json", "sources.json", *suite.metadata["cases"]}
    for case in suite.cases.values():
        names.update(case[key] for key in ["task", "reference", "rubric"])
        names.update(case.get("evaluator_files", []))
        names.update(case["lean_checks"])
        names.update(item["source"] for item in case["solver_files"])
    destination.mkdir(parents=True, exist_ok=False)
    for name in sorted(names):
        target = destination / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes((suite.root / name).read_bytes())
        target.chmod(0o444)
    frozen = Suite.load(destination)
    if frozen.sha256 != suite.sha256:
        raise RuntimeError("Snapshot differs from shared Suite fingerprint")
    return frozen


def prepare(root, catalog_path):
    if (root / "runtime/freeze.json").exists():
        raise ValueError("Freeze already exists; do not rewrite a released plan")
    qualification = load(root / "preflight/qualification.json")
    if qualification.get("passed") is not True:
        raise ValueError("Both clients need completed preflight before freeze")
    catalog, suites = catalog_suites(catalog_path)
    if catalog.get("snapshot_status") != "final-catalog-snapshot":
        raise ValueError("Catalog owner has not finalized the source snapshot")
    entries = {entry["case_id"]: entry for entry in catalog["case_entries"]}
    runtime = root / "runtime"; runtime.mkdir(parents=True, exist_ok=True)
    frozen_catalog = runtime / "catalog.frozen.json"
    frozen_catalog.write_bytes(Path(catalog_path).read_bytes()); frozen_catalog.chmod(0o444)
    snapshots, rows = [], []
    for index, (catalog_row, suite) in enumerate(suites):
        frozen = snapshot_suite(suite, root / "frozen-suites" / str(index))
        snapshots.append({"root": str(frozen.root), "original_root": str(suite.root), "suite_sha256": frozen.sha256})
        for case in frozen.select(catalog_row["cases"]):
            request = frozen.request(case); message = candidate_message(request)
            payload = root / "payloads" / (case["id"] + ".md")
            payload.parent.mkdir(parents=True, exist_ok=True)
            payload.write_bytes(message.encode("utf-8")); payload.chmod(0o444)
            sessions = {}
            for model in ["terra", "gemini"]:
                session = root / "sessions" / model / case["id"]
                session.parent.mkdir(parents=True, exist_ok=True)
                prepare_session(load(root / "config" / (model + ".json")), payload, session)
                open_probe(session); network_probe(session)
                sessions[model] = str(session)
            entry = entries[case["id"]]
            rows.append({"case_id": case["id"], "version": case["version"], "task_kind": entry["task_kind"], "family_id": entry["family_id"], "section": entry["section"], "author_lean_coverage": entry["author_lean_coverage"], "suite_root": str(frozen.root), "suite_sha256": frozen.sha256, "request_sha256": text_digest(json.dumps(request, ensure_ascii=False, sort_keys=True)), "candidate_message_sha256": text_digest(message), "candidate_message_bytes": len(message.encode("utf-8")), "attachment_names": [f["name"] for f in request["files"]], "sessions": sessions})
    bindings = qualification["bindings"] + [{"path": str(root / "preflight/qualification.json"), "sha256": digest(root / "preflight/qualification.json")}]
    freeze = {"schema": "math-gauge.comparison-freeze/v1", "utc": now(), "catalog_path": str(frozen_catalog), "catalog_original_path": str(Path(catalog_path).resolve()), "catalog_sha256": digest(frozen_catalog), "runtime_root": str(root), "runner_sha256": runner_fingerprint(), "code_identity": code_identity(), "preflight_bindings": bindings, "suite_snapshots": snapshots, "cases": rows, "model_order": ["terra", "gemini"], "parallel_per_model": 2, "timeout_seconds": 2700, "automatic_retry": False, "mathematical_requests": 0}
    save(runtime / "snapshot-plan.json", freeze, exclusive=True)
    print(json.dumps({"status": "prepared-awaiting-runtime-finalization", "snapshot_plan": str(runtime / "snapshot-plan.json"), "catalog_sha256": freeze["catalog_sha256"], "case_count": len(rows)}))


def finalize(root):
    runtime = root / "runtime"
    draft = runtime / "snapshot-plan.json"
    freeze = load(draft)
    if digest(freeze["catalog_path"]) != freeze["catalog_sha256"]:
        raise ValueError("Prepared catalog changed")
    for snapshot in freeze["suite_snapshots"]:
        if Suite.load(snapshot["root"]).sha256 != snapshot["suite_sha256"]:
            raise ValueError("Prepared suite changed")
    for row in freeze["cases"]:
        suite = Suite.load(row["suite_root"])
        case = suite.cases[row["case_id"]]
        request = suite.request(case)
        rubric = suite.root / case["rubric"]
        row["rubric_sha256"] = digest(rubric)
        row["audit_expected"] = load(rubric)["expected"] if row["task_kind"] == "audit" else None
        if row["task_kind"] == "audit" and row["audit_expected"] not in {"aligned", "misaligned"}:
            raise ValueError("Audit rubric lacks a binary expected verdict")
        if text_digest(candidate_message(request)) != row["candidate_message_sha256"] or text_digest(json.dumps(request, ensure_ascii=False, sort_keys=True)) != row["request_sha256"]:
            raise ValueError("Prepared candidate projection changed")
        for session_path in row["sessions"].values():
            session = Path(session_path)
            if (session / "runtime/execution.json").exists():
                raise ValueError("Cannot freeze a previously attempted mathematical session")
            if digest(session / "input/task.md") != row["candidate_message_sha256"]:
                raise ValueError("Prepared session input changed")
            prepared = load(session / "runtime/prepared-hashes.json")
            for name, expected in prepared.items():
                if digest(session / name) != expected:
                    raise ValueError("Prepared session policy artifact changed")
    for item in freeze["preflight_bindings"]:
        if digest(item["path"]) != item["sha256"]:
            raise ValueError("Prepared preflight changed")
    bindings = []
    for row in freeze["cases"]:
        for session_path in row["sessions"].values():
            session = Path(session_path)
            names = {"runtime/prepared-hashes.json", "runtime/preparation-extension.json", "runtime/open-probe.json", "runtime/network-probe.json", *load(session / "runtime/prepared-hashes.json")}
            names.discard("runtime/attempt-ledger.json")
            if load(session / "runtime/plan.json")["client"] == "agy":
                names.add("state/antigravity-cli/settings.json")
            for name in sorted(names):
                path = session / name
                bindings.append({"path": str(path), "sha256": digest(path)})
    freeze.update(utc=now(), code_identity=code_identity(), runner_sha256=runner_fingerprint(), snapshot_plan_sha256=digest(draft), session_bindings=bindings)
    save(runtime / "freeze.json", freeze, exclusive=True)
    print(json.dumps({"status": "frozen-awaiting-root-release", "freeze": str(runtime / "freeze.json"), "freeze_sha256": digest(runtime / "freeze.json"), "catalog_sha256": freeze["catalog_sha256"], "case_count": len(freeze["cases"])}))


def run_queue(root, release):
    runtime = root / "runtime"
    freeze = verify_release(runtime, release)
    save(runtime / "queue-start.json", {"started_utc": now(), "release_path": str(release), "release_sha256": digest(release), "freeze_sha256": digest(runtime / "freeze.json"), "model_order": freeze["model_order"], "parallel_per_model": 2}, exclusive=True)
    progress = runtime / "progress.ndjson"
    lock = threading.Lock()
    stop = threading.Event()
    results = []

    def emit(record):
        record = dict(utc=now(), **record)
        with lock:
            with progress.open("a") as stream:
                stream.write(json.dumps(record, ensure_ascii=False) + "\n")
            print(json.dumps(record, ensure_ascii=False), flush=True)

    def one(model, item):
        cid = item["case_id"]
        if stop.is_set():
            record = {"model": model, "case_id": cid, "status": "not-started-after-operational-failure", "request_count": 0}
            emit(record)
            return record
        destination = root / "records" / model / cid
        config = load(root / "config" / (model + ".json"))
        command = [sys.executable, "-B", str(REPO / "scripts/benchmark/cli_adapter.py"), "--runtime", str(runtime), "--release", str(release), "--model", model, "--case", cid]
        emit({"model": model, "case_id": cid, "status": "starting", "record_root": str(destination)})
        try:
            verify_release(runtime, release)
            metadata = runner_run(Suite.load(item["suite_root"]), destination, ids=[cid], command=command, model=config["model"] + "/" + config["effort"], timeout=freeze["timeout_seconds"] + 90)
            execution_path = Path(item["sessions"][model]) / "runtime/execution.json"
            execution = load(execution_path) if execution_path.is_file() else {}
            record = {"model": model, "case_id": cid, "status": "completed" if metadata["execution_failures"] == 0 else "failed", "request_count": execution.get("request_count", 0), "record_root": str(destination), "execution_path": str(execution_path), "response_path": str(destination / cid / "response.md"), "requested_model": config["model"], "requested_effort": config["effort"], "observed_model": execution.get("observed_model"), "observed_effort": execution.get("observed_effort")}
            if record["status"] != "completed":
                stop.set()
        except BaseException as error:
            stop.set()
            record = {"model": model, "case_id": cid, "status": "launcher-failed", "error": type(error).__name__ + ": " + str(error)}
        emit(record)
        return record

    for model in freeze["model_order"]:
        if stop.is_set():
            for item in freeze["cases"]:
                record = {"model": model, "case_id": item["case_id"], "status": "not-started-after-operational-failure", "request_count": 0}
                emit(record); results.append(record)
            break
        emit({"model": model, "status": "model-phase-started"})
        with concurrent.futures.ThreadPoolExecutor(max_workers=2) as executor:
            futures = [executor.submit(one, model, item) for item in freeze["cases"]]
            for future in concurrent.futures.as_completed(futures):
                results.append(future.result())
                save(runtime / "queue-status.json", {"utc": now(), "halt_new_starts": stop.is_set(), "results": results})
                save(runtime / "model-runs.json", model_run_index(root, results))
        if not stop.is_set():
            emit({"model": model, "status": "model-phase-completed"})
    save(runtime / "queue-final.json", {"finished_utc": now(), "completed": len(results) == 82 and all(x["status"] == "completed" for x in results), "halt_new_starts": stop.is_set(), "results": results, "mathematical_scoring_performed": False})
    save(runtime / "model-runs.json", model_run_index(root, results))
    return 1 if stop.is_set() else 0


def model_run_index(root, results):
    mapping, assessments, receipt_map = {}, [], {}
    for model in ["terra", "gemini"]:
        config = load(root / "config" / (model + ".json"))
        label = config["model"] + "/" + config["effort"]
        mapping[label] = []
        receipt_map[label] = {}
        for row in results:
            if row["model"] == model and row.get("record_root") and (Path(row["record_root"]) / "run.json").is_file():
                mapping[label].append(row["record_root"])
                receipt = Path(row["record_root"]) / row["case_id"] / "execution-assessment.json"
                if receipt.is_file():
                    assessments.append({"path": str(receipt), "sha256": digest(receipt)})
                    receipt_map[label][row["case_id"]] = str(receipt)
    return {"utc": now(), "model_runs": mapping, "execution_receipts": receipt_map, "execution_assessment_files": assessments}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["prepare", "finalize", "run"])
    parser.add_argument("--root", type=Path, default=DEFAULT_ROOT)
    parser.add_argument("--catalog", type=Path, default=REPO / "exercises/catalog.json")
    parser.add_argument("--release", type=Path)
    args = parser.parse_args()
    if args.action == "prepare":
        prepare(args.root, args.catalog)
    elif args.action == "finalize":
        finalize(args.root)
    else:
        if not args.release:
            parser.error("run requires an explicit root-authored release file")
        return run_queue(args.root, args.release)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
