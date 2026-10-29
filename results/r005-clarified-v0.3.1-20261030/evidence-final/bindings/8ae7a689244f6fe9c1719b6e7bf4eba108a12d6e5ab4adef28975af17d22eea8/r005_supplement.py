"""Single-case supplement orchestration; uses the unchanged shared runner/adapter.

No command creates preflight sessions or sends inference during import or inspect.
prepare requires a root-authored adoption gate after the original archive/replay.
run requires a second root-authored release bound to the new freeze.
"""
import argparse
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
sys.dont_write_bytecode = True
sys.path.insert(0, str(REPO / "scripts/benchmark"))
sys.path.insert(0, str(HERE))
from common import (Suite, candidate_message, code_identity, digest, load, now,
                    runner_fingerprint, save, text_digest, verify_release)
from isolation import prepare_session, open_probe
from preflight import network_probe
from run_comparison import snapshot_suite, finalize as shared_finalize, model_run_index
from math_gauge.execution import run as runner_run
from postprocess import audit_case
from replay_comparison import verified_archive

CASE = "MG-R005"
VERSION = "0.3.1"
MODELS = {"terra": ("gpt-6.1-terra", "max"),
          "gemini": ("gemini-3.8-flash-high", "high")}
DEFAULT_ROOT = Path("/private/tmp/math-gauge-r005-clarified-20261030")
ORIGINAL_FREEZE = "df6ae5742b9609cb634eba026f478614b39207743b205c7465d62a14d1f23d73"


def bound(path):
    path = Path(path).resolve()
    return {"path": str(path), "sha256": digest(path)}


def single_catalog(path):
    """Select one case from an existing multi-case suite; no source duplication."""
    data = load(path)
    if (data.get("schema") != "math-gauge.exercise-catalog/v1"
            or data.get("snapshot_status") != "final-catalog-snapshot"
            or len(data.get("suites", [])) != 1
            or len(data.get("case_entries", [])) != 1):
        raise ValueError("An independent finalized one-case catalog is required")
    row, entry = data["suites"][0], data["case_entries"][0]
    if row.get("cases") != [CASE] or entry.get("case_id") != CASE:
        raise ValueError("Supplement selects exactly MG-R005")
    root = (REPO / row["root"]).resolve()
    if not root.is_relative_to(REPO):
        raise ValueError("Suite must belong to this repository")
    suite = Suite.load(root)
    case = suite.select([CASE])[0]
    if (suite.sha256 != row["suite_sha256"] or entry.get("suite_sha256") != suite.sha256
            or case["version"] != VERSION or entry.get("version") != VERSION
            or entry.get("task_kind") != "written"):
        raise ValueError("Revised case version, kind or suite fingerprint mismatch")
    return data, suite, entry


def prerequisites(gate_path, catalog_path, root):
    """Read only public/operator evidence; never read credential contents."""
    gate = load(gate_path)
    if (gate.get("schema") != "math-gauge.supplement-adoption/v1"
            or gate.get("released_by") != "/root"
            or gate.get("allow_session_preparation") is not True
            or gate.get("case_id") != CASE or gate.get("version") != VERSION
            or gate.get("catalog_sha256") != digest(catalog_path)
            or gate.get("new_mathematical_review_passed") is not True
            or gate.get("new_author_lean_validation_passed") is not True):
        raise ValueError("Root adoption and new-version review are required")
    for key in ("archive_manifest", "offline_verification", "original_comparison"):
        row = gate[key]
        if digest(row["path"]) != row["sha256"]:
            raise ValueError("Prerequisite evidence changed: " + key)
    archive = Path(gate["archive_manifest"]["path"]).resolve().parent
    manifest, _ = verified_archive(archive)
    old_root = Path(manifest["source_root"]).resolve()
    if (root == old_root or root.is_relative_to(old_root) or old_root.is_relative_to(root)
            or root == archive or root.is_relative_to(archive)):
        raise ValueError("Supplement must have a distinct new temporary root")
    if (digest(archive / "runtime/freeze.json") != ORIGINAL_FREEZE
            or manifest.get("global_integrity_passed") is not True
            or manifest.get("integrity_error_rows") != 0
            or manifest.get("unknown_request_count_rows") != 0
            or load(archive / "runtime/queue-final.json").get("completed") is not True):
        raise ValueError("Original 82-run archive is not complete and verified")
    replay = load(gate["offline_verification"]["path"])
    if (replay.get("schema") != "math-gauge.offline-comparison-check/v1"
            or replay.get("matched") is not True
            or replay.get("archive_manifest_sha256") != digest(archive / "manifest.json")
            or replay.get("reference_sha256") != gate["original_comparison"]["sha256"]
            or replay.get("freeze_sha256") != ORIGINAL_FREEZE
            or load(gate["original_comparison"]["path"]).get("complete") is not True):
        raise ValueError("Final original scores must survive offline replay")
    return gate, archive, old_root


def same_config(root, archive, old_root, model):
    current = load(root / "config" / (model + ".json"))
    previous = load(archive / "config" / (model + ".json"))
    if (current.get("model"), current.get("effort")) != MODELS[model]:
        raise ValueError("Model substitution or effort change is forbidden")
    for key in ("schema", "client", "model", "effort", "deny_read_roots",
                "credential_links", "print_timeout"):
        if current.get(key) != previous.get(key):
            raise ValueError("Original execution contract changed: " + key)
    new_id_path = Path(current["cli_identity"]).resolve()
    if not new_id_path.is_relative_to(root):
        raise ValueError("Fresh identity evidence must belong to the supplement")
    new_id = load(new_id_path)
    old_id = load(archive / Path(previous["cli_identity"]).relative_to(old_root))
    for key in ("client", "sha256", "version"):
        if new_id[key] != old_id[key]:
            raise ValueError("CLI identity changed; explicit redesign required")
    if digest(new_id["resolved_binary"]) != new_id["sha256"]:
        raise ValueError("Inspected executable bytes changed")
    def exceptions(config, binary):
        return [{**x, "path": "<pinned-cli>" if x["path"] == binary else x["path"]}
                for x in config["read_exceptions"]]
    if exceptions(current, new_id["resolved_binary"]) != exceptions(previous, old_id["resolved_binary"]):
        raise ValueError("Read exceptions changed beyond pinned binary relocation")
    if any(x not in current["probes"] for x in previous["probes"]):
        raise ValueError("Original negative probes must remain")
    old_proxy, proxy = previous.get("proxy_exception"), current.get("proxy_exception")
    if bool(old_proxy) != bool(proxy) or (proxy and proxy.get("endpoint") != "127.0.0.1:7897"):
        raise ValueError("Proxy exception scope changed")
    if proxy:
        if not proxy.get("evidence"):
            raise ValueError("Refreshed proxy evidence is missing")
        for item in proxy["evidence"]:
            if not Path(item["path"]).resolve().is_relative_to(root) or digest(item["path"]) != item["sha256"]:
                raise ValueError("Proxy evidence is not fresh and bound")
    return current


def prepare(root, catalog_path, gate_path):
    root = Path(root).resolve()
    if not root.is_relative_to(Path("/private/tmp")) or root == Path("/private/tmp"):
        raise ValueError("Use a dedicated /private/tmp supplement directory")
    if any((root / name).exists() for name in ("sessions", "records", "frozen-suites", "runtime/snapshot-plan.json", "runtime/freeze.json")):
        raise ValueError("Supplement preparation is single-use; retain failed attempts")
    gate, archive, old_root = prerequisites(gate_path, catalog_path, root)
    _, suite, entry = single_catalog(catalog_path)
    configs = {m: same_config(root, archive, old_root, m) for m in MODELS}
    qualification_path = root / "preflight/qualification.json"
    qualification = load(qualification_path)
    if qualification.get("passed") is not True or qualification.get("mathematical_requests") != 0:
        raise ValueError("Fresh preflight with zero mathematical requests is required")
    required_bindings = {str((root / "config" / (m + ".json")).resolve()) for m in MODELS}
    required_bindings |= {str(Path(configs[m]["cli_identity"]).resolve()) for m in MODELS}
    required_bindings |= {str((root / "preflight" / (m + "-model-inventory.json")).resolve()) for m in MODELS}
    if not required_bindings.issubset({str(Path(x["path"]).resolve()) for x in qualification["bindings"]}):
        raise ValueError("Fresh configuration, identity and inventory must be bound by preflight")
    for item in qualification["bindings"]:
        if digest(item["path"]) != item["sha256"]:
            raise ValueError("Preflight binding changed")
    runtime = root / "runtime"
    runtime.mkdir(parents=True, exist_ok=True)
    catalog_copy = runtime / "catalog.frozen.json"
    with catalog_copy.open("xb") as stream:
        stream.write(Path(catalog_path).read_bytes())
    catalog_copy.chmod(0o444)
    frozen = snapshot_suite(suite, root / "frozen-suites/public")
    case = frozen.cases[CASE]
    request = frozen.request(case)
    message = candidate_message(request)
    payload = root / "payloads" / (CASE + ".md")
    payload.parent.mkdir(parents=True, exist_ok=True)
    with payload.open("xb") as stream:
        stream.write(message.encode("utf-8"))
    payload.chmod(0o444)
    sessions = {}
    for model in MODELS:
        session = root / "sessions" / model / CASE
        session.parent.mkdir(parents=True, exist_ok=True)
        prepare_session(configs[model], payload, session)
        open_probe(session)
        network_probe(session)
        sessions[model] = str(session)
    bindings = [*qualification["bindings"], bound(qualification_path), bound(gate_path),
                bound(__file__), bound(HERE / "postprocess.py"), bound(HERE / "replay_comparison.py"),
                bound(HERE / "supplement_preflight.py"), bound(HERE / "supplement_archive.py"),
                bound(HERE / "supplement_replay.py")]
    bindings += [gate[k] for k in ("archive_manifest", "offline_verification", "original_comparison")]
    bindings += [bound(root / "config" / (m + ".json")) for m in MODELS]
    item = {"case_id": CASE, "version": VERSION, "task_kind": "written",
            "family_id": entry["family_id"], "section": entry["section"],
            "author_lean_coverage": entry["author_lean_coverage"],
            "suite_root": str(frozen.root), "suite_sha256": frozen.sha256,
            "request_sha256": text_digest(json.dumps(request, ensure_ascii=False, sort_keys=True)),
            "candidate_message_sha256": text_digest(message),
            "candidate_message_bytes": len(message.encode("utf-8")),
            "attachment_names": [x["name"] for x in request["files"]], "sessions": sessions}
    plan = {"schema": "math-gauge.comparison-freeze/v1", "experiment": "r005-clarified-supplement",
            "utc": now(), "catalog_path": str(catalog_copy), "catalog_original_path": str(Path(catalog_path).resolve()),
            "catalog_sha256": digest(catalog_copy), "runtime_root": str(root),
            "runner_sha256": runner_fingerprint(), "code_identity": code_identity(),
            "preflight_bindings": bindings,
            "suite_snapshots": [{"root": str(frozen.root), "original_root": str(suite.root), "suite_sha256": frozen.sha256}],
            "cases": [item], "model_order": list(MODELS), "parallel_per_model": 2,
            "effective_parallel_per_model": 1, "timeout_seconds": 2700,
            "automatic_retry": False, "mathematical_requests": 0, "planned_mathematical_requests": 2,
            "original_freeze_sha256": ORIGINAL_FREEZE,
            "supplement_script_sha256": digest(__file__), "adoption_gate": bound(gate_path)}
    save(runtime / "snapshot-plan.json", plan, exclusive=True)
    return {"status": "prepared-not-released", "case_count": 1, "mathematical_requests": 0}


def check_plan(freeze):
    if (freeze.get("experiment") != "r005-clarified-supplement"
            or [(x["case_id"], x["version"]) for x in freeze["cases"]] != [(CASE, VERSION)]
            or freeze.get("model_order") != list(MODELS)
            or freeze.get("timeout_seconds") != 2700 or freeze.get("automatic_retry") is not False
            or freeze.get("planned_mathematical_requests") != 2
            or freeze.get("supplement_script_sha256") != digest(__file__)):
        raise ValueError("Supplement plan or script identity changed")


def run_queue(root, release):
    root, release = Path(root).resolve(), Path(release).resolve()
    runtime = root / "runtime"
    freeze = verify_release(runtime, release)
    check_plan(freeze)
    if (release.parent != runtime or load(release).get("experiment") != freeze["experiment"]
            or load(release).get("planned_mathematical_requests") != 2):
        raise ValueError("A separate root release for exactly two requests is required")
    item = freeze["cases"][0]
    for model in MODELS:
        session = Path(item["sessions"][model])
        if (not session.is_relative_to(root / "sessions")
                or load(session / "runtime/attempt-ledger.json")["attempts"]
                or (session / "runtime/execution.json").exists()
                or (root / "records" / model / CASE).exists()):
            raise ValueError("Each model needs a fresh unattempted session; no resume/retry")
    save(runtime / "queue-start.json", {"started_utc": now(), "release": bound(release),
         "release_path": str(release), "release_sha256": digest(release),
         "freeze_sha256": digest(runtime / "freeze.json"),
         "freeze": bound(runtime / "freeze.json"), "model_order": list(MODELS),
         "case_count": 1, "planned_mathematical_requests": 2}, exclusive=True)
    def emit(event):
        event = {"utc": now(), **event}
        with (runtime / "progress.ndjson").open("a", encoding="utf-8") as stream:
            stream.write(json.dumps(event, ensure_ascii=False) + "\n")
        print(json.dumps(event, ensure_ascii=False), flush=True)

    results, stopped = [], False
    for model in MODELS:
        destination = root / "records" / model / CASE
        if stopped:
            session = Path(item["sessions"][model])
            untouched = (not load(session / "runtime/attempt-ledger.json")["attempts"]
                         and not (session / "runtime/execution.json").exists() and not destination.exists())
            row = {"model": model, "case_id": CASE, "status": "not-started-after-operational-failure" if untouched else "unaccounted-external-attempt",
                   "request_count": 0 if untouched else None,
                   "basis": "not invoked and terminal empty ledger checked" if untouched else "missing-or-conflicting-evidence"}
        else:
            emit({"model": model, "status": "model-phase-started"})
            emit({"model": model, "case_id": CASE, "status": "starting", "record_root": str(destination)})
            row = {"model": model, "case_id": CASE, "record_root": str(destination), "request_count": None}
            try:
                verify_release(runtime, release)
                config = load(root / "config" / (model + ".json"))
                if (config["model"], config["effort"]) != MODELS[model]:
                    raise ValueError("Requested identity changed")
                command = [sys.executable, "-B", str(REPO / "scripts/benchmark/cli_adapter.py"),
                           "--runtime", str(runtime), "--release", str(release), "--model", model, "--case", CASE]
                metadata = runner_run(Suite.load(item["suite_root"]), destination,
                    ids=[CASE], command=command, model="/".join(MODELS[model]), timeout=2790)
                integrity = audit_case(root, item, model, {"status": "completed"})
                save(runtime / (model + "-execution-audit.json"), integrity, exclusive=True)
                row.update(request_count=integrity["request_count"],
                           status="completed" if metadata["execution_failures"] == 0 and integrity["valid_execution"] else "failed",
                           integrity_audit=str(runtime / (model + "-execution-audit.json")))
                stopped = row["status"] != "completed"
            except BaseException as error:
                stopped = True
                row.update(status="launcher-failed", error=type(error).__name__ + ": " + str(error))
                evidence = Path(item["sessions"][model]) / "runtime/execution.json"
                if evidence.is_file():
                    count = load(evidence).get("request_count")
                    if type(count) is int and count in (0, 1):
                        row["request_count"] = count
        row["utc"] = now()
        results.append(row)
        emit(row)
        if row["status"] == "completed":
            emit({"model": model, "status": "model-phase-completed"})
        save(runtime / "queue-status.json", {"halt_new_starts": stopped, "results": results})
        save(runtime / "model-runs.json", model_run_index(root, results))
    save(runtime / "queue-final.json", {"finished_utc": now(),
         "completed": len(results) == len(MODELS) and all(x["status"] == "completed" for x in results),
         "halt_new_starts": stopped, "results": results, "planned_cases": 1,
         "planned_mathematical_requests": 2, "mathematical_scoring_performed": False}, exclusive=True)
    return int(stopped)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["inspect", "prepare", "finalize", "run"])
    parser.add_argument("--root", type=Path, default=DEFAULT_ROOT)
    parser.add_argument("--catalog", type=Path)
    parser.add_argument("--adoption-gate", type=Path)
    parser.add_argument("--release", type=Path)
    args = parser.parse_args()
    if args.action in ("inspect", "prepare") and not args.catalog:
        parser.error("inspect/prepare require the independent one-case catalog")
    if args.action == "inspect":
        _, suite, entry = single_catalog(args.catalog)
        print(json.dumps({"case": CASE, "version": VERSION, "suite_sha256": suite.sha256,
                          "selected_cases": 1, "available_suite_cases": len(suite.cases), "model_requests": 0}))
    elif args.action == "prepare":
        if not args.adoption_gate:
            parser.error("prepare requires root's adoption gate after original archive/replay")
        print(json.dumps(prepare(args.root, args.catalog, args.adoption_gate)))
    elif args.action == "finalize":
        check_plan(load(args.root / "runtime/snapshot-plan.json"))
        shared_finalize(args.root)
    else:
        if not args.release:
            parser.error("run requires a separate root-authored release")
        return run_queue(args.root, args.release)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
