"""Shared runner adapter: validate frozen projection, execute one isolated CLI."""

import argparse
import json
import sys
from pathlib import Path

from common import candidate_message, digest, helper, load, now, save, text_digest, verify_release
from isolation import execute_session


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runtime", required=True, type=Path)
    parser.add_argument("--release", required=True, type=Path)
    parser.add_argument("--model", required=True, choices=["terra", "gemini"])
    parser.add_argument("--case", required=True)
    args = parser.parse_args()
    freeze = verify_release(args.runtime, args.release)
    item = next(row for row in freeze["cases"] if row["case_id"] == args.case)
    request = json.load(sys.stdin)
    request_sha = text_digest(json.dumps(request, ensure_ascii=False, sort_keys=True))
    if request_sha != item["request_sha256"]:
        raise ValueError("Shared runner request differs from frozen projection")
    payload = candidate_message(request)
    if text_digest(payload) != item["candidate_message_sha256"]:
        raise ValueError("Neutral candidate message differs from frozen payload")
    session = Path(item["sessions"][args.model])
    if digest(session / "input/task.md") != item["candidate_message_sha256"]:
        raise ValueError("CLI input differs from candidate payload")
    metadata = load(Path.cwd().parent.parent / "run.json")
    plan = load(session / "runtime/plan.json")
    expected_label = plan["model"] + "/" + plan["effort"]
    if not isinstance(metadata.get("run_id"), str) or not metadata["run_id"] or metadata.get("model_label") != expected_label:
        raise ValueError("Shared runner identity is missing or belongs to a different model")
    response, failure = "", None
    try:
        response, execution = execute_session(session, kind="math", timeout=freeze["timeout_seconds"])
    except BaseException as error:
        failure = error
    finally:
        evidence_path = session / "runtime/execution.json"
        execution = load(evidence_path) if evidence_path.is_file() else {}
        audit = helper.audit(session)
        valid = failure is None and execution.get("status") == "completed" and execution.get("request_count") == 1 and audit["artifact_checks_passed"] and not audit["credential_links_remaining"] and len(execution.get("workers", [])) > 0 and execution.get("tool_mismatch") is None
        assessment = {"schema": "math-gauge.execution-assessment/v1", "case_id": args.case, "utc": now(), "response_sha256": text_digest(response), "request_sha256": request_sha, "candidate_message_sha256": text_digest(payload), "mathematical_request_count": execution.get("request_count", 0), "valid_for_comparison": bool(valid), "outcome": "completed" if valid else "operational-failure-or-insufficient-evidence", "requested_model": execution.get("requested_model"), "requested_effort": execution.get("requested_effort"), "observed_model": execution.get("observed_model"), "observed_effort": execution.get("observed_effort"), "evidence": {"execution_path": str(evidence_path), "execution_sha256": digest(evidence_path) if evidence_path.is_file() else None, "raw_artifacts": execution.get("artifact_hashes", {}), "local_audit": audit, "proxy_exception": load(session / "runtime/plan.json").get("proxy_exception"), "preflight_bindings": freeze["preflight_bindings"], "limits": ["Fresh-session OS process policy and effective tool events checked; backend identity may be unobserved", "No mathematical scoring is performed by this receipt"]}}
        assessment.update(run_id=metadata["run_id"], model_label=expected_label)
        save(Path.cwd().parent / "execution-assessment.json", assessment, exclusive=True)
    if failure:
        raise failure
    if not valid:
        raise RuntimeError("Execution qualification failed")
    sys.stdout.buffer.write(response.encode("utf-8")); sys.stdout.buffer.flush()


if __name__ == "__main__":
    try:
        main()
    except BaseException as error:
        print(type(error).__name__ + ": " + str(error), file=sys.stderr)
        raise SystemExit(1)
