"""Synthetic external-source contracts only; no candidate client is executed.

The reusable helper builds an offline command-origin seam with raw source files
and explicitly synthetic human-shaped audit data in a temporary directory.
These records test software gates; they are never benchmark results/approvals.
"""

import copy
import json
from datetime import datetime, timedelta
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

from math_gauge.benchmarks import BenchmarkProfile, build_plan, identity, select_slots
from math_gauge.catalog import Suite, digest_bytes, read_json, write_json
from math_gauge.eligibility import (AUDIT_CHECKS, AUDIT_SOURCE_KINDS, REQUIREMENTS, copy_execution_eligibility,
                                  execution_eligibility_templates, import_execution_eligibility,
                                  verify_execution_eligibility)
from math_gauge.reliability import execute_reliability_run, inspect_reliability_run, _slot_path

ROOT = Path(__file__).resolve().parents[1]


def frozen_requirements():
    return {"schema": REQUIREMENTS, "allowed_tools": [], "internal_tools": ["finish"],
            "denied_categories": ["reference", "history", "prior_run", "memory", "global_config"],
            "read_exceptions": [], "tool_control_tool": "search_web"}


def synthetic_run(destination, *, replay=False, result=None, requirements=None, targets=None, reuse_runs=None):
    """Patch the transport seam so command-origin testing performs zero calls."""
    suite = Suite.load(ROOT / "cases")
    profile = BenchmarkProfile.load(ROOT / "protocol/benchmark-profile.json", suite)
    plan = build_plan(profile, suite, ["neutral"], runtime={
        "model_label": "SYNTHETIC OFFLINE SOFTWARE TEST", "adapter_identity": "synthetic-never-executed",
        "candidate_parameters": {"model": "synthetic-model", "reasoning_effort": "max"},
        "budget": {"timeout_seconds": 2, "output_tokens": 1000},
        "execution_requirements": requirements if requirements is not None else frozen_requirements()})

    def transport(command, projected, workspace, timeout, **kwargs):
        text = "synthetic response\r\n" if len(projected["messages"]) == 1 else "KEEP\r\nsynthetic rationale\r\n"
        return result(projected) if callable(result) else result or {
            "stdout": text, "stderr": b"", "status": "ok", "exit_code": 0, "usage": {"total_tokens": 1}}

    with patch("math_gauge.reliability.invoke_conversation", side_effect=transport), \
         patch("subprocess.Popen", side_effect=AssertionError("offline test cannot launch a client")):
        if replay:
            replies = {s["slot_id"]: "synthetic replay" if s["kind"] == "independent" else "KEEP\nsynthetic"
                       for s in select_slots(plan, targets)}
            execute_reliability_run(plan, suite, destination, replay=replies, targets=targets, reuse_runs=reuse_runs)
        else:
            execute_reliability_run(plan, suite, destination, command=["synthetic-never-executed"],
                                    targets=targets, reuse_runs=reuse_runs)
    return inspect_reliability_run(destination)


def synthetic_submission(run, sid, destination, *, session_mode="stateful"):
    """Construct independently re-openable source bytes for acceptance mutation."""
    destination = Path(destination)
    destination.mkdir(parents=True)
    meta, records = inspect_reliability_run(run)
    record = records[sid]
    template = next(x for x in execution_eligibility_templates(run)["slots"] if x["slot_id"] == sid)
    projected = read_json(Path(run) / _slot_path(sid) / "projected-request.json")
    requirements = meta["plan"]["runtime"]["execution_requirements"]
    artifacts = []

    def artifact(name, value, kind, origin="client", *, binary=False):
        data = value if binary else json.dumps(value, ensure_ascii=False, indent=2).encode()
        path = destination / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
        artifacts.append({"path": name, "bytes": len(data), "sha256": digest_bytes(data), "kind": kind, "origin": origin})
        return {"artifact": name} if binary else {"artifact": name, "pointer": ""}

    def field(reference, key):
        return dict(reference, pointer="/" + key)

    policy = artifact("raw/policy.sb", b"synthetic offline policy bytes; not an applied OS sandbox\n", "policy", "os", binary=True)
    earliest = datetime.fromisoformat(record["attempts"][0]["started_at"])
    controls = {}
    for enabled in (False, True):
        condition = "enabled" if enabled else "denied"
        controls[condition] = artifact("raw/control-" + condition + ".json", {
            "prompt_sha256": digest_bytes(b"SYNTHETIC NON-MATH CONTROL"), "tool": requirements["tool_control_tool"],
            "effective_tools": requirements["allowed_tools"] + ([requirements["tool_control_tool"]] if enabled else []),
            "result": "succeeded" if enabled else "denied", "request_id": sid + "-control-" + condition,
            "finished_at": (earliest - timedelta(seconds=1)).isoformat(),
            "fixture_notice": "Synthetic capability records, not real tool calls."}, "tool-control")
    observation_rows = []
    for attempt in record["attempts"]:
        number = attempt["number"]
        prefix = f"raw/attempt-{number}"
        request_id = record["evidence_id"] + "-" + str(number)
        session_id = "synthetic-session-" + request_id if session_mode == "stateful" else None
        request = artifact(prefix + "-request.json", {"request_id": request_id, **projected}, "provider-request", "request")
        metadata = artifact(prefix + "-metadata.json", {
            "request_id": request_id, "provider": "synthetic-provider", "model": projected["parameters"]["model"],
            "reasoning_effort": projected["parameters"].get("reasoning_effort"), "parameters": projected["parameters"],
            "fixture_notice": "Synthetic provider-shaped metadata; no real provider response."}, "provider-metadata", "provider-return")
        response = artifact(prefix + "-response.json", {"request_id": request_id,
            "text": (Path(run) / attempt["response_path"]).read_bytes().decode()}, "provider-response", "provider-return")
        error = artifact(prefix + "-stderr.txt", (Path(run) / _slot_path(sid) / "attempts" / str(number) / "stderr.txt").read_bytes(), "stderr", binary=True)
        events = artifact(prefix + "-events.ndjson", (json.dumps({"fixture_only": True, "request_id": request_id,
            "effective_tools": [{"name": tool, "classification": category, "permission": "allowed"}
                                for category, tools in (("candidate", requirements["allowed_tools"]),
                                                        ("internal", requirements["internal_tools"])) for tool in tools],
            "tool_calls": []}) + "\n").encode(), "cli-events", binary=True)
        start, finish = (datetime.fromisoformat(attempt[key]) for key in ("started_at", "finished_at"))
        # Client observations can share a timestamp; runner owns their interval.
        invocation_value = {"argv": meta["command"], "request_id": request_id,
            "request_sha256": record["projected_request_sha256"], "response_sha256": attempt["response_sha256"],
            "stderr_sha256": attempt["stderr_sha256"], "events_sha256": artifacts[-1]["sha256"],
            "request_count": 1, "transport_status": attempt["status"], "exit_code": attempt.get("exit_code"),
            "timeout_seconds": meta["timeout_seconds"], "started_at": start.isoformat(),
            "submitted_at": start.isoformat(), "finished_at": finish.isoformat(),
            "deadline_at": (start + timedelta(seconds=meta["timeout_seconds"])).isoformat(),
            "session_mode": session_mode, "session_id": session_id, "parent_pid": 1000 + number}
        invocation = artifact(prefix + "-invocation.json", invocation_value, "invocation")
        context = artifact(prefix + "-context.json", {"session_id": session_id, "session_mode": session_mode,
            "supplied_messages_complete": True, "hidden_session": False, "fresh": True, "resumed_from": None,
            "history_sha256": record["history_sha256"], "messages": projected["messages"],
            "ancestors": template["binding"]["ancestors"],
            "excluded_context": ["prior_answers", "peer_branches", "review_material", "memory"]}, "context")
        negatives = [{"category": "reference", "path": str(Path(run) / meta["inputs"][record["case_id"]][key]["path"]),
                      "sha256_before_run": meta["inputs"][record["case_id"]][key]["sha256"], "exists_before_run": True}
                     for key in ("reference", "rubric")]
        negatives += [{"category": category, "path": "/synthetic-protected/" + category,
                       "exists_before_run": True} for category in requirements["denied_categories"] if category != "reference"]
        manifest = {"positive": "/synthetic-input/" + request_id + ".json",
                    "sha256": digest_bytes(json.dumps(projected, ensure_ascii=False).encode()), "negative": negatives}
        paths = [manifest["positive"]] + [x["path"] for x in negatives]

        def checks(role=None, pid=None):
            return {"kind": "actual-file-open" if role is None else "live-pid-policy-query", "role": role,
                    "pid": pid or 9000, "utc": start.isoformat(), "prompt_sha256": manifest["sha256"],
                    "passed": True, "checks": [{"path": path, "expected": "allowed" if i == 0 else "denied",
                        "passed": True, **({"outcome": "DENIED", "errno": 13} if role is None and i else {}),
                        **({"observed_sha256": manifest["sha256"]} if role is None and i == 0 else {}),
                        **({"result": 0 if i == 0 else 1} if role else {})} for i, path in enumerate(paths)]}

        parent, worker = invocation_value["parent_pid"], 2000 + number
        network = [artifact(prefix + "-network-" + role + ".json", {
            "kind": "live-pid-network-query", "role": role, "pid": pid, "utc": start.isoformat(),
            "target": target, "address": address, "port": port, "result": "denied", "result_code": 1},
            "network-probe", "os") for role, pid, target, address, port in (
                ("parent", parent, "localhost", "127.0.0.1", 9876), ("worker", worker, "internet", "example.invalid", 443))]
        isolation = artifact(prefix + "-isolation.json", {
            "policy": policy, "policy_sha256": next(x["sha256"] for x in artifacts if x["path"] == policy["artifact"]),
            "evaluator_root": str(Path(run)), "deny_roots": [str(Path(run)), "/synthetic-protected"],
            "read_exceptions": requirements["read_exceptions"], "probe_manifest": manifest, "open_probe": checks(),
            "processes": [{"role": role, "pid": pid, "ppid": ppid, "executable_sha256": digest_bytes(role.encode()),
                           "started_at": start.isoformat()} for role, pid, ppid in (("parent", parent, 1), ("worker", worker, parent))],
            "pid_checks": [checks("parent", parent), checks("worker", worker)],
            "policy_inheritance": {"parent_pid": parent, "worker_pids": [worker], "verified_at": start.isoformat()},
            "fresh_state": {"path": "/synthetic-state/" + request_id, "created_at": start.isoformat(),
                            "initial_entries": [], "resumed_from": None},
            "tools": {"effective_allowed": requirements["allowed_tools"], "internal": requirements["internal_tools"],
                      "calls": [], "controls": controls,
                      "registry": dict(events, pointer="/effective_tools", line=1),
                      "call_records": dict(events, pointer="/tool_calls", line=1)},
            "network_probes": network}, "isolation", "os")
        observation_rows.append({"number": number, "submission_state": "submitted",
            "request": {key: field(request, key) for key in ("messages", "parameters", "request_id")},
            "backend": {key: field(metadata, key) for key in ("provider", "model", "reasoning_effort", "parameters", "request_id")},
            "response": {key: field(response, key) for key in ("text", "request_id")},
            "stderr": error, "events": events, "invocation": invocation, "context": context, "isolation": isolation})
    origin_manifest = read_json(Path(run) / "run.json")
    manifest_ref = artifact("raw/origin-manifest.json", origin_manifest, "ledger")
    peers = [{"evidence_id": eid, "slot_id": item["slot_id"], "slot_record_sha256": item["slot_record_sha256"],
              "transport_attempts": item["transport_attempts"]}
             for eid, item in sorted(origin_manifest["budget_evidence"].items()) if eid != record["evidence_id"]]
    ledger = artifact("raw/ledger.json", {"origin_run_id": record["evidence_origin_run_id"],
        "origin_manifest": manifest_ref, "peer_provenance": peers,
        "attempts": [{"evidence_id": record["evidence_id"], "number": a["number"],
                     "request_sha256": record["projected_request_sha256"], "response_sha256": a["response_sha256"],
                     "stderr_sha256": a["stderr_sha256"], "status": a["status"], "request_count": 1}
                    for a in record["attempts"]], "other_activity": [
                        {"id": sid + "-controls", "kind": "non_math_canary", "request_count": 2,
                         "sources": list(controls.values())}]}, "ledger")
    template.update(artifacts=artifacts, observations={"attempts": observation_rows, "ledger": ledger})
    template["audit"] = {"reviewer": "SYNTHETIC HUMAN-SHAPED SOFTWARE FIXTURE", "reviewer_kind": "human",
        "reviewed_at": (datetime.fromisoformat(record["attempts"][-1]["finished_at"]) + timedelta(seconds=1)).isoformat(),
        "decision": "accept", "checks": {key: {"decision": "verified", "rationale":
            "Synthetic offline fixture exercises this gate; no human approval or live authenticity is claimed.",
            "sources": [{"artifact": x["path"], "pointer": ""}
                        if x["kind"] not in {"policy", "cli-events"} else {"artifact": x["path"]}
                        for x in artifacts if x["kind"] in AUDIT_SOURCE_KINDS[key]]} for key in AUDIT_CHECKS}}
    path = destination / "submission.json"
    write_json(path, template)
    return path


def rewrite_source(submission_path, artifact_name, mutate):
    """Change raw source bytes and honestly refresh the explicit source manifest."""
    submission = read_json(submission_path)
    descriptor = next(x for x in submission["artifacts"] if x["path"] == artifact_name)
    path = Path(submission_path).parent / artifact_name
    value = read_json(path)
    mutate(value)
    write_json(path, value)
    raw = path.read_bytes()
    descriptor.update(bytes=len(raw), sha256=digest_bytes(raw))
    write_json(submission_path, submission)


class ExecutionEligibilityTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        self.run = self.root / "run"
        self.meta, self.records = synthetic_run(self.run)
        self.sid = next(iter(self.records))

    def submission(self, sid=None, name="sources", **kwargs):
        return synthetic_submission(self.run, sid or self.sid, self.root / name, **kwargs)

    def test_missing_forms_are_unapproved_and_old_runs_stay_provisional(self):
        forms = execution_eligibility_templates(self.run)
        self.assertEqual(forms["slots"][0]["audit"]["decision"], "unresolved")
        status = verify_execution_eligibility(self.run)
        self.assertIsNone(status["audit_snapshot"])
        self.assertFalse(status["slots"][self.sid]["eligible"])
        self.assertIn("execution_evidence_missing", status["reasons"])

    def test_complete_external_bytes_unlock_gate_and_tamper_is_detected(self):
        source = self.submission()
        imported = import_execution_eligibility(self.run, self.sid, source)
        self.assertTrue(imported["eligible"])
        selected = verify_execution_eligibility(self.run)["slots"][self.sid]
        self.assertTrue(selected["eligible"])
        self.assertEqual(selected["receipt_sha256"], imported["receipt_sha256"])
        # Source directory may disappear; the receipt carries all original bytes.
        shutil.rmtree(source.parent)
        self.assertTrue(verify_execution_eligibility(self.run)["slots"][self.sid]["eligible"])
        copied = self.run / Path(imported["receipt_path"]).parent / "artifacts/raw/attempt-1-metadata.json"
        copied.write_text("{}")
        with self.assertRaisesRegex(ValueError, "hash changed"):
            verify_execution_eligibility(self.run)

    def test_unknown_metadata_is_not_filled_from_request_or_label(self):
        source = self.submission()
        rewrite_source(source, "raw/attempt-1-metadata.json", lambda x: x.update(model=None))
        imported = import_execution_eligibility(self.run, self.sid, source)
        self.assertFalse(imported["eligible"])
        self.assertIn("attempt_1_backend_observation_unknown", imported["reasons"])

    def test_rejected_revision_retains_old_snapshot(self):
        source = self.submission()
        accepted = import_execution_eligibility(self.run, self.sid, source)
        submission = read_json(source)
        submission["audit"]["decision"] = "reject"
        submission["audit"]["checks"]["external_authenticity"].update(decision="rejected", rationale="Synthetic later withdrawal.")
        write_json(source, submission)
        with self.assertRaisesRegex(ValueError, "explicit revise"):
            import_execution_eligibility(self.run, self.sid, source)
        rejected = import_execution_eligibility(self.run, self.sid, source, revise=True,
                                               expected_snapshot=accepted["audit_snapshot"]["sha256"])
        self.assertFalse(rejected["eligible"])
        self.assertFalse(verify_execution_eligibility(self.run)["slots"][self.sid]["eligible"])
        historical = verify_execution_eligibility(self.run, audit_snapshot=accepted["audit_snapshot"]["sha256"])
        self.assertTrue(historical["slots"][self.sid]["eligible"])
        self.assertTrue(historical["audit_snapshot"]["historical"])

    def test_stateless_transport_does_not_invent_session_ids(self):
        source = self.submission(session_mode="stateless")
        self.assertTrue(import_execution_eligibility(self.run, self.sid, source)["eligible"])

    def test_fixture_origin_cannot_be_upgraded_by_a_human_shaped_audit(self):
        run = self.root / "replay"
        _, records = synthetic_run(run, replay=True)
        sid = next(iter(records))
        source = synthetic_submission(run, sid, self.root / "replay-sources")
        imported = import_execution_eligibility(run, sid, source)
        self.assertFalse(imported["eligible"])
        self.assertIn("execution_origin_not_command", imported["reasons"])

    def test_child_requires_every_original_ancestor_receipt(self):
        child = next(sid for sid in self.records if sid.endswith(":neutral:2"))
        source = self.submission(child, "child-sources")
        import_execution_eligibility(self.run, child, source)
        row = verify_execution_eligibility(self.run)["slots"][child]
        self.assertFalse(row["eligible"])
        self.assertIn("ancestor_execution_ineligible", row["reasons"])
        a1 = child.split(":")[0] + ":A1"
        r1 = child.rsplit(":", 1)[0] + ":1"
        for name, sid in (("a1", a1), ("r1", r1)):
            import_execution_eligibility(self.run, sid, self.submission(sid, name))
        self.assertTrue(verify_execution_eligibility(self.run)["slots"][child]["eligible"])

    def test_readable_timeout_can_have_sufficient_execution_evidence(self):
        run = self.root / "timeout"
        _, records = synthetic_run(run, result={"stdout": "synthetic readable timeout", "stderr": "timeout",
                                                "status": "timeout", "exit_code": -9, "usage": {}})
        sid = next(iter(records))
        source = synthetic_submission(run, sid, self.root / "timeout-sources")
        self.assertTrue(import_execution_eligibility(run, sid, source)["eligible"])

    def test_manifest_rejects_symlink_and_path_traversal(self):
        source = self.submission()
        raw = source.parent / "raw/attempt-1-metadata.json"
        original = raw.read_bytes()
        target = source.parent / "outside.json"
        target.write_bytes(original)
        raw.unlink()
        raw.symlink_to(target)
        with self.assertRaisesRegex(ValueError, "symlinks"):
            import_execution_eligibility(self.run, self.sid, source)
        raw.unlink()
        raw.write_bytes(original)
        submission = read_json(source)
        submission["artifacts"][0]["path"] = "../outside.json"
        write_json(source, submission)
        with self.assertRaisesRegex(ValueError, "Unsafe relative"):
            import_execution_eligibility(self.run, self.sid, source)

    def test_copied_receipt_keeps_original_audit_without_source_directory(self):
        imported = import_execution_eligibility(self.run, self.sid, self.submission())
        destination = self.root / "copied"
        destination.mkdir()
        copied = copy_execution_eligibility(self.run, destination, [self.records[self.sid]["evidence_id"]])
        self.assertIsNotNone(copied)
        self.assertEqual(read_json(destination / imported["receipt_path"])["receipt_sha256"], imported["receipt_sha256"])

    def test_all_retry_attempts_need_their_own_sources(self):
        counter = 0
        def retry(projected):
            nonlocal counter
            counter += 1
            failed = counter % 2 == 1
            return {"stdout": "" if failed else "synthetic readable retry", "stderr": "temporary" if failed else "",
                    "status": "transient_error" if failed else "ok", "exit_code": 75 if failed else 0, "usage": {}}
        run = self.root / "retry"
        _, records = synthetic_run(run, result=retry)
        sid = next(iter(records))
        self.assertEqual(len(records[sid]["attempts"]), 2)
        source = synthetic_submission(run, sid, self.root / "retry-sources")
        value = read_json(source)
        value["observations"]["attempts"][0]["backend"]["model"] = None
        write_json(source, value)
        imported = import_execution_eligibility(run, sid, source)
        self.assertFalse(imported["eligible"])
        self.assertIn("attempt_1_backend_model_unverified", imported["reasons"])

    def test_concurrent_writer_is_rejected_without_moving_audit_head(self):
        source = self.submission()
        lock = self.run / "eligibility/.write-lock"
        lock.mkdir(parents=True)
        with self.assertRaisesRegex(ValueError, "writer is already active"):
            import_execution_eligibility(self.run, self.sid, source)
        self.assertFalse((self.run / "eligibility/current.json").exists())
        lock.rmdir()
        self.assertTrue(import_execution_eligibility(self.run, self.sid, source)["eligible"])

    def test_reject_revision_archives_true_model_mismatch_and_revokes_current_gate(self):
        source = self.submission()
        accepted = import_execution_eligibility(self.run, self.sid, source)
        rewrite_source(source, "raw/attempt-1-metadata.json", lambda x: x.update(model="observed-wrong-model"))
        value = read_json(source)
        value["audit"]["decision"] = "reject"
        value["audit"]["checks"]["provider_metadata_origin"].update(
            decision="rejected", rationale="Corrected raw record exposes the wrong actual model; reject without altering it.")
        write_json(source, value)
        rejected = import_execution_eligibility(self.run, self.sid, source, revise=True,
                                               expected_snapshot=accepted["audit_snapshot"]["sha256"])
        self.assertFalse(rejected["eligible"])
        self.assertIn("execution_observation_rejected", rejected["reasons"])
        self.assertTrue(any("backend model" in x for x in rejected["observation_errors"]))
        self.assertFalse(verify_execution_eligibility(self.run)["slots"][self.sid]["eligible"])
        old = verify_execution_eligibility(self.run, audit_snapshot=accepted["audit_snapshot"]["sha256"])
        self.assertTrue(old["slots"][self.sid]["eligible"])
        # A rejection cannot hide a corrupt source pointer or mismatched bytes.
        value["observations"]["attempts"][0]["backend"]["model"]["pointer"] = "/nonexistent"
        write_json(source, value)
        with self.assertRaisesRegex(ValueError, "pointer is missing"):
            import_execution_eligibility(self.run, self.sid, source, revise=True,
                                         expected_snapshot=rejected["audit_snapshot"]["sha256"])

    def test_proven_unsubmitted_failure_needs_no_invented_provider_or_worker(self):
        counter = 0
        def retry(projected):
            nonlocal counter
            counter += 1
            failed = counter % 2 == 1
            return {"stdout": "" if failed else "synthetic final readable body", "stderr": "local startup failed" if failed else "",
                    "status": "transient_error" if failed else "ok", "exit_code": 75 if failed else 0, "usage": {}}
        run = self.root / "local-failure"
        _, records = synthetic_run(run, result=retry)
        sid = next(iter(records))
        source = synthetic_submission(run, sid, self.root / "local-failure-sources")
        rewrite_source(source, "raw/attempt-1-invocation.json", lambda x: x.update(
            request_count=0, submitted_at=None, request_id=None, parent_pid=None,
            session_mode="unstarted", session_id=None, failure_stage="startup", failure_reason="Recorded local startup failure before stdin submission."))
        rewrite_source(source, "raw/ledger.json", lambda x: x["attempts"][0].update(request_count=0))
        value = read_json(source)
        discarded = {x["path"] for x in value["artifacts"] if x["path"].startswith("raw/attempt-1-")
                     and x["kind"] not in {"invocation", "stderr", "cli-events"}}
        value["artifacts"] = [x for x in value["artifacts"] if x["path"] not in discarded]
        raw_name = "raw/attempt-1-client-output.txt"
        (source.parent / raw_name).write_bytes(b"")
        value["artifacts"].append({"path": raw_name, "bytes": 0, "sha256": digest_bytes(b""),
                                   "kind": "client-output", "origin": "client"})
        first = value["observations"]["attempts"][0]
        first.update(submission_state="not-submitted", request={key: None for key in first["request"]},
                     backend={key: None for key in first["backend"]}, context=None, isolation=None,
                     response={"text": {"artifact": raw_name}, "request_id": None})
        for check in value["audit"]["checks"].values():
            check["sources"] = [ref for ref in check["sources"] if ref["artifact"] not in discarded]
        write_json(source, value)
        admitted = import_execution_eligibility(run, sid, source)
        self.assertTrue(admitted["eligible"])
        self.assertEqual(len(admitted["observed_request_ids"]), 1)
        frozen = read_json(run / admitted["receipt_path"])["submission"]
        self.assertIsNone(frozen["observations"]["attempts"][0]["backend"]["model"])


if __name__ == "__main__":
    unittest.main()
