"""Claude Code evidence admission preserves transport and native/cleanup boundaries."""
import hashlib
import json
import tempfile
import unittest
from pathlib import Path

from math_gauge.claude_code_evidence import validate_delivery, validate_attempt_history
from math_gauge.records import evidence_bytes, _native_research_completed, _validate_research_tool_evidence


class ClaudeCodeEvidenceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def keep(self, name, value):
        raw = value if isinstance(value, bytes) else json.dumps(value).encode()
        path = self.root / name
        path.write_bytes(raw)
        return {"path": name, "bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest()}

    def fixture(self, *, exit_code=0, subtype="success", native_text="Full answer", late=False,
                offered=None, tool="Bash", network=None, extra_result=False, fresh=True):
        prompt, answer = b"Frozen question", b"Full answer"
        model, effort, session, cwd = "claude-opus-5-5[1m]", "max", "original-session", "/original/work"
        catalog = ["Bash", "Read", "Write", "Edit", "Glob", "Grep"]
        argv = ["tclaude", "-p", "--model", model, "--effort", effort, "--session-id", session,
                "--tools", ",".join(catalog), "--strict-mcp-config", "--disable-slash-commands",
                "--setting-sources", "user"]
        launch = {"argv": argv, "cwd": cwd, "session_id": session, "resume": not fresh,
                  "prompt_sha256": hashlib.sha256(prompt).hexdigest(), "prompt_bytes": len(prompt),
                  "timeout_seconds": 2700}
        terminal = {"type": "result", "subtype": subtype, "is_error": subtype != "success",
                    "result": native_text, "session_id": session, "stop_reason": "end_turn"}
        events = [{"type": "assistant", "message": {"content": [{"type": "tool_use", "name": tool}]}}, terminal]
        if extra_result:
            events.append(dict(terminal))
        stream = b"\n".join(json.dumps(e).encode() for e in events) + b"\n"
        metadata = {"init": {"tools": offered or catalog, "model": model, "cwd": cwd, "mcp_servers": [],
                    "skills": [], "slash_commands": [], "memory_paths": None}, "session_id": session,
                    "resume": not fresh, "process": {"exit_code": exit_code, "killed_after_result": exit_code == 130,
                    "result_before_deadline": not late, "timed_out": False}, "timeout_seconds": 2700,
                    "deadline_at": "2026-11-09T01:45:00+00:00", "status_derivation": {"status": "ok"},
                    "answer_extraction": {"result_text_sha256": hashlib.sha256(answer).hexdigest()}}
        settings = {"sandbox": {"enabled": True, "allowUnsandboxedCommands": False,
                    "network": {"strictAllowlist": True, "allowedDomains": network or []},
                    "filesystem": {"allowRead": [cwd], "denyRead": ["/original"]}},
                    "permissions": {"blockReadsOutsideWorkingDirectories": True, "deny": ["WebSearch", "WebFetch"]},
                    "hooks": {"PreToolUse": [{"matcher": "Write|Edit", "hooks": ["original guard"]}]},
                    "autoMemoryEnabled": False}
        sources = {"request": self.keep("request.json", {"parameters": {"model": model, "reasoning_effort": effort},
                    "messages": [{"role": "user", "content": prompt.decode()}]}),
                   "launch": self.keep("launch.json", launch), "metadata": self.keep("metadata.json", metadata),
                   "settings": self.keep("settings.json", settings), "events": self.keep("events.jsonl", stream),
                   "event_times": self.keep("times.jsonl", json.dumps({"end_offset": len(stream),
                    "seen_at": "2026-11-09T01:00:00+00:00"}).encode()),
                   "prompt": self.keep("prompt.txt", prompt), "answer": self.keep("response.md", answer)}
        evidence = self.keep("evidence.json", {"schema": "math-gauge.claude-code-native-evidence/v1",
            "post_observation": True, "source_raw_bytes_rewritten": False, "provider_identity_verified": False,
            "effective_sandbox_verified": False, "physical_request": 1, "effective_model_attempt": 1, "sources": sources})
        plan = self.keep("plan.json", {"schema": "math-gauge.claude-code-execution-plan-adapter/v1",
            "post_observation": True, "client": "claude-code", "native_launch": sources["launch"],
            "model": model, "effort": effort, "argv": argv, "cwd": cwd,
            "local_tool_policy": "math-gauge.local-tools-no-search/v1", "tool_network_access": False,
            "search_allowed": False})
        execution = self.keep("execution.json", {"schema": "math-gauge.claude-code-execution-observation-adapter/v1",
            "post_observation": True, "client": "claude-code", "kind": "math", "native_metadata": sources["metadata"],
            "request_count": 1, "tool_mismatch": None, "exit_code": exit_code, "argv": argv, "cwd": cwd,
            "requested_model": model, "requested_effort": effort})
        return {"external_harness_evidence": evidence, "response": sources["answer"],
                "original_input": sources["prompt"], "execution_plan": plan, "execution": execution,
                "native_tool_settings": sources["settings"], "execution_track": "math-gauge.local-tools-no-search/v1"}

    def test_original_success_with_failed_cli_cleanup_keeps_actual_cleanup(self):
        row = self.fixture(exit_code=130)
        result = validate_delivery(self.root, row, evidence_bytes)
        self.assertEqual(result["cli_exit_code"], 130)
        self.assertTrue(result["cli_killed_after_result"])
        self.assertFalse(result["provider_identity_verified"])
        self.assertFalse(result["effective_sandbox_verified"])
        execution = json.loads(evidence_bytes(self.root, row["execution"]))
        self.assertTrue(_native_research_completed(self.root, row, execution))
        _validate_research_tool_evidence(self.root, row, execution, {"local_tools_allowed": True})

    def test_readable_error_is_not_a_delivered_answer(self):
        with self.assertRaises(ValueError):
            validate_delivery(self.root, self.fixture(subtype="error"), evidence_bytes)

    def test_answer_must_equal_the_original_native_final(self):
        with self.assertRaises(ValueError):
            validate_delivery(self.root, self.fixture(native_text="Different final"), evidence_bytes)

    def test_success_after_deadline_is_rejected(self):
        with self.assertRaises(ValueError):
            validate_delivery(self.root, self.fixture(late=True), evidence_bytes)

    def test_declared_no_network_cannot_override_real_settings(self):
        with self.assertRaises(ValueError):
            validate_delivery(self.root, self.fixture(network=["example.com"]), evidence_bytes)

    def test_unoffered_tool_and_multiple_native_terminals_are_rejected(self):
        for kwargs in ({"tool": "WebFetch"}, {"extra_result": True}, {"fresh": False}):
            with self.subTest(kwargs=kwargs), self.assertRaises(ValueError):
                validate_delivery(self.root, self.fixture(**kwargs), evidence_bytes)

    def test_tampered_raw_bytes_fail_even_before_semantic_admission(self):
        row = self.fixture()
        (self.root / "events.jsonl").write_bytes(b"{}\n")
        with self.assertRaises(ValueError):
            validate_delivery(self.root, row, evidence_bytes)

    def counted_fixture(self, *, earlier_delivered=False, reuse_workspace=False):
        """Two physical invocations, retaining a genuine missing-final first."""
        row = self.fixture()
        data = json.loads(evidence_bytes(self.root, row["external_harness_evidence"]))
        sources = data["sources"]
        if not earlier_delivered:
            meta = json.loads(evidence_bytes(self.root, sources["metadata"]))
            meta["process"].update(timed_out=True, result_before_deadline=False)
            meta["status_derivation"]["status"] = "timeout"
            sources["metadata"] = self.keep("first-meta.json", meta)
            sources["answer"] = self.keep("first-answer.md", b"")
            sources["events"] = self.keep("first-events.jsonl", b"")
            sources["event_times"] = self.keep("first-times.jsonl", b"")
        first_sources = {k: self.keep("first-" + k, evidence_bytes(self.root, v))
                         for k, v in sources.items()}
        row = self.fixture()
        data = json.loads(evidence_bytes(self.root, row["external_harness_evidence"]))
        sources = data["sources"]
        if not reuse_workspace:
            # A second invocation must have a different native session and cwd.
            for name, key in (("launch", "launch"), ("metadata", "metadata"),
                              ("plan", "execution_plan"), ("execution", "execution")):
                descriptor = sources[key] if key in sources else row[key]
                raw = evidence_bytes(self.root, descriptor).decode()
                raw = raw.replace("original-session", "retry-session").replace("/original/work", "/retry/work")
                updated = self.keep(name + ".json", raw.encode())
                if key in sources:
                    sources[key] = updated
                else:
                    row[key] = updated
            settings = evidence_bytes(self.root, sources["settings"]).decode().replace("/original/work", "/retry/work")
            sources["settings"] = self.keep("settings.json", settings.encode())
            row["native_tool_settings"] = sources["settings"]
            stream = evidence_bytes(self.root, sources["events"]).replace(b"original-session", b"retry-session")
            sources["events"] = self.keep("events.jsonl", stream)
            sources["event_times"] = self.keep("times.jsonl", json.dumps({"end_offset": len(stream),
                "seen_at": "2026-11-09T01:00:00+00:00"}).encode())
            plan = json.loads(evidence_bytes(self.root, row["execution_plan"]))
            plan["native_launch"] = sources["launch"]
            row["execution_plan"] = self.keep("plan.json", plan)
            execution = json.loads(evidence_bytes(self.root, row["execution"]))
            execution["native_metadata"] = sources["metadata"]
            row["execution"] = self.keep("execution.json", execution)
        data.update(schema="math-gauge.claude-code-native-evidence/v2", physical_request=2,
                    effective_model_attempt=2, attempts=[
            dict(physical_request=1, effective_model_attempt=1, excluded_pure_system_failure=False,
                 outcome="delivered" if earlier_delivered else "timeout_no_final", sources=first_sources),
            dict(physical_request=2, effective_model_attempt=2, excluded_pure_system_failure=False,
                 outcome="delivered", sources=sources)])
        row["external_harness_evidence"] = self.keep("counted.json", data)
        return row, data

    def test_timeout_consumes_attempt_and_first_normal_delivery_is_selected(self):
        row, data = self.counted_fixture()
        self.assertTrue(validate_delivery(self.root, row, evidence_bytes)["delivered"])
        self.assertEqual(validate_attempt_history(self.root, data, evidence_bytes)["effective_model_attempt"], 2)
        data["attempts"][0]["excluded_pure_system_failure"] = True
        with self.assertRaises(ValueError):
            validate_attempt_history(self.root, data, evidence_bytes)

    def test_retry_cannot_inherit_workspace_or_follow_a_delivered_answer(self):
        for kwargs in ({"reuse_workspace": True}, {"earlier_delivered": True}):
            with self.subTest(kwargs=kwargs):
                row, _ = self.counted_fixture(**kwargs)
                with self.assertRaises(ValueError):
                    validate_delivery(self.root, row, evidence_bytes)

    def test_later_notification_cannot_replace_first_native_final(self):
        row = self.fixture()
        data = json.loads(evidence_bytes(self.root, row["external_harness_evidence"]))
        sources = data["sources"]
        events = [json.loads(line) for line in evidence_bytes(self.root, sources["events"]).splitlines()]
        later = dict(events[-1], result="Later notification rewrite")
        events.append(later)
        lines = [json.dumps(event).encode() + b"\n" for event in events]
        stream = b"".join(lines)
        sources["events"] = self.keep("events.jsonl", stream)
        sources["event_times"] = self.keep("times.jsonl", json.dumps({"end_offset": len(stream),
            "seen_at": "2026-11-09T01:00:00+00:00"}).encode())
        original_last = self.keep("original-exported-answer.md", later["result"].encode())
        metadata = json.loads(evidence_bytes(self.root, sources["metadata"]))
        metadata["answer_extraction"]["result_text_sha256"] = original_last["sha256"]
        sources["metadata"] = self.keep("metadata.json", metadata)
        execution = json.loads(evidence_bytes(self.root, row["execution"]))
        execution["native_metadata"] = sources["metadata"]
        row["execution"] = self.keep("execution.json", execution)
        data.update(schema="math-gauge.claude-code-native-evidence/v2", attempts=[dict(
            physical_request=1, effective_model_attempt=1, excluded_pure_system_failure=False,
            outcome="delivered", sources=sources)], first_terminal_selection=dict(
                first_terminal_event_index=1, first_terminal_end_offset=sum(map(len, lines[:2])),
                ignored_later_terminals=1, original_recorded_answer=original_last))
        row["external_harness_evidence"] = self.keep("evidence.json", data)
        self.assertEqual(validate_delivery(self.root, row, evidence_bytes)["text"], "Full answer")
        # Choosing the later native final must fail even with a source-bound
        # original export that happened to contain it.
        data["first_terminal_selection"]["first_terminal_event_index"] = 2
        row["external_harness_evidence"] = self.keep("evidence.json", data)
        with self.assertRaises(ValueError):
            validate_delivery(self.root, row, evidence_bytes)

    def observed_fixture(self, outcome):
        row = self.fixture(native_text="" if outcome == "empty_success_without_content" else "Full answer")
        data = json.loads(evidence_bytes(self.root, row["external_harness_evidence"]))
        sources = data["sources"]
        sources["answer"] = self.keep("response.md", b"")
        meta = json.loads(evidence_bytes(self.root, sources["metadata"]))
        if outcome != "empty_success_without_content":
            sources["events"] = self.keep("events.jsonl", b"")
            sources["event_times"] = self.keep("times.jsonl", b"")
            meta["process"].update(result_before_deadline=False, result_seen_at=None)
            meta.update(finished_at="2026-11-09T02:00:00+00:00")
            meta["status_derivation"]["status"] = "transient_error"
        sources["metadata"] = self.keep("metadata.json", meta)
        data.update(schema="math-gauge.claude-code-native-evidence/v3", attempts=[dict(
            physical_request=1, effective_model_attempt=1, excluded_pure_system_failure=False,
            outcome=outcome, sources=sources)])
        return data

    def test_empty_native_success_is_counted_zero_not_a_mathematical_delivery(self):
        data = self.observed_fixture("empty_success_without_content")
        self.assertFalse(validate_attempt_history(self.root, data, evidence_bytes)["delivered"])
        data["schema"] = "math-gauge.claude-code-native-evidence/v2"
        with self.assertRaises(ValueError):
            validate_attempt_history(self.root, data, evidence_bytes)

    def test_elapsed_deadline_zero_preserves_transient_status_and_rejects_early_stop(self):
        data = self.observed_fixture("observed_deadline_without_final")
        self.assertFalse(validate_attempt_history(self.root, data, evidence_bytes)["delivered"])
        meta = json.loads(evidence_bytes(self.root, data["sources"]["metadata"]))
        self.assertFalse(meta["process"]["timed_out"])
        meta["finished_at"] = "2026-11-09T01:30:00+00:00"
        data["sources"]["metadata"] = self.keep("metadata.json", meta)
        with self.assertRaises(ValueError):
            validate_attempt_history(self.root, data, evidence_bytes)

    def test_native_payload_extraction_retains_both_original_and_exact_final(self):
        row = self.fixture()
        data = json.loads(evidence_bytes(self.root, row["external_harness_evidence"]))
        sources = data["sources"]
        selected = sources["answer"]
        sources["answer"] = self.keep("collected.md", b"# Full answer")
        meta = json.loads(evidence_bytes(self.root, sources["metadata"]))
        meta["answer_extraction"]["recorded_response_sha256"] = sources["answer"]["sha256"]
        sources["metadata"] = self.keep("metadata.json", meta)
        execution = json.loads(evidence_bytes(self.root, row["execution"]))
        execution["native_metadata"] = sources["metadata"]
        row["execution"] = self.keep("execution.json", execution)
        data.update(schema="math-gauge.claude-code-native-evidence/v3", attempts=[dict(
            physical_request=1, effective_model_attempt=1, excluded_pure_system_failure=False,
            outcome="delivered", sources=sources)], native_payload_extraction=dict(
                first_terminal_event_index=1,
                first_terminal_end_offset=len(evidence_bytes(self.root, sources["events"])),
                original_recorded_answer=sources["answer"], selected_native_answer=selected))
        row["external_harness_evidence"] = self.keep("evidence.json", data)
        self.assertEqual(validate_delivery(self.root, row, evidence_bytes)["text"], "Full answer")
        data["native_payload_extraction"]["first_terminal_end_offset"] -= 1
        row["external_harness_evidence"] = self.keep("evidence.json", data)
        with self.assertRaises(ValueError):
            validate_delivery(self.root, row, evidence_bytes)

    def test_unclosed_snapshot_requires_user_adoption_and_cannot_hide_a_result(self):
        data = self.observed_fixture("observed_deadline_without_final")
        sources = {k: self.keep("unclosed-" + k, evidence_bytes(self.root, v))
                   for k, v in data["sources"].items() if k not in {"answer", "metadata"}}
        launch = json.loads(evidence_bytes(self.root, sources["launch"]))
        launch.update(cwd="/unclosed/work", session_id="unclosed-session")
        sources["launch"] = self.keep("unclosed-launch", launch)
        data.update(unclosed_requests=[dict(physical_request=2, effective_model_attempt=2,
            native_closure_observed=False, outcome="no_terminal_in_supplied_snapshot", sources=sources)],
            unclosed_snapshot_adoption=self.keep("adoption", dict(post_observation=True,
                source_raw_bytes_rewritten=False, no_delivered_answer_scores_zero=True)))
        self.assertFalse(validate_attempt_history(self.root, data, evidence_bytes)["delivered"])
        sources["events"] = self.keep("unclosed-events", b'{"type":"result","result":"late answer"}\n')
        with self.assertRaises(ValueError):
            validate_attempt_history(self.root, data, evidence_bytes)


if __name__ == "__main__":
    unittest.main()
