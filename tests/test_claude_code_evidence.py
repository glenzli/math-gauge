"""Claude Code evidence admission preserves transport and native/cleanup boundaries."""
import hashlib
import json
import tempfile
import unittest
from pathlib import Path

from math_gauge.claude_code_evidence import validate_delivery
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


if __name__ == "__main__":
    unittest.main()
