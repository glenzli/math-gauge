"""Operational evidence fixtures; no model calls or mathematical judgments."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from math_gauge.agy_evidence import SCHEMA, validate_delivery, validate_failure
from math_gauge.attempt_conditions import load_sources
from math_gauge.records import (descriptor, evidence_bytes, validate_native_delivery_failure,
                                load_manuscript_completion_inputs)


class AgyEvidenceTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.answer = self.put("answer.md", b"Original complete native return")
        candidate = self.put("task.md", b"SYNTHETIC TASK")
        request = self.put("request.ndjson", {"event": "user", "message": {"content": "SYNTHETIC TASK"}})
        self.terminal = {"event": "result", "result": {"status": "SUCCESS", "response": "Original complete native return"}}
        terminal = self.put("terminal.json", self.terminal)
        self.events = self.put("events.ndjson", (json.dumps(self.terminal) + "\n").encode())
        probe = dict(pid=101, passed=True, prompt_sha256=candidate["sha256"],
                     checks=[dict(expected="allowed", passed=True), dict(expected="denied", passed=True)])
        process = self.put("parent-probe.json", probe)
        self.execution = dict(kind="math", request_count=1, stdin_write_calls=1,
            stdin_bytes_written=request["bytes"], requested_model="argon", requested_effort="high",
            argv=["agy", "--sandbox"], cwd="/synthetic/work", permission_mode="proceed-in-sandbox",
            status="failed", exit_code=-9, tool_mismatch=None, tool_events=[], workers=[],
            parent_identity=dict(pid=101, policy_evidence="/original/parent-probe.json"),
            artifact_hashes={"input/task.md": candidate["sha256"], "output/events.ndjson": self.events["sha256"]})
        execution = self.put("execution.json", self.execution)
        plan = dict(client="agy", model="argon", effort="high", argv=self.execution["argv"], cwd=self.execution["cwd"],
            local_tool_policy="math-gauge.local-tools-no-search/v1", tool_network_access=False, search_allowed=False,
            expected_permission_mode="proceed-in-sandbox", stdin_sha256=request["sha256"], prompt_sha256=candidate["sha256"])
        settings = dict(enableTerminalSandbox=True, toolPermission="proceed-in-sandbox",
                        permissions=dict(allow=["command(*)"], deny=["read_url(*)", "execute_url(*)", "mcp(*)"]))
        control = dict(passed=True, mathematical_requests=0,
            execution=dict(kind="non_math_canary", requested_model="argon", requested_effort="high"),
            report=dict(all_denials_and_allows_passed=True, work_roundtrip=True, tool_network_denied=True, source_bytes_read=0))
        self.data = dict(schema=SCHEMA, case_id="S", phase="A1", post_observation=True, source_raw_bytes_rewritten=False,
            outcome="response_received", native_execution=execution, native_plan=self.put("plan.json", plan),
            candidate_input=candidate, native_request=request, native_events=self.events,
            native_terminal_event=terminal, response=self.answer,
            dispatch=self.put("dispatch.json", dict(case_id="S", outer_budget_seconds=10)),
            native_terminal_seal=self.put("seal.json", dict(native_status="SUCCESS", normal_complete_delivery=True,
                answer_sha256=self.answer["sha256"], raw_terminal_sha256=terminal["sha256"])),
            collection_qualification=self.put("qualification.json", dict(collection_status="qualified",
                answer_sha256=self.answer["sha256"], checks=dict(native_success=True, first_native_terminal_exact=True))),
            local_tools=dict(settings=self.put("settings.json", settings), native_control=self.put("control.json", control),
                open_probe=self.put("open-probe.json", probe), network_probe=self.put("network.json", dict(passed=True)),
                artifact_audit=self.put("audit.json", dict(artifact_checks_passed=True, credential_links_remaining=[])),
                process_checks=[dict(original_path="/original/parent-probe.json", pid=101, evidence=process)]))
        self.row = dict(id="S:A1", case_id="S", response=self.answer, review=None,
                        evaluation=dict(completion=dict(lower=0, upper=0, exact=0), strict_pass=False))
        self.save()

    def put(self, name, value):
        path = self.root / name
        path.write_bytes(value if isinstance(value, bytes) else (json.dumps(value) + "\n").encode())
        return descriptor(self.root, path)

    def save(self):
        self.row["agy_native_evidence"] = self.put("admission.json", self.data)

    def test_exact_native_success_survives_failed_cli_cleanup(self):
        result = validate_delivery(self.root, self.row, evidence_bytes)
        self.assertTrue(result["delivered"])
        self.assertEqual(result["cli_exit_code"], -9)
        self.row["response"] = self.put("different.md", b"Altered extraction")
        with self.assertRaises(ValueError):
            validate_delivery(self.root, self.row, evidence_bytes)

    def test_followup_or_different_input_cannot_enter_an_initial_answer(self):
        self.data["phase"] = "R1"
        self.save()
        with self.assertRaises(ValueError):
            validate_delivery(self.root, self.row, evidence_bytes)
        self.data["phase"] = "A1"
        self.save()
        self.row["source"] = dict(candidate_input=self.put("other-input.md", b"Other input"))
        with self.assertRaisesRegex(ValueError, "source selection"):
            validate_delivery(self.root, self.row, evidence_bytes)

    def test_retry_record_keeps_its_original_mathematical_phase(self):
        self.row["id"] = "S:A1:retry2"
        self.assertTrue(validate_delivery(self.root, self.row, evidence_bytes)["delivered"])
        self.row["id"] = "S:R1:retry2"
        with self.assertRaises(ValueError):
            validate_delivery(self.root, self.row, evidence_bytes)

    def test_error_or_additional_terminal_cannot_supply_a_success(self):
        for status, extra in [("ERROR", False), ("SUCCESS", True)]:
            with self.subTest(status=status, extra=extra):
                event = copy.deepcopy(self.terminal)
                event["result"]["status"] = status
                raw = (json.dumps(event) + "\n").encode() * (2 if extra else 1)
                self.data["native_events"] = self.put("events.ndjson", raw)
                self.execution["artifact_hashes"]["output/events.ndjson"] = self.data["native_events"]["sha256"]
                self.data["native_execution"] = self.put("execution.json", self.execution)
                self.data["native_terminal_event"] = self.put("terminal.json", event)
                self.save()
                with self.assertRaises(ValueError):
                    validate_delivery(self.root, self.row, evidence_bytes)

    def test_gcp_tools_require_actual_process_and_network_evidence(self):
        original = copy.deepcopy(self.data)
        for broken in ("network", "registered-process", "original-input"):
            with self.subTest(broken=broken):
                self.data = copy.deepcopy(original)
                if broken == "network":
                    self.data["local_tools"]["network_probe"] = self.put("network.json", dict(passed=False))
                elif broken == "registered-process":
                    self.data["local_tools"]["process_checks"] = []
                else:
                    self.data["candidate_input"] = self.put("different-task.md", b"A DIFFERENT TASK")
                self.save()
                with self.assertRaises(ValueError):
                    validate_delivery(self.root, self.row, evidence_bytes)
                self.put("network.json", dict(passed=True))

    def deadline(self):
        self.execution.update(elapsed_seconds=10.2, failure=dict(type="TimeoutError"))
        self.data["native_events"] = self.put("events.ndjson", b"")
        self.execution["artifact_hashes"]["output/events.ndjson"] = self.data["native_events"]["sha256"]
        self.data.update(outcome="delivery_failed", native_execution=self.put("execution.json", self.execution),
            mathematical_judgment="not_adjudicated", additional_mathematical_penalty=0,
            native_terminal_event=None, native_terminal_seal=None, response=None,
            no_native_terminal_seal=self.put("no-terminal.json", dict(reason=
                "Native process already stopped by execution session after deadline/failure; actual work sealed without editing")))
        self.row.update(response=None, review=None)
        self.save()
        self.row["delivery_failure"] = self.row["agy_native_evidence"]

    def test_deadline_without_terminal_is_operational_zero(self):
        self.deadline()
        self.assertEqual(validate_native_delivery_failure(self.root, self.row)["mathematical_judgment"], "not_adjudicated")
        self.execution["elapsed_seconds"] = 9
        self.data["native_execution"] = self.put("execution.json", self.execution)
        self.save(); self.row["delivery_failure"] = self.row["agy_native_evidence"]
        with self.assertRaisesRegex(ValueError, "actual fixed limit"):
            validate_failure(self.root, self.row, evidence_bytes)

    def test_delivered_terminal_cannot_be_hidden_as_a_deadline(self):
        self.deadline()
        self.data["native_events"] = self.put("events.ndjson", (json.dumps(self.terminal) + "\n").encode())
        self.execution["artifact_hashes"]["output/events.ndjson"] = self.data["native_events"]["sha256"]
        self.data["native_execution"] = self.put("execution.json", self.execution)
        self.save()
        with self.assertRaises(ValueError):
            validate_failure(self.root, self.row, evidence_bytes)

    def test_manuscript_failure_uses_agy_evidence_and_its_exact_task(self):
        self.deadline()
        policy = copy.deepcopy(json.loads((Path(__file__).resolve().parents[1]
            / "protocol/scoring-policy.json").read_bytes())["manuscript_completion"])
        policy.update(version="0.1.0", public_cases=0, public_case_ids=[], private_cases=1, families=1)
        task = self.data["candidate_input"]
        contract = self.put("manuscript-contract.json", dict(id="S", kind="research_exploration",
            dimensions=[dict(id="model", points=100)]))
        case = dict(case_id="S", family_id="synthetic-manuscript", component="manuscript-completion",
            source_visibility="private", contract_kind="research_exploration", task_kind="written",
            criteria=[dict(criterion_id="model", points=100)], total_weight=100,
            original_task=task, task_sha256=task["sha256"], contract=contract,
            contract_sha256=contract["sha256"], reference=self.put("reference.md", b"Synthetic reference."),
            source_rubric=self.put("manuscript-rubric.json", dict(task_sha256=task["sha256"],
                post_observation=True, criteria=[dict(id="model", points=100)])))
        self.row.update(slot_id="S:A1", attempt_label="A1", status="delivery_failed", points=0,
            complete=False, execution=self.data["native_execution"])
        inputs = dict(schema="math-gauge.manuscript-completion-inputs/v1", benchmark_version="0.6.0",
            model_label="Synthetic AGY", attempt_labels=["A1"], policy=policy, human_review="pending",
            formal_comparison_eligible=False, case_index=[case], slots=[self.row])
        def check():
            return load_manuscript_completion_inputs(self.root,
                dict(manuscript_completion_inputs=self.put("manuscript-inputs.json", inputs)))
        with patch("math_gauge.claude_code_evidence.validate_failure",
                   side_effect=AssertionError("Wrong native harness")):
            actual = check()["slots"][0]
            self.assertEqual(actual["points"], 0)
            self.assertIsNone(actual["review"])
            original = copy.deepcopy(case)
            other = self.put("other-manuscript-task.md", b"A different frozen question.")
            case.update(original_task=other, task_sha256=other["sha256"],
                source_rubric=self.put("other-manuscript-rubric.json", dict(task_sha256=other["sha256"],
                    post_observation=True, criteria=[dict(id="model", points=100)])))
            with self.assertRaisesRegex(ValueError, "exact task"):
                check()
            inputs["case_index"] = [original]
            self.data["native_events"] = self.put("events.ndjson", (json.dumps(self.terminal) + "\n").encode())
            self.execution["artifact_hashes"]["output/events.ndjson"] = self.data["native_events"]["sha256"]
            self.data["native_execution"] = self.put("execution.json", self.execution)
            self.save()
            self.row.update(execution=self.data["native_execution"],
                delivery_failure=self.row["agy_native_evidence"])
            with self.assertRaisesRegex(ValueError, "actual fixed limit"):
                check()

    def attempt_record(self):
        bundles = {}
        for condition, prefix in [("single_attempt", ""), ("nonlogical_retry_3", "retry-")]:
            slot = dict(slot_id="S:A1", case_id="S",
                        response_sha256=(self.row.get("response") or {}).get("sha256"),
                        delivery_status=self.row.get("delivery_status", "response_received"), **self.row["evaluation"])
            bundles[condition] = dict(scoring_inputs=self.put(prefix + "scoring-inputs.json", dict(
                plan={"synthetic_contract_fixture": True}, model_label="fixture", slots=[slot])),
                formalization_review=self.put(prefix + "formal.json", dict(cases=[])),
                alignment_review=self.put(prefix + "alignment.json", dict(rounds=[])),
                manuscript_completion_inputs=self.put(prefix + "manuscript.json", dict(slots=[])),
                source_records=self.put(prefix + "records.json", dict(records=[self.row])))
        manifest = dict(schema="math-gauge.attempt-condition-sources/v1",
            selection="first_normal_delivery_after_counted_operational_failures", conditions=bundles,
            human_review="pending", formal_comparison_eligible=False)
        record = dict(model=dict(requested_label="fixture"), formalization_evidence_location="public_archive",
            formalization_review=bundles["single_attempt"]["formalization_review"],
            manuscript_completion_inputs=bundles["single_attempt"]["manuscript_completion_inputs"],
            attempt_condition_sources=self.put("conditions.json", manifest))
        return record

    def test_attempt_bundles_validate_agy_without_claiming_claude_evidence(self):
        record = self.attempt_record()
        with patch("math_gauge.benchmarks.validate_plan", side_effect=lambda value: value), \
                patch("math_gauge.claude_code_evidence.validate_delivery", side_effect=AssertionError("Wrong harness")):
            selected = load_sources(self.root, record, "nonlogical_retry_3", public_root=self.root)
        self.assertEqual(selected["inputs"]["slots"][0]["response_sha256"], self.answer["sha256"])

    def test_unrun_attempt_has_unknown_credit_without_inventing_a_failure(self):
        self.row.update(response=None, delivery_status="not_run")
        self.row.pop("agy_native_evidence")
        self.row["evaluation"] = dict(completion=dict(lower=0, upper=1, exact=None), strict_pass=None)
        record = self.attempt_record()
        with patch("math_gauge.benchmarks.validate_plan", side_effect=lambda value: value), \
                patch("math_gauge.records.validate_native_delivery_failure", side_effect=AssertionError("No native request")):
            selected = load_sources(self.root, record, "nonlogical_retry_3", public_root=self.root)
        self.assertIsNone(selected["inputs"]["slots"][0]["completion"]["exact"])

    def test_missing_failure_evidence_cannot_be_disguised_as_unrun(self):
        self.row.update(response=None, delivery_status="delivery_failed")
        self.row.pop("agy_native_evidence")
        record = self.attempt_record()
        with patch("math_gauge.benchmarks.validate_plan", side_effect=lambda value: value):
            with self.assertRaisesRegex(ValueError, "native failure evidence"):
                load_sources(self.root, record, "nonlogical_retry_3", public_root=self.root)


if __name__ == "__main__":
    unittest.main()
