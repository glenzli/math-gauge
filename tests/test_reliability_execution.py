"""Offline conversation/material contracts. No candidate service or Lean calls."""

import copy
from contextlib import redirect_stderr, redirect_stdout
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

from math_gauge.benchmarks import BenchmarkProfile, build_plan, identity, select_slots
from math_gauge.catalog import Suite, candidate_message, read_json, write_json
from math_gauge.cli import main
from math_gauge.reliability import (compose_material, execute_reliability_run,
                                    inspect_reliability_run, _slot_path)

ROOT = Path(__file__).resolve().parents[1]


class ReliabilityExecutionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.suite = Suite.load(ROOT / "cases")
        cls.profile = BenchmarkProfile.load(ROOT / "protocol/benchmark-profile.json", cls.suite)

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def plan(self, targets=None, **runtime):
        settings = {"model_label": "offline-fixture", "adapter_identity": "test-reliability-v1",
                    "budget": {"timeout_seconds": 2, "output_tokens": 1000},
                    "fresh_context": True}
        settings.update(runtime)
        return build_plan(self.profile, self.suite, targets or ["all"], runtime=settings)

    def replies(self, plan, targets=None):
        return {s["slot_id"]: "initial fixture 原文\r\n" if s["kind"] == "independent" else "KEEP\r\n本轮核查。\r\n"
                for s in select_slots(plan, targets)}

    def execute(self, plan=None, replies=None, name="run", **kwargs):
        plan = plan or self.plan(["neutral"])
        destination = self.root / name
        if "adapter" not in kwargs and "command" not in kwargs:
            kwargs["replay"] = replies if replies is not None else self.replies(plan, kwargs.get("targets"))
        meta = execute_reliability_run(plan, self.suite, destination, **kwargs)
        return destination, meta

    def test_all_177_messages_are_projected_and_branch_isolated(self):
        seen = []
        def adapter(request):
            seen.append(copy.deepcopy(request))
            return f"independent-{len(seen)}\r\n" if len(request["messages"]) == 1 else "KEEP\r\nchecked\r\n"
        plan = self.plan()
        root, meta = self.execute(plan, adapter=adapter)
        _, records = inspect_reliability_run(root)
        self.assertEqual(len(seen), 177)
        self.assertEqual(len(records), 177)
        self.assertEqual(meta["candidate_calls"], 0)
        self.assertFalse(meta["fresh_context_verified"])
        self.assertTrue(meta["fresh_context_declared"])
        self.assertEqual(sum(len(p["messages"]) == 1 for p in seen), 129)
        slot_index = {s["slot_id"]: s for s in plan["slots"]}
        for slot, projected in zip(plan["slots"], seen):
            self.assertEqual(set(projected), {"schema", "messages", "parameters"})
            self.assertEqual(projected["parameters"], {"max_output_tokens": 1000})
            case = self.suite.cases[slot["case_id"]]
            self.assertEqual(projected["messages"][0]["content"], candidate_message(self.suite.request(case)))
            self.assertNotIn("expected_truth", json.dumps(projected))
            if slot["kind"] == "followup":
                self.assertEqual(len(projected["messages"]), 3 if slot["round"] == 1 else 5)
                a1 = records[f"{slot['case_id']}:A1"]
                self.assertEqual(projected["messages"][1]["content"].encode(), (root / a1["response_path"]).read_bytes())
                if slot["round"] == 2:
                    previous = records[slot["parent_slot"]]
                    self.assertEqual(projected["messages"][3]["content"].encode(), (root / previous["response_path"]).read_bytes())
                    self.assertEqual(slot_index[slot["parent_slot"]]["arm"], slot["arm"])

    def test_full_replaces_and_keep_inherits_exact_utf8_bytes(self):
        a1 = {"slot_id": "TEST:A1", "kind": "independent", "parent_slot": None}
        body = "证明。\r\n```lean filename=证明.lean\r\n-- α\r\ndef α := 1\r\n```\r\n".encode()
        initial = compose_material(a1, body)
        first = {"slot_id": "TEST:neutral:1", "kind": "followup", "parent_slot": "TEST:A1"}
        kept = compose_material(first, "\r\n\nKEEP\r\n本轮理由 α。\r\n".encode(), initial)
        self.assertEqual(kept[1], body)
        self.assertEqual(kept[2], "本轮理由 α。\r\n".encode())
        self.assertEqual(kept[0]["body_origin"], initial[0]["body_origin"])
        self.assertEqual(kept[0]["files"], initial[0]["files"])
        second = {"slot_id": "TEST:neutral:2", "kind": "followup", "parent_slot": first["slot_id"]}
        replacement = b"\r\n new body with no old source\r\n"
        full = compose_material(second, b"FULL\r\n" + replacement, kept)
        self.assertEqual(full[1], replacement)
        self.assertIsNone(full[2])
        self.assertEqual(full[0]["files"], [])
        self.assertEqual(full[0]["body_origin"]["start_byte"], len(b"FULL\r\n"))

    def test_mixed_modes_and_keep_replacement_need_format_review(self):
        initial = compose_material({"slot_id": "TEST:A1", "kind": "independent"}, b"original")
        slot = {"slot_id": "TEST:neutral:1", "kind": "followup", "parent_slot": "TEST:A1"}
        invalid = compose_material(slot, b"FULL\nnew\nKEEP\nstill old", initial)
        self.assertEqual(invalid[0]["status"], "unresolved")
        kept = compose_material(slot, "KEEP\n把结论替换为新结论。\n".encode(), initial)
        self.assertEqual(kept[1], b"original")
        self.assertEqual(kept[0]["format_status"], "review_required")

    def test_invalid_r1_is_visible_to_r2_and_full_can_recover(self):
        plan = self.plan(["neutral"])
        replies = self.replies(plan)
        cid = plan["reliability"]["selection"]["cases"][0]["case_id"]
        replies[f"{cid}:neutral:1"] = "missing mode\r\n原文错误格式\r\n"
        replies[f"{cid}:neutral:2"] = "FULL\r\n完整替换。\r\n"
        root, _ = self.execute(plan, replies)
        _, records = inspect_reliability_run(root)
        self.assertEqual(records[f"{cid}:neutral:1"]["material"]["status"], "unresolved")
        second = records[f"{cid}:neutral:2"]
        self.assertEqual(second["material"]["status"], "resolved")
        history = read_json(root / _slot_path(second["slot_id"]) / "history.json")
        self.assertEqual(history[3]["content"], replies[f"{cid}:neutral:1"])
        self.assertEqual((root / _slot_path(second["slot_id"]) / "material-body.md").read_bytes(), "完整替换。\r\n".encode())

    def test_keep_cannot_skip_invalid_immediate_parent(self):
        plan = self.plan(["neutral"])
        replies = self.replies(plan)
        cid = plan["reliability"]["selection"]["cases"][0]["case_id"]
        replies[f"{cid}:neutral:1"] = "invalid r1"
        root, _ = self.execute(plan, replies)
        _, records = inspect_reliability_run(root)
        material = records[f"{cid}:neutral:2"]["material"]
        self.assertEqual(material["status"], "unresolved")
        self.assertIsNone(material["body_origin"])
        self.assertIn("unresolved_immediate_parent", material["issues"])

    def test_missing_r1_blocks_r2_without_filling_from_a1(self):
        plan = self.plan(["neutral"])
        replies = self.replies(plan)
        cid = plan["reliability"]["selection"]["cases"][0]["case_id"]
        replies[f"{cid}:neutral:1"] = [{"stdout": "", "status": "permanent_error", "stderr": "auth denied"}]
        root, meta = self.execute(plan, replies)
        _, records = inspect_reliability_run(root)
        self.assertEqual(records[f"{cid}:neutral:2"]["status"], "blocked")
        self.assertFalse(records[f"{cid}:neutral:2"]["started"])
        self.assertEqual(len(records[f"{cid}:neutral:1"]["attempts"]), 1)
        self.assertEqual(meta["transport_attempts"], 23)

    def test_retry_only_without_readable_body_and_lock_timeout_text(self):
        plan = self.plan(["neutral"])
        replies = self.replies(plan)
        cid, other = [x["case_id"] for x in plan["reliability"]["selection"]["cases"][:2]]
        replies[f"{cid}:A1"] = [{"stdout": b"\xff", "status": "transient_error"}, "first readable\r\n"]
        replies[f"{other}:A1"] = [{"stdout": "refusal but readable\r\n", "status": "timeout"}, "must not run"]
        root, meta = self.execute(plan, replies)
        _, records = inspect_reliability_run(root)
        self.assertEqual(records[f"{cid}:A1"]["locked_attempt"], 2)
        self.assertEqual(records[f"{other}:A1"]["locked_attempt"], 1)
        self.assertEqual(len(records[f"{other}:A1"]["attempts"]), 1)
        self.assertEqual(meta["transport_attempts"], 25)

    def test_attempt_budget_and_same_request_on_transport_retry(self):
        calls = []
        def adapter(request):
            calls.append(request)
            return {"stdout": "", "status": "transient_error"} if len(calls) == 1 else "answer"
        plan = self.plan(["neutral"], budget={"timeout_seconds": 2, "output_tokens": 1000, "max_transport_attempts": 2})
        root, meta = self.execute(plan, adapter=adapter)
        _, records = inspect_reliability_run(root)
        self.assertEqual(calls[0], calls[1])
        self.assertEqual(meta["transport_attempts"], 2)
        self.assertEqual(meta["status"], "budget_exhausted")
        self.assertEqual(sum(r["started"] for r in records.values()), 1)

    def test_unknown_token_usage_stops_total_token_budget(self):
        plan = self.plan(["neutral"], budget={"timeout_seconds": 2, "max_total_tokens": 1000})
        root, meta = self.execute(plan, adapter=lambda _: "answer")
        self.assertEqual(meta["transport_attempts"], 1)
        self.assertFalse(meta["token_usage_complete"])
        self.assertIsNone(meta["total_tokens"])
        self.assertEqual(meta["budget_stop_reason"], "usage_unavailable_for_total_token_budget")
        inspect_reliability_run(root)

    def test_stdout_nonzero_is_raw_and_locks_slot(self):
        raw = "原文\r\nKEEP\r\n".encode()
        command = [sys.executable, "-c", "import sys;sys.stdin.buffer.read();sys.stdout.buffer.write(" + repr(raw) + ");sys.exit(75)"]
        plan = self.plan(["neutral"])
        root, meta = self.execute(plan, command=command)
        _, records = inspect_reliability_run(root)
        self.assertEqual(meta["transport_attempts"], 24)
        self.assertEqual(meta["candidate_calls"], 24)
        for record in records.values():
            self.assertEqual((root / record["response_path"]).read_bytes(), raw)
            self.assertEqual(record["locked_attempt"], 1)

    def test_history_and_material_tampering_are_detected(self):
        root, _ = self.execute()
        _, records = inspect_reliability_run(root)
        first = next(iter(records))
        path = root / _slot_path(first) / "history.json"
        original = path.read_bytes()
        value = read_json(path)
        value[0]["content"] += " evaluator feedback"
        write_json(path, value)
        with self.assertRaisesRegex(ValueError, "visible history"):
            inspect_reliability_run(root)
        path.write_bytes(original)
        body = root / _slot_path(first) / "material-body.md"
        body.write_bytes(body.read_bytes() + b" changed")
        with self.assertRaisesRegex(ValueError, "material bytes"):
            inspect_reliability_run(root)

    def test_case_approval_source_is_frozen_and_legacy_absence_stays_readable(self):
        root, _ = self.execute()
        meta, _ = inspect_reliability_run(root)
        cid = next(iter(meta["inputs"]))
        self.assertTrue(meta["case_approval_evidence_verified"][cid])
        source = root / meta["inputs"][cid]["case_approval_source"]["path"]
        value = read_json(source)
        self.assertEqual(value["status"], "draft")
        value["status"] = "approved"
        write_json(source, value)
        with self.assertRaisesRegex(ValueError, "case approval source changed"):
            inspect_reliability_run(root)
        legacy = self.plan(["neutral"])
        for case in legacy["case_index"]:
            case.pop("case_approval_source")
        legacy["plan_sha256"] = identity({key: item for key, item in legacy.items() if key != "plan_sha256"})
        old, _ = self.execute(legacy, name="legacy")
        inspected, _ = inspect_reliability_run(old)
        self.assertFalse(any(inspected["case_approval_evidence_verified"].values()))

    def test_same_plan_projection_reuses_exact_a1_without_new_calls(self):
        plan = self.plan()
        one, _ = self.execute(plan, name="one", targets=["neutral"])
        two, meta = self.execute(plan, name="two", targets=["stance"], reuse_runs=[one])
        a_meta, a = inspect_reliability_run(one)
        _, b = inspect_reliability_run(two)
        self.assertEqual(meta["transport_attempts"], 32)
        self.assertEqual(len(meta["reused_from"]), 8)
        for sid in meta["reused_from"]:
            self.assertEqual(a[sid]["evidence_id"], b[sid]["evidence_id"])
            self.assertEqual(a_meta["slot_record_sha256"][sid], meta["slot_record_sha256"][sid])
            self.assertEqual((one / _slot_path(sid) / "record.json").read_bytes(),
                             (two / _slot_path(sid) / "record.json").read_bytes())

    def test_reused_execution_audit_conflict_stops_before_dependent_invocations(self):
        plan = self.plan()
        one, _ = self.execute(plan, name="one", targets=["neutral"], adapter=lambda _: "fixture response")
        seen = []
        with patch("math_gauge.eligibility.copy_execution_eligibility",
                   side_effect=ValueError("Conflicting original execution audits")) as copy_audit:
            with self.assertRaisesRegex(ValueError, "Conflicting original execution audits"):
                self.execute(plan, name="two", targets=["stance"], reuse_runs=[one],
                             adapter=lambda request: seen.append(request) or "fixture response")
        self.assertEqual(seen, [])
        self.assertEqual(copy_audit.call_count, 1)
        selected_originals = {record["evidence_id"] for sid, record in inspect_reliability_run(one)[1].items()
                              if sid.endswith(":A1")}
        self.assertEqual(copy_audit.call_args.kwargs["evidence_ids"], selected_originals)

    def test_evidence_cli_exports_direct_submission_and_reports_missing_evidence_offline(self):
        root, before = self.execute()
        sid = before["selected_slot_ids"][0]
        template = self.root / "submission.json"
        checked = self.root / "evidence-check.json"
        with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            self.assertEqual(main(["benchmark-evidence-template", "--run", str(root),
                                   "--slot", sid, "--out", str(template)]), 0)
            self.assertEqual(main(["benchmark-evidence-check", "--run", str(root),
                                   "--out", str(checked)]), 1)
        form = read_json(template)
        self.assertEqual(form["slot_id"], sid)
        self.assertEqual(form["schema"], "math-gauge.execution-eligibility-submission/v1")
        self.assertEqual(form["audit"]["decision"], "unresolved")
        self.assertIn("execution_evidence_missing", read_json(checked)["slots"][sid]["reasons"])
        after, _ = inspect_reliability_run(root)
        self.assertEqual(after["candidate_calls"], 0)
        self.assertEqual(after["slot_record_sha256"], before["slot_record_sha256"])

    def test_distinct_generation_evidence_conflicts_even_for_identical_text(self):
        plan = self.plan()
        one, _ = self.execute(plan, name="one", targets=["neutral"])
        two, _ = self.execute(plan, name="two", targets=["neutral"])
        _, a = inspect_reliability_run(one)
        _, b = inspect_reliability_run(two)
        first = next(iter(a))
        self.assertEqual(a[first]["response_sha256"], b[first]["response_sha256"])
        self.assertNotEqual(a[first]["evidence_id"], b[first]["evidence_id"])
        with self.assertRaisesRegex(ValueError, "Conflicting original generation"):
            self.execute(plan, name="three", targets=["stance"], reuse_runs=[one, two])

    def test_changed_plan_cannot_reuse_dependencies(self):
        plan = self.plan()
        one, _ = self.execute(plan, name="one", targets=["neutral"])
        changed = self.plan()
        with self.assertRaisesRegex(ValueError, "same complete frozen plan"):
            self.execute(changed, name="two", targets=["stance"], reuse_runs=[one])

    def test_unfrozen_real_run_and_parameter_leakage_rejected(self):
        plan = build_plan(self.profile, self.suite, ["neutral"])
        with self.assertRaisesRegex(ValueError, "Freeze runtime"):
            self.execute(plan, command=[sys.executable, "-c", "pass"])
        plan = self.plan(["neutral"], candidate_parameters={"expected_truth": True})
        with self.assertRaisesRegex(ValueError, "whitelisted"):
            self.execute(plan)

    def test_supplied_invalid_execution_requirements_fail_before_transport(self):
        valid = {"schema": "math-gauge.execution-requirements/v1", "allowed_tools": [],
                 "internal_tools": ["finish"], "tool_control_tool": "search_web",
                 "denied_categories": ["reference", "history", "prior_run", "memory", "global_config"],
                 "read_exceptions": []}
        base = self.plan(["neutral"], execution_requirements=valid)
        for invalid in (None, [], {}, dict(valid, allowed_tools=["search_web"]),
                        dict(valid, read_exceptions=[{"kind": "subpath", "path": "relative", "purpose": "invalid"}])):
            with self.subTest(requirements=invalid):
                with self.assertRaises(ValueError):
                    self.plan(["neutral"], execution_requirements=invalid)
                forged = copy.deepcopy(base)
                forged["runtime"]["execution_requirements"] = invalid
                forged["runtime_sha256"] = identity(forged["runtime"])
                forged["plan_sha256"] = identity({key: value for key, value in forged.items() if key != "plan_sha256"})
                with patch("math_gauge.reliability.invoke_conversation") as invoke:
                    with self.assertRaises(ValueError):
                        self.execute(forged, name="invalid", command=["must-not-launch"])
                    invoke.assert_not_called()

    def test_rehashed_cross_branch_plan_is_still_rejected(self):
        plan = self.plan()
        row = next(s for s in plan["slots"] if s.get("arm") == "neutral" and s.get("round") == 2)
        row["parent_slot"] = row["parent_slot"].replace("neutral", "affirm")
        plan["plan_sha256"] = identity({k: v for k, v in plan.items() if k != "plan_sha256"})
        with self.assertRaises(ValueError):
            self.execute(plan)

    def test_reused_fragment_all_original_attempts_count_toward_budget(self):
        plan = self.plan(budget={"timeout_seconds": 2, "max_transport_attempts": 40})
        one, a = self.execute(plan, name="one", targets=["neutral"])
        two, b = self.execute(plan, name="two", targets=["stance"], reuse_runs=[one])
        inspect_reliability_run(two)
        self.assertEqual(a["transport_attempts"], 24)
        self.assertEqual(b["prior_transport_attempts"], 24)
        self.assertEqual(b["transport_attempts"], 16)
        self.assertEqual(b["cumulative_transport_attempts"], 40)
        self.assertEqual(len(b["prior_budget_evidence"]), 24)
        self.assertEqual(b["status"], "budget_exhausted")
        self.assertFalse(b["unseen_plan_fragments_accounted_for"])
        # Both runs include A1 dependencies. The third accounting view must not
        # count those original attempts, or the first run's neutral nodes, twice.
        three, c = self.execute(plan, name="three", targets=["neutral"], reuse_runs=[one, two])
        inspect_reliability_run(three)
        self.assertEqual(c["transport_attempts"], 0)
        self.assertEqual(c["cumulative_transport_attempts"], 40)

    def test_reused_fragment_unknown_token_usage_blocks_new_requests(self):
        plan = self.plan(budget={"timeout_seconds": 2, "max_total_tokens": 1000})
        one, _ = self.execute(plan, name="one", targets=["neutral"])
        two, meta = self.execute(plan, name="two", targets=["stance"], reuse_runs=[one])
        inspect_reliability_run(two)
        self.assertEqual(meta["transport_attempts"], 0)
        self.assertEqual(meta["cumulative_transport_attempts"], 1)
        self.assertFalse(meta["cumulative_token_usage_complete"])
        self.assertIsNone(meta["cumulative_total_tokens"])

    def test_known_tokens_are_cumulative_across_fragments(self):
        plan = self.plan(budget={"timeout_seconds": 2, "max_total_tokens": 60})
        first_replies = {sid: {"stdout": text, "usage": {"total_tokens": 2}}
                         for sid, text in self.replies(plan, ["neutral"]).items()}
        one, _ = self.execute(plan, first_replies, name="one", targets=["neutral"])
        second_replies = {sid: {"stdout": text, "usage": {"total_tokens": 2}}
                          for sid, text in self.replies(plan, ["stance"]).items()}
        two, meta = self.execute(plan, second_replies, name="two", targets=["stance"], reuse_runs=[one])
        inspect_reliability_run(two)
        self.assertEqual(meta["prior_known_total_tokens"], 48)
        self.assertEqual(meta["transport_attempts"], 6)
        self.assertEqual(meta["cumulative_total_tokens"], 60)
        self.assertTrue(meta["cumulative_token_usage_complete"])

    def test_invalid_transport_metadata_cannot_discard_readable_response(self):
        plan = self.plan(["neutral"])
        replies = self.replies(plan)
        sid = select_slots(plan)[0]["slot_id"]
        replies[sid] = {"stdout": "readable refusal\r\n", "status": "unrecognized-status"}
        root, _ = self.execute(plan, replies)
        _, records = inspect_reliability_run(root)
        self.assertEqual(records[sid]["locked_attempt"], 1)
        self.assertEqual((root / records[sid]["response_path"]).read_bytes(), b"readable refusal\r\n")

    def test_changed_frozen_runner_identity_is_rejected(self):
        plan = self.plan(["neutral"])
        plan["runner_sha256"] = "0" * 64
        plan["plan_sha256"] = identity({k: v for k, v in plan.items() if k != "plan_sha256"})
        with self.assertRaisesRegex(ValueError, "Runner source changed"):
            self.execute(plan)


if __name__ == "__main__":
    unittest.main()
