"""Offline external ingestion contracts; synthetic records are not model runs."""

import copy
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

from math_gauge.benchmarks import BenchmarkProfile, build_plan, identity, select_slots
from math_gauge.catalog import Suite, digest_bytes, read_json, write_json
from math_gauge.harness import candidate_request_from_bundle, export_harness_bundle
from math_gauge.harness_import import import_harness_submission
from math_gauge.reliability import (apply_reliability_reviews, inspect_reliability_run,
                                    reliability_review_templates, reliability_score_inputs, _slot_path)
from math_gauge.scoring import render_score, score_runs

ROOT = Path(__file__).resolve().parents[1]
CID = "MG-GR002"


class HarnessImportTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.suite = Suite.load(ROOT / "cases")
        cls.profile = BenchmarkProfile.load(ROOT / "protocol/benchmark-profile.json", cls.suite)

    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name).resolve()
        self.runtime = {"model_label": "offline-harness-fixture", "adapter_identity": {"kind": "fixture"},
                        "budget": {"timeout_seconds": 2, "output_tokens": 1000},
                        "candidate_parameters": {"reasoning_effort": "high"}, "fresh_context": True}
        self.plan = build_plan(self.profile, self.suite, ["all"], runtime=self.runtime)
        self.bundle = self.root / "bundle"
        self.manifest = export_harness_bundle(self.plan, self.suite, self.bundle, targets=["neutral", "stance"])
        self.source = self.root / "source"
        self.source.mkdir()
        self.input = self.source / "submission.json"
        self.output = self.root / "imported"

    def descriptor(self, name, raw):
        raw = raw.encode() if isinstance(raw, str) else raw
        path = self.source / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)
        return {"path": name, "bytes": len(raw), "sha256": digest_bytes(raw)}

    def submission(self, replies=None, *, origin="fixture", fixture_only=True):
        replies = replies or {}
        answers, rows = {}, []
        slots = {s["slot_id"]: s for s in select_slots(self.plan, ["neutral", "stance"])}
        for sid, slot in slots.items():
            if sid not in replies:
                continue
            chain, parent = {}, slot["parent_slot"]
            while parent is not None:
                chain[parent] = answers[parent]
                parent = slots[parent]["parent_slot"]
            projected = candidate_request_from_bundle(self.bundle, sid, chain)
            specs = replies[sid]
            specs = specs if isinstance(specs, list) else [specs]
            attempts = []
            for number, spec in enumerate(specs, 1):
                spec = dict(spec) if isinstance(spec, dict) else {"stdout": spec}
                raw = spec.pop("stdout", b"")
                raw = raw.encode() if isinstance(raw, str) else raw
                stderr = spec.pop("stderr", b"")
                prefix = sid.replace(":", "-") + f"/{number}"
                attempt = {"number": number, "status": spec.pop("status", "ok"),
                           "response": self.descriptor(prefix + "/response.md", raw),
                           "stderr": self.descriptor(prefix + "/stderr.txt", stderr),
                           "usage": spec.pop("usage", {"total_tokens": 5}),
                           "projected_request_sha256": identity(projected), **spec}
                attempts.append(attempt)
                try:
                    text = raw.decode()
                except UnicodeDecodeError:
                    text = ""
                if text.strip() and sid not in answers:
                    answers[sid] = raw
            rows.append({"slot_id": sid, "projected_request": projected, "attempts": attempts})
        value = {"schema": "math-gauge.harness-submission/v1", "bundle_sha256": self.manifest["bundle_sha256"],
                 "plan_sha256": self.plan["plan_sha256"], "runtime_sha256": self.plan["runtime_sha256"],
                 "origin": origin, "fixture_only": fixture_only, "declared_external_calls": 0,
                 "slots": rows}
        write_json(self.input, value)
        return value

    def import_run(self, value=None, destination=None):
        if value is not None:
            write_json(self.input, value)
        return import_harness_submission(self.bundle, self.input, self.plan, self.suite, destination or self.output)

    def rejected(self, value, message):
        with self.assertRaisesRegex(ValueError, message):
            self.import_run(value)
        self.assertFalse(self.output.exists())

    def test_roundtrip_preserves_all_evidence_without_execution_and_survives_source_deletion(self):
        raw = "书面答卷 fixture 原字节。\r\n".encode()
        value = self.submission({CID + ":A1": {
            "stdout": raw, "stderr": "service note\r\n", "status": "timeout", "usage": {"total_tokens": 7},
            "started_at": "2026-11-01T00:00:00Z", "finished_at": "2026-11-01T00:00:01Z", "elapsed_seconds": 1,
            "metadata": {"provider": "synthetic fixture", "model": "declared only", "finish_reason": "length"}}})
        value["metadata"] = {"command": ["touch", str(self.root / "must-not-exist")],
                             "provider_session": "synthetic-declaration", "configuration": {"reasoning": "high"}}
        value["artifacts"] = [self.descriptor("logs/transport.ndjson", b'{"fixture":true}\n')]
        original = (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()
        with patch("subprocess.Popen", side_effect=AssertionError("Importer executed a process")), \
                patch("math_gauge.execution.invoke_conversation", side_effect=AssertionError("Importer called a candidate")):
            meta = self.import_run(value)
        self.assertEqual(meta["origin"], "external_import")
        self.assertEqual((meta["candidate_calls"], meta["external_candidate_calls_declared"]), (0, 0))
        self.assertFalse((self.root / "must-not-exist").exists())
        self.assertEqual((self.output / "external-import/submission.json").read_bytes(), original)
        shutil.rmtree(self.source)
        shutil.rmtree(self.bundle)
        inspected, records = inspect_reliability_run(self.output)
        record = records[CID + ":A1"]
        self.assertEqual((self.output / record["response_path"]).read_bytes(), raw)
        self.assertEqual(record["locked_attempt"], 1)
        self.assertEqual(record["attempts"][0]["external_source"], value["slots"][0]["attempts"][0])
        self.assertEqual(record["attempts"][0]["started_at"], "2026-11-01T00:00:00Z")
        self.assertEqual(inspected["known_total_tokens"], 7)
        self.assertTrue(reliability_review_templates(self.output))
        inputs = reliability_score_inputs(self.output)
        row = next(r for r in inputs["slots"] if r["slot_id"] == CID + ":A1")
        self.assertTrue(row["fixture_only"])
        self.assertIn("external_origin_unverified", row["execution_eligibility"]["reasons"])
        report = score_runs([self.output])
        self.assertEqual(report["result_kind"], "fixture")
        self.assertFalse(report["model_result"])
        self.assertIn("177", render_score(report))
        self.assertEqual(report["source_runs"][0]["candidate_calls"], 0)
        self.assertEqual(report["source_runs"][0]["external_candidate_calls_declared"], 0)

    def test_partial_import_keeps_missing_slots_and_fixed_full_denominator(self):
        self.submission({CID + ":A1": "fixture initial"})
        meta = self.import_run()
        _, records = inspect_reliability_run(self.output)
        other = next(sid for sid in records if sid.endswith(":A1") and not sid.startswith(CID))
        self.assertEqual(records[other]["status"], "not_run")
        self.assertEqual(records[other]["reason"], "submission_missing")
        self.assertEqual(records[other.replace(":A1", ":neutral:1")]["status"], "blocked")
        self.assertEqual(records[CID + ":neutral:1"]["reason"], "submission_missing")
        self.assertEqual(records[CID + ":neutral:2"]["status"], "blocked")
        self.assertEqual(len(meta["selected_slot_ids"]), 56)
        report = score_runs([self.output])
        self.assertEqual(report["execution_coverage"]["full_plan_slots"], 177)
        self.assertEqual(report["execution_coverage"]["unique_started_slots"], 1)
        self.assertIsNone(report["metrics"]["overall"]["exact"])
        self.assertEqual(report["metrics"]["strict_pass_rate"]["coverage"]["planned"], 129)

    def test_keep_full_and_exact_branch_history_use_shared_material_owner(self):
        initial = "initial α\r\n"
        replies = {CID + ":A1": initial, CID + ":neutral:1": "KEEP\r\n第一轮说明。\r\n",
                   CID + ":neutral:2": "FULL\r\n新答卷 β\r\n",
                   CID + ":affirm:1": "FULL\n支持分支\n", CID + ":affirm:2": "KEEP\n本轮说明\n",
                   CID + ":deny:1": "KEEP\n怀疑分支\n", CID + ":deny:2": "KEEP\n仍保持\n"}
        self.submission(replies)
        self.import_run()
        _, records = inspect_reliability_run(self.output)
        first = records[CID + ":neutral:1"]
        second = records[CID + ":neutral:2"]
        self.assertEqual((self.output / _slot_path(first["slot_id"]) / "material-body.md").read_bytes(), initial.encode())
        self.assertEqual((self.output / _slot_path(second["slot_id"]) / "material-body.md").read_bytes(), "新答卷 β\r\n".encode())
        history = read_json(self.output / _slot_path(CID + ":affirm:2") / "history.json")
        self.assertEqual(history[1]["content"], initial)
        self.assertEqual(history[3]["content"], replies[CID + ":affirm:1"])
        self.assertNotIn(replies[CID + ":neutral:1"], [m["content"] for m in history])
        self.assertNotIn("expected_truth", json.dumps(history))

    def test_transient_invalid_utf8_retry_locks_first_readable_text(self):
        value = self.submission({CID + ":A1": [{"stdout": b"\xff\xfe", "status": "transient_error", "usage": {}},
                                               {"stdout": "readable fixture\r\n", "status": "timeout"}]})
        self.import_run(value)
        _, records = inspect_reliability_run(self.output)
        record = records[CID + ":A1"]
        self.assertEqual(record["locked_attempt"], 2)
        self.assertEqual(len(record["attempts"]), 2)
        self.assertIsNone(record["attempts"][0]["started_at"])
        self.assertEqual((self.output / record["attempts"][0]["response_path"]).read_bytes(), b"\xff\xfe")
        self.assertIsNone(read_json(self.output / "run.json")["total_tokens"])

    def test_first_readable_failure_retry_and_permanent_retry_are_rejected(self):
        for first, message in (({"stdout": "refusal fixture", "status": "timeout"}, "locked readable"),
                               ({"stdout": "", "status": "permanent_error"}, "permanent")):
            with self.subTest(first=first):
                value = self.submission({CID + ":A1": [first, "selected second"]})
                self.rejected(value, message)

    def test_failed_service_blocks_all_followups_and_is_not_math_failure(self):
        self.submission({CID + ":A1": {"stdout": "", "status": "permanent_error", "stderr": "auth failure fixture"}})
        self.import_run()
        _, records = inspect_reliability_run(self.output)
        self.assertEqual(records[CID + ":A1"]["status"], "execution_error")
        self.assertEqual(records[CID + ":deny:1"]["reason"], "parent_without_readable_response")
        row = next(r for r in reliability_score_inputs(self.output)["slots"] if r["slot_id"] == CID + ":A1")
        self.assertEqual(row["whole_math"]["state"], "E")
        self.assertIsNone(row["strict_pass"])

    def test_branch_history_and_parameter_drift_are_rejected(self):
        base = self.submission({CID + ":A1": "initial", CID + ":neutral:1": "KEEP\nchecked", CID + ":neutral:2": "KEEP\nsecond"})
        for kind in ("peer", "a1", "parameters", "attempt"):
            value = copy.deepcopy(base)
            row = value["slots"][-1]
            if kind == "peer":
                row["projected_request"]["messages"][3]["content"] = "peer stance answer"
            elif kind == "a1":
                row["projected_request"]["messages"][1]["content"] = "different original"
            elif kind == "parameters":
                row["projected_request"]["parameters"]["max_output_tokens"] = 2000
            else:
                row["attempts"][0]["projected_request_sha256"] = "0" * 64
            with self.subTest(kind=kind):
                self.rejected(value, "history|parameters|request")

    def test_followup_cannot_supply_its_own_missing_a1_or_replace_with_a2(self):
        value = self.submission({CID + ":A1": "original", CID + ":neutral:1": "KEEP\nchecked"})
        value["slots"].pop(0)
        self.rejected(value, "branch parent")

    def test_duplicate_unknown_and_excess_attempts_are_rejected(self):
        base = self.submission({CID + ":A1": "answer"})
        for kind in ("duplicate", "unknown", "excess", "number"):
            value = copy.deepcopy(base)
            if kind == "duplicate":
                value["slots"].append(copy.deepcopy(value["slots"][0]))
            elif kind == "unknown":
                value["slots"][0]["slot_id"] = "MG-GR002:A2"
            elif kind == "excess":
                value["slots"][0]["attempts"] *= 3
            else:
                value["slots"][0]["attempts"][0]["number"] = 2
            with self.subTest(kind=kind):
                self.rejected(value, "duplicate|Unknown|one or two|ordering")

    def test_submitted_slots_must_preserve_frozen_relative_order(self):
        value = self.submission({CID + ":A1": "first", CID + ":neutral:1": "KEEP\nchecked"})
        value["slots"].reverse()
        self.rejected(value, "frozen sequential order")

    def test_source_hash_path_symlink_and_duplicate_json_key_fail_closed(self):
        base = self.submission({CID + ":A1": "answer"})
        response = base["slots"][0]["attempts"][0]["response"]
        bad = copy.deepcopy(base)
        bad["slots"][0]["attempts"][0]["response"]["sha256"] = "0" * 64
        self.rejected(bad, "hash or size")
        bad = copy.deepcopy(base)
        bad["slots"][0]["attempts"][0]["response"]["path"] = "../outside"
        self.rejected(bad, "Unsafe")
        target = self.source / response["path"]
        original = target.read_bytes()
        target.unlink()
        target.symlink_to(self.source / "outside.md")
        (self.source / "outside.md").write_bytes(original)
        self.rejected(base, "symlinks")
        target.unlink()
        target.write_bytes(original)
        self.input.write_text('{"schema":"wrong","schema":"math-gauge.harness-submission/v1"}')
        with self.assertRaisesRegex(ValueError, "Duplicate JSON"):
            self.import_run()
        self.assertFalse(self.output.exists())

    def test_generated_lean_files_are_exact_named_original_blocks_and_never_substitute_answer(self):
        body = "not a proof\r\n```lean filename=Main.lean\r\ndef a := 1\r\n```\r\n".encode()
        value = self.submission({CID + ":A1": body})
        start = body.index(b"def a")
        end = body.index(b"```", start)
        generated = {"name": "Main.lean", **self.descriptor("generated/Main.lean", body[start:end]),
                     "extraction": {"response_sha256": digest_bytes(body), "start_byte": start, "end_byte": end}}
        value["slots"][0]["attempts"][0]["generated_files"] = [generated]
        self.import_run(value)
        shutil.rmtree(self.source)
        _, records = inspect_reliability_run(self.output)
        record = records[CID + ":A1"]
        saved = record["attempts"][0]["generated_files"][0]
        self.assertEqual((self.output / saved["path"]).read_bytes(), body[start:end])
        self.assertEqual((self.output / _slot_path(CID + ":A1") / "material-body.md").read_bytes(), body)
        self.assertEqual(record["material"]["files"][0]["sha256"], generated["sha256"])

    def test_generated_file_repair_or_wrong_name_is_rejected(self):
        body = b"```lean filename=Main.lean\ndef a := 1\n```\n"
        base = self.submission({CID + ":A1": body})
        start, end = body.index(b"def a"), body.rindex(b"```")
        for name, content in (("Main.lean", b"def a := 2\n"), ("Other.lean", body[start:end])):
            value = copy.deepcopy(base)
            item = {"name": name, **self.descriptor("generated/" + name, content),
                    "extraction": {"response_sha256": digest_bytes(body), "start_byte": start, "end_byte": end}}
            value["slots"][0]["attempts"][0]["generated_files"] = [item]
            with self.subTest(name=name):
                self.rejected(value, "original response extraction|named original answer block")

    def test_replay_fixture_and_import_checkbox_cannot_upgrade_to_formal(self):
        value = self.submission({CID + ":A1": "fixture"}, origin="replay")
        bad = copy.deepcopy(value)
        bad["fixture_only"] = False
        self.rejected(bad, "cannot become")
        self.import_run(value)
        meta = read_json(self.output / "run.json")
        meta.update(model_identity_verified=True, fresh_context_verified=True, candidate_tools_verified_disabled=True,
                    external_origin_verified=True)
        write_json(self.output / "run.json", meta)
        inputs = reliability_score_inputs(self.output)
        row = next(r for r in inputs["slots"] if r["started"])
        self.assertTrue(row["fixture_only"])
        self.assertFalse(row["comparison_eligible"])
        self.assertIn("external_origin_unverified", row["execution_eligibility"]["reasons"])
        report = score_runs([self.output])
        self.assertEqual(report["result_kind"], "fixture")
        self.assertIsNone(report["metrics"]["overall"]["formal_score"])
        meta["fixture_only"] = False
        write_json(self.output / "run.json", meta)
        with self.assertRaisesRegex(ValueError, "origin or call"):
            inspect_reliability_run(self.output)

    def test_imported_answer_can_receive_shared_fixture_review_without_formal_score(self):
        self.submission({CID + ":A1": "synthetic fixture"})
        self.import_run()
        entry = next(x for x in reliability_review_templates(self.output) if x["slot_id"] == CID + ":A1")
        entry.update(reviewer="offline fixture reviewer", reviewer_kind="fixture", decision="pass",
                     assumption_fidelity="clean", proof_validity="valid", scope_accuracy="correct",
                     unnecessary_restriction=False, notes="Synthetic bookkeeping only, no mathematical judgment.")
        entry["format_review"] = {"decision": "valid", "notes": "Synthetic fixture format."}
        for row in entry["stages"]:
            row.update(decision="pass", assumption_fidelity="clean", proof_validity="valid", scope_accuracy="correct",
                       failure_category="none", notes="Synthetic review only.")
            row["math_review"].update(decision="pass", assumption_fidelity="clean", proof_validity="valid",
                                      scope_accuracy="correct", unnecessary_restriction=False, reasons=[], notes="Fixture.")
        entry["focus_review"].update(decision="pass", assumption_fidelity="clean", proof_validity="valid",
                                     scope_accuracy="correct", unnecessary_restriction=False, reasons=[],
                                     notes="Synthetic focus bookkeeping, no mathematical claim.")
        focus = next(x for x in self.plan["reliability"]["selection"]["cases"] if x["case_id"] == CID)
        entry["focus_review"]["verdict"] = focus["expected_truth"]
        apply_reliability_reviews(self.output, [entry])
        report = score_runs([self.output])
        self.assertAlmostEqual(report["papers"][CID]["completion"]["lower"], 100 / 3)
        self.assertIsNone(report["papers"][CID]["completion"]["exact"])
        self.assertEqual(report["result_kind"], "fixture")
        self.assertIsNone(report["metrics"]["overall"]["formal_score"])

    def test_original_source_and_history_tampering_are_detected(self):
        self.submission({CID + ":A1": "fixture"})
        self.import_run()
        source = self.output / "external-import/submission.json"
        raw = source.read_bytes()
        source.write_bytes(raw + b" ")
        with self.assertRaisesRegex(ValueError, "Original external submission"):
            inspect_reliability_run(self.output)
        source.write_bytes(raw)
        history = self.output / _slot_path(CID + ":A1") / "history.json"
        value = read_json(history)
        value[0]["content"] += " added evaluator feedback"
        write_json(history, value)
        with self.assertRaisesRegex(ValueError, "visible history"):
            inspect_reliability_run(self.output)

    def test_plan_runtime_and_runner_drift_rejected_without_output(self):
        base = self.submission({CID + ":A1": "fixture"})
        for key in ("bundle_sha256", "plan_sha256", "runtime_sha256"):
            value = copy.deepcopy(base)
            value[key] = "0" * 64
            with self.subTest(key=key):
                self.rejected(value, "different bundle, plan or runtime")
        write_json(self.input, base)
        with patch("math_gauge.harness_import.runner_fingerprint", return_value="0" * 64):
            with self.assertRaisesRegex(ValueError, "Runner source changed"):
                self.import_run()
        self.assertFalse(self.output.exists())

    def test_existing_output_is_never_overwritten(self):
        self.submission({CID + ":A1": "fixture"})
        self.output.mkdir()
        (self.output / "keep.txt").write_text("existing data")
        with self.assertRaisesRegex(ValueError, "already exists"):
            self.import_run()
        self.assertEqual((self.output / "keep.txt").read_text(), "existing data")

    def test_frozen_attempt_budget_stops_further_imported_calls(self):
        self.runtime["budget"]["max_transport_attempts"] = 1
        self.plan = build_plan(self.profile, self.suite, runtime=self.runtime)
        self.bundle = self.root / "limited-bundle"
        self.manifest = export_harness_bundle(self.plan, self.suite, self.bundle, targets=["neutral", "stance"])
        value = self.submission({CID + ":A1": [{"stdout": b"", "status": "transient_error"}, "second"]})
        self.rejected(value, "budget stopped")

    def test_missing_usage_under_total_token_budget_prevents_later_calls(self):
        self.runtime["budget"]["max_total_tokens"] = 100
        self.plan = build_plan(self.profile, self.suite, runtime=self.runtime)
        self.bundle = self.root / "token-limited-bundle"
        self.manifest = export_harness_bundle(self.plan, self.suite, self.bundle, targets=["neutral", "stance"])
        value = self.submission({CID + ":A1": {"stdout": "initial", "usage": {}},
                                 CID + ":neutral:1": "KEEP\nchecked"})
        self.rejected(value, "budget stopped")
        value["slots"].pop()
        meta = self.import_run(value)
        self.assertFalse(meta["token_usage_complete"])
        self.assertEqual(meta["budget_stop_reason"], "usage_unavailable_for_total_token_budget")
        self.assertIsNone(meta["total_tokens"])

    def test_shared_input_freezer_accepts_supported_nonempty_candidate_instruction(self):
        from math_gauge.reliability import _freeze_inputs

        original = self.suite.request
        def request(case):
            value = original(case)
            value["instruction"] = "Neutral instruction fixture."
            return value
        plan = copy.deepcopy(self.plan)
        with patch.object(type(self.suite), "request", side_effect=request):
            for row in plan["case_index"]:
                value = request(self.suite.cases[row["case_id"]])
                row["request_sha256"] = digest_bytes(json.dumps(value, ensure_ascii=False, sort_keys=True).encode())
            target = self.root / "frozen-with-instruction"
            requests, _ = _freeze_inputs(plan, self.suite, target)
        self.assertEqual((target / "inputs" / CID / "solver/prompt.md").read_bytes(),
                         ("Neutral instruction fixture.\n\n" + requests[CID]["task"]).encode())


if __name__ == "__main__":
    unittest.main()
