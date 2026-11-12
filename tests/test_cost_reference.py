import copy
import hashlib
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from math_gauge.costs import (normalize_usage, unit_cost, summarize_model,
                              project_public, source_descriptor, verify_source, pareto_frontier,
                              resolved_reference_cost)
from scripts.collect_cost_reference import Collector
from scripts.cost_reference import build_reference


def usage(**changes):
    return {"input_tokens": 100, "output_tokens": 20, "cached_input_tokens": 60,
            "cache_write_input_tokens": 0, "reasoning_output_tokens": 10, **changes}


def fixture():
    attempt = hashlib.sha256(b"selected-only").hexdigest()
    ids = [f"T{i:03}:A1" for i in range(39)] + [f"MG-C003:R{i}" for i in range(1, 4)]
    model = {"model_id": "sol-6.1-max", "record_id": "example", "slots": [
        {"id": name, "state": "not_run", "selection": "not_run", "units": []} for name in ids]}
    model["slots"][0].update(state="complete", selection="retained_final", attempt_identity_sha256=attempt,
        units=[{"identity_sha256": hashlib.sha256(b"native-unit").hexdigest(),
                "attempt_identity_sha256": attempt, "usage": usage(),
                "convention": "input_includes_cache", "price_id": "standard"}])
    prices = {"standard": {"id": "standard", "label": "Reference", "source_url": "https://example.com/prices",
                           "rates_per_million": {"input": 2, "cached_input": .1, "output": 10, "cache_write": 2.5}}}
    return model, prices


class CostReferenceTest(unittest.TestCase):
    def test_supplement_preserves_declared_reference_basis_without_replacing_usage(self):
        model, prices = fixture()
        original_slots = copy.deepcopy(model["slots"])
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            supplement = root / "supplement.json"
            supplement.write_text(json.dumps({"model_id": model["model_id"],
                "record_id": model["record_id"], "pricing_basis": "caller_recorded_usage_reference",
                "slots": []}))
            Collector(root, root, root / "out").supplement(model, supplement)
        self.assertEqual(model["pricing_basis"], "caller_recorded_usage_reference")
        self.assertEqual(model["slots"], original_slots)
        self.assertEqual(summarize_model(model, prices)["status"], "observed")

    def test_cache_and_reasoning_are_not_charged_twice(self):
        normalized = normalize_usage(usage(), "input_includes_cache")
        self.assertEqual(normalized["uncached_input_tokens"], 40)
        self.assertEqual(normalized["total_tokens"], 120)
        normalized = normalize_usage(usage(), "input_excludes_cache")
        self.assertEqual(normalized["total_tokens"], 180)
        m, p = fixture()
        value, _ = unit_cost(m["slots"][0]["units"][0], p)
        self.assertAlmostEqual(value, .000286)

    def test_missing_cache_is_not_assumed_zero(self):
        value = usage()
        del value["cached_input_tokens"]
        with self.assertRaises(ValueError):
            normalize_usage(value, "input_includes_cache")

    def test_native_unknown_price_cannot_bypass_repricing(self):
        m, p = fixture()
        u = m["slots"][0]["units"][0]
        u.update(reported_list_cost_usd=5, reported_cost_basis="unknown")
        with self.assertRaises(ValueError):
            unit_cost(u, p)

    def test_unknown_usage_keeps_the_whole_total_unknown(self):
        m, p = fixture()
        m["slots"][1].update(state="missing", selection="last_retained_failure")
        row = summarize_model(m, p)
        self.assertIsNone(row["total_usd"])
        self.assertGreater(row["known_usd"], 0)
        self.assertEqual(row["status"], "partial")

    def test_other_attempts_and_duplicate_units_are_rejected(self):
        m, p = fixture()
        m["slots"][0]["units"][0]["attempt_identity_sha256"] = "f" * 64
        with self.assertRaises(ValueError):
            summarize_model(m, p)
        m, p = fixture()
        m["slots"][0]["units"].append(copy.deepcopy(m["slots"][0]["units"][0]))
        with self.assertRaises(ValueError):
            summarize_model(m, p)

    def test_reported_receipt_resolution_keeps_usage_gaps_and_binds_selected_attempt(self):
        m, p = fixture()
        slot = m["slots"][0]
        slot["state"] = "partial"
        before = summarize_model(m, p)
        unit = slot["units"][0]
        m["pricing_basis"] = "reported_native_usage_reference"
        m["cost_resolution"] = {
            "kind": "reported_terminal_usage", "model_id": m["model_id"], "record_id": m["record_id"],
            "basis": "User selected the final cumulative reported usage as the reference-cost scope",
            "sources": [{"path": "confirmation.json"}], "receipts": [{"slot_id": slot["id"],
                "attempt_identity_sha256": slot["attempt_identity_sha256"],
                "unit_identity_sha256": unit["identity_sha256"], "usage": copy.deepcopy(unit["usage"])}]}
        after = summarize_model(m, p)
        self.assertEqual(after["status"], "observed")
        self.assertEqual(after["total_usd"], before["known_usd"])
        self.assertEqual(after["coverage"], before["coverage"])
        self.assertEqual(after["tokens"], before["tokens"])
        m["cost_resolution"]["receipts"][0]["attempt_identity_sha256"] = "f" * 64
        with self.assertRaisesRegex(ValueError, "retained native receipt"):
            summarize_model(m, p)
        m["cost_resolution"]["receipts"][0]["attempt_identity_sha256"] = slot["attempt_identity_sha256"]
        m["slots"][1].update(state="missing", selection="last_retained_failure")
        with self.assertRaisesRegex(ValueError, "missing attempts"):
            summarize_model(m, p)

    def test_cost_resolution_checks_confirmation_and_native_receipt_bytes(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            confirmation = root / "confirmation.json"; confirmation.write_text('{"confirmed":true}')
            native = root / "native.json"; native.write_text('{"native_final_usage_present":true}')
            m, p = fixture();slot = m["slots"][0];unit = slot["units"][0]
            slot.update(state="partial", sources=[source_descriptor(native, root)])
            m["pricing_basis"] = "reported_native_usage_reference"
            m["cost_resolution"] = {"kind": "reported_terminal_usage", "model_id": m["model_id"],
                "record_id": m["record_id"], "basis": "Adopt reported cumulative usage",
                "sources": [source_descriptor(confirmation, root)], "receipts": [{"slot_id": slot["id"],
                    "attempt_identity_sha256": slot["attempt_identity_sha256"],
                    "unit_identity_sha256": unit["identity_sha256"], "usage": unit["usage"]}]}
            self.assertEqual(resolved_reference_cost(m, .000286, root=root), .000286)
            confirmation.write_text('{"confirmed":false}')
            with self.assertRaisesRegex(ValueError, "source bytes changed"):
                resolved_reference_cost(m, .000286, root=root)

    def test_test_date_free_charge_does_not_invent_token_usage(self):
        m, p = fixture()
        m.update(model_id="dot-underlying-model-20261108", record_id="20261108",
                 pricing_basis="test_date_zero_charge")
        for slot in m["slots"]:
            slot.update(state="missing", selection="retained_final" if slot["id"].endswith(":A1") else "fixed_round", units=[])
        self.assertIsNone(summarize_model(m, p)["total_usd"])
        m["cost_resolution"] = {"kind": "test_date_zero_charge", "model_id": m["model_id"],
            "record_id": m["record_id"], "test_date": "2026-11-08", "total_usd": 0,
            "basis": "User confirmed free native use on the test date", "sources": [{"path": "confirmation.json"}]}
        value = summarize_model(m, p)
        self.assertEqual((value["status"], value["total_usd"]), ("observed", 0))
        self.assertEqual(value["coverage"]["missing"], 42)
        self.assertTrue(all(not slot["units"] for slot in m["slots"]))
        m["cost_resolution"]["test_date"] = "2026-11-09"
        with self.assertRaisesRegex(ValueError, "selected Dot test date"):
            summarize_model(m, p)
        m["cost_resolution"]["test_date"] = "2026-11-08"
        m["cost_resolution"]["total_usd"] = 1
        with self.assertRaisesRegex(ValueError, "zero charge"):
            summarize_model(m, p)

    def test_wrong_answer_and_missing_fixed_round_are_rejected(self):
        m, p = fixture()
        answers = {s["id"]: None for s in m["slots"]}
        answers["T000:A1"] = "a" * 64
        with self.assertRaises(ValueError):
            summarize_model(m, p, expected_answers=answers)
        m["slots"].pop()
        with self.assertRaises(ValueError):
            summarize_model(m, p)

    def test_estimate_is_explicit_and_never_below_known_cost(self):
        m, p = fixture()
        m["estimate"] = {"total_usd": 1, "range_usd": [.5, 2], "basis": "Timing calibration", "sources": [{"path": "private.json"}]}
        for name in ("terra-6.1-max", "gemini-3.8-flash-high", "kimi-3.1-pro-max", "glm-5.3-max"):
            with self.subTest(model=name):
                m["model_id"] = name
                self.assertEqual(summarize_model(m, p)["status"], "estimated")
        m["estimate"]["total_usd"] = 0
        with self.assertRaises(ValueError):
            summarize_model(m, p)
        m["estimate"]["total_usd"] = 1
        m["model_id"] = "sol-6.1-max"
        with self.assertRaisesRegex(ValueError, "explicitly selected model"):
            summarize_model(m, p)

    def test_source_bytes_and_paths_are_verified(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder);p = root / "source.json";p.write_text("{}")
            d = source_descriptor(p, root);verify_source(root, d)
            p.write_text('{"changed":true}')
            with self.assertRaises(ValueError):
                verify_source(root, d)
            with self.assertRaises(ValueError):
                verify_source(root, {**d, "path": "../outside.json"})

    def test_public_projection_drops_private_cases_and_tokens(self):
        m, p = fixture()
        document = {"schema": "math-gauge.cost-reference/v1", "version": "0.1.0", "as_of": "2026-11-12",
                    "selection_rule": "one_retained_attempt_per_slot", "other_retries_included": False,
                    "models": [m], "prices": list(p.values())}
        public = project_public(document, source_sha256="a" * 64)
        text = str(public)
        self.assertNotIn("T000", text)
        self.assertNotIn("input_tokens", text)
        self.assertNotIn("attempt_identity", text)

    def test_no_usage_is_unavailable_rather_than_a_free_model(self):
        m, p = fixture()
        m["slots"][0].update(state="missing", selection="unresolved", units=[])
        value = summarize_model(m, p)
        self.assertEqual(value["status"], "unavailable")
        self.assertIsNone(value["total_usd"])

    def test_cli_cumulative_snapshot_includes_internal_turns_once(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder);p = root / "input";p.mkdir()
            (p / "metadata.json").write_text(json.dumps({"session_id": "native", "resume": False}))
            raw = {"input_tokens": 12, "output_tokens": 20, "cache_read_input_tokens": 30,
                   "cache_creation_input_tokens": 5, "thinking_tokens": 0}
            (p / "usage.json").write_text(json.dumps(raw))
            first = {"type": "result", "usage": {"input_tokens": 7, "output_tokens": 15}}
            last = {"type": "result", "usage": {"input_tokens": 5, "output_tokens": 5}, "modelUsage": {
                "custom-kimi": {"inputTokens": 12, "outputTokens": 20, "cacheReadInputTokens": 30,
                                "cacheCreationInputTokens": 5, "costBasis": "unknown", "costUSD": 999}}}
            (p / "stdout.jsonl").write_text(json.dumps(first) + "\n" + json.dumps(last) + "\n")
            collector = Collector(root, root, root / "out")
            value = collector.native("kimi-3.1-pro-max", "T000:A1", p / "metadata.json", expected_answer="a" * 64)
            self.assertEqual(value["state"], "complete")
            self.assertEqual(value["units"][0]["usage"]["input_tokens"], 12)
            self.assertNotIn("reported_list_cost_usd", value["units"][0])

    def test_timed_out_stream_uses_unique_messages_and_excludes_inherited_sessions(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder);p = root / "input";p.mkdir();(p / "transcript").mkdir()
            (p / "metadata.json").write_text(json.dumps({"session_id": "current"}))
            def message(mid, count, session="current"):
                return {"type": "assistant", "sessionId": session, "message": {"id": mid, "usage": {
                    "input_tokens": 1, "output_tokens": count, "cache_read_input_tokens": 0,
                    "cache_creation_input_tokens": 0}}}
            events = [message("one", 4), message("one", 4), message("one", 6), message("parent", 100, "parent")]
            (p / "transcript/main.jsonl").write_text("\n".join(json.dumps(x) for x in events) + "\n")
            collector = Collector(root, root, root / "out")
            value = collector.native("glm-5.3-max", "T000:A1", p / "metadata.json", expected_answer=None)
            self.assertEqual(value["state"], "partial")
            self.assertEqual(len(value["units"]), 1)
            self.assertEqual(value["units"][0]["usage"]["output_tokens"], 6)

    def test_agy_aggregate_keeps_failed_generation_usage_unknown(self):
        raw = {"input_tokens": 100, "output_tokens": 20, "cache_read_tokens": 60,
               "thinking_tokens": 10, "total_tokens": 120}
        known = {"conversation_id": "native", "step_index": 1, "state": "DONE",
                 "step_type": "agent_response", "usage": raw}
        zero = {key: 0 for key in raw}
        scenarios = [
            ({"state": "DONE", "usage": zero}, "zero_usage_generation_followed_by_error", None),
            ({"state": "ACTIVE"}, "generation_unfinished_at_cutoff", None),
            ({"state": "DONE"}, "generation_usage_missing", None),
            (None, "native_stream_failure_usage_unresolved", "API error: request failed: stream idle timeout"),
            (None, None, None),
        ]
        for changed, reason, error in scenarios:
            with self.subTest(reason=reason), tempfile.TemporaryDirectory() as folder:
                root = Path(folder);run = root / "run"
                (run / "runtime").mkdir(parents=True);(run / "output").mkdir()
                events = [{"event": "init", "conversation_id": "native"},
                          {"event": "step_update", "step_update": known}]
                if changed is not None:
                    events += [
                        {"event": "step_update", "step_update": {
                            "conversation_id": "native", "step_index": 2,
                            "step_type": "agent_response", **changed}},
                        {"event": "step_update", "step_update": {
                            "conversation_id": "native", "step_index": 3,
                            "step_type": "error_message", "state": "DONE"}},
                    ]
                events.append({"event": "result", "result": {"status": "ERROR", "usage": raw, "error": error}})
                (run / "output/events.ndjson").write_text("\n".join(json.dumps(x) for x in events) + "\n")
                meta = run / "runtime/execution.json"
                meta.write_text(json.dumps({"status": "failed", "request_utc": "2026-11-12T00:00:00Z", "usage": raw}))
                collector = Collector(root, root, root / "out")
                value = collector.native("gemini-4-carbon", "T000:A1", meta, expected_answer=None)
                self.assertEqual(value["state"], "partial" if reason else "complete")
                self.assertEqual(len(value["units"]), 1)
                self.assertEqual(value["units"][0]["usage"]["output_tokens"], 20)
                source = json.loads((collector.out / value["sources"][0]["path"]).read_text())
                self.assertTrue(source["native_final_usage_present"])
                self.assertEqual([row["reason"] for row in source["native_usage_coverage_gaps"]],
                                 [reason] if reason else [])

    def test_copied_native_session_cannot_be_charged_in_two_slots(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            collector = Collector(root, root, root / "out")
            slots = []
            for name in ("first-copy", "sealed-copy"):
                path = root / name;path.mkdir()
                (path / "metadata.json").write_text(json.dumps({"session_id": "same-native-call"}))
                (path / "transcript").mkdir()
                event = {"type": "assistant", "sessionId": "same-native-call", "message": {
                    "id": "same-provider-message", "usage": {"input_tokens": 1, "output_tokens": 2,
                    "cache_read_input_tokens": 0, "cache_creation_input_tokens": 0}}}
                (path / "transcript/log.jsonl").write_text(json.dumps(event) + "\n")
                slot = collector.native("kimi-3.1-pro-max", "T000:A1", path / "metadata.json", expected_answer=None)
                slot.update(selection="last_retained_failure")
                slots.append(slot)
            self.assertEqual(slots[0]["attempt_identity_sha256"], slots[1]["attempt_identity_sha256"])
            model, prices = fixture()
            model["slots"][0] = {**slots[0], "id": "T000:A1"}
            model["slots"][1] = {**slots[1], "id": "T001:A1"}
            prices["kimi-standard"] = prices["standard"]
            with self.assertRaisesRegex(ValueError, "duplicated"):
                summarize_model(model, prices)

    def test_frontier_preserves_ties_and_zero_and_excludes_incomplete_costs(self):
        def row(name, cost, score, **extra):
            return {"model_id": name, "total_usd": cost, "score": score, "status": "observed", "score_complete": True, **extra}
        rows = [row("zero", 0, 0), row("best", 2, 90), row("tied", 2, 90), row("dominated", 5, 80),
                row("subtotal", .01, 100, status="partial"), row("estimate", 1, 99, status="estimated"),
                row("unfinished", .01, 100, score_complete=False)]
        self.assertEqual(pareto_frontier(rows), ["zero", "best", "tied"])

    def test_time_frontier_uses_known_time_independently_of_cost_coverage(self):
        def row(name, seconds, score, **extra):
            return {"model_id": name, "seconds": seconds, "score": score,
                    "status": "observed", "score_complete": True, **extra}
        rows = [row("unknown-cost", 30, 80, status="unavailable"),
                row("estimated-cost", 60, 90, status="estimated"),
                row("dominated", 90, 70), row("missing-clock", None, 100),
                row("unfinished-score", 1, 100, score_complete=False)]
        self.assertEqual(pareto_frontier(rows, axis="time"), ["unknown-cost", "estimated-cost"])

    def test_last_recovered_failure_excludes_earlier_native_counters(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            archive = root / "results/v0.6.0/sol-6.1-max/example"
            archive.mkdir(parents=True)
            record = {"records": [{"id": "T000:A1", "source": {"native_metadata": {
                "path": "earlier/metadata.json", "sha256": "a" * 64}}}]}
            record_path = archive / "record.json"
            record_path.write_text(json.dumps(record))
            proof = archive / "last-physical-attempt.json"
            proof.write_text('{"physical_attempt":2,"native_usage":null}')
            recovery = {"schema": "math-gauge.source-recovery-review/v1", "status": "complete",
                        "record": source_descriptor(record_path, archive), "resolved_initials": [{
                            "case_id": "T000", "physical_attempt": 2, "classification": "blank",
                            "native_terminal_available": False, "evidence": [source_descriptor(proof, archive)]}]}
            (archive / "review-completion-private.json").write_text(json.dumps(recovery))
            expected = {slot["id"]: None for slot in fixture()[0]["slots"]}
            context = {"name": "record.json", "private_record": record, "expected": expected}
            collector = Collector(root, root, root / "out")
            with patch("scripts.collect_cost_reference.record_context", return_value=context), \
                    patch.object(collector, "native", side_effect=AssertionError("Earlier retry was charged")):
                model, _ = collector.model("sol-6.1-max", "example")
            slot = model["slots"][0]
            self.assertEqual(slot["state"], "missing")
            self.assertEqual(slot["selection"], "last_retained_failure")
            self.assertEqual(slot["units"], [])
            expected["T000:A1"] = "a" * 64
            with patch("scripts.collect_cost_reference.record_context", return_value=context):
                with self.assertRaises(ValueError):
                    collector.model("sol-6.1-max", "example")

    def test_display_joins_source_scores_and_rejects_stale_record_bytes(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            archive = root / "results/v0.6.0/sol-6.1-max/example"
            archive.mkdir(parents=True)
            source = archive / "record.json"; source.write_text("{}")
            cost = {"schema": "math-gauge.cost-reference-public/v1", "other_retries_included": False,
                "as_of": "2026-11-12", "private_source_sha256": "a" * 64, "prices": [], "models": [{
                    "model_id": "sol-6.1-max", "record_id": "example", "status": "observed",
                    "record_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                    "total_usd": 4, "known_usd": 4, "estimate_range_usd": None, "coverage": {},
                    "pricing_basis": "standard_api_reference"}]}
            path = root / "results/costs/v0.1.0/current.json";path.parent.mkdir(parents=True)
            path.write_text(json.dumps(cost))
            def score(value):
                return {"metrics": {"earned": {"confirmed": value}, "overall": {"exact": value}}}
            display = {"models": [{"id": "sol-6.1-max", "label": "Sol", "theme": {}, "logo": {},
                "retry": {"combined": score(60)}, "capability": {"nonlogical_retry_3": score(80)},
                "strict": {"nonlogical_retry_3": score(20)},
                "evaluation_progress": {"nonlogical_retry_3": {"incomplete": False}}}]}
            timings = {"models": [{"id": "sol-6.1-max", "summaries": {"daily": {"weighted_mean_seconds": 120}}}]}
            value = build_reference(root, display_data=display, timing_reference=timings)
            self.assertEqual(value["models"][0]["scores"]["partial"]["value"], 60)
            self.assertEqual(value["models"][0]["seconds"], 120)
            self.assertEqual(value["frontiers"]["strict"]["cost"], ["sol-6.1-max"])
            selected = display["models"][0]["retry"]["combined"]
            for normal, forced, complete in ((39, 0, True), (38, 1, False), (0, 39, False)):
                selected["submission_summary"] = {"planned": 39, "active_final": normal,
                                                  "forced_content": forced}
                delivery = build_reference(root, display_data=display, timing_reference=timings)["models"][0]["answer_delivery"]
                self.assertEqual(delivery, {"planned": 39, "active_final": normal, "complete": complete})
            display["models"][0]["answer_delivery"] = {"planned": 39, "active_final": 39}
            self.assertFalse(build_reference(root, display_data=display, timing_reference=timings)
                             ["models"][0]["answer_delivery"]["complete"],
                             "The selected submission summary takes precedence over fallback counts")
            display["models"][0]["evaluation_progress"]["nonlogical_retry_3"]["incomplete"] = True
            self.assertEqual(build_reference(root, display_data=display, timing_reference=timings)["frontiers"]["partial"]["cost"], [])
            source.write_text('{"changed":true}')
            with self.assertRaises(ValueError):
                build_reference(root, display_data=display, timing_reference=timings)
