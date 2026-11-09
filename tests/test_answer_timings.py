"""Timing evidence is independent from scores, coverage and runtime certification."""
import copy
import json
import tempfile
import unittest
from pathlib import Path

from math_gauge.timings import descriptor, project_public, summaries, summary, validate_private


class AnswerTimingsTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def keep(self, name, data):
        p = self.root / name
        p.write_text(json.dumps(data))
        return descriptor(p, self.root)

    def row(self, name="public", seconds=12, delivery="delivered"):
        item = self.keep(name + ".json", {"elapsed_seconds": seconds, "timeout_seconds": 2700})
        return {"id": name + ":A1", "case_id": name, "phase": "A1", "answer_sha256": "a" * 64,
                "delivery_status": delivery, "availability": "known", "seconds": seconds,
                "method": "execution_elapsed", "quality": "retained_native_metadata",
                "time_binding": {"kind": "elapsed_field", "source": item, "pointer": "/elapsed_seconds"},
                "evidence": [item], "note": "Original execution duration.", "public_note": "Execution duration."}

    def document(self, rows):
        return {"schema": "math-gauge.answer-timings/v1", "version": "0.1.0", "visibility": "private",
                "benchmark_version": "0.6.0", "model_id": "fixture", "record_id": "fixture",
                "new_candidate_calls": 0, "scores_modified": False, "rows": rows,
                "summary": summaries(rows), "interpretation": "Timing does not grant mathematical credit."}

    def check(self, rows):
        doc = self.document(rows)
        return validate_private(doc, self.root, {row["id"]: row["answer_sha256"] for row in rows})

    def test_missing_and_failed_time_do_not_become_delivered_zeroes(self):
        good = self.row()
        failed = self.row("failed", 900, "delivery_failed")
        unrun = self.row("unrun", 2700, "not_run")
        unrun.update(availability="unknown", seconds=None, method=None, time_binding=None)
        self.check([good, failed, unrun])
        report = summary([good, failed, unrun])
        self.assertEqual(report["timed_delivered"], 1)
        self.assertEqual(report["maximum_seconds"], 12)
        self.assertEqual(report["mean_seconds"], 12)
        self.assertEqual(report["timed_failures"], 1)
        self.assertEqual(report["not_run"], 1)

    def test_configured_budget_is_not_a_recovered_measurement(self):
        row = self.row(seconds=2700)
        row["time_binding"]["pointer"] = "/timeout_seconds"
        with self.assertRaisesRegex(ValueError, "configured limit"):
            self.check([row])

    def test_attempt_times_remain_source_bound_and_outside_selected_statistics(self):
        row = self.row()
        failed = self.keep("earlier-attempt.json", {"elapsed_seconds": 900})
        doc = self.document([row])
        doc["physical_attempt_timings"] = [{"slot_id": row["id"], "seconds": 900,
            "method": "operator_reported_elapsed", "evidence": [failed],
            "time_binding": {"kind": "elapsed_field", "source": failed, "pointer": "/elapsed_seconds"}}]
        validate_private(doc, self.root, {row["id"]: row["answer_sha256"]})
        self.assertEqual(doc["summary"]["initial_answers"]["maximum_seconds"], 12)
        doc["physical_attempt_timings"][0]["seconds"] = 12
        with self.assertRaisesRegex(ValueError, "attempt elapsed time"):
            validate_private(doc, self.root, {row["id"]: row["answer_sha256"]})

    def test_first_native_terminal_excludes_later_cli_cleanup(self):
        row = self.row()
        item = self.keep("native.json", {"started_utc": "2026-11-09T00:00:00+00:00",
            "native_terminal": "2026-11-09T00:00:20+00:00", "cli_exit": "2026-11-09T00:03:00+00:00"})
        row.update(seconds=20, method="native_terminal_wall", started_at="2026-11-09T00:00:00+00:00",
                   ended_at="2026-11-09T00:00:20+00:00", evidence=[item],
                   time_binding={"kind": "timestamp_difference", "start": {"source": item, "pointer": "/started_utc"},
                                 "end": {"source": item, "pointer": "/native_terminal"}})
        self.check([row])
        row["seconds"] = 180
        with self.assertRaisesRegex(ValueError, "source bytes"):
            self.check([row])

    def test_changed_answer_and_tampered_source_are_rejected(self):
        row = self.row()
        with self.assertRaisesRegex(ValueError, "different selected answer"):
            validate_private(self.document([row]), self.root, {row["id"]: "b" * 64})
        (self.root / "public.json").write_text("{}")
        with self.assertRaises(ValueError):
            self.check([row])

    def test_public_projection_keeps_combined_statistics_without_private_paths(self):
        public, private = self.row(), self.row("secret-case", 24)
        private["note"] = "/private/reference/secret-case"
        doc = self.document([public, private])
        result = project_public(doc, ["public"], record={"sha256": "c" * 64}, public_tasks={}, private_sha256="d" * 64)
        text = json.dumps(result)
        self.assertNotIn("secret-case", text)
        self.assertNotIn("/private/reference", text)
        self.assertNotIn("time_binding", text)
        self.assertEqual(result["summary"]["initial_answers"]["mean_seconds"], 18)
        self.assertEqual(len(result["rows"]), 1)

    def test_historical_extraction_cannot_change_the_original_metadata(self):
        original = {"elapsed_seconds": 17, "response_sha256": "a" * 64, "status": "ok"}
        item = self.keep("historical.json", {"schema": "math-gauge.historical-timing-extract/v1",
            "extraction_only": True, "runtime_independently_verified": False, "original_excerpt": repr(original),
            "timing": original, "original_session_sha256": "e" * 64, "original_event_sha256": "f" * 64})
        row = self.row(seconds=17)
        row.update(method="historical_reported_elapsed", evidence=[item],
                   time_binding={"kind": "elapsed_field", "source": item, "pointer": "/timing/elapsed_seconds"})
        self.check([row])
        changed = copy.deepcopy(original)
        changed["elapsed_seconds"] = 18
        payload = json.loads((self.root / "historical.json").read_text())
        payload["timing"] = changed
        row["time_binding"]["source"] = self.keep("historical.json", payload)
        row.update(evidence=[], seconds=18)
        with self.assertRaisesRegex(ValueError, "literal excerpt"):
            self.check([row])

    def test_selfcheck_is_separate_and_unknown_summary_is_not_estimated(self):
        row = self.row()
        row.update(id="public:R1", phase="R1")
        report = summaries([row])
        self.assertIsNone(report["initial_answers"]["maximum_seconds"])
        self.assertEqual(report["selfcheck_rounds"]["maximum_seconds"], 12)
        doc = self.document([row])
        doc["summary"]["selfcheck_rounds"]["maximum_seconds"] = 10800
        with self.assertRaisesRegex(ValueError, "summary differs"):
            validate_private(doc, self.root, {row["id"]: row["answer_sha256"]})


if __name__ == "__main__":
    unittest.main()
