"""Contracts for anonymous attempt history, independent of mathematical scores."""

import copy
from collections import Counter
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from scripts import results_attempt_history as history_view


class AttemptHistoryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.history_path = self.root / "private-history.json"
        self.record_path = self.root / "public-record.json"
        self.rows = []
        self.add_row("private-alpha", "A1", "historical", 1, history_view.FAILURE)
        self.add_row("private-alpha", "A1", "resumed", 1, history_view.NORMAL)
        self.add_row("private-beta", "A1", "historical", 1, history_view.FAILURE)
        self.add_row("private-beta", "A1", "resumed", 1,
                     "source-bound-candidate-TLS-handshake-system-failure")
        self.add_row("private-beta", "A1", "resumed", 2, history_view.FAILURE)
        self.add_row("private-beta", "A1", "resumed", 3, history_view.NORMAL)
        for phase in ("R1", "R2", "R3"):
            self.add_row("private-alpha", phase, "resumed", 1, history_view.NORMAL)
        self.history = {
            "schema": "math-gauge.complete-physical-request-retention/v1",
            "source_benchmark_version": "0.6.0", "model_id": "sample-model",
            "ready_for_record_binding": True, "original_bytes_rewritten": False,
            "new_candidate_calls": 0, "new_mathematical_judgments": 0,
            "source_epoch_roots_scanned": ["/private/example/historical", "/private/example/resumed"],
            "physical_lifecycle_records": self.rows,
        }
        self.record = {
            "schema": "math-gauge.result-record/v1", "benchmark_version": "0.6.0",
            "model_id": "sample-model", "record_id": "20261116", "human_review": "pending",
            "formal_comparison_eligible": False,
            "execution_summary": {"planned_initial_tasks": 2, "prescribed_selfcheck_rounds": 3,
                                  "delivered_initial_tasks": 2, "delivered_selfcheck_rounds": 3,
                                  "physical_model_requests": None},
        }
        self.write_sources()

    def add_row(self, case_id, phase, epoch, physical, classification):
        effective = int(classification in {history_view.NORMAL, history_view.FAILURE})
        tail = f"attempts/{case_id}" if phase == "A1" else f"alignment/{phase}"
        identity = f"/private/example/{epoch}/{tail}/physical-{physical}"
        self.rows.append({
            "case_id": case_id, "phase": phase, "original_attempt_root": identity,
            "reported_effective_consumption": effective, "source_classification": classification,
            "closed_result_present": True,
            "primary_source_entry": {
                "case_id": case_id, "physical_request_number": physical,
                "native_started_utc": f"2026-11-01T00:{len(self.rows):02}:00+00:00",
                "normal_complete_delivery": classification == history_view.NORMAL,
                "normal_final_locks_selection_regardless_of_mathematical_quality": classification == history_view.NORMAL,
            },
        })

    def write_sources(self, *, refresh_summary=True):
        if refresh_summary:
            normal = sum(row["source_classification"] == history_view.NORMAL for row in self.rows)
            effective = sum(row["reported_effective_consumption"] for row in self.rows)
            rounds = [row for row in self.rows if row["phase"] != "A1"]
            parent = [row for row in self.rows if row["case_id"] == "private-alpha" and row["phase"] == "A1"]
            self.history["summary"] = {
                "retained_lifecycle_records": len(self.rows), "closed_result_records": len(self.rows),
                "source_reported_effective_attempts": effective,
                "effective_attempts_after_source_bound_correction": effective,
                "source_reported_nonconsumed_lifecycles": len(self.rows) - effective,
                "observed_normal_native_finals": normal,
                "source_classification_counts": dict(Counter(row["source_classification"] for row in self.rows)),
                "fixed_round_lifecycles": len(rounds),
                "fixed_round_source_effective_attempts": sum(row["reported_effective_consumption"] for row in rounds),
                "C003_lifecycles": len(parent),
                "C003_source_effective_attempts": sum(row["reported_effective_consumption"] for row in parent),
                "actual_cloud_candidate_call_count": None,
            }
        data = json.dumps(self.history).encode()
        self.history_path.write_bytes(data)
        self.record["execution_summary"]["physical_history_sha256"] = hashlib.sha256(data).hexdigest()
        self.record["execution_summary"]["request_history_counts"] = copy.deepcopy(self.history["summary"])
        self.record_path.write_text(json.dumps(self.record))

    def build(self):
        return history_view.build_from_sources(self.history_path, self.record_path,
                                                historical_epochs=["/private/example/historical"])

    def test_conserves_attempts_and_fixed_slot_denominators(self):
        document, binding = self.build()
        row = document["models"]["sample-model"]
        self.assertEqual(row["totals"], {
            "lifecycle_records": 9, "effective_attempts": 8, "system_exclusions": 1,
            "normal_finals": 5, "consumed_delivery_failures": 3, "planned_slots": 5,
            "additional_lifecycles": 4, "additional_effective_attempts": 3,
        })
        self.assertEqual(row["segments"]["historical"]["lifecycle_records"], 2)
        self.assertEqual(row["segments"]["resumed"]["lifecycle_records"], 7)
        self.assertEqual(row["phases"]["A1"]["planned_slots"], 2)
        self.assertEqual(row["phases"]["selfcheck"]["planned_slots"], 3)
        self.assertEqual(len(binding["lifecycle_partition"]), 9)

    def test_public_allowlist_never_exposes_case_ids_or_epoch_paths(self):
        document, binding = self.build()
        text = json.dumps(document)
        self.assertNotIn("private-alpha", text)
        self.assertNotIn("private-beta", text)
        self.assertNotIn("/private/", text)
        self.assertIn("private-alpha", json.dumps(binding))
        for branch in [document, document["models"]["sample-model"],
                       document["models"]["sample-model"]["source_binding"],
                       document["models"]["sample-model"]["totals"]]:
            branch["source_path"] = "/private/leaked"
            with self.assertRaisesRegex(ValueError, "fields"):
                history_view.validate_public(document)
            del branch["source_path"]

    def test_rejects_source_history_tampering_against_public_record(self):
        self.history_path.write_bytes(self.history_path.read_bytes() + b"\n")
        with self.assertRaisesRegex(ValueError, "History bytes differ"):
            self.build()

    def test_recomputes_summary_instead_of_trusting_counters(self):
        self.history["summary"]["retained_lifecycle_records"] += 1
        self.write_sources(refresh_summary=False)
        with self.assertRaisesRegex(ValueError, "recomputed retained_lifecycle_records"):
            self.build()

    def test_checks_public_record_counters_against_lifecycles(self):
        self.record["execution_summary"]["request_history_counts"]["source_reported_effective_attempts"] += 1
        self.record_path.write_text(json.dumps(self.record))
        with self.assertRaisesRegex(ValueError, "Public record summary differs"):
            self.build()

    def test_segments_must_be_exact_nonoverlapping_and_cover_every_lifecycle(self):
        for epochs in [["/private/example"], ["/private/example/historical"] * 2,
                       self.history["source_epoch_roots_scanned"]]:
            with self.assertRaisesRegex(ValueError, "exact, nonempty disjoint"):
                history_view.build_from_sources(self.history_path, self.record_path, historical_epochs=epochs)
        self.history["source_epoch_roots_scanned"].append("/private/example")
        self.write_sources()
        with self.assertRaisesRegex(ValueError, "without overlap"):
            self.build()

    def test_duplicate_lifecycle_is_not_a_second_attempt(self):
        self.rows.append(copy.deepcopy(self.rows[0]))
        self.write_sources()
        with self.assertRaisesRegex(ValueError, "Duplicate"):
            self.build()

    def test_a_normal_mathematical_error_still_locks_selection(self):
        self.rows[1]["primary_source_entry"]["mathematical_reviewed"] = True
        self.rows[1]["primary_source_entry"]["mathematical_correct"] = False
        self.add_row("private-alpha", "A1", "resumed", 2, history_view.FAILURE)
        self.write_sources()
        with self.assertRaisesRegex(ValueError, "first normal final locks selection"):
            self.build()

    def test_unknown_api_count_cannot_be_rendered_as_zero_or_lifecycles(self):
        document, _ = self.build()
        row = document["models"]["sample-model"]
        self.assertIsNone(row["actual_candidate_api_calls"])
        for value in [0, row["totals"]["lifecycle_records"]]:
            row["actual_candidate_api_calls"] = value
            with self.assertRaisesRegex(ValueError, "not API-call counts"):
                history_view.validate_public(document)

    def test_public_partitions_and_boolean_counts_cannot_be_changed(self):
        document, _ = self.build()
        row = document["models"]["sample-model"]
        row["segments"]["historical"]["normal_finals"] = 1
        with self.assertRaises(ValueError):
            history_view.validate_public(document)
        document, _ = self.build()
        document["models"]["sample-model"]["totals"]["system_exclusions"] = True
        with self.assertRaisesRegex(ValueError, "nonnegative integers"):
            history_view.validate_public(document)

    def test_missing_projection_stays_unknown_and_valid_projection_loads(self):
        self.assertIsNone(history_view.load_public(self.root))
        document, _ = self.build()
        target = self.root / history_view.PUBLIC_PATH
        target.parent.mkdir(parents=True)
        target.write_text(json.dumps(document))
        self.assertEqual(history_view.load_public(self.root), document)

    def test_private_source_binding_cannot_be_written_to_public_repository(self):
        with self.assertRaisesRegex(ValueError, "outside the public repository"):
            history_view.main(["--history", str(self.history_path), "--record", str(self.record_path),
                               "--historical-epoch", "/private/example/historical",
                               "--private-binding", str(history_view.ROOT / "private-leak.json")])


if __name__ == "__main__":
    unittest.main()
