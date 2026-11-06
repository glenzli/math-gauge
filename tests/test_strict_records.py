"""Strict public archives bind sources without publishing private task records."""
import copy
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from math_gauge.records import evidence_bytes, load_strict_results

ROOT = Path(__file__).resolve().parents[1]


class StrictRecordTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = ROOT / "results/v0.6.0/deepseek-v4.1-flash-1017/20261105"
        cls.record = json.loads((cls.root / "record.json").read_bytes())

    def poisoned(self, change):
        def read(root, item):
            raw = evidence_bytes(root, item)
            if item["path"] == self.record["strict_results"]["single_attempt"]["path"]:
                value = json.loads(raw)
                change(value)
                return json.dumps(value).encode()
            return raw
        return patch("math_gauge.records.evidence_bytes", side_effect=read)

    def test_selected_conditions_are_source_bound_and_do_not_change_the_record(self):
        original = copy.deepcopy(self.record)
        scores = load_strict_results(self.root, self.record)
        self.assertEqual(set(scores), {"single_attempt", "nonlogical_retry_3"})
        self.assertEqual(self.record, original)
        for score in scores.values():
            self.assertEqual(score["metrics"]["earned"]["exact"], 25.2941176471)
            self.assertNotIn("tasks", score)

    def test_wrong_condition_review_status_or_engineering_source_is_rejected(self):
        for mutation in (lambda x: x.update(attempt_condition="nonlogical_retry_3"),
                         lambda x: x.update(human_review="approved"),
                         lambda x: x.update(primary_metric="old_capability"),
                         lambda x: x["source_bindings"].update(engineering_review_sha256="0" * 64)):
            with self.poisoned(mutation), self.assertRaisesRegex(ValueError, "identity, condition or evidence"):
                load_strict_results(self.root, self.record)

    def test_source_condition_cannot_be_rebound_to_another_partial_aggregate(self):
        with self.poisoned(lambda x: x["source_bindings"].update(assessment_policy_sha256="0" * 64)), \
                self.assertRaisesRegex(ValueError, "identity, condition or evidence"):
            load_strict_results(self.root, self.record)

    def test_private_tasks_and_internal_metric_diagnostics_cannot_enter_public_projection(self):
        for mutation in (lambda x: x.update(tasks=[{"case_id": "PRIVATE-FIXTURE"}]),
                         lambda x: x["metrics"]["earned"].update(formal_eligibility={"slot_id": "PRIVATE-FIXTURE"})):
            with self.poisoned(mutation), self.assertRaisesRegex(ValueError, "only projected aggregates"):
                load_strict_results(self.root, self.record)

    def test_missing_condition_and_unprovided_private_policy_root_are_rejected(self):
        record = copy.deepcopy(self.record)
        record["strict_results"].pop("nonlogical_retry_3")
        with self.assertRaisesRegex(ValueError, "both attempt conditions"):
            load_strict_results(self.root, record)
        record = dict(self.record, formalization_evidence_location="public_archive")
        with self.assertRaisesRegex(ValueError, "explicit public evidence"):
            load_strict_results(self.root, record)


if __name__ == "__main__":
    unittest.main()
