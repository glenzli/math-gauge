"""Final-record integrity and finite-state contracts; no models or grading."""

import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from math_gauge.records import (SCHEMA, descriptor, evidence_bytes, trajectory,
                                validate_record, validate_self_assessment)
from math_gauge.scoring import score_record_inputs

ROOT = Path(__file__).resolve().parents[1]


class RecordIntegrityTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.raw = "FULL\n未完成全部目标。\n".encode()
        path = self.root / "answer.md"
        path.write_bytes(self.raw)
        self.file = descriptor(self.root, path)
        self.assessment = {"value": "incomplete", "scope": "full_task",
            "origin": "extracted_from_original", "evidence": [{"source": self.file,
                "start_byte": 5, "end_byte": len(self.raw), "quote": "未完成全部目标。\n"}]}
        row = {"id": "SYNTHETIC:A1", "case_id": "SYNTHETIC", "kind": "independent",
               "parent_id": None, "response": self.file, "self_assessment": self.assessment,
               "source": {"response_sha256": self.file["sha256"]},
               "evaluation": {"complete_count": 0, "total": 1}, "artifacts": []}
        self.record = {"schema": SCHEMA, "benchmark_version": "0.6.0", "record_id": "synthetic",
            "model": {"label": "SYNTHETIC SOFTWARE FIXTURE"}, "harness": {"name": "fixture"},
            "scope": "public", "retention": {"user_requested": True}, "records": [row],
            "evidence": [], "human_review": "pending", "formal_comparison_eligible": False,
            "candidate_calls_by_migration": 0}

    def check(self):
        (self.root / "record.json").write_text(json.dumps(self.record))
        return validate_record(self.root)

    def test_exact_original_utf8_quote_and_hash_validate(self):
        self.assertTrue(self.check()["passed"])
        self.assertEqual(evidence_bytes(self.root, self.file), self.raw)

    def test_modified_answer_or_quote_is_rejected(self):
        for field, value in [("start_byte", 6), ("quote", "全部完成")]:
            changed = copy.deepcopy(self.assessment)
            changed["evidence"][0][field] = value
            with self.subTest(field=field), self.assertRaises((ValueError, UnicodeError)):
                validate_self_assessment(self.root, changed)
        (self.root / "answer.md").write_bytes(self.raw + b"edited")
        with self.assertRaisesRegex(ValueError, "bytes changed"):
            self.check()

    def test_paths_symlinks_and_execution_hash_are_bound(self):
        for name in ["../answer.md", "/answer.md", "nested/../answer.md", "nested\\answer.md"]:
            with self.subTest(name=name), self.assertRaises(ValueError):
                evidence_bytes(self.root, dict(self.file, path=name))
        (self.root / "alias.md").symlink_to(self.root / "answer.md")
        with self.assertRaisesRegex(ValueError, "symlink"):
            evidence_bytes(self.root, dict(self.file, path="alias.md"))
        self.record["records"][0]["source"]["response_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "execution source"):
            self.check()

    def test_missing_fields_do_not_become_candidate_judgments(self):
        for value in ["not_requested", "not_stated", "unresolved"]:
            validate_self_assessment(self.root, {"value": value, "scope": "full_task",
                "origin": "not_available", "reason": "Synthetic missing original field.", "evidence": []})
        for origin in ["model_structured", "extracted_from_original", "not_available"]:
            with self.subTest(origin=origin), self.assertRaises(ValueError):
                validate_self_assessment(self.root, {"value": "complete", "scope": "full_task",
                    "origin": origin, "reason": "No evidence", "evidence": []})

    def test_parent_cycles_cross_task_links_and_duplicate_ids_fail(self):
        row = self.record["records"][0]
        for mutation in ["cycle", "other_task", "duplicate", "missing"]:
            changed = copy.deepcopy(row)
            changed.update(id="SYNTHETIC:R1", parent_id=row["id"])
            self.record["records"] = [row, changed]
            if mutation == "cycle":
                row["parent_id"] = changed["id"]
            elif mutation == "other_task":
                changed["case_id"] = "ANOTHER"
            elif mutation == "duplicate":
                changed["id"] = row["id"]
            else:
                changed["parent_id"] = "MISSING"
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                self.check()
            row["parent_id"] = None

    def test_missing_response_has_an_explicit_reason(self):
        row = self.record["records"][0]
        row["response"] = None
        with self.assertRaisesRegex(ValueError, "explicit reason"):
            self.check()
        row["missing_response_reason"] = "Synthetic absent original; not regenerated."
        self.assertTrue(self.check()["passed"])

    def test_record_migration_cannot_promote_human_approval(self):
        self.record["human_review"] = "approved"
        with self.assertRaisesRegex(ValueError, "promote"):
            self.check()

    def test_shared_engineering_evidence_requires_an_explicit_public_root(self):
        self.record["formalization_review"] = {"path": "reviews/formalization.json", "bytes": 1, "sha256": "0" * 64}
        self.record["formalization_evidence_location"] = "public_archive"
        with self.assertRaisesRegex(ValueError, "explicitly selected public engineering archive"):
            self.check()

    def test_current_method_cannot_fall_back_to_response_only_grading(self):
        (self.root / "scoring-policy.json").write_text(json.dumps({"version": "0.4.0"}))
        with self.assertRaisesRegex(ValueError, "all four source-bound reviews"):
            self.check()

    def test_structured_status_is_bound_to_the_original_reply_span(self):
        import hashlib
        body = b'{"items":[{"id":"O1","status":"complete"}]}'
        (self.root / "alignment.json").write_bytes(body)
        (self.root / "answer.md").write_bytes(b"FULL\n" + body)
        item = {"kind": "structured_alignment", "source": descriptor(self.root, self.root / "alignment.json"),
                "reported_complete": 1, "total": 1,
                "response_source": descriptor(self.root, self.root / "answer.md"),
                "response_span": {"start_byte": 5, "end_byte": 5 + len(body),
                                  "sha256": hashlib.sha256(body).hexdigest()}}
        assessment = {"value": "complete", "scope": "formalization_obligations",
                      "origin": "model_structured", "evidence": [item]}
        validate_self_assessment(self.root, assessment)
        changed = body.replace(b"complete", b"incomplete")
        (self.root / "alignment.json").write_bytes(changed)
        item["source"] = descriptor(self.root, self.root / "alignment.json")
        item["reported_complete"] = 0
        with self.assertRaisesRegex(ValueError, "original response"):
            validate_self_assessment(self.root, assessment)


class FiniteTrajectoryTests(unittest.TestCase):
    def rows(self, counts, claims=None):
        return [{"evaluation": {"complete_count": count, "total": 2,
                    "false_complete_claim": claim == "complete" and count != 2},
                 "self_assessment": {"value": claim, "scope": "full_task"}}
                for count, claim in zip(counts, claims or ["incomplete"] * len(counts))]

    def test_last_prescribed_round_is_used_and_regression_visible(self):
        result = trajectory(self.rows([2, 2, 1], ["complete"] * 3), planned_rounds=3)
        self.assertEqual(result["last_complete_count"], 1)
        self.assertEqual(result["state"], "regressed")
        self.assertEqual(result["first_verified_complete_round"], 1)
        self.assertEqual(result["verified_maintenance_rounds_after_first_complete"], 1)
        self.assertEqual(result["false_complete_claim_rounds"], [3])

    def test_stable_count_with_known_obligation_regression_is_not_stable(self):
        rows = self.rows([1, 1, 1])
        rows[1]["evaluation"]["regressed"] = 1
        self.assertEqual(trajectory(rows, planned_rounds=3)["state"], "regressed")

    def test_missing_and_unknown_rounds_keep_the_fixed_limit(self):
        self.assertEqual(trajectory(self.rows([1]), planned_rounds=3)["state"], "interrupted")
        self.assertEqual(trajectory(self.rows([1, None, 1]), planned_rounds=3)["state"], "unresolved")
        self.assertEqual(trajectory(self.rows([1, 1, 1]), planned_rounds=3)["state"], "incomplete_stable")
        self.assertEqual(trajectory(self.rows([0, 1, 1]), planned_rounds=3)["state"], "incomplete_changed")
        self.assertEqual(trajectory(self.rows([0, 1, 2]), planned_rounds=3)["state"], "verified_complete")
        with self.assertRaises(ValueError):
            trajectory(self.rows([1, 1, 1]), planned_rounds=2)

    def test_local_completion_does_not_claim_full_task(self):
        rows = self.rows([1, 1, 1], ["complete"] * 3)
        for row in rows:
            row["self_assessment"]["scope"] = "compilation"
        self.assertIsNone(trajectory(rows, planned_rounds=3)["first_claimed_complete_round"])


class CurrentArchiveTests(unittest.TestCase):
    def test_selected_archives_reproduce_the_existing_public_scores(self):
        expected = {"terra-6.1-max": 91.6211151369, "gemini-3.8-flash-high": 70.7669021739,
                    "deepseek-v4.1-flash-1017": 74.2149456522}
        for model, score in expected.items():
            root = ROOT / "results/v0.6.0" / model / "20261105"
            self.assertTrue(validate_record(root)["passed"])
            load = lambda name: json.loads((root / name).read_bytes())
            result = score_record_inputs(load("scoring-inputs.json"), load("reviews/alignment.json"),
                load("scoring-policy.json"), formalization_review=load("reviews/formalization.json"))
            self.assertEqual(result["metrics"]["overall"]["exact"], score)
            self.assertEqual(load("result.json")["metrics"]["overall"]["exact"], score)
            self.assertEqual(load("record.json")["candidate_calls_by_migration"], 0)
            rows = {r["id"]: r for r in load("record.json")["records"]}
            for cid, count in [("LCH01", 8), ("LCH02", 20), ("HCH02", 40)]:
                claim = rows[cid + ":A1"]["self_assessment"]
                self.assertEqual(claim["origin"], "model_structured")
                self.assertEqual(claim["scope"], "formalization_obligations")
                self.assertEqual(claim["structured_obligation_claim"]["complete"], count)

    def test_native_status_does_not_override_original_owner_gate(self):
        root = ROOT / "results/v0.6.0/gemini-3.8-flash-high/20261105"
        record = json.loads((root / "record.json").read_bytes())
        rounds = [r for r in record["records"] if r["kind"] == "alignment_followup"]
        self.assertEqual([r["execution"]["native_status"] for r in rounds], ["SUCCESS", "ERROR", "SUCCESS"])
        self.assertTrue(all(r["execution"]["accepted_as_delivered"] is False for r in rounds))
        self.assertEqual(record["trajectory"]["last_complete_count"], 74)
        self.assertEqual(record["trajectory"]["false_complete_claim_rounds"], [1, 2, 3])


class SharedAggregateCheckTests(unittest.TestCase):
    def test_private_recompute_rejects_a_different_public_total_or_source(self):
        spec = importlib.util.spec_from_file_location("record_cli_fixture", ROOT / "scripts/records.py")
        cli = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cli)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            private, public = root / "private", root / "public"
            relative = Path("results/v0.6.0/SOFTWARE-FIXTURE/fixture")
            folder, source = private / relative, public / relative
            folder.mkdir(parents=True)
            (source / "reviews").mkdir(parents=True)
            result = {"metrics": {"overall": {"exact": 50, "lower": 50, "upper": 50}},
                      "engineering_review_sha256": "1" * 64, "scoring_method_version": "0.4.0",
                      "source_score_sha256": "2" * 64}
            files = {"record.json": {"formalization_evidence_location": "public_archive"},
                     "scoring-inputs.json": {}, "alignment-review.json": {}, "scoring-policy.json": {},
                     "result.json": result}
            for name, data in files.items():
                (folder / name).write_text(json.dumps(data))
            (source / "reviews/formalization.json").write_text("{}")
            aggregate = source / "combined-aggregate.json"
            aggregate.write_text(json.dumps(result))
            with patch.object(cli, "validate_record", return_value={"passed": True}) as validator, \
                    patch.object(cli, "score_record_inputs", return_value={"metrics": result["metrics"]}):
                self.assertTrue(cli.check(private, public_root=public)["passed"])
                validator.assert_called_with(folder, formalization_root=source)
                for mutation in ("total", "source"):
                    changed = copy.deepcopy(result)
                    if mutation == "total":
                        changed["metrics"]["overall"]["exact"] = 51
                    else:
                        changed["engineering_review_sha256"] = "3" * 64
                    aggregate.write_text(json.dumps(changed))
                    with self.subTest(mutation=mutation), self.assertRaisesRegex(ValueError, "Public combined aggregate"):
                        cli.check(private, public_root=public)


if __name__ == "__main__":
    unittest.main()
