"""The descriptive panel keeps failures, unknown clocks and exact answer selection."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from scripts.render_timing_reference import write_reference
from scripts.timing_reference import CASE_IDS, build_reference, load_supplement, select_timing, summarize, daily_summary


class TimingReferenceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def keep(self, path, data):
        path = self.root / path
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(data))
        return path

    def row(self, cid="MG-C003", seconds=10800, status="delivery_failed", answer=None):
        return {"id": cid + ":A1", "case_id": cid, "phase": "A1", "answer_sha256": answer,
                "delivery_status": status, "availability": "unknown" if seconds is None else "known",
                "seconds": seconds, "method": "execution_elapsed" if seconds is not None else None,
                "strict_pass": False}

    def model(self, model_id="fixture", record_id="new", *, timing_id=None):
        folder = Path("results/v0.6.0") / model_id / record_id
        self.keep(folder / "record.json", {"record": model_id + record_id})
        tasks = [{"case_id": cid, "response_sha256": str(i) * 64,
                  "completion": {"exact": 0.5}, "strict_pass": False} for i, cid in enumerate(CASE_IDS)]
        self.keep(folder / "public-task-scores.json", {"views": {"partial": {
            "nonlogical_retry_3": {"tasks": tasks}}}})
        tid = timing_id or record_id
        old = Path("results/v0.6.0") / model_id / tid
        record = self.keep(old / "record.json", {"record": model_id + tid})
        rows = [self.row(cid, (i + 1) * 60, "delivered", str(i) * 64) for i, cid in enumerate(CASE_IDS)]
        doc = {"schema": "math-gauge.answer-timings/v1", "visibility": "public-projection",
               "model_id": model_id, "record_id": tid, "public_case_ids": list(CASE_IDS),
               "record": {"path": "record.json", "sha256": hashlib.sha256(record.read_bytes()).hexdigest()},
               "rows": rows, "summary": {"private_metadata": "must never enter display"}}
        path = self.keep(old / "answer-timings.json", doc)
        return folder, path

    def fixture(self):
        self.keep("protocol/scoring-policy.json", {"subcategories": [{"id": k, "weight": v} for k, v in [("written-argument", 25), ("argument-review", 10), ("background-check", 10), ("theorem-extension", 10), ("manuscript-completion", 10)]]})
        self.keep("benchmark.json", {"version": "0.6.0", "selected_result_record_ids": {"fixture": "new"}})
        self.keep("site/data.json", {"models": [
            {"id": mid, "label": mid, "harness_display_name": "Harness", "theme": {"color": "#333"},
             "logo": {"label": "Provider", "data_url": ""}} for mid in ("fixture", "dot-underlying-model-20261108")]})
        self.model("dot-underlying-model-20261108", "20261108")

    def test_failed_run_is_included_missing_is_not_zero_and_known_zero_survives(self):
        rows = [self.row(seconds=60, status="delivered"), self.row(), self.row(seconds=None),
                self.row(seconds=0, status="delivered")]
        result = summarize(rows)
        self.assertEqual(result["timed"], 3)
        self.assertEqual(result["median_seconds"], 60)
        self.assertEqual(result["mean_seconds"], 3620)
        self.assertEqual(result["sum_seconds"], 10860)

    def test_historical_timing_needs_identical_answer_not_case_id(self):
        row = self.row(seconds=900, status="delivered", answer="a" * 64)
        sources = [{"current": False, "rows": {"MG-C003": row}}]
        self.assertEqual(select_timing("MG-C003", "b" * 64, sources), (None, None))
        self.assertEqual(select_timing("MG-C003", "a" * 64, sources)[1]["seconds"], 900)

    def test_null_hash_cannot_reuse_an_older_failed_request(self):
        sources = [{"current": False, "rows": {"MG-C003": self.row()}}]
        self.assertEqual(select_timing("MG-C003", None, sources), (None, None))
        sources[0]["current"] = True
        self.assertEqual(select_timing("MG-C003", None, sources)[1]["seconds"], 10800)

    def test_conflicting_old_clocks_do_not_select_the_fastest(self):
        row = self.row(answer="a" * 64)
        sources = [{"current": False, "rows": {"MG-C003": row}},
                   {"current": False, "rows": {"MG-C003": dict(row, seconds=12)}}]
        with self.assertRaisesRegex(ValueError, "Conflicting"):
            select_timing("MG-C003", "a" * 64, sources)

    def test_daily_weights_use_fixed_denominator_and_require_all_clocks(self):
        rows = [self.row("a", 60, "delivered"), self.row("b", 600)]
        result = daily_summary(rows, {"a": 25, "b": 10})
        self.assertAlmostEqual(result["weighted_mean_seconds"], 7500 / 35)
        self.assertEqual(result["median_seconds"], 330)
        rows[1]["seconds"] = None
        result = daily_summary(rows, {"a": 25, "b": 10})
        self.assertIsNone(result["weighted_mean_seconds"])
        self.assertIsNone(result["median_seconds"])

    def test_current_answer_binding_and_private_projection(self):
        self.fixture()
        folder, path = self.model(timing_id="old")
        document = json.loads(path.read_text())
        document["rows"].append(self.row("private-secret-case", 99999))
        path.write_text(json.dumps(document))
        tasks = json.loads((self.root / folder / "public-task-scores.json").read_text())
        tasks["views"]["partial"]["nonlogical_retry_3"]["tasks"][CASE_IDS.index("MG-C003")]["response_sha256"] = "f" * 64
        (self.root / folder / "public-task-scores.json").write_text(json.dumps(tasks))
        data = build_reference(self.root)
        model = next(m for m in data["models"] if m["id"] == "fixture")
        self.assertEqual(model["summaries"]["daily"]["timed"], 5)
        self.assertIsNone(next(r for r in model["rows"] if r["case_id"] == "MG-C003")["seconds"])
        self.assertTrue(model["rows"][0]["source_reused"])
        self.assertNotIn("private-secret", json.dumps(data))
        self.assertNotIn("private_metadata", json.dumps(data))

    def test_tampered_record_cannot_supply_a_clock(self):
        folder, path = self.model()
        (self.root / folder / "record.json").write_text("{}")
        with self.assertRaisesRegex(ValueError, "different source record"):
            load_supplement(path, "new")

    def test_current_failed_run_remains_visible_in_sample(self):
        self.fixture()
        folder, path = self.model()
        document = json.loads(path.read_text())
        document["rows"][CASE_IDS.index("MG-C003")] = self.row()
        path.write_text(json.dumps(document))
        scores_path = self.root / folder / "public-task-scores.json"
        scores = json.loads(scores_path.read_text())
        scores["views"]["partial"]["nonlogical_retry_3"]["tasks"][CASE_IDS.index("MG-C003")]["response_sha256"] = None
        scores_path.write_text(json.dumps(scores))
        data = build_reference(self.root)
        model = next(m for m in data["models"] if m["id"] == "fixture")
        self.assertEqual(model["summaries"]["MG-C003"]["median_seconds"], 10800)
        self.assertEqual(model["summaries"]["MG-C003"]["nondelivery"], 1)

    def test_generated_consumer_does_not_mutate_scores_or_import_private_summaries(self):
        self.fixture()
        folder, _ = self.model()
        path = self.root / folder / "public-task-scores.json"
        original = path.read_bytes()
        out = self.root / "site/timings"
        data = write_reference(self.root, out)
        self.assertEqual(path.read_bytes(), original)
        self.assertFalse(data["scores_modified"])
        page = (out / "index.html").read_text()
        self.assertIn("<script defer", page)
        self.assertNotIn("@@TIMING_DATA@@", page)
        self.assertNotIn("private_metadata", page)
        manifest = json.loads((out / "generated-pages.json").read_text())
        for asset in manifest:
            self.assertTrue((out / asset).is_file())

    def test_abandoned_run_is_excluded_from_display_and_selected_summary(self):
        self.fixture()
        folder, _ = self.model()
        source = self.keep("site/timings/observed-clocks.json", {
            "schema": "math-gauge.timing-reference-observations/v1", "rows": [{
                "model_id": "fixture", "record_id": "new", "case_id": "MG-C003", "kind": "other_run",
                "seconds": 10800, "method": "operator_reported_elapsed", "delivery_status": "delivery_failed",
                "source_sha256": "a" * 64,
                "selected_record_sha256": hashlib.sha256((self.root / folder / "record.json").read_bytes()).hexdigest()}]})
        original = source.read_bytes()
        data = build_reference(self.root)
        model = next(m for m in data["models"] if m["id"] == "fixture")
        row = next(r for r in model["rows"] if r["case_id"] == "MG-C003")
        self.assertEqual(model["summaries"]["MG-C003"]["mean_seconds"], 360)
        self.assertEqual(row["other_runs"], [])
        self.assertEqual(row["seconds"], 360)
        self.assertEqual(source.read_bytes(), original)

    def test_supplemental_selected_clock_cannot_bind_another_answer(self):
        self.fixture()
        folder, _ = self.model()
        self.keep("site/timings/observed-clocks.json", {
            "schema": "math-gauge.timing-reference-observations/v1", "rows": [{
                "model_id": "fixture", "record_id": "new", "case_id": "MG-C003", "kind": "selected_answer",
                "answer_sha256": "f" * 64, "seconds": 360, "method": "execution_elapsed",
                "source_sha256": "a" * 64,
                "selected_record_sha256": hashlib.sha256((self.root / folder / "record.json").read_bytes()).hexdigest()}]})
        with self.assertRaisesRegex(ValueError, "another answer"):
            build_reference(self.root)

    def test_archived_engineering_without_text_hash_is_not_a_failed_delivery(self):
        self.fixture()
        folder, path = self.model()
        path.unlink()
        scores_path = self.root / folder / "public-task-scores.json"
        scores = json.loads(scores_path.read_text())
        scores["views"]["partial"]["nonlogical_retry_3"]["tasks"][CASE_IDS.index("MG-C003")]["response_sha256"] = None
        scores_path.write_text(json.dumps(scores))
        model = next(m for m in build_reference(self.root)["models"] if m["id"] == "fixture")
        row = next(r for r in model["rows"] if r["case_id"] == "MG-C003")
        self.assertEqual(row["delivery_status"], "delivered")
        self.assertIsNone(row["seconds"])


if __name__ == "__main__":
    unittest.main()
