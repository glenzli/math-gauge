"""External harness CLI integration using only explicit offline fixture bytes."""

import contextlib
import io
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from math_gauge.benchmarks import identity, read_plan
from math_gauge.catalog import Suite, digest_bytes, read_json, write_json
from math_gauge.cli import main
from math_gauge.harness import candidate_request_from_bundle

ROOT = Path(__file__).resolve().parents[1]
RUNTIME = {
    "model_label": "offline-external-fixture",
    "adapter_identity": {"kind": "fixture", "name": "no-model-cli-test"},
    "candidate_parameters": {"model": "offline-fixture"},
    "budget": {"timeout_seconds": 2, "output_tokens": 1000, "max_transport_attempts": 354},
    "fresh_context": True,
}


class HarnessCliTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name).resolve()
        self.bundle = self.root / "bundle"
        self.evaluator = self.root / "bundle.evaluator"
        self.no_process = patch(
            "subprocess.Popen", side_effect=AssertionError("External CLI preparation/import cannot call a model"))
        self.no_process.start()
        self.addCleanup(self.no_process.stop)

    def invoke(self, arguments):
        output, errors = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(output), contextlib.redirect_stderr(errors):
            result = main(arguments)
        return result, output.getvalue(), errors.getvalue()

    def succeed(self, arguments):
        result, output, errors = self.invoke(arguments)
        self.assertEqual(result, 0, errors)
        return output

    def export(self, *, frozen=True, extra=None):
        arguments = ["benchmark-export", "--suite", str(ROOT / "cases"),
                     "--profile", str(ROOT / "protocol/benchmark-profile.json"),
                     "--target", "lean-audit", "--out", str(self.bundle)]
        if frozen:
            runtime = self.root / "runtime.json"
            write_json(runtime, RUNTIME)
            arguments += ["--runtime", str(runtime)]
        arguments += extra or []
        return json.loads(self.succeed(arguments))

    def submission(self, *, answer=b"Offline external transport fixture. No mathematical result.\r\n"):
        source = self.root / "submission"
        source.mkdir()
        manifest = read_json(self.bundle / "manifest.json")
        request = candidate_request_from_bundle(self.bundle, "MG-GF101:A1")

        def original_file(name, raw):
            (source / name).write_bytes(raw)
            return {"path": name, "bytes": len(raw), "sha256": digest_bytes(raw)}

        data = read_json(self.bundle / "submission-template.json")
        data.update(bundle_sha256=manifest["bundle_sha256"], origin="fixture", fixture_only=True,
                    declared_external_calls=0, slots=[{
                        "slot_id": "MG-GF101:A1", "projected_request": request,
                        "attempts": [{"number": 1, "status": "ok", "exit_code": 0,
                                      "response": original_file("answer.txt", answer),
                                      "stderr": original_file("stderr.txt", b""),
                                      "usage": {}, "projected_request_sha256": identity(request)}],
                    }])
        path = source / "submission.json"
        write_json(path, data)
        return path

    def import_arguments(self, submission, output):
        return ["benchmark-import", "--bundle", str(self.bundle), "--input", str(submission),
                "--plan", str(self.evaluator / "plan.json"), "--suite", str(ROOT / "cases"),
                "--out", str(output)]

    def test_one_command_preparation_and_read_only_check_do_not_need_runtime(self):
        summary = self.export(frozen=False)
        self.assertTrue(summary["preparation_only"])
        self.assertFalse(summary["runtime_frozen"])
        self.assertEqual(summary["candidate_calls"], 0)
        self.assertEqual(summary["evaluator_plan"], str(self.evaluator / "plan.json"))
        self.assertFalse((self.bundle / "plan.json").exists())
        self.assertEqual(read_plan(self.evaluator / "plan.json")["planned"]["all_slots"], 177)
        paths = [p for root in (self.bundle, self.evaluator) for p in root.rglob("*") if p.is_file()]
        before = {p: (p.read_bytes(), p.stat().st_mtime_ns) for p in paths}
        for extra in ([], ["--plan", str(self.evaluator / "plan.json"),
                           "--suite", str(ROOT / "cases")]):
            checked = json.loads(self.succeed(["benchmark-export-check", "--bundle", str(self.bundle), *extra]))
            self.assertEqual(checked["bundle_sha256"], summary["bundle_sha256"])
            self.assertTrue(checked["preparation_only"])
        self.assertEqual(before, {p: (p.read_bytes(), p.stat().st_mtime_ns) for p in paths})

    def test_existing_plan_export_preserves_full_denominators_and_refuses_runtime_or_profile_override(self):
        runtime_path = self.root / "runtime.json"
        write_json(runtime_path, RUNTIME)
        plan_path = self.root / "full-plan.json"
        self.succeed(["benchmark-plan", "--suite", str(ROOT / "cases"),
                      "--profile", str(ROOT / "protocol/benchmark-profile.json"),
                      "--target", "all", "--runtime", str(runtime_path), "--out", str(plan_path)])
        before = plan_path.read_bytes()
        second_bundle = self.root / "second-bundle"
        second_evaluator = self.root / "operator-only"
        output = json.loads(self.succeed([
            "benchmark-export", "--plan", str(plan_path), "--suite", str(ROOT / "cases"),
            "--target", "lean-audit", "--out", str(second_bundle),
            "--evaluator-out", str(second_evaluator)]))
        self.assertEqual(output["plan_sha256"], read_plan(plan_path)["plan_sha256"])
        self.assertEqual(output["planned"]["all_slots"], 177)
        self.assertEqual(output["planned"]["selected_slots"], 177)
        self.assertEqual(output["exported_slots"], 18)
        self.assertEqual(plan_path.read_bytes(), before)
        self.assertEqual(read_plan(second_evaluator / "plan.json")["plan_sha256"], output["plan_sha256"])
        invalid = self.root / "invalid"
        result, _, errors = self.invoke([
            "benchmark-export", "--plan", str(plan_path), "--profile", str(ROOT / "protocol/benchmark-profile.json"),
            "--out", str(invalid)])
        self.assertEqual(result, 2)
        self.assertIn("--profile", errors)
        self.assertFalse(invalid.exists())
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as raised:
            main(["benchmark-export", "--plan", str(plan_path), "--runtime", str(self.root / "runtime.json"),
                  "--out", str(invalid)])
        self.assertEqual(raised.exception.code, 2)
        self.assertFalse(invalid.exists())

    def test_external_fixture_import_continues_through_shared_review_and_fixed_denominator_report(self):
        summary = self.export()
        self.assertFalse(summary["preparation_only"])
        submission = self.submission()
        run = self.root / "imported"
        imported = json.loads(self.succeed(self.import_arguments(submission, run)))
        self.assertEqual(imported["candidate_calls"], 0)
        meta = read_json(run / "run.json")
        self.assertEqual(meta["origin"], "external_import")
        self.assertEqual(meta["candidate_calls"], 0)
        self.assertEqual(meta["external_candidate_calls_declared"], 0)
        self.assertTrue(meta["fixture_only"])
        self.assertEqual(len(meta["unrun_slots"]), 17)
        self.succeed(["benchmark-check", "--run", str(run)])
        template = self.root / "review.json"
        self.succeed(["benchmark-review-template", "--run", str(run), "--out", str(template)])
        reviews = [entry for entry in read_json(template) if entry["slot_id"] == "MG-GF101:A1"]
        self.assertTrue(reviews)
        for entry in reviews:
            entry.update(reviewer="Offline harness CLI fixture", reviewer_kind="fixture", decision="partial",
                         notes="Synthetic fixture bytes; no model mathematics was assessed.")
            entry["format_review"].update(decision="valid", notes="Offline material transport fixture.")
            for stage in entry["stages"]:
                stage.update(decision="partial", failure_category="mathematical", notes="Synthetic incomplete stage.")
                stage["math_review"].update(decision="partial", reasons=["candidate_incomplete"],
                                            notes="Fixture does not supply a mathematical argument.")
            if "focus_review" in entry:
                entry["focus_review"].update(decision="partial", reasons=["candidate_incomplete"],
                                               notes="Synthetic incomplete focus; no mathematical judgment.")
        write_json(template, reviews)
        self.succeed(["benchmark-review", "--run", str(run), "--input", str(template)])
        collected = self.root / "collected.json"
        self.succeed(["benchmark-collect", "--run", str(run), "--out", str(collected)])
        report = self.root / "report"
        self.succeed(["benchmark-report", "--run", str(run), "--out", str(report)])
        result = read_json(report / "report.json")
        self.assertEqual(result["result_kind"], "fixture")
        self.assertFalse(result["model_result"])
        self.assertIsNone(result["metrics"]["overall"]["exact"])
        self.assertIsNone(result["metrics"]["overall"]["formal_score"])
        self.assertEqual(Suite.load(ROOT / "cases").sha256,
                         read_plan(self.evaluator / "plan.json")["suite"]["sha256"])

    def test_tampered_external_source_is_rejected_without_publishing_a_run(self):
        self.export()
        submission = self.submission()
        (submission.parent / "answer.txt").write_bytes(b"Changed after original submission hashing")
        run = self.root / "rejected"
        result, _, errors = self.invoke(self.import_arguments(submission, run))
        self.assertEqual(result, 2)
        self.assertIn("hash or size changed", errors)
        self.assertFalse(run.exists())

    def test_preparation_only_bundle_cannot_accept_an_execution_submission(self):
        self.export(frozen=False)
        submission = self.submission()
        run = self.root / "not-frozen"
        result, _, errors = self.invoke(self.import_arguments(submission, run))
        self.assertEqual(result, 2)
        self.assertIn("runtime frozen before execution", errors)
        self.assertFalse(run.exists())


if __name__ == "__main__":
    unittest.main()
