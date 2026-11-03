"""Local private-shaped releases use the shared portable controller and importer."""

import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
import zipfile

from test_composite_suites import RUNTIME, synthetic_profile, synthetic_suite
from math_gauge.catalog import candidate_message, read_json
from math_gauge.harness import freeze_release_runtime, inspect_release_dataset, release_candidate_request
from math_gauge.harness_answers import issue_answer_request, pack_answer_archive, record_answer_attempt
from math_gauge.harness_import import import_answer_archive
from math_gauge.reliability import _raw, inspect_reliability_run

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("math_gauge_external_release", ROOT / "scripts/release.py")
release = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(release)


class ExternalReleaseTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="math-gauge-external-release-fixture-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.source = self.root / "unborn-source"
        self.suite = synthetic_suite(self.source / "cases", "SYN-PRIVATE")
        self.profile = synthetic_profile(self.source, self.suite)
        subprocess.run(["git", "init", "--quiet", str(self.source)], check=True, capture_output=True)

    def build(self, output="assets"):
        with patch("math_gauge.execution.invoke_conversation", side_effect=AssertionError("No model calls")):
            return release.build_external_release(self.root / output, suite_paths=[self.suite.root],
                                                  profile_path=self.profile.path)

    def test_dirty_unborn_dataset_is_version_aligned_exact_and_runtime_free(self):
        receipt = self.build()
        self.assertEqual(receipt["release_version"], self.suite.metadata["version"])
        self.assertEqual(receipt["candidate_calls"], 0)
        dataset = release.check_release_archive(receipt["archive"], checksums=receipt["checksums"], external=True)
        self.assertEqual(dataset["planned"]["all_slots"], 1)
        self.assertNotIn("runtime", dataset)
        self.assertNotIn("profile", dataset)
        anchor = read_json(receipt["evaluator_plan"])
        self.assertIsNone(anchor["release_provenance"]["repositories"][0]["head"])
        self.assertTrue(anchor["release_provenance"]["repositories"][0]["dirty"])
        with zipfile.ZipFile(receipt["archive"]) as archive:
            names = set(archive.namelist())
            self.assertFalse(any(Path(name).name in {"case.json", "reference.md", "rubric.json", "contract.json", "profile.json", "evaluator-plan.json"}
                                 for name in names))
            self.assertEqual(archive.read("benchmark-v1.2.3/cases/SYN-PRIVATE/task.md"),
                             self.suite.case_file("SYN-PRIVATE", self.suite.cases["SYN-PRIVATE"]["task"]).read_bytes())
            for name in names:
                raw = archive.read(name)
                self.assertNotIn(b"EVALUATOR_PRIVATE", raw)
                self.assertNotIn(str(self.source).encode(), raw)
                self.assertNotIn(b"source_suites", raw)
        with self.assertRaisesRegex(ValueError, "cannot assert a clean source"):
            release.check_release_archive(receipt["archive"], external=True, source_commit="a" * 40)
        with self.assertRaisesRegex(ValueError, "suite version"):
            release.build_external_release(self.root / "wrong-version", suite_paths=[self.suite.root],
                                           profile_path=self.profile.path, version="9.9.9")
        self.assertFalse((self.root / "wrong-version").exists())

    def test_relocated_helper_and_answer_archive_reenter_the_same_runner(self):
        receipt = self.build()
        with zipfile.ZipFile(receipt["archive"]) as archive:
            archive.extractall(self.root / "download")
        dataset_root = self.root / "download/benchmark-v1.2.3"
        isolated = subprocess.run([sys.executable, "-I", "-S", str(dataset_root / "tools/benchmark.py"), "check"],
                                  cwd=self.root, capture_output=True)
        self.assertEqual(isolated.returncode, 0, isolated.stderr.decode())
        self.assertEqual(json.loads(isolated.stdout)["candidate_calls"], 0)
        run = self.root / "portable-run"
        freeze_release_runtime(dataset_root, RUNTIME, run)
        request = release_candidate_request(run, "SYN-PRIVATE:A1")
        self.assertEqual(request["messages"][0]["content"], candidate_message(self.suite.request(self.suite.cases["SYN-PRIVATE"])))
        responses = self.root / "portable-answers"
        issued = self.root / "request.json"
        issue_answer_request(run, responses, "SYN-PRIVATE:A1", issued)
        raw = self.root / "answer.md"
        raw.write_bytes(b"Synthetic fixture response, not a real model result.\r\n")
        record_answer_attempt(run, responses, "SYN-PRIVATE:A1", issued, raw, status="ok")
        answer_archive = self.root / "answers.zip"
        pack_answer_archive(run, responses, answer_archive)
        imported = self.root / "imported"
        with patch("math_gauge.execution.invoke_conversation", side_effect=AssertionError("No model calls")):
            import_answer_archive(answer_archive, read_json(receipt["evaluator_plan"]), self.suite, imported)
        meta, records = inspect_reliability_run(imported)
        self.assertEqual(meta["candidate_calls"], 0)
        self.assertTrue(records["SYN-PRIVATE:A1"]["fixture_only"])
        self.assertEqual(_raw(imported, records["SYN-PRIVATE:A1"]), raw.read_bytes())

    def test_changed_source_discards_partial_assets(self):
        from math_gauge.harness import export_simple_release_dataset

        def changed_source(*args, **kwargs):
            value = export_simple_release_dataset(*args, **kwargs)
            (self.suite.root / "paper/reference.md").write_text("Changed evaluator-only input")
            return value

        with patch("math_gauge.harness.export_simple_release_dataset", side_effect=changed_source):
            with self.assertRaisesRegex(ValueError, "Source changed|differs from its current source"):
                self.build()
        self.assertFalse((self.root / "assets").exists())


if __name__ == "__main__":
    unittest.main()
