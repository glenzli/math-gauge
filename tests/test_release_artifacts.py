"""Download artifact acceptance: isolated stdlib consumers, offline fixtures only."""

import importlib.util
import json
from pathlib import Path
import stat
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
import warnings
import zipfile

from math_gauge.benchmarks import identity
from math_gauge.catalog import digest_bytes, read_json, write_json
from math_gauge.harness import export_release_dataset, inspect_release_run
from math_gauge.harness_import import import_harness_submission
from math_gauge.reliability import inspect_reliability_run


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("math_gauge_release_artifacts", ROOT / "scripts/release.py")
release = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(release)


class ReleaseArtifactsTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.workspace = tempfile.TemporaryDirectory(prefix="math-gauge-artifact-fixture-")
        cls.addClassCleanup(cls.workspace.cleanup)
        cls.shared = Path(cls.workspace.name).resolve()
        cls.config = release.load_config()
        cls.plan, cls.suite = release.release_plan()
        cls.dataset_root = cls.shared / "exported-dataset"
        with patch("math_gauge.execution.invoke_conversation", side_effect=AssertionError("No model calls")):
            cls.dataset = export_release_dataset(cls.plan, cls.suite, cls.dataset_root)
        cls.bindings = release._input_bindings(ROOT, cls.dataset_root, cls.dataset, cls.suite)
        cls.wrappers = {
            "README.md": (ROOT / cls.config["readme"]).read_bytes(),
            "LICENSE": (ROOT / "LICENSE").read_bytes(),
            "THIRD_PARTY_NOTICES.md": (ROOT / cls.config["third_party_notices"]).read_bytes(),
        }
        # A synthetic source identity is explicit test data, never a published receipt.
        cls.source = {"repository": cls.config["repository"], "commit": "0" * 40, "tree": "1" * 40}
        cls.code_hashes = {"scripts/release.py": digest_bytes((ROOT / "scripts/release.py").read_bytes())}

    def setUp(self):
        self.workspace = tempfile.TemporaryDirectory(prefix="math-gauge-download-consumer-")
        self.addCleanup(self.workspace.cleanup)
        self.root = Path(self.workspace.name).resolve()
        self.archive = self.root / "math-gauge-tasks-v0.1.0.zip"
        self.package(self.archive)
        self.checksums = self.root / "SHA256SUMS"
        self.checksums.write_text(f"{digest_bytes(self.archive.read_bytes())}  {self.archive.name}\n", encoding="ascii")

    def package(self, archive):
        return release.package_dataset(
            self.dataset_root, archive, config=self.config, source=self.source,
            wrappers=self.wrappers, input_bindings=self.bindings,
            source_files_sha256=self.code_hashes, plan=self.plan, suite=self.suite)

    def controller(self, bundle, *arguments):
        result = subprocess.run(
            [sys.executable, "-I", "-S", str(bundle / "controller.py"), *arguments],
            cwd=self.root, env={"PYTHONPATH": str(self.root / "unavailable-repository")},
            capture_output=True, check=False)
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        return json.loads(result.stdout) if result.stdout else None

    def descriptor(self, directory, name, raw):
        (directory / name).write_bytes(raw)
        return {"path": name, "bytes": len(raw), "sha256": digest_bytes(raw)}

    def mutate(self, extra=None, replacements=None):
        changed = self.root / "changed.zip"
        with zipfile.ZipFile(self.archive) as source, zipfile.ZipFile(changed, "w") as target:
            for member in source.infolist():
                target.writestr(member, (replacements or {}).get(member.filename, source.read(member)))
            if extra is not None:
                target.writestr(*extra)
        return changed

    def regular(self, name):
        member = zipfile.ZipInfo("math-gauge-tasks-v0.1.0/" + name, release.ZIP_TIME)
        member.create_system = 3
        member.external_attr = (stat.S_IFREG | 0o644) << 16
        return member

    def test_archive_is_byte_deterministic_and_has_exact_candidate_allowlist(self):
        second = self.root / "same-again.zip"
        self.package(second)
        self.assertEqual(self.archive.read_bytes(), second.read_bytes())
        manifest = release.check_release_archive(
            self.archive, checksums=self.checksums, source_commit=self.source["commit"])
        self.assertEqual((manifest["case_count"], manifest["slot_count"]), (43, 177))
        self.assertEqual(manifest["suite"]["version"], "0.2.0")
        self.assertEqual(manifest["release_version"], "0.1.0")
        self.assertEqual(manifest["candidate_calls"], 0)
        self.assertFalse(manifest["runtime_frozen"])
        with zipfile.ZipFile(self.archive) as source:
            names = set(source.namelist())
            self.assertFalse(any(part in {".git", "evaluator", "tests", "verification"}
                                 or part.endswith(".evaluator")
                                 for name in names for part in Path(name).parts))
            self.assertFalse(any(Path(name).name in {"plan.json", "case.json", "reference.md", "rubric.json"}
                                 for name in names))
            self.assertEqual(source.read("math-gauge-tasks-v0.1.0/LICENSE"), (ROOT / "LICENSE").read_bytes())
            for binding in self.bindings:
                self.assertEqual(source.read("math-gauge-tasks-v0.1.0/" + binding["path"]),
                                 (ROOT / binding["source"]).read_bytes())
        self.assertEqual(len(self.bindings), 94)  # 43 complete tasks and all 51 declared attachments.
        self.assertNotIn("profile", self.dataset)
        self.assertNotIn("runtime", self.dataset)
        self.assertNotIn("case_index", self.dataset)
        self.assertNotIn("expected_truth", json.dumps(self.dataset))

    def test_recreated_evaluator_anchor_has_identical_bytes_after_sidecar_deletion(self):
        original = self.root / "original-plan.json"
        original.write_bytes(release._json_bytes(self.plan))
        original_raw = original.read_bytes()
        original.unlink()
        rebuilt, suite = release.release_plan()
        recovered = self.root / "recovered-plan.json"
        recovered.write_bytes(release._json_bytes(rebuilt))
        self.assertEqual(recovered.read_bytes(), original_raw)
        self.assertEqual(rebuilt["plan_sha256"], self.dataset["base_plan_sha256"])
        self.assertEqual(suite.sha256, self.suite.sha256)
        self.assertEqual(rebuilt["candidate_calls"], 0)
        self.assertIsNone(rebuilt["runtime"])

    def test_isolated_extracted_consumer_freezes_requests_returns_fixture_and_imports(self):
        release.check_release_archive(self.archive, checksums=self.checksums)
        consumer = self.root / "consumer"
        with zipfile.ZipFile(self.archive) as source:
            source.extractall(consumer)
        payload = consumer / "math-gauge-tasks-v0.1.0/payload"
        self.assertFalse(payload.is_relative_to(ROOT))
        checked = self.controller(payload, "check", "--bundle", str(payload))
        self.assertEqual(checked["dataset_sha256"], self.dataset["dataset_sha256"])
        self.assertFalse(checked["runtime_frozen"])
        runtime = read_json(payload / "runtime-template.json")
        runtime.update(model_label="offline-download-fixture", adapter_identity={"kind": "fixture"},
                       candidate_parameters={"model": "offline-fixture", "temperature": 0},
                       budget={"timeout_seconds": 2, "output_tokens": 1000})
        runtime_path = self.root / "runtime.json"
        write_json(runtime_path, runtime)
        raw_runtime = runtime_path.read_bytes()
        frozen = self.root / "frozen-run"
        self.controller(payload, "freeze", "--bundle", str(payload), "--runtime", str(runtime_path),
                        "--target", "neutral", "--out", str(frozen))
        second = self.root / "another-independent-run"
        self.controller(payload, "freeze", "--bundle", str(payload), "--runtime", str(runtime_path),
                        "--target", "neutral", "--out", str(second))
        first_manifest, second_manifest = inspect_release_run(frozen), inspect_release_run(second)
        self.assertNotEqual(first_manifest["run_id"], second_manifest["run_id"])
        self.assertNotEqual(first_manifest["run_sha256"], second_manifest["run_sha256"])
        self.assertEqual(first_manifest["dataset_sha256"], second_manifest["dataset_sha256"])
        self.assertEqual(runtime_path.read_bytes(), raw_runtime)
        for name in {"manifest.json", *self.dataset["files_sha256"]}:
            self.assertEqual((frozen / "dataset" / name).read_bytes(), (payload / name).read_bytes())
            self.assertEqual((second / "dataset" / name).read_bytes(), (payload / name).read_bytes())

        cid = "MG-GR002"
        slots = [cid + ":A1", cid + ":neutral:1", cid + ":neutral:2"]
        raw_replies = ["下载验收 fixture 原字节。\r\n".encode(),
                       "KEEP\r\n离线软件验收说明。\r\n".encode(),
                       "KEEP\r\n第二轮原字节。\r\n".encode()]
        source = self.root / "returned-submission"
        source.mkdir()
        submission_path = source / "submission.json"
        self.controller(frozen, "template", "--bundle", str(frozen), "--out", str(submission_path))
        submission = read_json(submission_path)
        self.assertTrue(submission["fixture_only"])
        self.assertEqual(submission["declared_external_calls"], 0)
        ancestors = {}
        for number, (sid, raw) in enumerate(zip(slots, raw_replies)):
            arguments = ["request", "--bundle", str(frozen), "--slot", sid]
            if ancestors:
                answers_path = self.root / f"answers-{number}.json"
                write_json(answers_path, ancestors)
                arguments += ["--answers", str(answers_path)]
            projected = self.controller(frozen, *arguments)
            self.assertEqual([m["role"] for m in projected["messages"]],
                             ["user"] + ["assistant", "user"] * number)
            self.assertIn(self.suite.request(self.suite.cases[cid])["task"],
                          projected["messages"][0]["content"])
            if number:
                self.assertEqual(projected["messages"][-2]["content"], raw_replies[number - 1].decode())
            submission["slots"].append({"slot_id": sid, "projected_request": projected,
                "attempts": [{"number": 1, "status": "ok", "projected_request_sha256": identity(projected),
                              "response": self.descriptor(source, f"response-{number}.md", raw),
                              "stderr": self.descriptor(source, f"stderr-{number}.txt", b""),
                              "usage": {}}]})
            ancestors[sid] = raw.decode()
        write_json(submission_path, submission)
        original_submission = submission_path.read_bytes()
        original_manifest = (frozen / "manifest.json").read_bytes()
        imported = self.root / "imported"
        with patch("math_gauge.execution.invoke_conversation", side_effect=AssertionError("No model calls")):
            imported_meta = import_harness_submission(frozen, submission_path, self.plan, self.suite, imported)
        self.assertEqual(imported_meta["candidate_calls"], 0)
        self.assertEqual((imported / "external-import/submission.json").read_bytes(), original_submission)
        self.assertEqual((frozen / "manifest.json").read_bytes(), original_manifest)
        inspected, records = inspect_reliability_run(imported)
        self.assertEqual(inspected["origin"], "external_import")
        self.assertTrue(inspected["fixture_only"])
        self.assertEqual(inspected["external_candidate_calls_declared"], 0)
        for sid, raw in zip(slots, raw_replies):
            self.assertEqual((imported / records[sid]["response_path"]).read_bytes(), raw)
        self.assertEqual(inspected["selected_slot_ids"], first_manifest["selected_slot_ids"])

    def test_unsafe_duplicate_and_unlisted_members_are_rejected_before_extraction(self):
        bad = self.regular("../escape.txt")
        with self.assertRaisesRegex(ValueError, "Unsafe"):
            release.check_release_archive(self.mutate(extra=(bad, b"escape")))
        bad = self.regular("payload/linked-input.md")
        bad.external_attr = (stat.S_IFLNK | 0o777) << 16
        with self.assertRaisesRegex(ValueError, "regular files"):
            release.check_release_archive(self.mutate(extra=(bad, b"/outside")))
        bad = self.regular("evaluator/plan.json")
        with self.assertRaisesRegex(ValueError, "Unlisted"):
            release.check_release_archive(self.mutate(extra=(bad, b'{"expected_truth":true}')))
        bad = self.regular("README.md")
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", UserWarning)
            with self.assertRaisesRegex(ValueError, "Duplicate"):
                release.check_release_archive(self.mutate(extra=(bad, b"duplicate")))
        bad = self.regular("Readme.md")
        with self.assertRaisesRegex(ValueError, "aliased"):
            release.check_release_archive(self.mutate(extra=(bad, b"case alias")))
        self.assertFalse((self.root / "escape.txt").exists())

    def test_source_checksums_content_and_original_input_bindings_are_enforced(self):
        with self.assertRaisesRegex(ValueError, "source commit"):
            release.check_release_archive(self.archive, source_commit="f" * 40)
        self.checksums.write_bytes(b"0" * 64 + b"  math-gauge-tasks-v0.1.0.zip\n")
        with self.assertRaisesRegex(ValueError, "checksum"):
            release.check_release_archive(self.archive, checksums=self.checksums)
        prefix = "math-gauge-tasks-v0.1.0/"
        with self.assertRaisesRegex(ValueError, "content changed"):
            release.check_release_archive(self.mutate(replacements={prefix + "README.md": b"tampered"}))
        with zipfile.ZipFile(self.archive) as source:
            manifest = json.loads(source.read(prefix + "RELEASE.json"))
        manifest["input_bindings"].pop()
        with self.assertRaisesRegex(ValueError, "Incomplete original input"):
            release.check_release_archive(self.mutate(replacements={prefix + "RELEASE.json": release._json_bytes(manifest)}))

    def test_non_utf8_member_names_and_false_counts_are_rejected(self):
        changed = self.mutate(extra=(self.regular("café.txt"), b"unlisted"))
        raw = bytearray(changed.read_bytes())
        # The added member is last in both ZIP header tables. Clear only its
        # UTF-8 declarations to create a real legacy-encoded filename fixture.
        for signature, displacement in ((b"PK\x03\x04", 6), (b"PK\x01\x02", 8)):
            offset = raw.rfind(signature) + displacement
            flags = int.from_bytes(raw[offset:offset + 2], "little")
            raw[offset:offset + 2] = (flags & ~0x800).to_bytes(2, "little")
        changed.write_bytes(raw)
        with self.assertRaisesRegex(ValueError, "must be UTF-8"):
            release.check_release_archive(changed)
        prefix = "math-gauge-tasks-v0.1.0/"
        with zipfile.ZipFile(self.archive) as source:
            manifest = json.loads(source.read(prefix + "RELEASE.json"))
        manifest["case_count"] = 42
        with self.assertRaisesRegex(ValueError, "fixed counts"):
            release.check_release_archive(self.mutate(replacements={prefix + "RELEASE.json": release._json_bytes(manifest)}))

    def test_publishable_build_requires_exact_clean_source(self):
        def git(*arguments):
            args = arguments[1:]
            if args == ("rev-parse", "--show-toplevel"):
                return str(ROOT)
            if args == ("rev-parse", "HEAD"):
                return self.source["commit"]
            if args == ("status", "--porcelain", "--untracked-files=all"):
                return " M scripts/release.py"
            raise AssertionError(args)

        with patch.object(release, "_git", side_effect=git):
            with self.assertRaisesRegex(ValueError, "clean source"):
                release.source_identity(ROOT, self.source["commit"], self.config)
            with self.assertRaisesRegex(ValueError, "checked-out revision"):
                release.source_identity(ROOT, "f" * 40, self.config)


if __name__ == "__main__":
    unittest.main()
