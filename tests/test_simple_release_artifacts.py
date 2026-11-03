"""Flat release ZIP boundary and relocated return workflow; synthetic replies only."""

import copy
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

from benchmark_fixtures import compact_release_root

from math_gauge.catalog import candidate_message, digest_bytes, read_json, write_json
from math_gauge.harness import (export_simple_release_dataset, inspect_release_dataset, inspect_release_run,
                                make_release_anchor)
from math_gauge.reliability import inspect_reliability_run
from math_gauge.release_projection import project_candidate_text, project_candidate_request
from math_gauge.harness_answers import issue_answer_request, record_answer_attempt, skip_answer_slot, pack_answer_archive
from math_gauge.harness import freeze_release_runtime, release_candidate_request
from math_gauge.harness_import import import_answer_archive


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("math_gauge_simple_release", ROOT / "scripts/release.py")
release = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(release)
PREFIX = "benchmark-v0.4.0/"


class SimpleReleaseArtifactsTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.workspace = tempfile.TemporaryDirectory(prefix="math-gauge-simple-release-fixture-")
        cls.addClassCleanup(cls.workspace.cleanup)
        cls.shared = Path(cls.workspace.name).resolve()
        cls.source_root = compact_release_root()
        original_load_config, original_git = release.load_config, release._git

        def fixture_config(root=cls.source_root, version="0.4.0"):
            return original_load_config(root, version)

        def fixture_git(root, *arguments):
            if Path(root).resolve() != cls.source_root:
                return original_git(root, *arguments)
            # Read Git metadata through a temporary work-tree view. No index,
            # worktree registration, commit or repository content is changed.
            result = subprocess.run(["git", "-C", str(ROOT),
                "--work-tree=" + str(cls.source_root), *arguments],
                check=True, capture_output=True)
            return result.stdout.decode("utf-8").strip()

        for name, replacement in (("load_config", fixture_config), ("_git", fixture_git)):
            replacement_patch = patch.object(release, name, replacement)
            replacement_patch.start()
            cls.addClassCleanup(replacement_patch.stop)
        cls.config = release.load_config()
        cls.plan, cls.suite = release.release_plan(root=cls.source_root, version="0.4.0")
        cls.bindings = release._simple_input_bindings(cls.source_root, cls.suite,
                                                     projection=cls.plan.get("candidate_projection"))
        hashes = release._release_source_files(cls.source_root, cls.config, cls.bindings)
        source = release._preview_source(cls.source_root, cls.config)
        source["source_sha256"] = release._source_digest(hashes, cls.plan["suite"], cls.plan["plan_sha256"])
        cls.provenance = {"schema": release.PROVENANCE_SCHEMA, "kind": "local_preview", "source": source,
                          "input_bindings": cls.bindings, "source_files_sha256": hashes}
        cls.dataset_root = cls.shared / "dataset"
        with patch("math_gauge.execution.invoke_conversation", side_effect=AssertionError("No model calls")):
            cls.dataset = export_simple_release_dataset(
                cls.plan, cls.suite, cls.dataset_root, release_version="0.4.0",
                readme=(cls.source_root / cls.config["readme"]).read_bytes(),
                extra_files={"LICENSE": (cls.source_root / "LICENSE").read_bytes(),
                             "THIRD_PARTY_NOTICES.md": (cls.source_root / cls.config["third_party_notices"]).read_bytes()},
                release_provenance=release._public_provenance(cls.provenance, cls.plan))

    def setUp(self):
        self.workspace = tempfile.TemporaryDirectory(prefix="math-gauge-simple-download-")
        self.addCleanup(self.workspace.cleanup)
        self.root = Path(self.workspace.name).resolve()
        self.archive = self.root / "benchmark-v0.4.0.zip"
        release.package_simple_dataset(self.dataset_root, self.archive, config=self.config,
                                       plan=self.plan, suite=self.suite)
        self.checksums = self.root / "SHA256SUMS"
        self.checksums.write_bytes(f"{digest_bytes(self.archive.read_bytes())}  {self.archive.name}\n".encode("ascii"))

    def regular(self, name):
        member = zipfile.ZipInfo(PREFIX + name, release.ZIP_TIME)
        member.create_system = 3
        member.external_attr = (stat.S_IFREG | 0o644) << 16
        return member

    def mutate(self, *, extra=None, replacements=None, omit=None):
        changed = self.root / "changed.zip"
        with zipfile.ZipFile(self.archive) as original, zipfile.ZipFile(changed, "w") as target:
            for member in original.infolist():
                if member.filename != omit:
                    target.writestr(member, (replacements or {}).get(member.filename, original.read(member)))
            if extra is not None:
                target.writestr(*extra)
        return changed

    def changed_manifest(self, update):
        manifest = copy.deepcopy(self.dataset)
        update(manifest)
        return self.mutate(replacements={PREFIX + "manifest.json": release._json_bytes(manifest)})

    def helper(self, helper, *arguments):
        result = subprocess.run([sys.executable, "-I", "-S", str(helper), *arguments],
                                cwd=self.root, env={"PYTHONPATH": str(self.root / "no-repository")},
                                capture_output=True, check=False)
        self.assertEqual(result.returncode, 0, result.stderr.decode("utf-8"))
        return json.loads(result.stdout) if result.stdout.strip() else None

    def test_single_guide_exact_input_bytes_and_deterministic_archive(self):
        second = self.root / "same-inputs.zip"
        release.package_simple_dataset(self.dataset_root, second, config=self.config,
                                       plan=self.plan, suite=self.suite)
        self.assertEqual(second.read_bytes(), self.archive.read_bytes())
        checked = release.check_release_archive(self.archive, checksums=self.checksums)
        self.assertEqual(checked["release_version"], checked["suite"]["version"])
        self.assertEqual((len(checked["cases"]), checked["exported_slots"]), (36, 84))
        self.assertEqual(checked["release_provenance"]["kind"], "local_preview")
        self.assertNotIn("source", checked["release_provenance"])
        self.assertEqual(len(self.bindings), sum(1 + len(case["solver_files"])
                                              for case in self.suite.cases.values()))
        with zipfile.ZipFile(self.archive) as original:
            names = set(original.namelist())
            expected = {PREFIX + name for name in {"manifest.json", *self.dataset["files_sha256"]}}
            self.assertEqual(names, expected)
            self.assertFalse(any("payload" in Path(name).parts for name in names))
            self.assertFalse(any(Path(name).name in {"CONTROLLER.md", "controller.py", "request.json",
                "message.txt", "instruction.txt", "RELEASE.json", "plan.json", "case.json",
                "reference.md", "rubric.json", "runtime-template.json"} for name in names))
            for binding in self.bindings:
                self.assertEqual(original.read(PREFIX + binding["path"]),
                                 project_candidate_text(Path(binding["path"]).name,
                                     (self.source_root / binding["source"]).read_text()).encode("utf-8"))
            for name in names:
                raw = original.read(name).lower()
                self.assertNotIn(b"math-gauge", raw, name)
                self.assertNotIn(b"mathgauge", raw, name)
                self.assertNotIn(b"math gauge", raw, name)
                self.assertNotIn(b"github.com", raw, name)
        self.assertNotIn("expected_truth", json.dumps(self.dataset))
        self.assertNotIn("profile", self.dataset)
        self.assertNotIn("runtime", self.dataset)

    def test_historical_fixture_keeps_current_suite_release_guard(self):
        self.assertNotEqual(self.suite.root, ROOT / "cases")
        self.assertEqual(self.suite.metadata["version"], "0.4.0")
        self.assertEqual(len(self.suite.cases), 36)
        with self.assertRaisesRegex(ValueError, "Release suite changed"):
            release.release_plan(root=ROOT, version="0.4.0")

    def test_traversal_windows_aliases_symlinks_duplicates_and_unlisted_members(self):
        for name in ("../escape.txt", "cases/../../escape.txt", "C:/escape.txt", "CON.txt", "CON .txt", "COM¹", "trailing. ",
                     "files\\escape.txt", "case:stream", "case/?.txt"):
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, "Unsafe"):
                release.check_release_archive(self.mutate(extra=(self.regular(name), b"unsafe")))
        symlink = self.regular("cases/link")
        symlink.external_attr = (stat.S_IFLNK | 0o777) << 16
        with self.assertRaisesRegex(ValueError, "regular files"):
            release.check_release_archive(self.mutate(extra=(symlink, b"/outside")))
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", UserWarning)
            with self.assertRaisesRegex(ValueError, "Duplicate"):
                release.check_release_archive(self.mutate(extra=(self.regular("README.md"), b"duplicate")))
        with self.assertRaisesRegex(ValueError, "aliased"):
            release.check_release_archive(self.mutate(extra=(self.regular("Readme.md"), b"alias")))
        with self.assertRaisesRegex(ValueError, "Unlisted"):
            release.check_release_archive(self.mutate(extra=(self.regular("evaluator/plan.json"), b"{}")))
        self.assertFalse((self.root / "escape.txt").exists())

    def test_tampering_missing_fields_wrong_version_and_input_bindings_fail(self):
        with self.assertRaisesRegex(ValueError, "checksum"):
            self.checksums.write_text("0" * 64 + "  " + self.archive.name + "\n", encoding="ascii")
            release.check_release_archive(self.archive, checksums=self.checksums)
        with self.assertRaisesRegex(ValueError, "expected version"):
            release.check_release_archive(self.archive, version="0.1.0")
        with self.assertRaisesRegex(ValueError, "version must equal"):
            release.check_release_archive(self.changed_manifest(lambda value: value.update(release_version="0.5.0")))
        with self.assertRaises(ValueError):
            release.check_release_archive(self.changed_manifest(lambda value: value.pop("suite")))
        with self.assertRaisesRegex(ValueError, "provenance"):
            release.check_release_archive(self.changed_manifest(lambda value: value.pop("release_provenance")))
        with self.assertRaisesRegex(ValueError, "Unlisted or missing"):
            release.check_release_archive(self.mutate(omit=PREFIX + "README.md"))
        with self.assertRaisesRegex(ValueError, "content changed"):
            release.check_release_archive(self.mutate(replacements={PREFIX + self.bindings[0]["path"]: b"edited"}))
        with self.assertRaisesRegex(ValueError, "Incomplete original"):
            release.check_release_archive(self.changed_manifest(
                lambda value: value["release_provenance"]["input_bindings"].pop()))
        with self.assertRaises(ValueError):
            release.check_release_archive(self.changed_manifest(
                lambda value: value["release_provenance"].update(source_sha256="0" * 64)))

    def test_preview_cannot_claim_the_parent_as_exact_source_commit(self):
        with self.assertRaisesRegex(ValueError, "parent commit"):
            release.check_release_archive(self.archive,
                source_commit=self.provenance["source"]["parent_commit"])
        with self.assertRaisesRegex(ValueError, "actual source hashes"):
            release.build_release(self.root / "invalid", local_preview=True,
                                  source_commit=self.provenance["source"]["parent_commit"],
                                  root=self.source_root, version="0.4.0")
        self.assertFalse((self.root / "invalid").exists())

    def test_new_config_rejects_release_and_dataset_version_divergence(self):
        root = self.root / "source-fixture"
        config_path = root / "releases/v0.4.0/config.json"
        config_path.parent.mkdir(parents=True)
        config = dict(self.config, suite_version="0.1.0")
        config_path.write_bytes(release._json_bytes(config))
        with self.assertRaisesRegex(ValueError, "Release version must equal"):
            release.load_config(root)

    def test_local_preview_build_repeats_bytes_and_keeps_evaluator_plan_outside(self):
        first = release.build_release(self.root / "preview-one", local_preview=True,
                                      root=self.source_root, version="0.4.0")
        second = release.build_release(self.root / "preview-two", local_preview=True,
                                       root=self.source_root, version="0.4.0")
        self.assertEqual(Path(first["archive"]).read_bytes(), Path(second["archive"]).read_bytes())
        self.assertEqual(first["source"], second["source"])
        self.assertEqual(first["provenance_kind"], "local_preview")
        self.assertEqual(first["candidate_calls"], 0)
        original_plan = Path(first["evaluator_plan"]).read_bytes()
        Path(first["evaluator_plan"]).unlink()
        recovered_path = self.root / "recovered-evaluator-plan.json"
        release.recover_evaluator_plan(recovered_path, local_preview=True,
                                      root=self.source_root, version="0.4.0")
        self.assertEqual(recovered_path.read_bytes(), original_plan)
        recovered = read_json(recovered_path)
        self.assertEqual(recovered["schema"], "math-gauge.release-anchor/v1")
        self.assertEqual(recovered["expected_dataset_sha256"], first["dataset_sha256"])
        self.assertEqual(recovered["base_plan"]["plan_sha256"], first["base_plan_sha256"])
        with zipfile.ZipFile(first["archive"]) as original:
            self.assertFalse(any(Path(name).name in {"plan.json", "evaluator-plan.json"}
                                 for name in original.namelist()))

    def test_source_drift_removes_partial_build_without_claiming_the_parent_identity(self):
        output = self.root / "source-drift-preview"
        original = release._release_source_files
        calls = 0

        def changed_snapshot(*arguments):
            nonlocal calls
            calls += 1
            hashes = original(*arguments)
            if calls > 1:
                hashes["math_gauge/harness.py"] = "0" * 64
            return hashes

        with patch.object(release, "_release_source_files", side_effect=changed_snapshot):
            with self.assertRaisesRegex(ValueError, "Source changed while building"):
                release.build_release(output, local_preview=True, root=self.source_root, version="0.4.0")
        self.assertFalse(output.exists())

    def test_extracted_helper_records_raw_attempts_packs_one_fixture_archive_and_imports(self):
        release.check_release_archive(self.archive)
        consumer = self.root / "relocated"
        with zipfile.ZipFile(self.archive) as original:
            original.extractall(consumer)
        dataset = consumer / PREFIX.rstrip("/")
        helper = dataset / "tools/benchmark.py"
        checked = self.helper(helper, "check")
        self.assertEqual(checked["dataset_sha256"], self.dataset["dataset_sha256"])
        runtime_path = self.root / "runtime.json"
        write_json(runtime_path, {"model_label": "synthetic-release-fixture",
            "adapter_identity": {"kind": "fixture"}, "candidate_parameters": {"model": "offline-fixture"},
            "budget": {"timeout_seconds": 2, "output_tokens": 1000}, "fresh_context": True})
        runtime_raw = runtime_path.read_bytes()
        run = self.root / "prepared-run"
        responses = self.root / "responses"
        self.helper(helper, "prepare", "--runtime", str(runtime_path), "--target", "neutral", "--out", str(run))
        frozen = inspect_release_run(run)
        self.assertEqual(runtime_raw, runtime_path.read_bytes())
        self.assertEqual(frozen["dataset_sha256"], self.dataset["dataset_sha256"])
        self.assertEqual(inspect_release_dataset(run / "dataset"), self.dataset)
        run_helper = run / "tools/benchmark.py"
        slots = ["MG-GR002:A1", "MG-GR002:neutral:1", "MG-GR002:neutral:2"]
        replies = ["合成软件验收初答。\r\n".encode(), "KEEP\r\n合成软件验收一。\r\n".encode(),
                   "KEEP\r\n合成软件验收二。\r\n".encode()]
        reply_by_slot = dict(zip(slots, replies))
        for sid in frozen["selected_slot_ids"]:
            if sid not in reply_by_slot:
                if sid.endswith(":A1"):
                    self.helper(run_helper, "skip", "--run", str(run), "--responses", str(responses),
                                "--slot", sid, "--reason", "Synthetic fixture covers one branch only")
                continue
            index, raw = slots.index(sid), reply_by_slot[sid]
            request_path = self.root / f"request-{index}.json"
            self.helper(run_helper, "request", "--run", str(run), "--responses", str(responses),
                        "--slot", sid, "--out", str(request_path))
            request = read_json(request_path)
            self.assertEqual([message["role"] for message in request["messages"]],
                             ["user"] + ["assistant", "user"] * index)
            self.assertEqual(request["messages"][0]["content"],
                             candidate_message(project_candidate_request(self.suite.request(self.suite.cases["MG-GR002"]))))
            if index:
                self.assertEqual(request["messages"][-2]["content"], replies[index - 1].decode())
            response_path = self.root / f"raw-{index}.md"
            response_path.write_bytes(raw)
            if index == 0:
                failed = self.root / "failed-response.txt"
                failed.write_bytes(b"\xff\xfe\r\n")
                self.helper(run_helper, "record", "--run", str(run), "--responses", str(responses),
                            "--slot", sid, "--request", str(request_path),
                            "--response", str(failed), "--status", "transient_error")
                retry_path = self.root / "retry-request.json"
                self.helper(run_helper, "request", "--run", str(run), "--responses", str(responses),
                            "--slot", sid, "--out", str(retry_path))
                self.assertEqual(read_json(retry_path), request)
                request_path = retry_path
            self.helper(run_helper, "record", "--run", str(run), "--responses", str(responses),
                        "--slot", sid, "--request", str(request_path),
                        "--response", str(response_path), "--status", "ok")
        answer_archive = self.root / "answers.zip"
        self.helper(run_helper, "pack", "--run", str(run), "--responses", str(responses), "--out", str(answer_archive))
        plan_path = self.root / "evaluator-plan.json"
        anchor = make_release_anchor(self.plan, self.dataset)
        write_json(plan_path, anchor)
        wrong_plan_path = self.root / "wrong-evaluator-plan.json"
        write_json(wrong_plan_path, dict(anchor, expected_dataset_sha256="0" * 64))
        rejected = self.root / "wrong-dataset-import"
        command = subprocess.run([sys.executable, "-m", "math_gauge", "benchmark-import", "--input", str(answer_archive),
                                  "--plan", str(wrong_plan_path), "--suite", str(self.suite.root),
                                  "--out", str(rejected)],
                                 cwd=ROOT, capture_output=True, check=False)
        self.assertNotEqual(command.returncode, 0)
        self.assertFalse(rejected.exists())
        imported = self.root / "imported-fixture"
        command = subprocess.run([sys.executable, "-m", "math_gauge", "benchmark-import", "--input", str(answer_archive),
                                  "--plan", str(plan_path), "--suite", str(self.suite.root),
                                  "--out", str(imported)],
                                 cwd=ROOT, capture_output=True, check=False)
        self.assertEqual(command.returncode, 0, command.stderr.decode())
        metadata, records = inspect_reliability_run(imported)
        self.assertTrue(metadata["fixture_only"])
        self.assertEqual(metadata["external_candidate_calls_declared"], 0)
        for sid, raw in zip(slots, replies):
            self.assertEqual((imported / records[sid]["response_path"]).read_bytes(), raw)
            actual = read_json(imported / "external-import/submission.json")
            row = next(r for r in actual["slots"] if r["slot_id"] == sid)
            self.assertEqual(row["projected_request"]["schema"], "benchmark.conversation/v1")
            self.assertEqual(records[sid]["attempts"][-1]["request_normalization"],
                             "neutral-transport-schema/v1")
        self.assertEqual(len(records[slots[0]]["attempts"]), 2)
        self.assertEqual((imported / records[slots[0]]["attempts"][0]["response_path"]).read_bytes(),
                         b"\xff\xfe\r\n")

    def test_neutral_local_tool_runtime_preserves_actual_messages_and_answer_namespace(self):
        run, responses = self.root / "local-run", self.root / "local-responses"
        runtime = {"model_label": "synthetic-neutral-tools", "adapter_identity": {"kind": "fixture"},
                   "candidate_parameters": {"model": "synthetic-no-calls"},
                   "budget": {"timeout_seconds": 2}, "fresh_context": True,
                   "execution_track": "benchmark.local-tools-no-search/v1"}
        frozen = freeze_release_runtime(self.dataset_root, runtime, run, targets=["neutral"])
        sid, followup = "MG-GR002:A1", "MG-GR002:neutral:1"
        for selected in frozen["selected_slot_ids"]:
            if selected == sid:
                path = self.root / "actual-request.json"
                actual = issue_answer_request(run, responses, sid, path)
                raw = b"Synthetic fixture only.\r\nnamespace TaskInputs.Sample\r\nend TaskInputs.Sample\r\n"
                answer = self.root / "actual-answer.md"
                answer.write_bytes(raw)
                record_answer_attempt(run, responses, sid, path, answer, status="timeout",
                                      metadata_path=None)
            elif selected == followup:
                path = self.root / "followup-request.json"
                request = issue_answer_request(run, responses, followup, path)
                self.assertTrue(request["messages"][-1]["content"].endswith("本轮不得访问网络或进行联网检索。\n"))
                self.assertEqual(request["messages"][-2]["content"], raw.decode("utf-8"))
                answer.write_bytes(b"KEEP\nSynthetic fixture only.\n")
                record_answer_attempt(run, responses, followup, path, answer, status="ok")
                break
            elif selected.endswith(":A1"):
                skip_answer_slot(run, responses, selected, "Synthetic fixture covers one branch")
        with self.assertRaisesRegex(ValueError, "order"):
            issue_answer_request(run, responses, sid, self.root / "forbidden-rerun.json")
        archive = self.root / "neutral-answers.zip"
        pack_answer_archive(run, responses, archive)
        imported = self.root / "neutral-imported"
        with patch("subprocess.Popen", side_effect=AssertionError("Downloaded code executed")):
            import_answer_archive(archive, make_release_anchor(self.plan, self.dataset), self.suite, imported)
        metadata, records = inspect_reliability_run(imported)
        self.assertEqual((imported / records[sid]["response_path"]).read_bytes(), raw)
        self.assertEqual(read_json(imported / "external-import/submission.json")["slots"][0]["projected_request"], actual)
        self.assertEqual(records[sid]["attempts"][0]["source_projected_request_sha256"],
                         records[sid]["attempts"][0]["external_source"]["projected_request_sha256"])
        self.assertEqual(metadata["plan"]["candidate_projection"], self.plan["candidate_projection"])
        self.assertFalse(metadata["external_origin_verified"])


if __name__ == "__main__":
    unittest.main()
