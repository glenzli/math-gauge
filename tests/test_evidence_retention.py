"""Local Git storage preserves original evaluator evidence and fails closed."""
import copy
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from math_gauge import evidence_retention as retained
from math_gauge.content_rates import verify_sources
from math_gauge.records import descriptor, evidence_bytes
from math_gauge.submission_evidence import _read as submission_read


class EvidenceRetentionTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.git("init", "-q")
        self.raw = "FULL\r\n尚未全部完成。\n".encode()
        self.logical = "results/source/raw/answer.md"
        self.source = "canonical/original.md"
        source = self.root / self.source
        source.parent.mkdir()
        source.write_bytes(self.raw)
        self.git("add", self.source)
        self.git("commit", "-q", "-m", "original evidence fixture")
        self.revision = self.git("rev-parse", "HEAD").decode().strip()
        self.blob = self.git("rev-parse", f"HEAD:{self.source}").decode().strip()
        self.sha = hashlib.sha256(self.raw).hexdigest()
        self.index = dict(schema=retained.SCHEMA, version=retained.VERSION,
            source_git_revision=self.revision,
            objects={self.sha: dict(bytes=len(self.raw), git_blob=self.blob, git_path=self.source)},
            files={self.logical: dict(sha256=self.sha, mode="100644", reason="same original bytes")})
        self.index_path = self.root / retained.INDEX_PATH
        self.write_index()

    def git(self, *args):
        env = os.environ.copy()
        for key in ("GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE", "GIT_OBJECT_DIRECTORY",
                    "GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_NAMESPACE"):
            env.pop(key, None)
        result = subprocess.run(["git", "-c", "core.hooksPath=/dev/null", "-c", "commit.gpgsign=false",
            "-c", "user.name=Evidence fixture", "-c", "user.email=fixture@example.invalid",
            "-c", "core.autocrlf=false", *args], cwd=self.root, env=env,
            capture_output=True, check=True)
        return result.stdout

    def write_index(self, value=None):
        self.index_path.parent.mkdir(parents=True, exist_ok=True)
        self.index_path.write_text(json.dumps(self.index if value is None else value))

    def file_descriptor(self):
        return dict(path="raw/answer.md", bytes=len(self.raw), sha256=self.sha)

    def retain_sources(self, values):
        """Create frozen canonical objects without creating the logical aliases."""
        for number, (logical, raw) in enumerate(values.items()):
            source = "canonical/extra-" + str(number)
            (self.root / source).write_bytes(raw)
            sha = hashlib.sha256(raw).hexdigest()
            self.git("add", source)
            blob = self.git("hash-object", source).decode().strip()
            self.index["objects"][sha] = dict(bytes=len(raw), git_blob=blob, git_path=source)
            self.index["files"][logical] = dict(sha256=sha, mode="100644", reason="original source")
        self.git("commit", "-q", "-m", "additional frozen evidence")
        self.index["source_git_revision"] = self.git("rev-parse", "HEAD").decode().strip()
        self.write_index()

    def test_exact_cold_bytes_and_shared_evidence_readers(self):
        path = self.root / self.logical
        self.assertFalse(path.exists())
        self.assertEqual(retained.read_bytes(path), self.raw)
        self.assertTrue(retained.exists(path))
        self.assertTrue(retained.is_file(path))
        archive = self.root / "results/source"
        self.assertEqual(evidence_bytes(archive, self.file_descriptor()), self.raw)
        self.assertEqual(submission_read(archive, self.file_descriptor()), self.raw)
        self.assertEqual(descriptor(archive, path), self.file_descriptor())
        self.assertFalse(path.exists(), "Reading cold evidence must not restore the worktree")

    def test_content_rates_keep_explicit_public_private_boundaries(self):
        private = self.root / "private-fixture"
        private.mkdir()
        source = dict(repository="public", path=self.logical, sha256=self.sha)
        review = dict(sources=[source], tasks=[])
        self.assertEqual(verify_sources(review, {"public": self.root, "private": private}), [source])
        source["repository"] = "private"
        with self.assertRaises(ValueError):
            verify_sources(review, {"public": self.root, "private": private})

    def test_hot_files_and_standalone_fixtures_need_no_git_or_index(self):
        self.index_path.unlink()
        source = self.root / self.source
        with patch.object(retained, "_git", side_effect=AssertionError("No Git needed")):
            self.assertEqual(retained.read_bytes(source), self.raw)
            self.assertFalse(retained.exists(self.root / self.logical))
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "plain.json"
            path.write_text('{"value": 7}')
            self.assertEqual(retained.read_json(path), {"value": 7})
            self.assertFalse(retained.is_file(path.parent))
            self.assertTrue(retained.exists(path.parent))

    def test_unknown_missing_path_never_uses_a_similar_hash_or_filename(self):
        path = self.root / "unlisted/answer.md"
        with patch.object(retained, "_git", side_effect=AssertionError("No guessed Git lookup")):
            self.assertFalse(retained.exists(path))
            self.assertFalse(retained.is_file(path))
            with self.assertRaises(FileNotFoundError):
                retained.read_bytes(path)

    def test_corrupt_hot_file_cannot_fall_back_to_valid_git(self):
        path = self.root / self.logical
        path.parent.mkdir(parents=True)
        path.write_bytes(self.raw + b"changed")
        with patch.object(retained, "_git", side_effect=AssertionError("Hot corruption cannot fall back")):
            with self.assertRaisesRegex(ValueError, "fallback is forbidden"):
                retained.read_bytes(path)

    def test_symlinks_and_nonregular_hot_paths_never_fall_back(self):
        path = self.root / self.logical
        path.parent.mkdir(parents=True)
        path.symlink_to(self.root / self.source)
        for operation in (retained.read_bytes, retained.exists, retained.is_file):
            with self.subTest(operation=operation.__name__), self.assertRaisesRegex(ValueError, "symlink"):
                operation(path)
        path.unlink()
        path.mkdir()
        with self.assertRaisesRegex(ValueError, "regular file"):
            retained.read_bytes(path)
        path.rmdir()
        path.parent.rmdir()
        path.parent.symlink_to(self.root / "absent-directory")
        with self.assertRaises(ValueError):
            retained.read_bytes(path)

    def test_bad_revision_blob_path_size_and_hash_are_rejected(self):
        changes = [
            lambda x: x.update(source_git_revision="0" * 40),
            lambda x: x.update(source_git_revision=self.git("rev-parse", "HEAD^{tree}").decode().strip()),
            lambda x: x["objects"][self.sha].update(git_blob="0" * 40),
            lambda x: x["objects"][self.sha].update(git_path="canonical/missing.md"),
            lambda x: x["objects"][self.sha].update(bytes=len(self.raw) + 1),
        ]
        for change in changes:
            value = copy.deepcopy(self.index)
            change(value)
            self.write_index(value)
            with self.subTest(value=value), self.assertRaises(ValueError):
                retained.read_bytes(self.root / self.logical)
        value = copy.deepcopy(self.index)
        other = "f" * 64
        value["objects"][other] = value["objects"].pop(self.sha)
        value["files"][self.logical]["sha256"] = other
        self.write_index(value)
        with self.assertRaisesRegex(ValueError, "bytes changed"):
            retained.read_bytes(self.root / self.logical)

    def test_unsafe_conflicting_and_case_aliased_index_paths_are_rejected(self):
        for name in ("../outside", "/absolute", "a/./b", "a//b", "a/../b", "a\\b", ".git/config"):
            value = copy.deepcopy(self.index)
            value["files"][name] = value["files"][self.logical]
            self.write_index(value)
            with self.subTest(name=name), self.assertRaises(ValueError):
                retained.read_bytes(self.root / self.logical)
        value = copy.deepcopy(self.index)
        value["files"][self.logical.upper()] = value["files"][self.logical]
        self.write_index(value)
        with self.assertRaisesRegex(ValueError, "aliased"):
            retained.read_bytes(self.root / self.logical)
        self.index_path.write_text('{"schema": 1, "schema": 2}')
        with self.assertRaisesRegex(ValueError, "Duplicate"):
            retained.read_bytes(self.root / self.logical)

    def test_git_symlink_mode_cannot_be_read_as_a_regular_blob(self):
        link = self.root / "canonical/link"
        link.symlink_to("original.md")
        self.git("add", "canonical/link")
        self.git("commit", "-q", "-m", "symlink fixture")
        value = copy.deepcopy(self.index)
        value["source_git_revision"] = self.git("rev-parse", "HEAD").decode().strip()
        value["objects"][self.sha].update(git_path="canonical/link",
            git_blob=self.git("rev-parse", "HEAD:canonical/link").decode().strip())
        self.write_index(value)
        with self.assertRaisesRegex(ValueError, "regular blob"):
            retained.read_bytes(self.root / self.logical)

    def test_missing_local_object_fails_and_git_reads_disable_network_hydration(self):
        real_run = subprocess.run
        calls = []
        def observed(*args, **kwargs):
            calls.append((args[0], kwargs.get("env", {})))
            return real_run(*args, **kwargs)
        object_path = self.root / ".git/objects" / self.blob[:2] / self.blob[2:]
        object_path.unlink()
        with patch.object(retained.subprocess, "run", side_effect=observed):
            with self.assertRaisesRegex(ValueError, "no network recovery"):
                retained.read_bytes(self.root / self.logical)
        self.assertTrue(calls)
        for argv, env in calls:
            self.assertIn("--no-lazy-fetch", argv)
            self.assertIn("--no-replace-objects", argv)
            self.assertNotIn("fetch", argv)
            self.assertEqual(env["GIT_NO_LAZY_FETCH"], "1")
            self.assertEqual(env["GIT_TERMINAL_PROMPT"], "0")

    def test_logical_inventory_aliases_and_temporary_tree_are_lossless(self):
        alias = "results/source/second/original.md"
        self.index["files"][alias] = dict(sha256=self.sha, mode="100755", reason="same bytes, original mode")
        self.write_index()
        root = self.root / "results/source"
        self.assertTrue(retained.exists(root))
        self.assertFalse(retained.is_file(root))
        self.assertEqual(list(retained.iter_files(root)), sorted([self.root / self.logical, self.root / alias]))
        self.assertIn(self.root / alias, list(retained.iter_files(self.root)))
        with retained.materialize_tree(root) as restored:
            self.assertEqual((restored / "raw/answer.md").read_bytes(), self.raw)
            executable = restored / "second/original.md"
            self.assertEqual(executable.read_bytes(), self.raw)
            self.assertTrue(executable.stat().st_mode & stat.S_IXUSR)
            self.assertFalse(executable.stat().st_mode & 0o222)
            target = restored
        self.assertFalse(target.exists())
        self.assertFalse(root.exists())

    def test_existing_hot_extra_files_remain_visible_and_temp_cleanup_survives_failure(self):
        root = self.root / "results/source"
        root.mkdir(parents=True)
        extra = root / "extra.json"
        extra.write_text('{"source": true}')
        self.assertIn(extra, list(retained.iter_files(root)))
        with self.assertRaisesRegex(RuntimeError, "review failed"):
            with retained.materialize_tree(root) as temporary:
                target = temporary
                self.assertEqual(retained.read_json(temporary / "extra.json"), {"source": True})
                raise RuntimeError("review failed")
        self.assertFalse(target.exists())
        self.assertTrue(extra.is_file())

    def test_repository_validation_counts_aliases_and_checks_git_even_when_hot(self):
        alias = "results/source/second.md"
        self.index["files"][alias] = dict(sha256=self.sha, mode="100644", reason="duplicate logical source")
        self.write_index()
        path = self.root / self.logical
        path.parent.mkdir(parents=True)
        path.write_bytes(self.raw)
        summary = retained.validate_repository(self.root, deep=True)
        self.assertEqual((summary["files"], summary["unique_objects"],
                          summary["logical_bytes"], summary["unique_bytes"]),
                         (2, 1, 2 * len(self.raw), len(self.raw)))
        # A previous successful read must not mask a now-missing local object.
        retained.read_bytes(self.root / alias)
        object_path = self.root / ".git/objects" / self.blob[:2] / self.blob[2:]
        object_path.unlink()
        self.assertEqual(retained.read_bytes(path), self.raw)
        with self.assertRaisesRegex(ValueError, "no network recovery"):
            retained.validate_repository(self.root, deep=True)
        self.index_path.unlink()
        self.assertFalse(retained.validate_repository(self.root)["present"])

    def test_source_links_use_fixed_git_identity_for_cold_and_hot_aliases(self):
        expected = dict(repository_root=str(self.root), revision=self.revision,
                        git_path=self.source, sha256=self.sha, bytes=len(self.raw))
        path = self.root / self.logical
        self.assertEqual(retained.source_location(path), expected)
        path.parent.mkdir(parents=True)
        path.write_bytes(self.raw)
        self.assertEqual(retained.source_location(path), expected)
        self.assertEqual(retained.source_location(self.root / self.source),
                         dict(expected, revision=None))
        path.write_bytes(b"damaged")
        with self.assertRaisesRegex(ValueError, "fallback is forbidden"):
            retained.source_location(path)

    def test_cost_collection_reads_cold_native_stream_and_usage_without_restoring_it(self):
        from math_gauge.costs import source_descriptor, verify_source
        from scripts.collect_cost_reference import Collector
        prefix = "results/cost-fixture"
        raw = dict(input_tokens=12, output_tokens=20, cache_read_input_tokens=30,
                   cache_creation_input_tokens=5)
        self.retain_sources({prefix + "/metadata.json": json.dumps(dict(session_id="native")).encode(),
            prefix + "/usage.json": json.dumps(raw).encode(),
            prefix + "/stdout.jsonl": json.dumps(dict(type="result", usage=raw)).encode() + b"\n"})
        collector = Collector(self.root, self.root, self.root / "out")
        value = collector.native("kimi-3.1-pro-max", "T000:A1", self.root / prefix / "metadata.json",
                                 expected_answer=self.sha)
        self.assertEqual(value["state"], "complete")
        self.assertEqual(value["units"][0]["usage"]["input_tokens"], 12)
        path = self.root / prefix / "stdout.jsonl"
        verify_source(self.root, source_descriptor(path, self.root))
        self.assertFalse(path.exists())

    def test_cost_collection_enumerates_cold_timeout_transcripts_without_inherited_turns(self):
        from scripts.collect_cost_reference import Collector
        prefix = "results/cost-fixture"
        def message(mid, count, session="current"):
            return dict(type="assistant", sessionId=session, message=dict(id=mid,
                usage=dict(input_tokens=1, output_tokens=count, cache_read_input_tokens=0,
                           cache_creation_input_tokens=0)))
        events = [message("one", 4), message("one", 6), message("parent", 100, "parent")]
        self.retain_sources({prefix + "/metadata.json": b'{"session_id":"current"}',
            prefix + "/transcript/main.jsonl": b"\n".join(json.dumps(item).encode() for item in events)})
        collector = Collector(self.root, self.root, self.root / "out")
        value = collector.native("glm-5.3-max", "T000:A1", self.root / prefix / "metadata.json",
                                 expected_answer=None)
        self.assertEqual(value["state"], "partial")
        self.assertEqual(len(value["units"]), 1)
        self.assertEqual(value["units"][0]["usage"]["output_tokens"], 6)
        self.assertFalse((self.root / prefix).exists())

    def test_nested_git_payload_requires_registration_and_never_owns_the_repository(self):
        logical = "archive/sealed/.git/config"
        self.retain_sources({logical: b"[core]\nrepositoryformatversion = 0\n"})
        nested = self.root / "archive/sealed/.git"
        nested.mkdir(parents=True)
        (nested / "unregistered").write_bytes(b"not retained")
        self.assertEqual(retained.read_bytes(self.root / logical),
                         b"[core]\nrepositoryformatversion = 0\n")
        with self.assertRaisesRegex(ValueError, "explicit retention"):
            retained.read_bytes(nested / "unregistered")
        self.assertEqual(list(retained.iter_files(nested)), [self.root / logical])
        self.assertEqual(retained.source_location(self.root / logical)["repository_root"], str(self.root))
        with retained.materialize_tree(nested.parent) as restored:
            self.assertEqual((restored / ".git/config").read_bytes(),
                             b"[core]\nrepositoryformatversion = 0\n")
            self.assertFalse((restored / ".git/unregistered").exists())
        for operation in (retained.read_bytes, retained.is_file, retained.exists, retained.iter_files):
            with self.subTest(operation=operation.__name__), self.assertRaisesRegex(ValueError, "live Git"):
                value = operation(self.root / ".git/config")
                if operation is retained.iter_files:
                    list(value)

    def test_retrospective_import_inspection_materializes_only_a_disposable_bundle(self):
        from test_harness_import import HarnessImportTests, CID
        from math_gauge.reliability import inspect_reliability_run
        fixture = HarnessImportTests()
        fixture.setUpClass()
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        fixture.submission({CID + ":A1": "original imported mathematical reply"})
        fixture.import_run()
        target = self.root / "results/import-fixture"
        shutil.copytree(fixture.output, target)
        source = target / "external-import/submission.json"
        logical = source.relative_to(self.root).as_posix()
        self.retain_sources({logical: source.read_bytes()})
        source.unlink()
        meta, records = inspect_reliability_run(target)
        self.assertEqual(meta["candidate_calls"], 0)
        self.assertIn(CID + ":A1", records)
        self.assertFalse(source.exists())


if __name__ == "__main__":
    unittest.main()
