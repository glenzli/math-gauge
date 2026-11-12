"""Destructive maintenance must prove original-byte recoverability first."""
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from math_gauge import evidence_retention as evidence
from scripts import retain_evidence as maintenance


class RetainEvidenceMaintenanceTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name).resolve()
        self.root = self.base / "repository"
        self.root.mkdir()
        self.git("init", "-q")
        self.git("config", "user.email", "evidence@example.invalid")
        self.git("config", "user.name", "Evidence fixture")
        self.original = b"original final\ncomplete: uncertain\n"
        for name, raw in (("results/current/answer.md", self.original),
                          ("results/current/cache.bin", b"sealed cache\x00")):
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)
        (self.root / "results/current/cache.bin").chmod(0o755)
        self.git("add", "results")
        self.git("commit", "-qm", "Original fixture")
        self.revision = self.git("rev-parse", "HEAD").decode().strip()
        self.plan = self.base / "plan.json"
        self.entries = {}
        for name in ("results/current/answer.md", "results/current/cache.bin"):
            raw = (self.root / name).read_bytes()
            self.entries[name] = {"sha256": hashlib.sha256(raw).hexdigest(), "bytes": len(raw),
                                  "reason": "reviewed original", "mode": "cold"}
        self.write_plan()

    def git(self, *arguments):
        return subprocess.run(["git", "-C", str(self.root), *arguments], check=True,
                              capture_output=True).stdout

    def write_plan(self):
        self.plan.write_text(json.dumps({"files": self.entries}))

    def prepare(self):
        return maintenance.prepare(self.root, self.plan, self.revision)

    def test_prune_and_explicit_restore_keep_exact_bytes_modes_and_original_git(self):
        before = self.git("rev-parse", "HEAD")
        self.assertEqual(self.prepare()["files"], 2)
        result = maintenance.prune(self.root)
        self.assertEqual(result["pruned_files"], 2)
        self.assertFalse((self.root / "results/current/answer.md").exists())
        self.assertEqual(evidence.read_bytes(self.root / "results/current/answer.md"), self.original)
        destination = self.base / "restored"
        maintenance.restore(self.root, "results/current", destination)
        self.assertEqual((destination / "answer.md").read_bytes(), self.original)
        self.assertTrue((destination / "cache.bin").stat().st_mode & 0o111)
        self.assertEqual(self.git("rev-parse", "HEAD"), before)
        self.assertFalse((self.root / "results/current/cache.bin").exists())

    def test_uncommitted_original_cannot_be_pruned(self):
        name = "results/current/uncommitted.md"
        raw = b"only local copy"
        (self.root / name).write_bytes(raw)
        self.entries[name] = {"sha256": hashlib.sha256(raw).hexdigest(), "bytes": len(raw),
                              "reason": "must first preserve"}
        self.write_plan()
        with self.assertRaisesRegex(ValueError, "committed regular blob"):
            self.prepare()
        self.assertEqual((self.root / name).read_bytes(), raw)
        self.assertFalse((self.root / evidence.INDEX_PATH).exists())

    def test_wrong_committed_alias_fails_deep_check_without_deleting_original(self):
        self.entries["results/current/answer.md"]["git_path"] = "results/current/cache.bin"
        self.write_plan()
        with self.assertRaisesRegex(ValueError, "bytes changed"):
            self.prepare()
        self.assertEqual((self.root / "results/current/answer.md").read_bytes(), self.original)
        self.assertFalse((self.root / evidence.INDEX_PATH).exists())

    def test_all_present_files_verified_before_any_prune(self):
        self.prepare()
        path = self.root / "results/current/cache.bin"
        path.write_bytes(b"late modification")
        with self.assertRaisesRegex(ValueError, "Refusing to prune"):
            maintenance.prune(self.root)
        self.assertEqual((self.root / "results/current/answer.md").read_bytes(), self.original)
        self.assertEqual(path.read_bytes(), b"late modification")

    def test_symlink_cannot_replace_a_cold_original(self):
        self.prepare()
        path = self.root / "results/current/cache.bin"
        path.unlink()
        outside = self.base / "outside"
        outside.write_bytes(b"sealed cache\x00")
        path.symlink_to(outside)
        with self.assertRaisesRegex(ValueError, "symlink"):
            maintenance.prune(self.root)
        self.assertEqual(outside.read_bytes(), b"sealed cache\x00")
        self.assertTrue((self.root / "results/current/answer.md").exists())

    def test_registered_untracked_alias_is_readable_but_not_swept(self):
        name = "results/current/local-alias.md"
        (self.root / name).write_bytes(self.original)
        self.entries[name] = {**self.entries["results/current/answer.md"],
                              "git_path": "results/current/answer.md"}
        self.write_plan()
        self.prepare()
        self.assertEqual(maintenance.prune(self.root)["pruned_files"], 2)
        self.assertTrue((self.root / name).exists())
        self.assertEqual(evidence.read_bytes(self.root / name), self.original)

    def test_restore_requires_a_new_directory_outside_the_repository(self):
        self.prepare()
        for target in (self.root / "restored", self.base):
            with self.subTest(target=target), self.assertRaisesRegex(ValueError, "new directory outside"):
                maintenance.restore(self.root, "results/current", target)

    def test_source_code_is_not_an_evidence_retention_target(self):
        for value in ("math_gauge/scoring.py", "../results/raw", "results/../record.json",
                      "/results/raw", "results//raw", "results\\raw"):
            with self.subTest(value=value), self.assertRaises(ValueError):
                maintenance.relative(value)


if __name__ == "__main__":
    unittest.main()
