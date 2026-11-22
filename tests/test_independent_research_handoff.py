"""Exercise the distributed offline operator flow with synthetic inputs only."""
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch
from zipfile import ZipFile

from math_gauge import independent_research_handoff as handoff
from scripts import export_independent_research_handoff as exporter
import test_taste_v130 as taste_fixture


class IndependentResearchHandoffTest(unittest.TestCase):
    def setUp(self):
        fixture = taste_fixture.ProtocolFixture("runTest")
        self.addCleanup(fixture.doCleanups)
        fixture.setUp()
        self.root = fixture.root
        self.case = fixture.case
        self.reg = fixture.reg
        self.registration = fixture.registration
        for name in ("second", "third", "fourth"):
            path = self.case / f"packet/figures/{name}.png"
            path.write_bytes(f"Synthetic {name} figure bytes".encode())
            self.reg["packet"].append(taste_fixture.descriptor(path, self.case))
        taste_fixture.write_json(self.registration, self.reg)
        evaluator = self.case / "evaluator"
        (evaluator / "extra.md").write_bytes(b"EVALUATOR-EXTRA-SENTINEL")
        (self.case / "candidate/R4.md").write_bytes(b"UNREGISTERED-FOURTH-ROUND-SENTINEL")
        self.receipt = exporter.build(self.registration, self.root / "built")
        self.archive = self.root / "built" / exporter.ARCHIVE_NAME
        self.bundle = self.root / "operator"
        with ZipFile(self.archive) as archive:
            archive.extractall(self.bundle)
        self.state = self.root / "state"
        self.session = "native-fixture-session"

    def cli(self, *args, ok=True):
        result = subprocess.run([sys.executable, "research_handoff.py", *map(str, args)],
                                cwd=self.bundle, text=True, capture_output=True,
                                env={**os.environ, "PYTHONPATH": ""})
        if ok:
            self.assertEqual(result.returncode, 0, result.stderr)
            return json.loads(result.stdout)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        return result.stderr

    def capture(self, round_id, **changes):
        capture = self.root / f"capture-{round_id}"
        capture.mkdir(exist_ok=True)
        raw = f"Full synthetic first {round_id} \u03bb\r\n  trailing whitespace  \r\n".encode()
        (capture / "native-final.md").write_bytes(raw)
        (capture / "native-events.ndjson").write_bytes(b'{"synthetic": true}\n')
        (capture / "never-copy.txt").write_bytes(b"UNSELECTED-OPERATOR-SENTINEL")
        observation = handoff.new_observation(round_id, self.session, fixture=True)
        observation.update(request_id=f"request-{round_id}", delivery="normal-final",
                           dispatched_at="2026-01-01T12:00:00Z",
                           boundary={"kind": "native-terminal", "at": "2026-01-01T12:01:01Z"},
                           native_terminal={"status": "completed", "classification": "success",
                                            "at": "2026-01-01T12:01:01Z"},
                           cli_cleanup={"exit_code": 130, "at": "2026-01-01T12:01:10Z"},
                           first_normal_final=True, first_normal_final_at="2026-01-01T12:01:00Z",
                           final="native-final.md", evidence_files=["native-events.ndjson"])
        observation.update(changes)
        (capture / "observation.json").write_bytes(handoff.json_bytes(observation))
        return capture, raw

    def prepare(self):
        handoff.prepare(self.bundle, self.state, self.session, fixture=True)

    def reveal(self, round_id, *, session=None, output=None):
        return handoff.reveal(self.bundle, self.state, session or self.session,
                              round_id, output or self.root / f"released-{round_id}")

    def freeze(self, round_id, capture, candidate_files=None):
        return handoff.freeze(self.bundle, self.state, self.session, round_id, capture,
                              candidate_files=candidate_files)

    def test_distributed_cli_and_exact_private_candidate_projection(self):
        self.assertEqual(self.receipt["archive"]["sha256"], hashlib.sha256(self.archive.read_bytes()).hexdigest())
        with ZipFile(self.archive) as archive:
            self.assertEqual(set(archive.namelist()), {
                "README.md", "research_handoff.py", "manifest.json", "control-inputs/rules.md",
                *(f"control-inputs/{round_id}.md" for round_id in handoff.ROUNDS),
                *(f"control-inputs/{ref['path']}" for ref in self.reg["packet"]),
            })
            combined = b"".join(archive.read(name) for name in archive.namelist())
            for marker in (b"EVALUATOR-ONLY-SENTINEL", b"EVALUATOR-EXTRA-SENTINEL",
                           b"UNREGISTERED-FOURTH-ROUND-SENTINEL", b"CASE-FIXTURE"):
                self.assertNotIn(marker, combined)
            source = Path(handoff.__file__).read_bytes()
            self.assertEqual(archive.read("research_handoff.py"), source)
        self.assertEqual(self.cli("check")["round_seconds"], 2700)
        common = ("--state", self.state, "--session-id", self.session)
        self.cli("prepare", *common, "--fixture")
        self.cli("reveal", *common, "--round", "R2", "--output", self.root / "too-soon", ok=False)
        self.assertFalse((self.root / "too-soon").exists())
        work = self.root / "stopped-candidate-scratch"
        work.mkdir()
        (work / "manuscript.md").write_bytes(b"Synthetic explicitly delivered manuscript\r\n")
        (work / "unsubmitted.md").write_bytes(b"Do not collect me")
        for round_id in handoff.ROUNDS:
            release = self.root / f"released-{round_id}"
            params = (*common, "--round", round_id)
            self.cli("reveal", *params, "--output", release)
            expected = {"task.md": self.reg["rounds"][round_id]}
            if round_id == "R1":
                expected["rules.md"] = self.reg["rules"]
                expected.update({ref["path"]: ref for ref in self.reg["packet"]})
            actual = {p.relative_to(release).as_posix() for p in release.rglob("*") if p.is_file()}
            self.assertEqual(actual, expected.keys())
            for name, ref in expected.items():
                self.assertEqual(hashlib.sha256((release / name).read_bytes()).hexdigest(), ref["sha256"])
            files = ["manuscript.md"] if round_id == "R1" else []
            capture, raw = self.capture(round_id, attachments=files)
            seal = self.cli("freeze", *params, "--capture", capture, "--candidate-files", work)
            self.assertEqual(seal["final"]["sha256"], hashlib.sha256(raw).hexdigest())
            self.assertEqual((self.state / round_id / "first-final.md").read_bytes(), raw)
            self.assertEqual((self.state / round_id / "observation.json").read_bytes(),
                             (capture / "observation.json").read_bytes())
            self.assertFalse((self.state / round_id / "delivered/unsubmitted.md").exists())
            self.assertFalse((self.state / round_id / "evidence/never-copy.txt").exists())
        self.assertEqual((self.state / "R1/delivered/manuscript.md").read_bytes(),
                         (work / "manuscript.md").read_bytes())
        final = self.cli("check", "--state", self.state)
        self.assertEqual(final["sealed"], {round_id: "normal-final" for round_id in handoff.ROUNDS})
        self.assertIsNone(final["next_round"])
        self.cli("reveal", *common, "--round", "R4", "--output", self.root / "r4", ok=False)
        self.assertFalse((self.root / "r4").exists())

    def test_reject_changed_frozen_bytes_and_duplicate_or_switched_rounds(self):
        self.prepare()
        with self.assertRaisesRegex(ValueError, "same session"):
            self.reveal("R1", session="another-thread")
        self.reveal("R1")
        capture, _ = self.capture("R1")
        self.freeze("R1", capture)
        with self.assertRaisesRegex(ValueError, "active issued round"):
            self.freeze("R1", capture)
        (self.state / "R1/first-final.md").write_bytes(b"Rewritten synthetic final")
        with self.assertRaisesRegex(ValueError, "hash or size"):
            handoff.check(self.bundle, self.state)
        with self.assertRaisesRegex(ValueError, "hash or size"):
            self.reveal("R2")
        self.assertFalse((self.root / "released-R2").exists())

    def test_known_deadline_and_failed_native_state_do_not_create_a_final(self):
        self.prepare()
        self.reveal("R1")
        error = {"status": "ERROR", "classification": "success", "at": "2026-01-01T12:01:01Z"}
        capture, _ = self.capture("R1", native_terminal=error)
        with self.assertRaisesRegex(ValueError, "native terminal"):
            self.freeze("R1", capture)
        capture, _ = self.capture("R1", delivery="delivery-failed", final=None, first_normal_final=None,
                                  first_normal_final_at=None, cli_cleanup=None, native_terminal=None,
                                  boundary={"kind": "deadline", "at": "2026-01-01T12:45:00Z"})
        seal = self.freeze("R1", capture)
        self.assertIsNone(seal["final"])
        self.assertFalse((self.state / "R1/first-final.md").exists())
        self.assertEqual(handoff.check(self.bundle, self.state)["sealed"], {"R1": "delivery-failed"})
        with self.assertRaisesRegex(ValueError, "preceding normal freezes"):
            self.reveal("R2")

    def test_reject_path_escape_and_untrusted_links_before_freeze(self):
        self.prepare()
        with self.assertRaisesRegex(ValueError, "separate trees"):
            self.reveal("R1", output=self.bundle / "unsafe")
        self.reveal("R1")
        scratch = self.root / "candidate-scratch"
        scratch.mkdir()
        outside = self.root / "outside"
        outside.mkdir()
        (outside / "private.md").write_bytes(b"Cannot leave the private tree")
        (scratch / "escape").symlink_to(outside, target_is_directory=True)
        (scratch / "symlink.md").symlink_to(outside / "private.md")
        os.link(outside / "private.md", scratch / "hardlink.md")
        for path in ("../outside/private.md", "escape/private.md", "symlink.md", "hardlink.md", "task.md"):
            with self.subTest(path=path):
                capture, _ = self.capture("R1", attachments=[path])
                with self.assertRaises(ValueError):
                    self.freeze("R1", capture, scratch)
                self.assertFalse((self.state / "R1").exists())

    def test_concurrent_attempt_cannot_issue_two_releases(self):
        self.prepare()

        def issue(name):
            try:
                self.reveal("R1", output=self.root / name)
                return True
            except (ValueError, FileExistsError):
                return False

        with ThreadPoolExecutor(2) as executor:
            self.assertEqual(sum(executor.map(issue, ("one-release", "another-release"))), 1)

    def test_interrupted_release_cannot_be_reissued_as_a_fresh_round(self):
        self.prepare()
        with patch.object(handoff, "_write_tree", side_effect=OSError("synthetic I/O failure")):
            with self.assertRaises(OSError):
                self.reveal("R1")
        self.assertTrue((self.state / ".pending-release").is_file())
        self.assertFalse((self.state / "R1.issue.json").exists())
        with self.assertRaisesRegex(ValueError, "Unexpected file in operator state"):
            self.reveal("R1", output=self.root / "retry")
        self.assertFalse((self.root / "retry").exists())


if __name__ == "__main__":
    unittest.main()
