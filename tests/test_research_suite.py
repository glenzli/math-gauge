"""Candidate projection contracts for the active research suite."""

import hashlib
import json
import shutil
import tempfile
import unittest
from pathlib import Path

from math_gauge.catalog import Suite, read_json, write_json

ROOT = Path(__file__).resolve().parents[1]
RECURSIVE_TASK_SHA256 = (
    "779bf275a6184fb848a12f3d72089a21d4704513512e10323aa48d4ee462cecd"
)


class ResearchSuiteTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.suite = Suite.load(ROOT / "cases/public")

    def test_active_suite_has_ten_task_only_unapproved_research_cases(self):
        self.assertEqual(
            list(self.suite.cases), [f"MG-R{i:03d}" for i in range(1, 11)]
        )
        for case in self.suite.cases.values():
            with self.subTest(case=case["id"]):
                self.assertEqual(case["track"], "exploration")
                self.assertEqual(case["candidate_instruction"], "")
                self.assertEqual(case["solver_files"], [])
                self.assertEqual(case["status"], "draft")
                self.assertEqual(case["review"]["human"], "pending")

    def test_every_candidate_workspace_contains_only_the_exact_task(self):
        for case in self.suite.cases.values():
            with self.subTest(case=case["id"]):
                dest = self.root / case["id"]
                request = self.suite.prepare(case, dest)
                task = (self.suite.root / case["task"]).read_bytes()
                self.assertEqual(
                    {p.name for p in dest.iterdir()}, {"prompt.md", "request.json"}
                )
                self.assertEqual((dest / "prompt.md").read_bytes(), task)
                self.assertEqual(request["task"].encode("utf-8"), task)
                self.assertEqual(request["instruction"], "")
                self.assertEqual(request["files"], [])
                self.assertEqual(
                    set(request),
                    {
                        "schema", "case_id", "case_version", "track",
                        "instruction", "task", "files",
                    },
                )
                self.assertEqual(read_json(dest / "request.json"), request)

    def test_recursive_task_retains_the_already_run_prompt_hash(self):
        case = self.suite.cases["MG-R001"]
        dest = self.root / "recursive"
        self.suite.prepare(case, dest)
        self.assertEqual(
            hashlib.sha256((dest / "prompt.md").read_bytes()).hexdigest(),
            RECURSIVE_TASK_SHA256,
        )

    def test_evaluator_edits_change_suite_identity_but_not_candidate_input(self):
        target = self.root / "suite"
        shutil.copytree(self.suite.root, target)
        case = self.suite.cases["MG-R001"]
        before = self.suite.request(case)
        marker = "EVALUATOR_ONLY_SENTINEL_708210"
        reference = target / case["reference"]
        reference.write_bytes(reference.read_bytes() + ("\n" + marker).encode())
        rubric_path = target / case["rubric"]
        rubric = read_json(rubric_path)
        rubric["critical_errors"].append(marker)
        write_json(rubric_path, rubric)
        metadata_path = target / "MG-R001/case.json"
        metadata = read_json(metadata_path)
        metadata["review"]["mathematical"] = marker
        write_json(metadata_path, metadata)
        sources = read_json(target / "sources.json")
        sources[case["sources"][0]]["title"] = marker
        write_json(target / "sources.json", sources)
        changed = Suite.load(target)
        self.assertNotEqual(changed.sha256, self.suite.sha256)
        after = changed.prepare(changed.cases[case["id"]], self.root / "changed")
        self.assertEqual(before, after)
        self.assertNotIn(marker, json.dumps(after))
        self.assertEqual(
            (self.root / "changed/prompt.md").read_bytes(),
            (self.suite.root / case["task"]).read_bytes(),
        )


if __name__ == "__main__":
    unittest.main()
