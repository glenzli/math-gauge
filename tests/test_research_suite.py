"""Candidate projection and identity contracts for the current 43-case benchmark."""

import json
import shutil
import tempfile
import unittest
from collections import Counter
from pathlib import Path

from math_gauge.catalog import Suite, candidate_message, read_json, write_json
from math_gauge.cli import parser

ROOT = Path(__file__).resolve().parents[1]


class BenchmarkSuiteTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.suite = Suite.load(ROOT / "cases")

    def case_snapshot(self, cid="MG-GR001"):
        """A single current case suffices to test evaluator-only identity edits."""
        case = self.suite.cases[cid]
        manifest = next(name for name in self.suite.metadata["cases"]
                        if read_json(self.suite.root / name)["id"] == cid)
        target = self.root / "suite"
        meta = dict(self.suite.metadata, cases=[manifest])
        write_json(target / "suite.json", meta)
        names = {"sources.json", manifest, case["task"], case["reference"], case["rubric"],
                 case["group_contract"], *case.get("evaluator_files", []), *case["lean_checks"],
                 *(item["source"] for item in case["solver_files"])}
        for name in names:
            destination = target / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(self.suite.root / name, destination)
        return Suite.load(target), manifest

    def test_default_suite_is_the_complete_current_benchmark(self):
        self.assertEqual(parser().parse_args(["validate"]).suite, "cases")
        expected = {
            "proofs": {*(f"MG-GR{i:03d}" for i in range(1, 21)),
                       *(f"MG-GR{i}" for i in range(101, 107)),
                       *(f"MG-GP{i:03d}" for i in range(1, 4))},
            "lean-audit": {f"MG-GF{i}" for i in range(101, 113, 2)},
            "lean-construction": {f"MG-GF{i}" for i in range(102, 113, 2)},
            "chapters": {"MG-C002", "MG-C003"},
        }
        self.assertEqual(set(self.suite.cases), set.union(*expected.values()))
        self.assertEqual(Counter(Path(c["task"]).parts[0] for c in self.suite.cases.values()),
                         {"proofs": 29, "lean-audit": 6, "lean-construction": 6, "chapters": 2})
        for category, ids in expected.items():
            for cid in ids:
                with self.subTest(case=cid):
                    case = self.suite.cases[cid]
                    self.assertEqual(Path(case["task"]).parts[:2], (category, cid))
                    self.assertEqual(case["path_base"], "case")
                    self.assertEqual(case["status"], "draft")
                    self.assertEqual(case["review"]["human"], "pending")
                    self.assertEqual(case["candidate_instruction"], "")
                    self.assertTrue(case["group_contract"])

    def test_every_workspace_is_the_exact_explicit_candidate_projection(self):
        for case in self.suite.cases.values():
            with self.subTest(case=case["id"]):
                dest = self.root / case["id"]
                request = self.suite.prepare(case, dest)
                task = (self.suite.root / case["task"]).read_bytes()
                visible = {"prompt.md", "request.json", *(x["target"] for x in case["solver_files"])}
                self.assertEqual({p.relative_to(dest).as_posix() for p in dest.rglob("*") if p.is_file()}, visible)
                self.assertEqual((dest / "prompt.md").read_bytes(), task)
                self.assertEqual(request["task"].encode(), task)
                self.assertEqual(request["instruction"], "")
                self.assertEqual(set(request), {"schema", "case_id", "case_version", "track", "instruction", "task", "files"})
                self.assertEqual(read_json(dest / "request.json"), request)
                self.assertEqual([item["name"] for item in request["files"]],
                                 [item["target"] for item in case["solver_files"]])
                for item, source in zip(request["files"], case["solver_files"]):
                    self.assertEqual(item["content"].encode(), (self.suite.root / source["source"]).read_bytes())
                    self.assertEqual((dest / item["name"]).read_bytes(), item["content"].encode())
                self.assertTrue(candidate_message(request).startswith(request["task"]))

    def test_evaluator_edits_change_suite_identity_without_changing_candidate_input(self):
        baseline, manifest = self.case_snapshot()
        case = baseline.cases["MG-GR001"]
        before = baseline.request(case)
        marker = "EVALUATOR_ONLY_SENTINEL_708210"
        reference = baseline.root / case["reference"]
        reference.write_bytes(reference.read_bytes() + ("\n" + marker).encode())
        rubric_path = baseline.root / case["rubric"]
        rubric = read_json(rubric_path)
        rubric["critical_errors"].append(marker)
        write_json(rubric_path, rubric)
        metadata = read_json(baseline.root / manifest)
        metadata["review"]["mathematical"] = marker
        write_json(baseline.root / manifest, metadata)
        sources = read_json(baseline.root / "sources.json")
        sources[case["sources"][0]]["title"] = marker
        write_json(baseline.root / "sources.json", sources)
        changed = Suite.load(baseline.root)
        self.assertNotEqual(changed.sha256, baseline.sha256)
        after = changed.prepare(changed.cases[case["id"]], self.root / "changed")
        self.assertEqual(before, after)
        self.assertNotIn(marker, json.dumps(after))
        self.assertNotIn(marker, candidate_message(after))

    def test_case_version_and_task_edits_cannot_reuse_input_identity(self):
        baseline, manifest = self.case_snapshot()
        before = baseline.request(baseline.cases["MG-GR001"])
        metadata = read_json(baseline.root / manifest)
        metadata["version"] += ".synthetic-test"
        write_json(baseline.root / manifest, metadata)
        task_path = baseline.root / baseline.cases["MG-GR001"]["task"]
        task_path.write_bytes(task_path.read_bytes() + b"\nSynthetic test change.\n")
        changed = Suite.load(baseline.root)
        after = changed.request(changed.cases["MG-GR001"])
        self.assertNotEqual(before["case_version"], after["case_version"])
        self.assertNotEqual(before["task"], after["task"])
        self.assertNotEqual(baseline.sha256, changed.sha256)


if __name__ == "__main__":
    unittest.main()
