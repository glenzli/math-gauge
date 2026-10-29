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

    def baseline_suite(self):
        """Rebuild the original ten-case layout without rewriting its manifests."""
        original_root = ROOT / "results/expansion-v0.4/baseline"
        original_suite = read_json(original_root / "suite.json")
        baseline_root = self.root / "baseline"
        baseline_root.mkdir()
        for name in ("suite.json", "sources.json"):
            shutil.copyfile(original_root / name, baseline_root / name)
        for manifest in original_suite["cases"]:
            cid = Path(manifest).parts[0]
            source = self.suite.root / cid
            if cid == "MG-R005":
                revision = read_json(source / "revision.json")
                self.assertEqual(revision["prior_version"], "0.3.0")
                self.assertEqual(revision["version"], "0.3.1")
                snapshot_path = source / revision["historical_snapshot"]
                self.assertEqual(
                    hashlib.sha256(snapshot_path.read_bytes()).hexdigest(),
                    revision["historical_snapshot_sha256"],
                )
                snapshot = read_json(snapshot_path)
                self.assertEqual(snapshot["case_id"], cid)
                self.assertEqual(snapshot["version"], revision["prior_version"])
                source = snapshot_path.parent
            shutil.copytree(source, baseline_root / cid)
        return Suite.load(baseline_root)

    def test_active_suite_has_twenty_task_only_unapproved_research_cases(self):
        self.assertEqual(
            list(self.suite.cases), [f"MG-R{i:03d}" for i in range(1, 21)]
        )
        self.assertEqual(self.suite.metadata["version"], "0.4.1")
        for case in self.suite.cases.values():
            with self.subTest(case=case["id"]):
                self.assertEqual(case["track"], "exploration")
                self.assertEqual(case["candidate_instruction"], "")
                self.assertEqual(case["solver_files"], [])
                self.assertEqual(case["status"], "draft")
                self.assertEqual(case["review"]["human"], "pending")
                expected_version = "0.3.0" if int(case["id"][-3:]) <= 10 else "0.4.0"
                if case["id"] == "MG-R005":
                    expected_version = "0.3.1"
                self.assertEqual(case["version"], expected_version)

    def test_baseline_case_bytes_versions_and_projection_are_preserved(self):
        evidence = read_json(ROOT / "results/expansion-v0.4/baseline-preservation.json")
        self.assertEqual(evidence["baseline_suite_version"], "0.3.0")
        original_root = ROOT / "results/expansion-v0.4/baseline"
        original_suite = read_json(original_root / "suite.json")
        self.assertEqual(original_suite["version"], "0.3.0")
        self.assertEqual(original_suite["cases"], [f"MG-R{i:03d}/case.json" for i in range(1, 11)])
        baseline = self.baseline_suite()
        self.assertEqual(baseline.metadata, original_suite)
        self.assertEqual(baseline.sha256, evidence["baseline_suite_sha256"])
        for item in evidence["baseline_case_files"]:
            with self.subTest(file=item["path"]):
                name = Path(item["path"]).relative_to("cases/public")
                content = (baseline.root / name).read_bytes()
                self.assertEqual(len(content), item["bytes"])
                self.assertEqual(
                    hashlib.sha256(content).hexdigest(),
                    item["sha256"],
                )
        for cid, recorded in evidence["candidate_projection"].items():
            with self.subTest(case=cid):
                case = baseline.cases[cid]
                request = baseline.request(case)
                self.assertEqual(case["version"], recorded["case_version"])
                self.assertEqual(
                    hashlib.sha256(request["task"].encode()).hexdigest(),
                    recorded["task_sha256"],
                )
                self.assertEqual(
                    hashlib.sha256(json.dumps(request, ensure_ascii=False, sort_keys=True).encode()).hexdigest(),
                    recorded["request_sha256"],
                )

    def test_revised_r005_current_projection_is_separate_from_the_baseline(self):
        baseline = self.baseline_suite()
        historical_request = baseline.request(baseline.cases["MG-R005"])
        case = self.suite.cases["MG-R005"]
        revision = read_json(self.suite.root / "MG-R005/revision.json")
        destination = self.root / "current-r005"
        request = self.suite.prepare(case, destination)
        task = (self.suite.root / case["task"]).read_bytes()
        self.assertEqual(historical_request["case_version"], "0.3.0")
        self.assertEqual(request["case_version"], "0.3.1")
        self.assertEqual(
            hashlib.sha256(task).hexdigest(),
            revision["prepared_files_sha256"]["task.md"],
        )
        self.assertNotEqual(request["task"], historical_request["task"])
        self.assertEqual(
            request,
            {**historical_request, "case_version": "0.3.1", "task": task.decode("utf-8")},
        )
        self.assertEqual(request["instruction"], "")
        self.assertEqual(request["files"], [])
        self.assertEqual(case["lean_checks"], [])
        self.assertEqual((destination / "prompt.md").read_bytes(), task)
        self.assertEqual(
            {p.name for p in destination.iterdir()}, {"prompt.md", "request.json"}
        )

    def test_current_r005_task_cannot_reuse_historical_identity(self):
        baseline = self.baseline_suite()
        evidence = read_json(ROOT / "results/expansion-v0.4/baseline-preservation.json")
        case = baseline.cases["MG-R005"]
        current_task = self.suite.root / self.suite.cases["MG-R005"]["task"]
        shutil.copyfile(current_task, baseline.root / case["task"])
        mixed = Suite.load(baseline.root)
        request = mixed.request(mixed.cases["MG-R005"])
        self.assertEqual(request["case_version"], "0.3.0")
        self.assertNotEqual(mixed.sha256, evidence["baseline_suite_sha256"])
        self.assertNotEqual(
            hashlib.sha256(json.dumps(request, ensure_ascii=False, sort_keys=True).encode()).hexdigest(),
            evidence["candidate_projection"]["MG-R005"]["request_sha256"],
        )

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
