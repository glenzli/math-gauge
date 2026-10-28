import json
import shutil
import sys
import tempfile
import unittest
from pathlib import Path

from math_gauge.catalog import Suite, read_json, write_json
from math_gauge.execution import run
from math_gauge.review import apply_reviews, inspect_run, report, templates

ROOT = Path(__file__).resolve().parents[1]


class RunnerContractTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.suite = Suite.load(ROOT / "cases/public")

    def replay(self, ids=None):
        ids = ids or ["MG-D001", "MG-F004", "MG-E003"]
        path = self.root / "responses.json"
        write_json(
            path, {cid: "测试响应：此内容仅检查传输，不是数学成绩。" for cid in ids}
        )
        run(self.suite, self.root / "run", ids, replay=path)
        return self.root / "run"

    def reviewed(self, path):
        entries = templates(path)
        for r in entries:
            r.update(
                reviewer="unit fixture",
                reviewer_kind="fixture",
                decision="pass",
                assumption_fidelity="clean",
                proof_validity="valid",
                scope_accuracy="correct",
                notes="Synthetic transport test, not an actual mathematical judgment.",
            )
        return entries

    def copy_suite(self):
        target = self.root / "suite"
        shutil.copytree(self.suite.root, target)
        return target

    def test_seed_catalog_is_balanced_and_unapproved(self):
        self.assertEqual(len(self.suite.cases), 15)
        self.assertEqual(
            [
                sum(c["track"] == t for c in self.suite.cases.values())
                for t in ("determinate", "alignment", "exploration")
            ],
            [6, 6, 3],
        )
        self.assertTrue(
            all(c["review"]["human"] == "pending" for c in self.suite.cases.values())
        )
        labels = [
            read_json(self.suite.root / c["rubric"])["expected"]
            for c in self.suite.cases.values()
            if c["track"] == "alignment"
        ]
        self.assertEqual(labels.count("aligned"), 3)
        self.assertEqual(labels.count("misaligned"), 3)

    def test_solver_projection_omits_all_evaluator_fields(self):
        case = self.suite.cases["MG-F004"]
        req = self.suite.prepare(case, self.root / "solver")
        self.assertEqual(
            {x.name for x in (self.root / "solver").iterdir()},
            {"prompt.md", "request.json", "candidate.lean"},
        )
        self.assertEqual(
            set(req),
            {
                "schema",
                "case_id",
                "case_version",
                "track",
                "instruction",
                "task",
                "files",
            },
        )
        self.assertNotIn("reviewer/repair.lean", json.dumps(req))
        self.assertNotIn("required_evidence", json.dumps(req))
        self.assertNotIn("misaligned", json.dumps(req))

    def test_replay_and_fixture_reviews_never_become_model_scores(self):
        path = self.replay()
        apply_reviews(path, self.reviewed(path))
        result, _ = report(path)
        self.assertEqual(sum(x["reviewed"] for x in result["tracks"].values()), 3)
        self.assertEqual(
            sum(x["eligible_for_model_comparison"] for x in result["tracks"].values()),
            0,
        )
        self.assertIsNone(result["tracks"]["exploration"]["strict_passes"])

    def test_path_traversal_is_rejected(self):
        target = self.copy_suite()
        p = target / "MG-D001/case.json"
        case = read_json(p)
        case["task"] = "../outside.md"
        (target.parent / "outside.md").write_text("not a question")
        write_json(p, case)
        with self.assertRaises(ValueError):
            Suite.load(target)

    def test_symlink_outside_suite_is_rejected(self):
        target = self.copy_suite()
        p = target / "MG-D001/task.md"
        p.unlink()
        outside = self.root / "outside.md"
        outside.write_text("outside")
        p.symlink_to(outside)
        with self.assertRaises(ValueError):
            Suite.load(target)

    def test_cross_case_reference_cannot_be_solver_input(self):
        target = self.copy_suite()
        p = target / "MG-D001/case.json"
        case = read_json(p)
        case["solver_files"].append(
            {"source": "MG-D002/reference.md", "target": "extra.md"}
        )
        write_json(p, case)
        with self.assertRaises(ValueError):
            Suite.load(target)

    def test_reviewer_only_lean_repair_cannot_be_solver_input(self):
        target = self.copy_suite()
        p = target / "MG-F004/case.json"
        case = read_json(p)
        case["solver_files"].append(
            {"source": "MG-F004/reviewer/repair.lean", "target": "hint.lean"}
        )
        write_json(p, case)
        with self.assertRaises(ValueError):
            Suite.load(target)

    def test_invalid_adapter_does_not_create_a_run(self):
        path = self.root / "invalid"
        with self.assertRaises(ValueError):
            run(
                self.suite,
                path,
                ["MG-D001"],
                command="not-an-argv-array",
                model="fixture",
            )
        self.assertFalse(path.exists())

    def test_tampering_with_response_invalidates_reviews(self):
        path = self.replay(["MG-D001"])
        apply_reviews(path, self.reviewed(path))
        (path / "MG-D001/response.md").write_text("changed")
        with self.assertRaises(ValueError):
            report(path)

    def test_reviews_bind_to_exact_response_before_any_write(self):
        path = self.replay()
        entries = self.reviewed(path)
        entries[-1]["response_sha256"] = "wrong"
        with self.assertRaises(ValueError):
            apply_reviews(path, entries)
        self.assertFalse((path / "reviews.json").exists())

    def test_pass_with_hidden_assumption_drift_is_rejected(self):
        path = self.replay(["MG-D001"])
        entries = self.reviewed(path)
        entries[0]["assumption_fidelity"] = "drift"
        with self.assertRaises(ValueError):
            apply_reviews(path, entries)

    def test_duplicate_review_is_not_silently_overwritten(self):
        path = self.replay(["MG-D001"])
        entries = self.reviewed(path)
        apply_reviews(path, entries)
        with self.assertRaises(ValueError):
            apply_reviews(path, entries)

    def test_run_directory_is_not_overwritten(self):
        path = self.replay(["MG-D001"])
        with self.assertRaises(FileExistsError):
            run(self.suite, path, ["MG-D001"], replay=self.root / "responses.json")

    def test_command_receives_only_request_and_preserves_unicode(self):
        cmd = [
            sys.executable,
            "-c",
            "import json,sys,os; r=json.load(sys.stdin); assert set(os.listdir('.'))=={'prompt.md','request.json','context.md'}; print(r['case_id']+'：已收到')",
        ]
        path = self.root / "command"
        run(self.suite, path, ["MG-D001"], command=cmd, model="synthetic adapter")
        meta, records = inspect_run(path)
        self.assertEqual(meta["origin"], "command")
        self.assertEqual(records["MG-D001"]["status"], "ok")
        self.assertEqual(
            (path / "MG-D001/response.md").read_text().strip(), "MG-D001：已收到"
        )

    def test_timeout_is_preserved_as_execution_failure(self):
        path = self.root / "timeout"
        run(
            self.suite,
            path,
            ["MG-D001"],
            command=[sys.executable, "-c", "import time; time.sleep(5)"],
            model="synthetic adapter",
            timeout=0.05,
        )
        _, records = inspect_run(path)
        self.assertEqual(records["MG-D001"]["status"], "timeout")
        entries = self.reviewed(path)
        with self.assertRaises(ValueError):
            apply_reviews(path, entries)

    def test_missing_adapter_is_recorded(self):
        path = self.root / "missing"
        run(
            self.suite,
            path,
            ["MG-D001"],
            command=["/nonexistent/math-gauge-test-adapter"],
            model="synthetic adapter",
        )
        _, records = inspect_run(path)
        self.assertEqual(records["MG-D001"]["status"], "error")
        self.assertEqual(read_json(path / "run.json")["execution_failures"], 1)

    def test_catalog_fingerprint_changes_with_reference(self):
        target = self.copy_suite()
        before = Suite.load(target).sha256
        with (target / "MG-D001/reference.md").open("a") as f:
            f.write("\nreview amendment\n")
        self.assertNotEqual(before, Suite.load(target).sha256)


if __name__ == "__main__":
    unittest.main()
