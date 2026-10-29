"""Focused non-inference contracts for snapshot/release/adapter ownership."""

import io
import json
import tempfile
import sys
import unittest
from pathlib import Path
from unittest.mock import patch

import cli_adapter
import common
import isolation
import run_comparison as comparison
from run_comparison import snapshot_suite
from math_gauge.execution import run as runner_run


def suite_fixture(root, *, case_local=False, group=False):
    meta = {"schema": "math-gauge.suite/v1", "id": "fixture", "version": "1", "visibility": "public", "cases": ["MG-X/case.json"]}
    case = {"schema": "math-gauge.case/v1", "id": "MG-X", "version": "1", "title": "Fixture", "language": "en", "track": "alignment", "visibility": "public", "status": "draft", "review": {"human": "pending"}, "sources": ["independent"], "task": "MG-X/task.md", "reference": "MG-X/reference.md", "rubric": "MG-X/rubric.json", "solver_files": [{"source": "MG-X/Input.lean", "target": "Input.lean"}], "evaluator_files": [], "lean_checks": []}
    common.save(root / "suite.json", meta)
    common.save(root / "sources.json", {"independent": {"title": "Independent"}})
    if group:
        case["group_contract"] = "MG-X/contract.json"
        common.save(root / "MG-X/contract.json", {
            "schema": "math-gauge.group-contract/v1", "id": "MG-X", "version": "1",
            "kind": "chapter_formalization", "turns": [], "stages": [
                {"id": "O" + str(i), "kind": "prove", "expected": "true", "depends_on": [],
                 "assumptions": ["fixture"], "required_evidence": ["fixture"],
                 "critical_errors": ["fixture"], "points": 1, "lean_required": False}
                for i in (1, 2)]})
    if case_local:
        case["path_base"] = "case"
        for key in ("task", "reference", "rubric", "group_contract"):
            if key in case:
                case[key] = Path(case[key]).relative_to("MG-X").as_posix()
        case["solver_files"][0]["source"] = "Input.lean"
    common.save(root / "MG-X/case.json", case)
    common.save(root / "MG-X/rubric.json", {"schema": "math-gauge.rubric/v1", "expected": "aligned", "required_evidence": ["Proof"], "critical_errors": ["Wrong"]})
    for name, value in [("task.md", "Question"), ("reference.md", "Hidden"), ("Input.lean", "def value := 1\n")]:
        (root / "MG-X" / name).write_text(value)
    return common.Suite.load(root)


class RuntimeTests(unittest.TestCase):
    def test_shared_runner_preserves_final_bytes_and_message_hash(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            suite = suite_fixture(root / "source")
            command = [sys.executable, "-c", "import json,sys;json.load(sys.stdin);sys.stdout.buffer.write('answer\\r\\nβ'.encode())"]
            result = runner_run(suite, root / "run", ids=["MG-X"], command=command, model="fixture/max")
            self.assertEqual(result["execution_failures"], 0)
            self.assertEqual((root / "run/MG-X/response.md").read_bytes(), "answer\r\nβ".encode())
            record = common.load(root / "run/MG-X/record.json")
            self.assertEqual(record["candidate_message_sha256"], common.text_digest(common.candidate_message(suite.request(suite.cases["MG-X"]))))

    def test_descendants_walks_each_parent_once(self):
        rows = {pid: {"pid": pid, "ppid": parent} for pid, parent in [(10, 1), (11, 10), (12, 10), (13, 11), (20, 1)]}
        self.assertEqual({row["pid"] for row in isolation.descendants(rows, 10)}, {11, 12, 13})
        self.assertEqual(isolation.descendants(rows, 20), [])

    def test_snapshot_keeps_shared_fingerprint_and_excludes_undeclared_files(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            suite = suite_fixture(root / "source")
            (suite.root / "unlisted-secret.md").write_text("Do not copy")
            copied = snapshot_suite(suite, root / "snapshot")
            self.assertEqual(copied.sha256, suite.sha256)
            self.assertFalse((copied.root / "unlisted-secret.md").exists())
            self.assertEqual(copied.request(copied.cases["MG-X"]), suite.request(suite.cases["MG-X"]))

    def test_snapshot_keeps_case_local_group_contract(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            suite = suite_fixture(root / "source", case_local=True, group=True)
            copied = snapshot_suite(suite, root / "snapshot")
            self.assertEqual(copied.sha256, suite.sha256)
            self.assertEqual(copied.cases["MG-X"]["group_contract"], "MG-X/contract.json")
            self.assertEqual((copied.root / "MG-X/contract.json").read_bytes(),
                             (suite.root / "MG-X/contract.json").read_bytes())

    def test_catalog_uses_current_schema_and_exact_category_coverage(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            suite = suite_fixture(root / "cases", case_local=True, group=True)
            catalog = {"schema": "math-gauge.case-catalog/v1",
                       "suites": [{"root": "cases", "suite_sha256": suite.sha256, "cases": ["MG-X"]}],
                       "entries": [{"case_id": "MG-X", "category": "lean-audit"}],
                       "categories": [{"id": "lean-audit", "case_ids": ["MG-X"]}]}
            path = root / "catalog.json"
            common.save(path, catalog)
            with patch.object(common, "REPO", root):
                loaded, suites = common.catalog_suites(path)
                self.assertEqual(loaded, catalog)
                self.assertEqual(suites[0][1].sha256, suite.sha256)
                catalog["categories"][0]["case_ids"].append("MG-X")
                common.save(path, catalog)
                with self.assertRaisesRegex(ValueError, "cover every selected case"):
                    common.catalog_suites(path)
                catalog["categories"][0]["case_ids"] = ["MG-X"]
                catalog["suites"][0]["suite_sha256"] = "0" * 64
                common.save(path, catalog)
                with self.assertRaisesRegex(ValueError, "suite has changed"):
                    common.catalog_suites(path)

    def test_group_finalization_freezes_stage_contract_without_binary_audit_assumption(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            suite = suite_fixture(root / "source", case_local=True, group=True)
            manifest = suite.root / "MG-X/case.json"
            common.save(manifest, dict(common.load(manifest), track="determinate"))
            rubric = suite.root / "MG-X/rubric.json"
            common.save(rubric, dict(common.load(rubric), expected="mixed"))
            suite = common.Suite.load(suite.root)
            request = suite.request(suite.cases["MG-X"])
            catalog = root / "catalog.json"
            common.save(catalog, {"synthetic_fixture_only": True})
            freeze = {"catalog_path": str(catalog), "catalog_sha256": common.digest(catalog),
                      "suite_snapshots": [{"root": str(suite.root), "suite_sha256": suite.sha256}],
                      "preflight_bindings": [], "cases": [{"case_id": "MG-X", "task_kind": "audit",
                          "suite_root": str(suite.root), "sessions": {},
                          "request_sha256": common.text_digest(json.dumps(request, ensure_ascii=False, sort_keys=True)),
                          "candidate_message_sha256": common.text_digest(common.candidate_message(request))}]}
            common.save(root / "runtime/snapshot-plan.json", freeze)
            with patch("sys.stdout", io.StringIO()):
                comparison.finalize(root)
            row = common.load(root / "runtime/freeze.json")["cases"][0]
            self.assertIsNone(row["audit_expected"])
            self.assertEqual(row["stage_expected"], {"O1": "true", "O2": "true"})
            self.assertEqual(row["group_contract_sha256"], common.digest(suite.root / "MG-X/contract.json"))

    def test_queue_completion_uses_frozen_case_count_with_no_model_execution(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            suite = suite_fixture(root / "source", case_local=True)
            release = root / "synthetic-release.json"
            common.save(release, {"synthetic_fixture_only": True})
            freeze = {"model_order": ["terra", "gemini"], "timeout_seconds": 1,
                      "cases": [{"case_id": "MG-X", "suite_root": str(suite.root),
                                 "sessions": {model: str(root / "sessions" / model) for model in ("terra", "gemini")}}]}
            common.save(root / "runtime/freeze.json", freeze)
            for model in freeze["model_order"]:
                common.save(root / "config" / (model + ".json"), {"model": "synthetic-" + model, "effort": "fixture"})
            with patch.object(comparison, "verify_release", return_value=freeze), \
                    patch.object(comparison, "runner_run", return_value={"execution_failures": 0}) as runner, \
                    patch("sys.stdout", io.StringIO()):
                self.assertEqual(comparison.run_queue(root, release), 0)
            self.assertEqual(runner.call_count, 2)
            final = common.load(root / "runtime/queue-final.json")
            self.assertTrue(final["completed"])
            self.assertEqual(len(final["results"]), 2)
            self.assertFalse(final["mathematical_scoring_performed"])

    def test_release_requires_root_and_exact_hashes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            suite = suite_fixture(root / "snapshot")
            catalog = root / "catalog.json"; catalog.write_text("{}")
            freeze = {"catalog_path": str(catalog), "catalog_sha256": common.digest(catalog), "code_identity": common.code_identity(), "runner_sha256": common.runner_fingerprint(), "preflight_bindings": [], "suite_snapshots": [{"root": str(suite.root), "suite_sha256": suite.sha256}]}
            common.save(root / "freeze.json", freeze)
            release = {"schema": "math-gauge.comparison-release/v1", "allow_mathematical_requests": True, "released_by": "/root", "freeze_sha256": common.digest(root / "freeze.json"), "catalog_sha256": freeze["catalog_sha256"], "model_order": ["terra", "gemini"]}
            common.save(root / "release.json", release)
            self.assertEqual(common.verify_release(root, root / "release.json"), freeze)
            release["released_by"] = "unconfirmed"
            common.save(root / "release.json", release)
            with self.assertRaises(ValueError):
                common.verify_release(root, root / "release.json")
            release["released_by"] = "/root"; common.save(root / "release.json", release)
            policy = root / "policy.json"; policy.write_text("strict")
            freeze["session_bindings"] = [{"path": str(policy), "sha256": common.digest(policy)}]
            common.save(root / "freeze.json", freeze)
            release["freeze_sha256"] = common.digest(root / "freeze.json")
            common.save(root / "release.json", release)
            policy.write_text("changed")
            with self.assertRaises(ValueError):
                common.verify_release(root, root / "release.json")
            policy.write_text("strict")
            (suite.root / "MG-X/reference.md").write_text("Changed evaluator material")
            with self.assertRaises(ValueError):
                common.verify_release(root, root / "release.json")

    def test_adapter_does_not_execute_before_release(self):
        argv = ["cli_adapter.py", "--runtime", "/tmp/runtime", "--release", "/tmp/release", "--model", "terra", "--case", "MG-X"]
        with patch("sys.argv", argv), patch.object(cli_adapter, "verify_release", side_effect=ValueError("Not released")), patch.object(cli_adapter, "execute_session") as execute:
            with self.assertRaises(ValueError):
                cli_adapter.main()
            execute.assert_not_called()

    def test_adapter_rejects_unbound_or_other_model_run(self):
        argv = ["cli_adapter.py", "--runtime", "/tmp/runtime", "--release", "/tmp/release", "--model", "terra", "--case", "MG-X"]
        message_hash = common.text_digest("prompt")
        freeze = {"cases": [{"case_id": "MG-X", "request_sha256": common.text_digest("{}"), "candidate_message_sha256": message_hash, "sessions": {"terra": "/tmp/session"}}]}
        plan = {"model": "gpt-6.1-terra", "effort": "max"}
        for metadata in [{"model_label": "gpt-6.1-terra/max"}, {"run_id": "fresh-run", "model_label": "other/max"}]:
            with self.subTest(metadata=metadata), patch("sys.argv", argv), patch("sys.stdin", io.StringIO("{}")), patch.object(cli_adapter, "verify_release", return_value=freeze), patch.object(cli_adapter, "candidate_message", return_value="prompt"), patch.object(cli_adapter, "digest", return_value=message_hash), patch.object(cli_adapter, "load", side_effect=[metadata, plan]), patch.object(cli_adapter, "execute_session") as execute:
                with self.assertRaises(ValueError):
                    cli_adapter.main()
                execute.assert_not_called()


if __name__ == "__main__":
    unittest.main()
