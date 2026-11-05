"""Future C003 budgets are explicit; historical profiles keep their identity."""

import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from math_gauge.benchmarks import BenchmarkProfile, build_plan, select_slots
from math_gauge.catalog import Suite, digest_bytes
from math_gauge.cli import parser
from math_gauge.execution_policy import declared_case_timeout_seconds, validate_case_execution_policy
from math_gauge.harness import _execution_projection, export_harness_bundle, inspect_harness_bundle
from math_gauge.reliability import execute_reliability_run


ROOT = Path(__file__).resolve().parents[1]
RUNTIME = {"model_label": "synthetic-budget-fixture", "adapter_identity": {"kind": "fixture"},
           "execution_track": "math-gauge.local-tools-no-search/v1",
           "candidate_parameters": {"model": "synthetic-no-model-calls"},
           "budget": {"timeout_seconds": 10800}, "fresh_context": True}


class C003BudgetTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.suite = Suite.load(ROOT / "cases")
        cls.old = BenchmarkProfile.load(ROOT / "protocol/benchmark-profile.json", cls.suite)
        cls.future = BenchmarkProfile.load(ROOT / "protocol/benchmark-profile.json", cls.suite)
        cls.components = {cid: row["id"] for row in cls.future.data["components"] for cid in row["case_ids"]}

    def runtime(self, seconds):
        runtime = copy.deepcopy(RUNTIME)
        runtime["budget"]["timeout_seconds"] = seconds
        return runtime

    def test_current_profile_freezes_each_lean_budget(self):
        self.assertEqual(digest_bytes(self.future.path.read_bytes()), self.future.sha256)
        for cid in self.suite.cases:
            seconds = declared_case_timeout_seconds(self.future.data, cid)
            self.assertEqual(seconds, 10800 if cid == "MG-C003" else 5400 if cid in
                {"AHR01", "AHR02", "AHR03", "AHR04", "LCH01", "LCH02", "HCH02"} else None, cid)
        self.assertNotIn("future_budget_variant", self.future.data)
        self.assertEqual(self.future.data["standard_version"], "0.6.0")

    def test_only_the_versioned_c003_override_is_accepted(self):
        validate_case_execution_policy(self.future.data, self.components)
        for override in ({}, {"MG-C003": True}, {"MG-C003": 5400}, {"AHR01": 10800},
                         {"MG-C003": 10800, "HCH02": 10800}):
            with self.subTest(override=override):
                data = copy.deepcopy(self.future.data)
                data["case_execution_policy"]["new_case_turn_timeout_seconds"] = override
                with self.assertRaisesRegex(ValueError, "only MG-C003"):
                    validate_case_execution_policy(data, self.components)
        data = copy.deepcopy(self.future.data)
        data["case_execution_policy"]["schema"] = "math-gauge.case-execution-policy/v1"
        with self.assertRaisesRegex(ValueError, "explicit v2"):
            validate_case_execution_policy(data, self.components)

    def test_new_target_export_is_portable_and_keeps_operator_policy_outside_candidates(self):
        plan = build_plan(self.future, self.suite, ["c003-180"], runtime=RUNTIME)
        self.assertEqual([s["slot_id"] for s in select_slots(plan)], ["MG-C003:A1"])
        self.assertEqual(plan["planned"]["all_slots"], 42)
        with tempfile.TemporaryDirectory() as directory:
            bundle = Path(directory) / "bundle"
            with patch("math_gauge.reliability.invoke_conversation", side_effect=AssertionError("no model calls")):
                manifest = export_harness_bundle(plan, self.suite, bundle)
                self.assertEqual(inspect_harness_bundle(bundle, plan=plan, suite=self.suite), manifest)
            self.assertEqual(manifest["execution"]["budget"]["timeout_seconds"], 10800)
            self.assertEqual(manifest["selected_slot_ids"], ["MG-C003:A1"])
            self.assertNotIn("case_execution_policy", (bundle / "manifest.json").read_text())
            for case in manifest["cases"]:
                message = (bundle / case["candidate_message_path"]).read_text()
                self.assertNotIn("lean-tool-budget-policy", message)
                self.assertNotIn("benchmark-profile-c003-180", message)
            result = subprocess.run([sys.executable, "-I", "-S", "-B", str(bundle / "controller.py"),
                                     "check", "--bundle", str(bundle)], capture_output=True, check=False)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(json.loads(result.stdout)["exported_slots"], 1)

    def test_wrong_or_mixed_runtime_is_rejected_before_execution_or_export(self):
        for targets, seconds in ((["c003-180"], 5400), (["lean-90"], 10800),
                                 (["c003-180", "lean-90"], 10800),
                                 (["c003-180", "lean-90"], 5400)):
            with self.subTest(targets=targets, seconds=seconds), tempfile.TemporaryDirectory() as directory:
                plan = build_plan(self.future, self.suite, targets, runtime=self.runtime(seconds))
                bundle, run = Path(directory) / "bundle", Path(directory) / "run"
                with patch("math_gauge.reliability.invoke_conversation", side_effect=AssertionError("no model calls")):
                    with self.assertRaisesRegex(ValueError, "frozen turn timeout"):
                        execute_reliability_run(plan, self.suite, run, command=["never-executed-fixture"])
                    with self.assertRaisesRegex(ValueError, "frozen turn timeout"):
                        export_harness_bundle(plan, self.suite, bundle)
                self.assertFalse(run.exists())
                self.assertFalse(bundle.exists())
                with self.assertRaisesRegex(ValueError, "frozen turn timeout"):
                    _execution_projection(plan, {s["case_id"] for s in select_slots(plan)})

    def test_outer_runner_receives_10800_and_other_lean_remains_5400(self):
        for targets, seconds, count in ((["c003-180"], 10800, 1), (["lean-90"], 5400, 7)):
            with self.subTest(targets=targets), tempfile.TemporaryDirectory() as directory:
                plan = build_plan(self.future, self.suite, targets, runtime=self.runtime(seconds))
                with patch("math_gauge.reliability.invoke_conversation", return_value={
                    "stdout": "Synthetic transport fixture; no mathematical claim.", "status": "ok", "exit_code": 0
                }) as invoke:
                    meta = execute_reliability_run(plan, self.suite, Path(directory) / "run",
                                                   command=["never-executed-fixture"])
                self.assertEqual(invoke.call_count, count)
                self.assertTrue(all(call.args[3] == seconds for call in invoke.call_args_list))
                self.assertEqual(meta["timeout_seconds"], seconds)

    def test_generic_cli_default_remains_120_seconds(self):
        parsed = parser().parse_args(["run", "--out", "unused", "--command-json", "[]"])
        self.assertEqual(parsed.timeout, 120)


if __name__ == "__main__":
    unittest.main()
