"""Current version and operator-return rules at the immutable dataset boundary."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from math_gauge.benchmarks import BenchmarkProfile, build_plan
from math_gauge.catalog import Suite
from math_gauge.harness import export_simple_release_dataset, inspect_release_dataset

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("current_release", ROOT / "scripts/release.py")
RELEASE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RELEASE)


class CurrentReleaseTests(unittest.TestCase):

    def test_execution_groups_do_not_duplicate_component_denominators(self):
        suite = Suite.load(ROOT / "cases")
        plan = build_plan(BenchmarkProfile.load(ROOT / "protocol/benchmark-profile.json", suite), suite)
        config = RELEASE.load_config()
        edition = json.loads((ROOT / "benchmark.json").read_bytes())
        self.assertEqual(RELEASE.VERSION, edition["version"])
        self.assertEqual(config["release_version"], config["suite_version"])
        self.assertEqual((config["case_count"], config["slot_count"]),
                         (len(suite.cases), plan["planned"]["all_slots"]))
        with tempfile.TemporaryDirectory() as directory:
            dest = Path(directory).resolve() / "dataset"
            with patch("subprocess.Popen", side_effect=AssertionError("No candidate or Lean call")):
                manifest = export_simple_release_dataset(plan, suite, dest, release_version="0.6.0",
                    readme=(ROOT / config["readme"]).read_bytes(), extra_files={
                        "LICENSE": (ROOT / "LICENSE").read_bytes(),
                        "THIRD_PARTY_NOTICES.md": (ROOT / config["third_party_notices"]).read_bytes()})
                self.assertEqual(inspect_release_dataset(dest, plan=plan, suite=suite), manifest)
            sizes = {name: len(ids) for name, ids in manifest["target_slot_ids"].items()}
            self.assertEqual({k: sizes[k] for k in ["proofs", "lean-audit", "lean-formalization", "answer-review", "theorem-extension", "background-check"]},
                             {"proofs": 8, "lean-audit": 4, "lean-formalization": 4, "answer-review": 4, "theorem-extension": 2, "background-check": 2})
            self.assertEqual({k: sizes[k] for k in ["c003-180", "lean-90", "written-new-panel", "written-refresh"]},
                             {"c003-180": 1, "lean-90": 7, "written-new-panel": 2, "written-refresh": 3})
            self.assertEqual(manifest["planned"]["all_slots"], 24)
            guide = (dest / "README.md").read_text()
            for phrase in ["self-assessment", "UTF-8", "KEEP/FULL", "last prescribed delivery", "fixed denominators"]:
                self.assertIn(phrase, guide)
            self.assertFalse(any(p.name in {"reference.md", "rubric.json", "record.json", "scoring-policy.json"}
                                 for p in dest.rglob("*")))
            # The embedded stdlib controller must admit the new component,
            # independently of the installed evaluator's target registry.
            checked = subprocess.run([sys.executable, "-I", "-S", "-B",
                str(dest / "tools/benchmark.py"), "check"], cwd=directory,
                capture_output=True, check=False)
            self.assertEqual(checked.returncode, 0, checked.stderr)


if __name__ == "__main__":
    unittest.main()
