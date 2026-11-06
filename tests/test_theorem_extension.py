"""Synthetic judgments exercise research credit, penalties and A1 provenance."""

import copy
import json
import hashlib
from pathlib import Path
import tempfile
import unittest

from math_gauge.benchmarks import BenchmarkProfile, build_plan
from math_gauge.catalog import Suite
from math_gauge.records import project_assessment_score, descriptor, load_theorem_extension_inputs
from math_gauge.scoring import score_assessment_inputs
from math_gauge.theorem_extension import validate_inputs

ROOT = Path(__file__).resolve().parents[1]


class TheoremExtensionScoringTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        suite = Suite.load(ROOT / "cases")
        profile = BenchmarkProfile.load(ROOT / "protocol/benchmark-profile.json", suite)
        cls.plan = build_plan(profile, suite, runtime={"model_label": "SYNTHETIC-RESEARCH",
            "adapter_identity": {"kind": "fixture"}, "budget": {"timeout_seconds": 10800},
            "execution_track": "math-gauge.local-tools-no-search/v1"})
        cls.policy = profile.data["assessment_policy"]
        cls.strict = json.loads((ROOT / "protocol/strict-scoring-policy.json").read_text())
        public = [copy.deepcopy(c) for c in cls.plan["case_index"] if c["component"] == "theorem-extension"]
        for case in public:
            case["source_visibility"] = "public"
            case["contract_sha256"] = case["group_contract_sha256"]
            original = suite.cases[case["case_id"]]
            case["task_sha256"] = hashlib.sha256(suite.case_file(original, original["task"]).read_bytes()).hexdigest()
        cls.cases = public
        for number in range(3):
            case = copy.deepcopy(public[0])
            case.update(case_id=f"Fixture-Private-{number}", family_id=f"Fixture-Private-{number}",
                        source_visibility="private")
            cls.cases.append(case)

    def research(self, levels=(2, 3, 1, 1, 0), baselines=(2, 2, 2, 2, 2)):
        data = {"schema": "math-gauge.theorem-extension-inputs/v1", "benchmark_version": "0.6.0",
            "model_label": self.plan["model_label"], "attempt_labels": ["A1"],
            "research_invitation_included": False, "case_index": copy.deepcopy(self.cases),
            "slots": [], "formal_comparison_eligible": False, "human_review": "pending"}
        for case, level, baseline in zip(self.cases, levels, baselines):
            data["slots"].append({"case_id": case["case_id"], "slot_id": case["case_id"] + ":A1",
                "attempt_label": "A1", "status": "response_received_execution_unverified",
                "baseline_B": baseline, "research_R": level,
                "response": {"path": "fixture/answer.md", "sha256": "a" * 64},
                "review": {"path": "fixture/review.json", "sha256": "b" * 64}})
        return data

    def score(self, data, mode="partial"):
        return score_assessment_inputs({"plan": self.plan, "model_label": self.plan["model_label"], "slots": []},
            self.policy, self.strict, mode=mode, theorem_extension_inputs=data)

    def test_five_families_are_equal_and_invited_results_do_not_backfill(self):
        data = self.research()
        ordinary, strict = self.score(data), self.score(data, "strict")
        self.assertAlmostEqual(ordinary["contributions"]["theorem-extension"]["exact"], 14 / 3)
        self.assertEqual(strict["contributions"]["theorem-extension"]["exact"], 2)
        data["slots"][0]["attempt_label"] = "A2"
        with self.assertRaises(ValueError):
            self.score(data)

    def test_correct_baseline_without_extension_is_zero_but_incorrect_baseline_is_negative(self):
        for baseline, expected in ((2, 0), (1, -10 / 3), (0, -20 / 3)):
            with self.subTest(baseline=baseline):
                result = self.score(self.research((0,) * 5, (baseline,) * 5))
                self.assertAlmostEqual(result["contributions"]["theorem-extension"]["exact"], expected)
                self.assertEqual(result["metrics"]["earned"]["confirmed"], 0)
                research_tasks = [t for t in result["tasks"] if t["subcategory"] == "theorem-extension"]
                self.assertTrue(all(t["research"]["baseline_B"] == baseline for t in research_tasks))

    def test_strict_requires_correct_baseline_even_with_complete_independent_extension(self):
        data = self.research((3,) * 5, (1,) * 5)
        self.assertAlmostEqual(self.score(data)["contributions"]["theorem-extension"]["exact"], 20 / 3)
        self.assertEqual(self.score(data, "strict")["contributions"]["theorem-extension"]["exact"], 0)

    def test_unrun_slots_keep_the_fixed_denominator_and_possible_penalty_bounds(self):
        data = self.research()
        for row in data["slots"]:
            row.update(status="not_run", baseline_B=None, research_R=None, response=None, review=None)
        result = self.score(data)
        metric = result["contributions"]["theorem-extension"]
        self.assertAlmostEqual(metric["lower"], -20 / 3)
        self.assertEqual(metric["upper"], 10)
        self.assertIsNone(metric["exact"])
        self.assertEqual(result["metrics"]["theorem-extension"]["coverage"]["planned"], 5)
        self.assertEqual(result["metrics"]["earned"]["confirmed"], 0)

    def test_missing_delivery_is_zero_without_a_mathematical_error_penalty(self):
        data = self.research()
        for row in data["slots"]:
            row.update(status="delivery_failed", baseline_B=None, research_R=0, response=None,
                       review=None, failure_reason="service_error", execution={"sha256": "c" * 64})
        self.assertEqual(self.score(data)["contributions"]["theorem-extension"]["exact"], 0)
        self.assertEqual(self.score(data, "strict")["contributions"]["theorem-extension"]["exact"], 0)

    def test_policy_and_public_projection_preserve_the_privacy_and_no_invitation_boundaries(self):
        changed = copy.deepcopy(self.policy["theorem_extension"])
        changed["research_invitation"] = True
        with self.assertRaises(ValueError):
            validate_inputs(self.research(), changed)
        public = project_assessment_score(self.score(self.research()))
        self.assertEqual(public["private_case_count"], 6)
        self.assertNotIn("tasks", public)
        self.assertNotIn("Fixture-Private-", json.dumps(public))

    def test_archive_rejects_invited_review_even_when_its_extension_is_complete(self):
        data = self.research()
        data["policy"] = self.policy["theorem_extension"]
        for row in data["slots"]:
            row.update(status="not_run", baseline_B=None, research_R=None, response=None, review=None)
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            raw = b"Synthetic final answer.\n"
            (root / "answer.md").write_bytes(raw)
            (root / "task.md").write_bytes((ROOT / "cases/theorem-extension/MG-TX001/task.md").read_bytes())
            (root / "execution.json").write_text(json.dumps({"kind": "math", "status": "completed",
                "exit_code": 0, "request_count": 1, "tool_events": [], "tool_mismatch": None,
                "fixture_only": True}))
            review = {"stage": "A1", "B": 2, "R": 3,
                      "answer_sha256": hashlib.sha256(raw).hexdigest()}
            row = data["slots"][0]
            row.update(status="response_received_execution_unverified", baseline_B=2, research_R=3,
                response=descriptor(root, root / "answer.md"),
                original_input=descriptor(root, root / "task.md"),
                source_prompt_sha256=hashlib.sha256((root / "task.md").read_bytes()).hexdigest(),
                execution=descriptor(root, root / "execution.json"), invited_answer_used=False)
            def archive():
                (root / "review.json").write_text(json.dumps(review))
                row["review"] = descriptor(root, root / "review.json")
                (root / "inputs.json").write_text(json.dumps(data))
                return {"theorem_extension_inputs": descriptor(root, root / "inputs.json")}
            load_theorem_extension_inputs(root, archive())
            review["stage"] = "A2"
            with self.assertRaisesRegex(ValueError, "original A1"):
                load_theorem_extension_inputs(root, archive())


if __name__ == "__main__":
    unittest.main()
