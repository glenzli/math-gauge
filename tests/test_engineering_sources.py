"""The score must use all four sealed sources without rewriting original answers."""

import copy
import json
from pathlib import Path
import tempfile
import unittest

from math_gauge.records import descriptor, validate_formalization_review
from math_gauge.scoring import score_record_inputs

ROOT = Path(__file__).resolve().parents[1]


class EngineeringSourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = ROOT / "results/v0.6.0/gemini-3.8-flash-high/20261105"
        load = lambda name: json.loads((cls.root / name).read_bytes())
        cls.inputs = load("scoring-inputs.json")
        cls.alignment = load("reviews/alignment.json")
        cls.policy = load("scoring-policy.json")
        cls.formalization = load("reviews/formalization.json")

    def score(self, formalization=None):
        return score_record_inputs(self.inputs, self.alignment, self.policy,
            formalization_review=self.formalization if formalization is None else formalization)

    def test_all_four_engineering_sources_reproduce_counts_and_family_aggregation(self):
        result = self.score()
        cases = result["lean_formalization_breakdown"]["cases"]
        self.assertEqual({row["case_id"]: (row["complete_count"], row["total"]) for row in cases},
                         {"LCH01": (8, 8), "LCH02": (19, 20), "HCH02": (38, 40), "MG-C003": (74, 92)})
        self.assertAlmostEqual(result["metrics"]["lean-formalization"]["exact"],
                               ((100 + 95 + 95) / 3 + 74 / 92 * 100) / 2)
        self.assertTrue(validate_formalization_review(self.root, self.inputs, self.formalization)["passed"])

    def test_method_requires_every_case_and_the_original_model_response(self):
        with self.assertRaisesRegex(ValueError, "identity"):
            score_record_inputs(self.inputs, self.alignment, self.policy)
        for mutation in ("missing", "duplicate", "model", "response", "version", "obligation"):
            changed = copy.deepcopy(self.formalization)
            case = changed["cases"][0]
            if mutation == "missing":
                changed["cases"].pop()
            elif mutation == "duplicate":
                changed["cases"][1] = copy.deepcopy(case)
            elif mutation == "model":
                changed["model_label"] = "OTHER MODEL"
            elif mutation == "response":
                case["original_response_sha256"] = "0" * 64
            elif mutation == "version":
                case["case_version"] = "unrelated"
            else:
                case["obligations"][0]["id"] = "UNRELATED"
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                self.score(changed)

    def test_method_rejects_a_policy_selecting_only_some_engineering_sources(self):
        changed = copy.deepcopy(self.policy)
        changed["formalization_source_policy"]["case_ids"].remove("HCH02")
        with self.assertRaisesRegex(ValueError, "four-case engineering source policy"):
            score_record_inputs(self.inputs, self.alignment, changed, formalization_review=self.formalization)

    def test_unknowns_keep_the_case_and_family_denominators(self):
        changed = copy.deepcopy(self.formalization)
        case = next(row for row in changed["cases"] if row["case_id"] == "HCH02")
        item = next(row for row in case["obligations"] if row["complete"] is True)
        item["complete"] = None
        result = self.score(changed)
        overall = result["metrics"]["overall"]
        self.assertIsNone(overall["exact"])
        self.assertAlmostEqual(overall["upper"] - overall["lower"], 100 * .7 * .3 / 2 / 3 / 40)
        self.assertAlmostEqual(overall["upper"], self.score()["metrics"]["overall"]["exact"])

    def test_c003_matches_individual_parent_judgments_and_source_not_only_count(self):
        for mutation in ("same_count_different_items", "source"):
            changed = copy.deepcopy(self.formalization)
            case = next(row for row in changed["cases"] if row["case_id"] == "MG-C003")
            if mutation == "source":
                case["source_sha256"] = "0" * 64
            else:
                yes = next(row for row in case["obligations"] if row["complete"] is True)
                no = next(row for row in case["obligations"] if row["complete"] is False)
                yes["complete"], no["complete"] = False, True
                no["declarations"] = copy.deepcopy(yes["declarations"])
            with self.subTest(mutation=mutation), self.assertRaisesRegex(ValueError, "alignment-study parent"):
                self.score(changed)

    def test_source_selection_does_not_promote_execution_or_change_followups(self):
        old_policy = dict(self.policy, version="0.3.0")
        old_alignment = dict(self.alignment, scoring_version="0.3.0")
        old = score_record_inputs(self.inputs, old_alignment, old_policy)
        current = self.score()
        self.assertAlmostEqual(current["metrics"]["overall"]["exact"] - old["metrics"]["overall"]["exact"], 3.325)
        for name in ("repeat", "stance", "neutral_written", "lean_alignment_selfcheck", "strict_pass_rate"):
            self.assertEqual(current["metrics"][name], old["metrics"][name], name)
        new_steps = dict(current["alignment_selfcheck"])
        old_steps = dict(old["alignment_selfcheck"])
        new_steps.pop("scoring_version")
        old_steps.pop("scoring_version")
        self.assertEqual(new_steps, old_steps)
        self.assertFalse(current["formal_comparison_eligible"])

    def test_completed_claim_needs_kernel_and_actual_declaration(self):
        for mutation in ("kernel", "empty_declarations", "missing_declaration"):
            changed = copy.deepcopy(self.formalization)
            case = changed["cases"][0]
            item = next(row for row in case["obligations"] if row["complete"] is True)
            if mutation == "kernel":
                case["kernel_status"] = "failed"
            elif mutation == "empty_declarations":
                item["declarations"] = []
            else:
                item["declarations"][0]["name"] = "unproved_candidate_claim"
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                validate_formalization_review(self.root, self.inputs, changed)

    def test_sealed_source_compiler_contract_and_predecessor_are_not_interchangeable(self):
        for mutation in ("sealed_hash", "source_file", "kernel_report", "contract", "predecessor"):
            changed = copy.deepcopy(self.formalization)
            case, other = changed["cases"][:2]
            if mutation == "sealed_hash":
                case["source_sha256"] = "0" * 64
            elif mutation == "source_file":
                name = next(iter(case["source_files"]))
                case["source_files"][name] = next(iter(other["source_files"].values()))
            elif mutation == "kernel_report":
                case["kernel_report"] = other["kernel_report"]
            elif mutation == "contract":
                case["case_contract"] = other["case_contract"]
            else:
                case["background_inputs"] = {}
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                validate_formalization_review(self.root, self.inputs, changed)

    def test_rehashed_kernel_report_cannot_claim_a_different_compiled_module(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            review = copy.deepcopy(self.formalization)
            for case in review["cases"]:
                case["review_evidence"] = []

            def localize(value):
                if isinstance(value, dict):
                    if {"path", "bytes", "sha256"} <= value.keys():
                        target = root / value["path"]
                        target.parent.mkdir(parents=True, exist_ok=True)
                        target.write_bytes((self.root / value["path"]).read_bytes())
                    for item in value.values():
                        localize(item)
                elif isinstance(value, list):
                    for item in value:
                        localize(item)

            localize(review)
            case = review["cases"][0]
            path = root / case["kernel_report"]["path"]
            original = json.loads(path.read_bytes())
            for mutation in ("different_source", "missing_module"):
                kernel = copy.deepcopy(original)
                module = next(row for row in kernel["modules"] if row["module"] == "Main")
                if mutation == "different_source":
                    module["source_sha256"] = "0" * 64
                else:
                    kernel["modules"].remove(module)
                path.write_text(json.dumps(kernel))
                case["kernel_report"] = descriptor(root, path)
                with self.subTest(mutation=mutation), self.assertRaisesRegex(ValueError, "Kernel module receipts"):
                    validate_formalization_review(root, self.inputs, review)


if __name__ == "__main__":
    unittest.main()
