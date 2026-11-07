"""Selection is a new aggregation view, never a rewrite of source evidence."""
import copy
import json
from pathlib import Path
import unittest

from math_gauge.benchmarks import identity, validate_assessment_policy, validate_plan
from math_gauge.case_selection import CANONICAL_PARENT_FAMILIES, RETIRED_PUBLIC_CASE_IDS
from math_gauge.scoring import score_assessment_inputs


ROOT = Path(__file__).resolve().parents[1]


def selection_for(plan):
    public = [row["case_id"] for row in plan["case_index"] if row["component"] != "exploration"]
    return {"schema": "math-gauge.case-selection/v1", "version": "0.1.0",
        "public_case_ids": [cid for cid in public if cid not in RETIRED_PUBLIC_CASE_IDS],
        "retired_public_case_ids": sorted(RETIRED_PUBLIC_CASE_IDS), "source_public_case_ids": public,
        "canonical_parent_families": dict(CANONICAL_PARENT_FAMILIES),
        "source_revision": "292c26709785836c27a847cdf113fda4f34f5af7"}


def assessment_policy(plan, *, selected=True):
    # Exercise the immutable pre-research 0.5 selection contract. The current
    # 0.6 policy adds a distinct component; it cannot serve as this fixture.
    policy = json.loads((ROOT / "protocol/scoring-policy.json").read_bytes())
    policy["version"] = "0.5.0"
    policy["score_modes"] = ["partial", "strict"]
    for key in ("default_score_mode", "capability_policy_version", "score_mode_catalog_version"):
        policy.pop(key, None)
    policy.pop("theorem_extension", None)
    policy.pop("background_check", None)
    background=next(row for row in policy["subcategories"] if row["id"]=="background-check")
    background.update(source_components=[],public_tasks=0,private_tasks=0,families=0,status="under_construction")
    research = next(row for row in policy["subcategories"] if row["id"] == "theorem-extension")
    research.update(source_components=[], public_tasks=0, private_tasks=0,
                    families=0, status="under_construction")
    policy.pop("case_selection", None)
    policy["subcategories"][0].update(public_tasks=8 if selected else 14, families=11 if selected else 17)
    public, total, families = (20, 23, 19) if selected else (26, 29, 21)
    policy["scope"].update(public_tasks=public, private_tasks=3, tasks=total, parent_families=families,
                           initial_slots=total, public_initial_slots=public)
    if selected:
        policy["case_selection"] = selection_for(plan)
    return policy


class CaseSelectionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        path = ROOT / "results/v0.6.0/gemini-3.8-flash-high/20261105/scoring-inputs.json"
        cls.source_bytes = path.read_bytes()
        cls.source = json.loads(cls.source_bytes)
        cls.strict = json.loads((ROOT / "protocol/strict-scoring-policy.json").read_bytes())
        cls.policy = assessment_policy(cls.source["plan"])

    def inputs(self):
        plan = copy.deepcopy(self.source["plan"])
        return {"plan": plan, "model_label": plan["model_label"], "slots": [
            {"slot_id": row["case_id"] + ":A1", "case_id": row["case_id"],
             "completion": {"lower": 1, "upper": 1, "exact": 1}, "strict_pass": True}
            for row in plan["case_index"]]}

    def score(self, inputs=None, policy=None, mode="partial"):
        return score_assessment_inputs(self.inputs() if inputs is None else inputs,
            self.policy if policy is None else policy, self.strict, mode=mode,
            strict_trajectory={"strict_pass": True})

    def test_retired_scores_cannot_affect_either_current_mode(self):
        inputs = self.inputs()
        for row in inputs["slots"]:
            if row["case_id"] in RETIRED_PUBLIC_CASE_IDS:
                row.update(completion={"lower": 0, "upper": 0, "exact": 0}, strict_pass=False)
        for mode in ("partial", "strict"):
            with self.subTest(mode=mode):
                self.assertEqual(self.score(inputs, mode=mode), self.score(mode=mode))
        self.assertEqual(len(self.score()["tasks"]), 20)
        self.assertEqual(self.score()["whole_task_counts"],
                         {"planned": 23, "passed": 20, "failed": 0, "unknown": 3})

    def test_missing_kept_answer_retains_the_eleven_family_denominator(self):
        inputs = self.inputs()
        inputs["slots"] = [row for row in inputs["slots"] if row["case_id"] != "MG-GP001"]
        result = self.score(inputs)
        metric = result["metrics"]["written-argument"]
        self.assertEqual(metric["coverage"]["planned"], 11)
        self.assertAlmostEqual(metric["upper"] - metric["lower"], 100 * 4 / 11)
        self.assertEqual(result["whole_task_counts"]["unknown"], 4)
        self.assertEqual(next(row for row in result["tasks"] if row["case_id"] == "MG-GP001")
                         ["completion"], {"lower": 0.0, "upper": 1.0, "exact": None})

    def test_unknown_duplicate_partition_and_parent_selector_errors_are_rejected(self):
        changes = [lambda s: s["public_case_ids"].__setitem__(0, "UNKNOWN"),
            lambda s: s["public_case_ids"].__setitem__(0, s["public_case_ids"][1]),
            lambda s: s["source_public_case_ids"].__setitem__(0, "UNKNOWN"),
            lambda s: s["retired_public_case_ids"].__setitem__(0, "MG-GP001"),
            lambda s: s["canonical_parent_families"].update({"MG-GR104": "WRONG"}),
            lambda s: s.update(version="unknown")]
        for change in changes:
            policy = copy.deepcopy(self.policy)
            change(policy["case_selection"])
            with self.subTest(change=change), self.assertRaisesRegex(ValueError, "case selection"):
                self.score(policy=policy)
        policy = copy.deepcopy(self.policy)
        selector = policy["case_selection"]
        replaced = selector["public_case_ids"][0]
        selector["public_case_ids"][0] = "UNKNOWN"
        selector["source_public_case_ids"][selector["source_public_case_ids"].index(replaced)] = "UNKNOWN"
        with self.assertRaisesRegex(ValueError, "source task inventory"):
            self.score(policy=policy)

    def test_selector_cannot_change_fixed_scope_or_admit_four_private_tasks(self):
        for update in ({"tasks": 24}, {"private_tasks": 4}, {"parent_families": 17}):
            policy = copy.deepcopy(self.policy)
            policy["scope"].update(update)
            with self.subTest(update=update), self.assertRaisesRegex(ValueError, "fixed denominators"):
                self.score(policy=policy)

    def test_legacy_policy_and_source_plan_identities_remain_unchanged(self):
        original = copy.deepcopy(self.source)
        legacy = assessment_policy(self.source["plan"], selected=False)
        validate_assessment_policy(legacy)
        before = self.score(self.source, legacy)
        selected = self.score(self.source)
        self.assertEqual(self.source, original)
        self.assertEqual(self.score(self.source, legacy), before)
        self.assertEqual(len(before["tasks"]), 26)
        self.assertEqual(selected["plan_sha256"], before["plan_sha256"])
        self.assertEqual(selected["case_selection_sha256"], identity(self.policy["case_selection"]))
        self.assertEqual(self.source_bytes, (ROOT / "results/v0.6.0/gemini-3.8-flash-high/20261105/scoring-inputs.json").read_bytes())

    def test_ar_parent_families_remain_canonical_with_or_without_retired_parents(self):
        from math_gauge.case_selection import assessment_family, selected_assessment_cases
        full = {row["case_id"]: row for row in self.source["plan"]["case_index"]}
        selected = selected_assessment_cases(full, self.policy["case_selection"])
        reviews = [case for case in full.values() if case["contract_kind"] == "answer_review"]
        for case in reviews:
            expected = CANONICAL_PARENT_FAMILIES[case["parent_family_id"]]
            self.assertEqual(assessment_family(case, full, self.policy["case_selection"]), expected)
            self.assertEqual(assessment_family(case, selected, self.policy["case_selection"]), expected)
        families = {assessment_family(case, selected, self.policy["case_selection"])
                    for case in selected.values()}
        self.assertEqual(len(families), 16)
        self.assertEqual({row["family_id"] for row in self.score()["tasks"]
                          if row["subcategory"] == "argument-review"}, set(CANONICAL_PARENT_FAMILIES.values()))

    def test_all_exploration_members_are_retained_and_missing_private_slots_stay_unknown(self):
        from math_gauge.case_selection import selected_assessment_cases
        cases = {row["case_id"]: row for row in self.source["plan"]["case_index"]}
        for number in range(1, 4):
            cases[f"SYN-PRIVATE-{number}"] = {"component": "exploration", "family_id": f"private-{number}"}
        selected = selected_assessment_cases(cases, self.policy["case_selection"])
        self.assertEqual(len(selected), 23)
        self.assertTrue(all(f"SYN-PRIVATE-{number}" in selected for number in range(1, 4)))
        cases["SYN-PRIVATE-4"] = {"component": "exploration", "family_id": "private-4"}
        with self.assertRaisesRegex(ValueError, "source task inventory"):
            selected_assessment_cases(cases, self.policy["case_selection"])

    def test_combined_source_plan_keeps_all_three_private_arguments(self):
        inputs = self.inputs()
        plan, data = inputs["plan"], inputs["plan"]["profile"]["data"]
        for key in ("case_execution_policy", "supplement_policy", "execution_groups"):
            data.pop(key, None)
        for component in data["components"]:
            component["weight"] *= .75
        data["components"].insert(-1, {"id": "exploration", "weight": 25,
            "aggregation": "family", "case_ids": [f"SYN-PRIVATE-{n}" for n in range(1, 4)]})
        template = copy.deepcopy(plan["case_index"][1])
        for number in range(1, 4):
            cid = f"SYN-PRIVATE-{number}"
            case = dict(template, case_id=cid, family_id=f"private-{number}", component="exploration",
                task_kind="exploration", contract_kind="research_exploration", track="exploration",
                source_visibility="private", stages=[{"stage_id": "judgment", "points": 100,
                                                       "lean_required": False}], total_weight=100)
            plan["case_index"].append(case)
            data["attempt_schedule"][cid] = ["A1"]
            slot = dict(plan["slots"][0], case_id=cid, slot_id=cid + ":A1",
                        ordinal_per_model=len(plan["slots"]) + 1)
            plan["slots"].append(slot)
            inputs["slots"].append({"case_id": cid, "slot_id": cid + ":A1", "strict_pass": True,
                                    "completion": {"lower": 1, "upper": 1, "exact": 1}})
        for key in ("papers", "independent_slots", "all_slots", "selected_slots"):
            plan["planned"][key] += 3
        plan["profile"]["data_sha256"] = identity(data)
        plan["plan_sha256"] = identity({key: value for key, value in plan.items() if key != "plan_sha256"})
        validate_plan(plan)
        result = self.score(inputs, mode="strict")
        self.assertEqual(result["whole_task_counts"], {"planned": 23, "passed": 23, "failed": 0, "unknown": 0})
        self.assertEqual(result["metrics"]["written-argument"]["exact"], 100)
        self.assertEqual(result["metrics"]["earned"]["exact"], 70)
        inputs["slots"] = [row for row in inputs["slots"] if row["case_id"] != "SYN-PRIVATE-1"]
        missing = self.score(inputs, mode="strict")
        self.assertEqual(missing["whole_task_counts"]["unknown"], 1)
        metric = missing["metrics"]["written-argument"]
        self.assertEqual(metric["coverage"]["planned"], 11)
        self.assertAlmostEqual(metric["upper"] - metric["lower"], 100 / 11)


if __name__ == "__main__":
    unittest.main()
