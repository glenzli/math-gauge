"""Version0.6 fixed denominators, family weighting and source-condition boundaries."""

import copy
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from benchmark_fixtures import source_profile, source_suite
from math_gauge.benchmarks import BenchmarkProfile, build_plan, identity, validate_plan, select_slots
from math_gauge.catalog import Suite, read_json, write_json
from math_gauge.execution_policy import execution_context
from math_gauge.harness import export_harness_bundle, inspect_harness_bundle
from math_gauge.reliability import execute_reliability_run
from math_gauge.reliability_review import apply_reliability_reviews, reliability_review_templates
from math_gauge.scoring import _compose_score_sources, public_score_projection, score_inputs
from test_scoring import fixture_rows

ROOT = Path(__file__).resolve().parents[1]
RUNTIME = {"model_label": "v06-offline-fixture", "adapter_identity": {"kind": "fixture"},
           "execution_track": "math-gauge.local-tools-no-search/v1",
           "candidate_parameters": {"model": "synthetic-no-model"},
           "budget": {"timeout_seconds": 5400}, "fresh_context": True}


class V06IntegrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.suite = Suite.load(ROOT / "cases")
        cls.profile = BenchmarkProfile.load(ROOT / "protocol/benchmark-profile.json", cls.suite)
        cls.plan = build_plan(cls.profile, cls.suite, runtime=RUNTIME)
        cls.old_suite = source_suite()
        cls.old_profile = source_profile(cls.old_suite)

    def score(self, rows):
        return score_inputs({"plan": self.plan, "model_label": RUNTIME["model_label"], "slots": rows})

    def test_default_reserve_and_family_counts_come_from_actual_contracts(self):
        self.assertEqual(self.plan["planned"], {"papers": 26, "independent_slots": 30,
            "neutral_slots": 4, "stance_slots": 8, "all_slots": 42, "selected_slots": 42})
        self.assertFalse((ROOT / "cases/reserve-suite.json").exists())
        self.assertEqual(len({x["family_id"] for x in self.plan["case_index"]
                              if x["contract_kind"] != "answer_review"}), 18)
        self.assertEqual(sum(len(x.get("stages", [])) for x in self.plan["case_index"]), 226)
        self.assertEqual(sum(len(x.get("criteria", [])) for x in self.plan["case_index"]), 15)
        audits = [x for x in self.plan["case_index"] if x["contract_kind"] == "semantic_audit"]
        self.assertEqual(sum(len(x["dimensions"]) for x in audits), 16)
        self.assertTrue(all("stages" not in x and x["assessment_unit"] == "review_dimension" for x in audits))
        supplement = select_slots(self.plan, ["lean-audit", "lean-formalization"])
        self.assertEqual(len(supplement), 8)
        self.assertEqual(sum(x["kind"] == "independent" and x["attempt_label"] == "A1" for x in supplement), 8)

    def test_family_first_prevents_three_ch02_ladders_from_tripling_weight(self):
        rows = fixture_rows(self.plan)
        for row in rows:
            if row["case_id"] == "MG-C003":
                row["completion"] = {"lower": 0, "upper": 0, "exact": 0}
        result = self.score(rows)
        self.assertEqual(result["metrics"]["lean-formalization"]["exact"], 50)
        self.assertEqual(result["metrics"]["lean-formalization"]["coverage"]["planned"], 2)
        self.assertEqual(result["metrics"]["core"]["exact"], 85)
        self.assertEqual(result["component_families"]["lean-formalization"]["oet-volume1-chapter02"]["variant_count"], 3)
        rows = [row for row in rows if row["slot_id"] != "HCH02:A1"]
        missing = self.score(rows)["metrics"]["lean-formalization"]
        self.assertIsNone(missing["exact"])
        self.assertLessEqual(missing["lower"], 100 / 3)
        self.assertEqual(missing["upper"], 50)
        self.assertEqual(missing["coverage"]["planned"], 2)

    def test_source_condition_fixture_preserves_current_candidate_identity(self):
        source = build_plan(self.old_profile, self.old_suite, runtime=RUNTIME)
        self.assertEqual(source["planned"]["all_slots"], 42)
        self.assertEqual(len(source["case_index"]), 26)
        current = {row["case_id"]: row for row in self.plan["case_index"]}
        for case in source["case_index"]:
            for key in ["request_sha256", "candidate_message_sha256", "group_contract_sha256"]:
                self.assertEqual(case[key], current[case["case_id"]][key])

    def test_not_run_public_projection_keeps_every_slot_missing(self):
        result = self.score([])
        public = public_score_projection(result, self.plan, private_aliases={})
        self.assertIsNone(public["metrics"]["overall"]["exact"])
        self.assertEqual(public["coverage"]["slots_planned"], 42)
        self.assertEqual(public["coverage"]["slots_reviewed"], 0)
        self.assertEqual(len(public["slot_evidence"]), 42)
        self.assertEqual(next(x for x in public["profile"]["components"] if x["id"] == "lean-formalization")["weight"], 30)

    def test_supplement_export_uses_shared_controller_and_exact_own_history(self):
        for target, seconds, count in [("lean-90", 5400, 7), ("c003-180", 10800, 1)]:
            runtime = copy.deepcopy(RUNTIME)
            runtime["budget"]["timeout_seconds"] = seconds
            plan = build_plan(self.profile, self.suite, [target], runtime=runtime)
            with tempfile.TemporaryDirectory() as directory:
                out = Path(directory) / "bundle"
                with patch("subprocess.Popen", side_effect=AssertionError("export must not call a model")):
                    export_harness_bundle(plan, self.suite, out)
                    bundle = inspect_harness_bundle(out, plan=plan, suite=self.suite)
                self.assertEqual(bundle["exported_slots"], count)
                self.assertEqual(bundle["planned"]["all_slots"], 42)
                self.assertNotIn("case_execution_policy", (out / "manifest.json").read_text())
                self.assertNotIn("expected_truth", (out / "manifest.json").read_text())

    def test_stratified_reuse_preserves_written_source_conditions_and_new_lean_budget(self):
        old_runtime = copy.deepcopy(RUNTIME)
        old_runtime.update(system_prompt="Original source system")
        old_runtime["budget"]["timeout_seconds"] = 2700
        old = build_plan(self.old_profile, self.old_suite, runtime=old_runtime)
        old_slot_ids = {row["slot_id"] for row in old["slots"]}
        lean_ids = {row["slot_id"] for row in select_slots(self.plan,["lean-audit","lean-formalization"])}
        new_ids = {row["slot_id"] for row in select_slots(self.plan,["written-new-panel"])} | lean_ids
        old_rows = [row for row in fixture_rows(old) if row["slot_id"] in {s["slot_id"] for s in self.plan["slots"]} - new_ids]
        self.assertEqual(len(old_rows), 24)
        fresh_rows = [row for row in fixture_rows(self.plan) if row["slot_id"] in lean_ids and row["case_id"] != "MG-C003"]
        long_runtime = copy.deepcopy(RUNTIME)
        long_runtime["budget"]["timeout_seconds"] = 10800
        long_plan = build_plan(self.profile, self.suite, runtime=long_runtime)
        long_rows = [row for row in fixture_rows(long_plan) if row["slot_id"] == "MG-C003:A1"]
        written_rows = [row for row in fixture_rows(self.plan) if row["slot_id"] in new_ids - lean_ids]
        written_plan = build_plan(self.profile,self.suite,runtime=old_runtime)
        result = _compose_score_sources(self.plan, [
            {"plan": old, "model_label": RUNTIME["model_label"], "slots": old_rows},
            {"plan": self.plan, "model_label": RUNTIME["model_label"], "slots": fresh_rows},
            {"plan": long_plan, "model_label": RUNTIME["model_label"], "slots": long_rows},
            {"plan": written_plan, "model_label": RUNTIME["model_label"], "slots": written_rows}],
            budget_policy="retain_source_budgets")
        self.assertIsNone(result["metrics"]["overall"]["exact"])
        self.assertIsNone(result["metrics"]["overall"]["formal_exact"])
        self.assertEqual(result["composition"]["method"], "post-observation mixed-condition development")
        self.assertEqual(result["composition"]["case_execution_strata"]["MG-GR002"]["conditions"]["timeout_seconds"], 2700)
        changed = copy.deepcopy(old_runtime)
        changed["budget"]["timeout_seconds"] = 3000
        drift = build_plan(self.old_profile, self.old_suite, runtime=changed)
        with self.assertRaisesRegex(ValueError, "drift within one case"):
            _compose_score_sources(self.plan, [
                {"plan": old, "model_label": RUNTIME["model_label"], "slots": [r for r in old_rows if r["slot_id"] == "MG-GR002:A1"]},
                {"plan": drift, "model_label": RUNTIME["model_label"], "slots": [r for r in old_rows if r["slot_id"] == "MG-GR002:A2"]}],
                budget_policy="retain_source_budgets")
        with self.assertRaisesRegex(ValueError, "frozen native budget"):
            _compose_score_sources(self.plan, [{"plan": written_plan, "model_label": RUNTIME["model_label"],
                "slots": [r for r in fixture_rows(written_plan) if r["slot_id"] == "MG-C003:A1"]}],
                budget_policy="retain_source_budgets")

    def test_older_standard_answers_cannot_fill_mandatory_fresh_supplement(self):
        old=build_plan(self.old_profile,self.old_suite,runtime=RUNTIME)
        old["profile"]["data"]["standard_version"]="synthetic-source-version"
        old["profile"]["data_sha256"]=identity(old["profile"]["data"])
        old["plan_sha256"]=identity({k:v for k,v in old.items() if k!="plan_sha256"})
        rows=[r for r in fixture_rows(old) if r['case_id'] in {'MG-GP001','MG-GP002','MG-C003'}]
        report=_compose_score_sources(self.plan,[{'plan':old,'model_label':RUNTIME['model_label'],'slots':rows}])
        self.assertEqual(report['evidence'],[])
        self.assertIsNone(report['metrics']['overall']['exact'])
        self.assertEqual(len(report['composition']['source_runs'][0]['superseded_source_slots']),len(rows))
        selected=select_slots(self.plan,['lean-audit','lean-formalization','written-new-panel'])
        self.assertEqual(len(selected),18)
        self.assertEqual(len([r for r in selected if r['case_id'] in {'MG-GP001','MG-GP002'}]),10)
        bad=copy.deepcopy(self.plan)
        bad['profile']['data']['supplement_policy']['standard_new_slots_per_model']=17
        bad['profile']['data_sha256']=identity(bad['profile']['data'])
        bad['plan_sha256']=identity({k:v for k,v in bad.items() if k!='plan_sha256'})
        with self.assertRaisesRegex(ValueError,'Fresh supplement slot count'):validate_plan(bad)

    def test_v5_unstarted_projection_does_not_conflict_with_actual_source(self):
        actual=next(r for r in fixture_rows(self.plan) if r['slot_id']=='MG-GP001:A1')
        placeholder={'slot_id':actual['slot_id'],'case_id':'MG-GP001','started':False,'reason':'not_selected'}
        def source(rows):return {'plan':self.plan,'model_label':RUNTIME['model_label'],'slots':rows}
        for sources in ([source([placeholder]),source([actual])],[source([actual]),source([placeholder])]):
            report=_compose_score_sources(self.plan,sources)
            self.assertEqual(len(report['evidence']),1)
            self.assertEqual(report['evidence'][0]['evidence_id'],actual['evidence_id'])
            self.assertIsNone(report['metrics']['overall']['exact'])
            self.assertFalse(report['composition']['formal_comparison_eligible'])
        changed=copy.deepcopy(actual);changed['evidence_id']='different-attempt'
        with self.assertRaisesRegex(ValueError,'Conflicting source evidence'):
            _compose_score_sources(self.plan,[source([actual]),source([changed])])

    def test_unknown_or_drifting_tracks_and_flat_aggregation_are_rejected(self):
        for change in (lambda p: p["profile"]["data"]["case_execution_policy"]["case_tracks"].update(AHR01="search"),
                       lambda p: p["profile"]["data"]["components"][2].update(aggregation="paper")):
            bad = copy.deepcopy(self.plan)
            change(bad)
            bad["profile"]["data_sha256"] = identity(bad["profile"]["data"])
            bad["plan_sha256"] = identity({k:v for k,v in bad.items() if k != "plan_sha256"})
            with self.assertRaises(ValueError):
                validate_plan(bad)

    def test_standard_audits_use_fresh_a1_and_no_written_followups(self):
        audits = select_slots(self.plan, ["lean-audit"])
        self.assertEqual([row["slot_id"] for row in audits], [f"AHR{i:02d}:A1" for i in range(1, 5)])
        self.assertTrue(all(row["kind"] == "independent" and row["context"] == "fresh" for row in audits))
        self.assertFalse({row["case_id"] for row in audits} &
            {row["case_id"] for row in self.plan["reliability"]["selection"]["cases"]})

    def test_failed_readable_raw_is_retained_but_cannot_start_followups_or_get_math_credit(self):
        from math_gauge.reliability import inspect_reliability_run, reliability_score_inputs
        with tempfile.TemporaryDirectory() as directory:
            out=Path(directory)/'run'
            selected=select_slots(self.plan,['neutral'])
            replay={s['slot_id']: 'KEEP\nSynthetic check.' if s['kind']=='followup' else 'Synthetic body.' for s in selected}
            raw='I have launched the process and will wait.'
            replay['MG-GP001:A1']={'stdout':raw,'status':'permanent_error','exit_code':1}
            execute_reliability_run(self.plan,self.suite,out,replay=replay,targets=['neutral'])
            meta,records=inspect_reliability_run(out)
            record=records['MG-GP001:A1']
            self.assertEqual((out/record['response_path']).read_text(),raw)
            self.assertEqual(record['attempts'][0]['status'],'permanent_error')
            self.assertFalse(records['MG-GP001:neutral:1']['started'])
            self.assertEqual(records['MG-GP001:neutral:1']['reason'],'parent_without_successful_terminal_delivery')
            review=next(r for r in reliability_review_templates(out) if r['slot_id']=='MG-GP001:A1')
            review.update(reviewer='Synthetic no-delivery reviewer',reviewer_kind='fixture',notes='Original readable error is retained; no terminal mathematical delivery.')
            bad=copy.deepcopy(review);bad['stages'][0].update(decision='fail',notes='Do not convert non-delivery into mathematical zero.')
            with self.assertRaisesRegex(ValueError,'must remain unresolved'):apply_reliability_reviews(out,[bad])
            apply_reliability_reviews(out,[review])
            row=next(r for r in reliability_score_inputs(out)['slots'] if r['slot_id']=='MG-GP001:A1')
            self.assertIsNone(row['completion']['exact'])
            self.assertEqual((row['completion']['lower'],row['completion']['upper']),(0,1))
            self.assertIsNone(row['strict_pass'])

    def test_current_lean_projection_has_only_eight_selected_a1(self):
        plan = build_plan(self.profile, self.suite, ["lean-audit", "lean-formalization"])
        self.assertEqual(plan["planned"]["all_slots"], 42)
        self.assertTrue(all(row["kind"] == "independent" and row["attempt_label"] == "A1" for row in select_slots(plan)))
        with tempfile.TemporaryDirectory() as directory:
            out = Path(directory) / "bundle"
            export_harness_bundle(plan, self.suite, out)
            manifest = inspect_harness_bundle(out, plan=plan, suite=self.suite)
            self.assertEqual(manifest["exported_slots"], 8)
            self.assertEqual(manifest["prompts"], [])

    def test_standard_reliability_population_is_four_written_families_only(self):
        from math_gauge.benchmarks import _declared_reliability_population
        rows=self.plan['reliability']['selection']['cases']
        self.assertEqual([r['case_id'] for r in rows],['MG-GR002','MG-GR014','MG-GP001','MG-GP002'])
        self.assertEqual({r['task_kind'] for r in rows},{'written'})
        self.assertEqual(self.plan['profile']['data']['reliability_panel']['truth_counts'],{'true':2,'false':2})
        bad=copy.deepcopy(self.suite.cases);bad['MG-GP001']['task_kind']='audit'
        with self.assertRaisesRegex(ValueError,'written-only'):_declared_reliability_population(self.profile.data,self.plan['reliability']['selection'],bad)
        self.assertTrue(all(':A2' not in s['slot_id'] and s['kind']=='independent' for s in select_slots(self.plan,['lean-audit','lean-formalization'])))
        study=read_json(ROOT/'protocol/lean-alignment/study.json')
        self.assertEqual(study['case_id'],'MG-C003')
        self.assertEqual(study['fixed_followup_rounds'],[1,2,3])
        self.assertFalse(study['standard_slot_inclusion'])
        self.assertEqual(study['overall_weight_percent'],10)
