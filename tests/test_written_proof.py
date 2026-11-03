"""Synthetic shared-runner evidence for unguided written mathematical papers."""

import copy
import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from math_gauge.benchmarks import BenchmarkProfile, build_plan, identity, validate_plan
from math_gauge.catalog import (Suite, candidate_message, digest_bytes, read_json,
                                validate_group_contract, write_json)
from math_gauge.execution import run
from math_gauge.harness import (export_harness_bundle, export_simple_release_dataset,
                                freeze_release_runtime, inspect_harness_bundle, make_release_anchor)
from math_gauge.harness_answers import issue_answer_request, pack_answer_archive, record_answer_attempt
from math_gauge.harness_import import import_answer_archive
from math_gauge.reliability import execute_reliability_run, inspect_reliability_run
from math_gauge.reliability_review import apply_reliability_reviews, reliability_review_templates
from math_gauge.review import (_validate_written_proof_review, apply_reviews, report, templates)
from math_gauge.scoring import public_score_projection, score_composed_runs, score_inputs, score_runs
from test_composite_suites import RUNTIME, synthetic_suite

ROOT = Path(__file__).resolve().parents[1]
CRITERIA = [("feasibility_counts_liftability", 30), ("fixed_classes_and_orbits", 25),
            ("reduction_maps_and_fixed_lifts", 15), ("optimal_quantitative_descent", 20),
            ("assertion_reliability", 10)]


def written_suite(root, *, rubric_container="criteria", ambiguous=False):
    synthetic_suite(root, "SYN-W", visibility="public", research=False)
    case = read_json(root / "paper/case.json")
    case["family_id"] = "SYN-PARENT"
    case["evaluator_files"] = ["diagnostic-rubric.json"]
    write_json(root / "paper/case.json", case)
    (root / "paper/task.md").write_bytes(
        b"# Synthetic paper\r\n\r\n1. First final goal.\r\n\r\n2. Second final goal.\r\n\r\n3. Third final goal.\r\n")
    diagnostic_path = root / "paper/diagnostic-rubric.json"
    diagnostic = {"schema": "math-gauge.design-rubric/v1", rubric_container: [
        {"id": key, "points": points} for key, points in CRITERIA]}
    if ambiguous:
        diagnostic["categories"] = copy.deepcopy(diagnostic[rubric_container])
    write_json(diagnostic_path, diagnostic)
    write_json(root / "paper/contract.json", {
        "schema": "math-gauge.group-contract/v2", "kind": "written_proof",
        "id": case["id"], "version": case["version"], "assessment_unit": "proof_criterion",
        "original_frozen_rubric": "diagnostic-rubric.json",
        "original_frozen_rubric_sha256": digest_bytes(diagnostic_path.read_bytes()),
        "criteria": [{"id": key, "title": key, "points": points,
                      "required_evidence": ["EVALUATOR_PRIVATE_CRITERION"],
                      "critical_errors": ["EVALUATOR_PRIVATE_ERROR"]} for key, points in CRITERIA]})
    return Suite.load(root)


def written_profile(root, suite):
    for name, data in (
        ("selection", {"protocol_version": "0.2.0", "source_suite_sha256": suite.sha256,
                       "case_count": 0, "truth_counts": {}, "cases": []}),
        ("prompts", {"protocol_version": "0.2.0", "messages": []}),
        ("schedule", {"protocol_version": "0.2.0", "slots": [
            {"slot_id": cid + ":A1", "case_id": cid, "kind": "independent",
             "attempt_label": "A1", "context": "fresh", "parent_slot": None,
             "message_id": None, "ordinal_per_model": number}
            for number, cid in enumerate(suite.cases, 1)]})):
        write_json(root / (name + ".json"), data)
    path = root / "profile.json"
    components = []
    for component, kind in (("proofs", "written_proof"), ("answer-review", "answer_review")):
        ids = [cid for cid, case in suite.cases.items()
               if read_json(suite.case_file(case, case["group_contract"]))["kind"] == kind]
        if ids:
            components.append({"id": component, "weight": 100, "case_ids": ids})
    if len(components) == 2:
        for component in components:
            component["weight"] = 50
    write_json(path, {
        "schema": "math-gauge.benchmark-profile/v4", "id": "synthetic-written-proof",
        "version": "fixture-1", "operator_only": True, "path_base": "repository",
        "suite": {"id": suite.metadata["id"], "version": suite.metadata["version"], "sha256": suite.sha256},
        "components": components,
        "attempt_schedule": {cid: ["A1"] for cid in suite.cases},
        "score_policy": {"core_attempt_labels": ["A1"], "repeat_case_ids": [],
                         "repeat_attempt_labels": ["A1", "A2", "A3"]},
        "overall_weights": {"core": 100, "repeat": 0, "neutral": 0, "stance": 0},
        "reliability": {"protocol_version": "0.2.0", "selection": "selection.json",
                        "prompts": "prompts.json", "schedule": "schedule.json"}})
    return BenchmarkProfile.load(path, suite, repository_root=root)


def reviewed(entry, scores=(20, 12.5, 7.5, 20, 5), *, decision="partial"):
    entry.update(reviewer="synthetic fixture", reviewer_kind="fixture", decision=decision,
                 assumption_fidelity="clean", proof_validity="valid", scope_accuracy="correct",
                 unnecessary_restriction=False, notes="Synthetic credit, not a model result", findings=[])
    for row, score in zip(entry["criteria"], scores):
        row.update(score=score, notes="Synthetic criterion evidence")
    if "format_review" in entry:
        entry["format_review"] = {"decision": "valid", "notes": "Complete original fixture bytes"}
    return entry


class WrittenProofTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="math-gauge-written-proof-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.suite = written_suite(self.root / "cases")
        self.contract = read_json(self.suite.root / "paper/contract.json")
        self.profile = written_profile(self.root / "profile", self.suite)
        self.plan = build_plan(self.profile, self.suite, runtime=RUNTIME)

    def test_contract_keeps_criteria_evaluator_only_without_proof_route_or_lean(self):
        validate_group_contract(self.contract)
        for field, value in (("stages", []), ("turns", []), ("dimensions", []),
                             ("alignment_manifest_required", False), ("required_output_files", [])):
            invalid = dict(self.contract, **{field: value})
            with self.subTest(field=field), self.assertRaises(ValueError):
                validate_group_contract(invalid)
        for field, value in (("points", True), ("depends_on", []), ("lean_required", False)):
            invalid = copy.deepcopy(self.contract)
            invalid["criteria"][0][field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                validate_group_contract(invalid)
        row = self.plan["case_index"][0]
        self.assertEqual(row["assessment_unit"], "proof_criterion")
        self.assertEqual(row["criteria"], [{"criterion_id": key, "points": points} for key, points in CRITERIA])
        self.assertNotIn("stages", row)
        self.assertNotIn("dimensions", row)
        invalid_plan = copy.deepcopy(self.plan)
        invalid_plan["reliability"]["selection"]["cases"] = [{"case_id": "SYN-W", "stage_id": "invented"}]
        invalid_plan["plan_sha256"] = identity({key: value for key, value in invalid_plan.items() if key != "plan_sha256"})
        with self.assertRaisesRegex(ValueError, "written-proof plan unit"):
            validate_plan(invalid_plan)
        request = self.suite.request(self.suite.cases["SYN-W"])
        self.assertEqual(request["task"].encode(), (self.suite.root / "paper/task.md").read_bytes())
        self.assertNotIn("EVALUATOR_PRIVATE", candidate_message(request))
        bundle = self.root / "bundle"
        export_harness_bundle(self.plan, self.suite, bundle, targets=["proofs"])
        inspect_harness_bundle(bundle, plan=self.plan, suite=self.suite)
        for path in bundle.rglob("*"):
            if path.is_file():
                self.assertNotIn(b"EVALUATOR_PRIVATE", path.read_bytes())
                self.assertNotIn(b"feasibility_counts_liftability", path.read_bytes())

    def test_fractional_credit_strict_pass_and_unresolved_bounds(self):
        entry = reviewed({"criteria": [{"criterion_id": key} for key, _ in CRITERIA]})
        diagnostic = _validate_written_proof_review(self.contract, entry, {"status": "ok"})
        self.assertEqual(diagnostic["completion"], {"lower": .65, "upper": .65, "exact": .65})
        self.assertEqual(diagnostic["criterion_count"], 5)
        self.assertFalse(diagnostic["strict_pass"])
        self.assertNotIn("core_completion", diagnostic)
        entry["decision"] = "pass"
        with self.assertRaisesRegex(ValueError, "full resolved credit"):
            _validate_written_proof_review(self.contract, entry, {"status": "ok"})
        reviewed(entry, [30, 25, 15, 20, 10], decision="pass")
        self.assertTrue(_validate_written_proof_review(self.contract, entry, {"status": "ok"})["strict_pass"])
        for field, value in (("proof_validity", "invalid"), ("assumption_fidelity", "drift"),
                             ("scope_accuracy", "incorrect"), ("unnecessary_restriction", True)):
            invalid = dict(entry, **{field: value})
            with self.subTest(field=field), self.assertRaises(ValueError):
                _validate_written_proof_review(self.contract, invalid, {"status": "ok"})
        with self.assertRaises(ValueError):
            _validate_written_proof_review(self.contract, entry, {"status": "error"})
        reviewed(entry)
        for invalid in (True, float("nan"), float("inf"), -1, 10.5, "5"):
            entry["criteria"][-1]["score"] = invalid
            with self.subTest(score=invalid), self.assertRaises(ValueError):
                _validate_written_proof_review(self.contract, entry, {"status": "ok"})
        entry["criteria"][-1]["score"] = None
        diagnostic = _validate_written_proof_review(self.contract, entry, {"status": "ok"})
        self.assertEqual(diagnostic["completion"], {"lower": .6, "upper": .7, "exact": None})
        self.assertFalse(diagnostic["strict_pass"])

    def test_ordinary_run_freezes_original_criteria_and_candidate_bytes(self):
        replay = self.root / "replay.json"
        write_json(replay, {"SYN-W": "Synthetic answer\r\n"})
        output = self.root / "ordinary"
        run(self.suite, output, replay=replay)
        entries = templates(output)
        self.assertNotIn("stages", entries[0])
        self.assertNotIn("dimensions", entries[0])
        apply_reviews(output, [reviewed(entries[0])])
        (self.suite.root / "paper/contract.json").write_text("Current source no longer a contract")
        result, text = report(output)
        self.assertEqual(result["group_diagnostics"]["SYN-W"]["completion"]["exact"], .65)
        self.assertIn("5 proof criteria", text)
        self.assertEqual((output / "SYN-W/response.md").read_bytes(), b"Synthetic answer\r\n")
        self.assertEqual(read_json(output / "SYN-W/solver/request.json")["task"].encode(),
                         (self.suite.root / "paper/task.md").read_bytes())

    def test_reliability_scoring_projection_and_frozen_score_reuse(self):
        output = self.root / "run"
        execute_reliability_run(self.plan, self.suite, output, replay={"SYN-W:A1": "Synthetic original\r\n"})
        entries = reliability_review_templates(output)
        apply_reliability_reviews(output, [reviewed(entries[0])])
        result = score_runs([output])
        self.assertEqual(result["metrics"]["proofs"]["exact"], 65)
        self.assertEqual(result["papers"]["SYN-W"]["criterion_weight_total"], 100)
        self.assertNotIn("stage_weight_total", result["papers"]["SYN-W"])
        self.assertFalse(result["evidence"][0]["strict_pass"])
        self.assertEqual(result["evidence"][0]["whole_math"]["state"], "U")
        projection = public_score_projection(result, self.plan, private_aliases={})
        row = projection["slot_evidence"][0]
        self.assertEqual(projection["coverage"]["parent_families"], 1)
        self.assertEqual((row["family_id"], row["criterion_count"]), ("SYN-PARENT", 5))
        self.assertNotIn("stages", row)
        self.assertEqual([item["score"] for item in row["criteria"]], [20, 12.5, 7.5, 20, 5])
        saved = self.root / "frozen-score.json"
        write_json(saved, result)
        index = read_json(output / "reliability-reviews.json")
        binding = {"path": str(saved), "sha256": digest_bytes(saved.read_bytes()),
                   "review_snapshot_sha256": index["snapshots"][0]["snapshot_sha256"]}
        with patch("math_gauge.reliability_review._validate_entry", side_effect=AssertionError("Frozen reuse")):
            reused = score_composed_runs(self.plan, [output], frozen_reports={str(output): binding})
        self.assertEqual(reused["metrics"]["core"]["exact"], 65)

    def test_release_archive_returns_to_shared_review_and_scoring(self):
        dataset = self.root / "dataset"
        base_plan = build_plan(self.profile, self.suite)
        manifest = export_simple_release_dataset(base_plan, self.suite, dataset,
            release_version=self.suite.metadata["version"], readme=b"# Synthetic only\n",
            extra_files={"LICENSE": b"Synthetic\n", "THIRD_PARTY_NOTICES.md": b"Synthetic\n"})
        anchor = make_release_anchor(base_plan, manifest)
        output, answers = self.root / "external", self.root / "answers"
        freeze_release_runtime(dataset, RUNTIME, output, targets=["proofs"])
        request, response = self.root / "request.json", self.root / "response.md"
        issue_answer_request(output, answers, "SYN-W:A1", request)
        response.write_bytes(b"Synthetic external answer\r\n")
        record_answer_attempt(output, answers, "SYN-W:A1", request, response, status="ok")
        archive, imported = self.root / "answers.zip", self.root / "imported"
        pack_answer_archive(output, answers, archive)
        with patch("math_gauge.execution.invoke_conversation", side_effect=AssertionError("No candidate calls")):
            import_answer_archive(archive, anchor, self.suite, imported)
        meta, records = inspect_reliability_run(imported)
        self.assertEqual(meta["plan"]["case_index"][0]["assessment_unit"], "proof_criterion")
        self.assertEqual(records["SYN-W:A1"]["response_sha256"], digest_bytes(response.read_bytes()))
        entries = reliability_review_templates(imported)
        apply_reliability_reviews(imported, [reviewed(entries[0])])
        self.assertEqual(score_runs([imported])["metrics"]["core"]["exact"], 65)

    def test_family_coverage_normalizes_review_parent_case_without_private_ids(self):
        from test_answer_review import fixture_suite
        answer_review = fixture_suite(self.root / "review/cases", "SYN-AR-PRIVATE", "SYN-W")
        suite = Suite.combine([self.suite, answer_review])
        plan = build_plan(written_profile(self.root / "combined-profile", suite), suite)
        result = score_inputs({"schema": "math-gauge.score-input/v1", "plan": plan,
                               "plan_sha256": plan["plan_sha256"], "slots": []})
        projection = public_score_projection(result, plan, private_aliases={"SYN-AR-PRIVATE": "Private-01"})
        self.assertEqual(projection["coverage"]["papers_planned"], 2)
        self.assertEqual(projection["coverage"]["parent_families"], 1)
        import json
        self.assertNotIn("SYN-AR-PRIVATE", json.dumps(projection))

    def test_taxonomy_evidence_uses_final_goal_paragraphs(self):
        spec = importlib.util.spec_from_file_location("written_focus_catalog", ROOT / "scripts/catalog.py")
        catalog = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(catalog)
        task = self.suite.root / "paper/task.md"
        source = {"case": self.suite.cases["SYN-W"], "contract": self.contract,
                  "paths": {"task": "cases/proofs/SYN-W/task.md"}, "source_bindings": {},
                  "goals": catalog.task_goals(task)}
        assignment = {"version": "fixture-1", "source_bindings": {},
                      "classification_review": {"status": "ai-fixture", "human": "pending"},
                      "focus": [{"focus_id": fid, "role": role, "evidence": [{
                          "criterion_id": CRITERIA[index][0], "contract_pointer": f"/criteria/{index}/required_evidence",
                          "note": "Synthetic final target", "task_locator": {"path": source["paths"]["task"],
                          "line": source["goals"][goal], "applies_to": goal}}]}
                          for fid, role, index, goal in (("F01", "primary", 0, "goal1"),
                              ("F02", "secondary", 1, "goal2"), ("F07", "secondary", 3, "goal3"))]}
        catalog.validate_assignment(assignment, source)
        changed = copy.deepcopy(assignment)
        changed["focus"][0]["evidence"][0]["task_locator"]["line"] += 1
        with self.assertRaisesRegex(ValueError, "final-goal locator drift"):
            catalog.validate_assignment(changed, source)
        whole = assignment["focus"][0]["evidence"][0]["task_locator"]
        whole.update(line=1, applies_to="whole-paper")
        catalog.validate_assignment(assignment, source)
        assignment["focus"][0]["focus_id"] = "F09"
        with self.assertRaisesRegex(ValueError, "does not require candidate Lean"):
            catalog.validate_assignment(assignment, source)

    def test_protocol_summary_keeps_proof_criteria_out_of_mathematical_stages(self):
        spec = importlib.util.spec_from_file_location("written_protocol", ROOT / "scripts/validate_protocol.py")
        protocol = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(protocol)
        summary = protocol.check_candidate(self.suite, self.suite.cases["SYN-W"], self.root / "protocol-solver")
        self.assertEqual(summary["mandatory_units"], 0)
        self.assertEqual(summary["proof_criteria"], 5)
        self.assertEqual(summary["assessment_unit"], "proof_criterion")
        self.assertNotIn("review_dimensions", summary)

    def ordinary_source(self):
        source_root = self.root / "ordinary-source/cases"
        synthetic_suite(source_root, "Q05", visibility="public", research=False)
        case = read_json(source_root / "paper/case.json")
        case.pop("group_contract")
        case["version"] = "original-exam-version"
        case["evaluator_files"] = ["diagnostic-rubric.json"]
        write_json(source_root / "paper/case.json", case)
        for name in ("task.md", "reference.md", "diagnostic-rubric.json"):
            (source_root / "paper" / name).write_bytes((self.suite.root / "paper" / name).read_bytes())
        original_suite = Suite.load(source_root)
        replay = self.root / "ordinary-replay.json"
        write_json(replay, {"Q05": "Synthetic original answer\r\n"})
        output = self.root / "ordinary-existing"
        run(original_suite, output, replay=replay)
        native = output / "original-native-receipt.json"
        write_json(native, {"source_case_id": "Q05", "synthetic": True})
        record = read_json(output / "Q05/record.json")
        record["native_evidence"] = {"receipt": {"path": str(native), "sha256": digest_bytes(native.read_bytes())}}
        write_json(output / "Q05/record.json", record)
        diagnostic_path = source_root / "paper/diagnostic-rubric.json"
        entry = reviewed({"criteria": [{"criterion_id": key} for key, _ in CRITERIA]})
        entry.update(case_id="SYN-W", source_case_id="Q05", response_sha256=record["response_sha256"],
                     group_contract_sha256=digest_bytes((self.suite.root / "paper/contract.json").read_bytes()),
                     rubric_sha256=digest_bytes((self.suite.root / "paper/rubric.json").read_bytes()),
                     reference_sha256=digest_bytes((self.suite.root / "paper/reference.md").read_bytes()),
                     original_rubric_sha256=digest_bytes(diagnostic_path.read_bytes()))
        reviews_path = self.root / "mapped-reviews.json"
        write_json(reviews_path, [entry])
        return {"run": str(output), "reviews": str(reviews_path),
                "post_observation_catalog_binding": True, "notes": "Synthetic original-ID mapping only",
                "case_bindings": [{"target_case_id": "SYN-W", "source_case_id": "Q05",
                    "original_rubric_path": str(diagnostic_path),
                    "original_rubric_sha256": digest_bytes(diagnostic_path.read_bytes())}]}

    def test_ordinary_case_id_mapping_preserves_original_evidence_and_65_credit(self):
        source = self.ordinary_source()
        output = Path(source["run"])
        before = {str(path): path.read_bytes() for path in output.rglob("*") if path.is_file()}
        with patch("math_gauge.execution.invoke_conversation", side_effect=AssertionError("No candidate calls")):
            result = score_composed_runs(self.plan, [], written_proof_sources=[source], suite=self.suite,
                                         model_aliases={"replay-fixture": RUNTIME["model_label"]})
        self.assertEqual(result["metrics"]["core"]["exact"], 65)
        row = result["evidence"][0]
        self.assertFalse(row["strict_pass"])
        self.assertFalse(row["comparison_eligible"])
        self.assertEqual(row["written_proof_reuse"]["source_case_id"], "Q05")
        self.assertEqual(row["written_proof_reuse"]["target_case_id"], "SYN-W")
        self.assertFalse(row["written_proof_reuse"]["execution_relabelled"])
        self.assertEqual(result["composition"]["new_candidate_calls"], 0)
        self.assertFalse(result["composition"]["independent_run"])
        projection = public_score_projection(result, self.plan, private_aliases={})
        self.assertEqual(projection["slot_evidence"][0]["source_kind"], "same_input_catalog_binding")
        self.assertEqual(before, {str(path): path.read_bytes() for path in output.rglob("*") if path.is_file()})
        self.assertFalse((output / "SYN-W").exists())
        entry = read_json(source["reviews"])[0]
        reviewed(entry, [30, 25, 15, 20, 10], decision="pass")
        write_json(source["reviews"], [entry])
        full = score_composed_runs(self.plan, [], written_proof_sources=[source], suite=self.suite,
                                   model_aliases={"replay-fixture": RUNTIME["model_label"]})
        self.assertEqual(full["metrics"]["core"]["exact"], 100)
        self.assertTrue(full["evidence"][0]["strict_pass"])
        self.assertFalse(full["metrics"]["core"]["formal_comparison_eligible"])
        self.assertEqual(before, {str(path): path.read_bytes() for path in output.rglob("*") if path.is_file()})

    def test_original_rubric_container_names_preserve_frozen_bytes(self):
        for name in ("dimensions", "categories", "ambiguous"):
            with self.subTest(container=name):
                root = self.root / name
                suite = written_suite(root / "cases", rubric_container=("dimensions" if name == "ambiguous" else name),
                                      ambiguous=name == "ambiguous")
                profile = written_profile(root, suite)
                plan = build_plan(profile, suite, targets=["all"], runtime=RUNTIME)
                with patch.object(self, "root", root), patch.object(self, "suite", suite):
                    source = self.ordinary_source()
                rubric_path = Path(source["case_bindings"][0]["original_rubric_path"])
                original = rubric_path.read_bytes()
                kwargs = {"written_proof_sources": [source], "suite": suite,
                          "model_aliases": {"replay-fixture": RUNTIME["model_label"]}}
                if name == "ambiguous":
                    with self.assertRaisesRegex(ValueError, "unambiguous frozen diagnostic rubric"):
                        score_composed_runs(plan, [], **kwargs)
                else:
                    result = score_composed_runs(plan, [], **kwargs)
                    self.assertEqual(result["metrics"]["core"]["exact"], 65)
                self.assertEqual(rubric_path.read_bytes(), original)

    def test_ordinary_mapping_rejects_changed_materials_unmapped_ids_and_duplicates(self):
        source = self.ordinary_source()
        options = {"written_proof_sources": [source], "suite": self.suite,
                   "model_aliases": {"replay-fixture": RUNTIME["model_label"]}}
        for field, value in (("source_case_id", "unmapped"), ("original_rubric_sha256", "0" * 64)):
            invalid = copy.deepcopy(source)
            invalid["case_bindings"][0][field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                score_composed_runs(self.plan, [], **dict(options, written_proof_sources=[invalid]))
        invalid = copy.deepcopy(source)
        invalid["case_bindings"].append(dict(invalid["case_bindings"][0]))
        with self.assertRaisesRegex(ValueError, "distinct explicit"):
            score_composed_runs(self.plan, [], **dict(options, written_proof_sources=[invalid]))
        with self.assertRaisesRegex(ValueError, "Repeated written-proof evidence"):
            score_composed_runs(self.plan, [], **dict(options, written_proof_sources=[source, source]))
        entry = read_json(source["reviews"])[0]
        entry["source_case_id"] = "unmapped"
        write_json(source["reviews"], [entry])
        with self.assertRaisesRegex(ValueError, "unmapped"):
            score_composed_runs(self.plan, [], **options)
        entry["source_case_id"] = "Q05"
        write_json(source["reviews"], [entry])
        original = Path(source["case_bindings"][0]["original_rubric_path"])
        frozen_bytes = original.read_bytes()
        original.write_bytes(frozen_bytes + b" ")
        with self.assertRaisesRegex(ValueError, "frozen diagnostic rubric"):
            score_composed_runs(self.plan, [], **options)
        original.write_bytes(frozen_bytes)
        native = Path(source["run"]) / "original-native-receipt.json"
        frozen_bytes = native.read_bytes()
        native.write_bytes(frozen_bytes + b" ")
        with self.assertRaisesRegex(ValueError, "Original native evidence changed"):
            score_composed_runs(self.plan, [], **options)
        native.write_bytes(frozen_bytes)
        task = self.suite.root / "paper/task.md"
        task.write_bytes(task.read_bytes() + b"Changed candidate text\r\n")
        changed_suite = Suite.load(self.suite.root)
        changed_plan = build_plan(written_profile(self.root / "changed-profile", changed_suite), changed_suite,
                                  runtime=RUNTIME)
        with self.assertRaisesRegex(ValueError, "candidate message"):
            score_composed_runs(changed_plan, [], **dict(options, suite=changed_suite))


if __name__ == "__main__":
    unittest.main()
