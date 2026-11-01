"""Current fixed reliability design and exact candidate boundaries; no execution."""
from __future__ import annotations

import copy
import importlib.util
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("reliability_material_checks", ROOT / "scripts/validate_protocol.py")
V = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(V)
PACKET = ROOT / V.PACKET


class ReliabilityMaterialsTests(unittest.TestCase):
    def setUp(self):
        self.plan = V.read(PACKET / "plan.json")
        self.selection = V.read(PACKET / "selection.json")
        self.prompts = V.read(PACKET / "prompts.json")
        self.schedule = V.read(PACKET / "schedule.json")
        self.reply = (PACKET / "reply-format.md").read_text()

    def test_all_current_materials_and_candidates_validate_without_changing_repository(self):
        paths = list(PACKET.glob("*.*"))
        before = {path: (path.read_bytes(), path.stat().st_mtime_ns) for path in paths}
        report = V.validate_materials()
        self.assertTrue(report["passed"])
        self.assertEqual(report["candidate_projections"], 43)
        self.assertEqual(report["dependent_review_obligations"], 372)
        self.assertEqual(report["frozen_followup_messages"], 48)
        self.assertEqual(report["planned_slots_per_model"], 177)
        self.assertEqual(report["isolated_followup_history_edges"], 48)
        self.assertEqual(report["candidate_model_calls"], 0)
        self.assertEqual(report["lean_compilations"], 0)
        self.assertFalse(report["human_approved"])
        self.assertEqual(before, {path: (path.read_bytes(), path.stat().st_mtime_ns) for path in paths})

    def test_material_refresh_cannot_authorize_execution_or_invent_results(self):
        for key, value in (("execution_authorized", True), ("candidate_calls", 1),
                           ("actual_results", {"pass": 43}), ("human_approved", True),
                           ("runtime_configuration_frozen", True)):
            with self.subTest(key=key):
                plan = copy.deepcopy(self.plan)
                plan[key] = value
                with self.assertRaises(ValueError):
                    V.check_plan(plan)

    def test_offline_acceptance_cannot_bless_changed_sources_or_candidate_results(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            names = set(V.RUNNER_FILES) | set(V.ACCEPTANCE_STANDARDS) | {
                "tests/test_reliability_materials.py",
                *("tests/" + name for name in V.ACCEPTANCE_TESTS),
            }
            for name in names:
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(name.encode())
            receipt = {"schema": "math-gauge.runner-offline-acceptance/v1", "status": "passed",
                       "real_candidate_model_calls": 0, "formal_model_result": False,
                       "lean_compilations": 0, "test_count": len(V.ACCEPTANCE_TESTS),
                       "input_sha256": {name: V.sha((root / name).read_bytes()) for name in names},
                       "checks": []}
            for name in V.ACCEPTANCE_TESTS:
                log = root / ("verification/runner/logs/" + name + ".log")
                log.parent.mkdir(parents=True, exist_ok=True)
                log.write_bytes(b".\nRan 1 test in 0.001s\n\nOK\n")
                receipt["checks"].append({
                    "command": ["python3", "-m", "unittest", "discover", "-s", "tests", "-p", name],
                    "exit_code": 0, "tests": 1, "skipped": 0,
                    "log": log.relative_to(root).as_posix(),
                    "log_sha256": V.sha(log.read_bytes())})
            path = root / "verification/runner/offline-acceptance.json"
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(V.encoded(receipt))
            plan = {"runner_multi_turn_acceptance": "offline-fixture-acceptance-passed",
                    "runner_acceptance": {"path": path.relative_to(root).as_posix(),
                                          "sha256": V.sha(path.read_bytes())}}
            checked = V.check_offline_acceptance(root, plan)
            self.assertFalse(checked["tests_rerun_by_material_check"])
            for name in ("math_gauge/eligibility.py", "tests/test_eligibility.py",
                         "tests/test_eligibility_acceptance.py", "tests/test_reliability_review.py",
                         "math_gauge/harness.py", "math_gauge/harness_import.py",
                         "tests/test_harness_export.py", "tests/test_harness_import.py",
                         "tests/test_harness_cli.py", "protocol/external-harness.md",
                         "scripts/release.py", "tests/test_release_runtime.py",
                         "tests/test_release_artifacts.py", "protocol/release-distribution.md",
                         "releases/v0.1.0/config.json", "releases/v0.1.0/THIRD_PARTY_NOTICES.md",
                         "docs/release-consumer-README.md", "docs/release-notes-v0.1.0.md", "LICENSE",
                         "protocol/execution-evidence.md", "protocol/isolated-cli-runs.md"):
                with self.subTest(omitted=name):
                    omitted = receipt["input_sha256"].pop(name)
                    path.write_bytes(V.encoded(receipt))
                    plan["runner_acceptance"]["sha256"] = V.sha(path.read_bytes())
                    with self.assertRaisesRegex(ValueError, "omits implementation, scoring or test"):
                        V.check_offline_acceptance(root, plan)
                    receipt["input_sha256"][name] = omitted
            path.write_bytes(V.encoded(receipt))
            plan["runner_acceptance"]["sha256"] = V.sha(path.read_bytes())
            log = root / receipt["checks"][0]["log"]
            before_log = log.read_bytes()
            log.write_bytes(b"Ran 1 test in 0.001s\n\nFAILED (failures=1)\n")
            with self.assertRaisesRegex(ValueError, "test output drift"):
                V.check_offline_acceptance(root, plan)
            log.write_bytes(before_log)
            source = root / "math_gauge/scoring.py"
            source.write_bytes(b"changed after tests")
            with self.assertRaisesRegex(ValueError, "Offline acceptance input drift"):
                V.check_offline_acceptance(root, plan)
            source.write_bytes(b"math_gauge/scoring.py")
            receipt["real_candidate_model_calls"] = 1
            path.write_bytes(V.encoded(receipt))
            plan["runner_acceptance"]["sha256"] = V.sha(path.read_bytes())
            with self.assertRaisesRegex(ValueError, "cannot claim actual candidate results"):
                V.check_offline_acceptance(root, plan)

    def test_offline_receipt_counts_skips_commands_and_no_execution_claims_are_bound(self):
        """These synthetic logs exercise the parser, never establish actual test execution."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            names = set(V.RUNNER_FILES) | set(V.ACCEPTANCE_STANDARDS) | {
                "tests/test_reliability_materials.py",
                *("tests/" + name for name in V.ACCEPTANCE_TESTS),
            }
            for name in names:
                file = root / name
                file.parent.mkdir(parents=True, exist_ok=True)
                file.write_bytes(name.encode())
            checks = []
            for name in V.ACCEPTANCE_TESTS:
                log = root / ("verification/runner/logs/" + name + ".log")
                log.parent.mkdir(parents=True, exist_ok=True)
                log.write_text("..s\nRan 3 tests in 0.001s\n\nOK (skipped=1)\n")
                checks.append({
                    "command": ["python3", "-m", "unittest", "discover", "-s", "tests", "-p", name],
                    "exit_code": 0, "tests": 3, "skipped": 1,
                    "log": log.relative_to(root).as_posix(), "log_sha256": V.sha(log.read_bytes())})
            receipt = {"schema": "math-gauge.runner-offline-acceptance/v1", "status": "passed",
                       "real_candidate_model_calls": 0, "lean_compilations": 0,
                       "formal_model_result": False, "test_count": 3 * len(checks),
                       "input_sha256": {name: V.sha((root / name).read_bytes()) for name in names},
                       "checks": checks}
            path = root / "verification/runner/offline-acceptance.json"
            plan = {"runner_multi_turn_acceptance": "offline-fixture-acceptance-passed",
                    "runner_acceptance": {"path": path.relative_to(root).as_posix()}}

            def check(value):
                path.write_bytes(V.encoded(value))
                plan["runner_acceptance"]["sha256"] = V.sha(path.read_bytes())
                return V.check_offline_acceptance(root, plan)

            self.assertFalse(check(receipt)["formal_model_result"])
            for key, value in (("real_candidate_model_calls", False), ("real_candidate_model_calls", 1),
                               ("lean_compilations", None), ("lean_compilations", 1),
                               ("formal_model_result", True), ("test_count", 1), ("test_count", True)):
                with self.subTest(key=key, value=value):
                    changed = copy.deepcopy(receipt)
                    changed[key] = value
                    with self.assertRaises(ValueError):
                        check(changed)
            for key, value in (("tests", 1), ("skipped", 0), ("skipped", 3),
                               ("skipped", True), ("exit_code", False),
                               ("command", ["python3", "-c", "print('OK')"])):
                with self.subTest(check_key=key, value=value):
                    changed = copy.deepcopy(receipt)
                    changed["checks"][0][key] = value
                    with self.assertRaises(ValueError):
                        check(changed)
            log = root / checks[0]["log"]
            log.write_text("Ran 3 tests in 0.001s\n\nOK (skipped=1)\nRan 3 tests in 0.001s\n\nOK (skipped=1)\n")
            receipt["checks"][0]["log_sha256"] = V.sha(log.read_bytes())
            with self.assertRaisesRegex(ValueError, "test output does not establish"):
                check(receipt)

    def test_author_summary_tracks_current_completed_lean_evidence(self):
        ledger = V.read(ROOT / "verification/author/ledger.json")
        summary = V.author_summary(ROOT)
        self.assertEqual(summary["full_papers"], ledger["counts"]["fully_formalized_papers"])
        self.assertEqual(summary["mandatory_units_complete"], ledger["counts"]["complete_items"])
        self.assertEqual(summary["partial_cases"], [])
        self.assertFalse(summary["candidate_results"])

    def test_refresh_rejects_changed_mathematics_before_writing_packet(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            shutil.copytree(ROOT/'cases', root/'cases', ignore=shutil.ignore_patterns('public'))
            shutil.copytree(ROOT/'verification', root/'verification')
            packet = root/V.PACKET
            shutil.copytree(PACKET, packet)
            before = {p.name: p.read_bytes() for p in packet.glob('*.*')}
            # GR001 is not one of the eight selected self-check targets.
            for name in ('task.md', 'reference.md', 'contract.json'):
                with self.subTest(name=name):
                    path = root/'cases/proofs/MG-GR001'/name
                    original = path.read_bytes()
                    if name == 'contract.json':
                        changed = json.loads(original)
                        changed['stages'][0]['assumptions'].append('Assume compactness.')
                        path.write_text(json.dumps(changed, ensure_ascii=False))
                    else:
                        path.write_bytes(original + b'\nAssume compactness.\n')
                    with self.assertRaisesRegex(ValueError, 'Author evidence must validate'):
                        V.validate_materials(root, refresh=True)
                    self.assertEqual(before, {p.name: p.read_bytes() for p in packet.glob('*.*')})
                    path.write_bytes(original)

    def test_selection_claim_reason_and_membership_are_immutable_design(self):
        for key in ("target_claim", "selection_reason", "case_id", "expected_truth"):
            with self.subTest(key=key):
                selected = copy.deepcopy(self.selection)
                selected["cases"][0][key] += " changed"
                with self.assertRaisesRegex(ValueError, "target claims or selection reasons"):
                    V.check_fixed_design(self.plan, selected, PACKET)

    def test_engineering_identity_rebinding_leaves_selection_semantics_unchanged(self):
        selection = copy.deepcopy(self.selection)
        selection["source_suite_sha256"] = "0" * 64
        for item in selection["cases"]:
            for key in ("task", "reference", "contract"):
                item[key] = "new/" + item[key]
                item[key + "_sha256"] = "0" * 64
        self.assertEqual(V.selection_semantics(self.selection), V.selection_semantics(selection))
        V.check_fixed_design(self.plan, selection, PACKET)

    def test_fixed_prompt_reply_and_schedule_bytes_are_not_silently_rebound(self):
        for name in ("prompts.json", "reply-format.md", "schedule.json"):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory:
                packet = Path(directory)
                for file_name in ("prompts.json", "reply-format.md", "schedule.json"):
                    (packet / file_name).write_bytes((PACKET / file_name).read_bytes())
                with (packet / name).open("ab") as stream:
                    stream.write(b"\n")
                with self.assertRaisesRegex(ValueError, "Fixed design bytes changed"):
                    V.check_fixed_design(self.plan, self.selection, packet)

    def test_message_arms_can_only_change_the_registered_stance(self):
        prompts = copy.deepcopy(self.prompts)
        message = next(item for item in prompts["messages"] if item["arm"] == "affirm")
        message["content"] += "Assume compactness.\n"
        message["content_sha256"] = V.sha(message["content"].encode())
        with self.assertRaisesRegex(ValueError, "beyond the registered stance"):
            V.check_messages(self.selection, prompts, self.reply)

    def test_evaluator_text_in_followup_is_rejected(self):
        prompts = copy.deepcopy(self.prompts)
        first = prompts["messages"][0]
        same_round = [item for item in prompts["messages"]
                      if item["case_id"] == first["case_id"] and item["round"] == first["round"]]
        for message in same_round:
            message["content"] += "expected_truth=true\n"
            message["content_sha256"] = V.sha(message["content"].encode())
        with self.assertRaisesRegex(ValueError, "Evaluator material leaked"):
            V.check_messages(self.selection, prompts, self.reply)

    def test_followup_cannot_read_other_branch_or_independent_attempt(self):
        for parent in ("MG-GR002:A2", "MG-GR002:affirm:1"):
            with self.subTest(parent=parent):
                schedule = copy.deepcopy(self.schedule)
                slot = next(item for item in schedule["slots"]
                            if item["slot_id"] == "MG-GR002:neutral:2")
                slot["parent_slot"] = parent
                with self.assertRaisesRegex(ValueError, "another branch or the wrong predecessor"):
                    V.check_schedule(self.plan, schedule, self.prompts)

    def test_planned_slots_cannot_contain_response_or_grade(self):
        schedule = copy.deepcopy(self.schedule)
        schedule["slots"][0]["response_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "invented result"):
            V.check_schedule(self.plan, schedule, self.prompts)

    def test_task_scoring_leakage_is_rejected_before_preparation(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "task.md").write_text("Prove the claim. 总分100。\n")
            fake_suite = type("FakeSuite", (), {"root": root})()
            with self.assertRaisesRegex(ValueError, "task scoring leakage"):
                V.check_candidate(fake_suite, {"id": "MG-TEST", "task": "task.md"}, root / "out")

    def test_all_candidate_materials_have_no_scoring_text_and_exact_attachments(self):
        suite = V.Suite.load(ROOT / "cases")
        with tempfile.TemporaryDirectory() as directory:
            for cid, case in suite.cases.items():
                with self.subTest(case=cid):
                    identity = V.check_candidate(suite, case, Path(directory) / cid)
                    self.assertEqual(identity["candidate_message_sha256"], next(
                        item["candidate_message_sha256"] for item in self.plan["cases"]
                        if item["case_id"] == cid))

    def test_prompt_tampering_is_not_repaired(self):
        suite = V.Suite.load(ROOT / "cases")
        case = suite.cases["MG-GR002"]
        original = suite.prepare
        def tamper(selected, destination):
            request = original(selected, destination)
            (destination / "prompt.md").write_text("A replaced prompt\n")
            return request
        with tempfile.TemporaryDirectory() as directory, patch.object(suite, "prepare", side_effect=tamper):
            with self.assertRaisesRegex(ValueError, "candidate prompt changed"):
                V.check_candidate(suite, case, Path(directory) / "out")


if __name__ == "__main__":
    unittest.main()
