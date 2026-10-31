"""Independent offline adversarial checks of source evidence and score handoff.

All command-origin records and human-shaped audits are synthetic temporary
fixtures. The transport seam is patched and subprocess launch is forbidden.
Nothing in these tests is an actual model result or human approval.
"""

import copy
from datetime import datetime, timedelta
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

from math_gauge.benchmarks import BenchmarkProfile, build_plan, identity
from math_gauge.catalog import Suite, digest_bytes, read_json, write_json
from math_gauge.eligibility import (execution_eligibility_templates,
                                   import_execution_eligibility,
                                   verify_execution_eligibility)
from math_gauge.reliability import (execute_reliability_run, inspect_reliability_run,
                                    apply_reliability_reviews, reliability_review_templates,
                                    reliability_score_inputs)
from math_gauge.scoring import score_runs
from test_eligibility import (ROOT, frozen_requirements, rewrite_source,
                              synthetic_run, synthetic_submission)


class EligibilityAcceptanceTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        self.no_process = patch("subprocess.Popen", side_effect=AssertionError(
            "independent offline acceptance cannot launch a candidate process"))
        self.no_process.start()
        self.addCleanup(self.no_process.stop)
        self.run = self.root / "run"
        self.meta, self.records = synthetic_run(self.run)
        self.sid = next(iter(self.records))

    def source(self, name="source"):
        return synthetic_submission(self.run, self.sid, self.root / name)

    def test_self_hashed_acceptance_flags_without_observations_never_unlock_a_slot(self):
        submission = next(x for x in execution_eligibility_templates(self.run)["slots"]
                          if x["slot_id"] == self.sid)
        for attempt in submission["observations"]["attempts"]:
            attempt["submission_state"] = "submitted"
        source = self.root / "flags"
        source.mkdir()
        data = b'{"model_identity_verified":true,"fresh_context_verified":true,"tools_disabled":true}'
        (source / "flags.json").write_bytes(data)
        submission["artifacts"] = [{"path": "flags.json", "bytes": len(data),
                                    "sha256": digest_bytes(data), "kind": "ledger", "origin": "operator"}]
        submission["audit"].update(reviewer="SYNTHETIC HUMAN-SHAPED FIXTURE", reviewer_kind="human",
                                    reviewed_at=(datetime.fromisoformat(self.records[self.sid]["attempts"][-1]["finished_at"])
                                                 + timedelta(seconds=1)).isoformat(), decision="accept")
        for check in submission["audit"]["checks"].values():
            check.update(decision="verified", rationale="Synthetic asserted flag; no underlying observations.",
                         sources=[{"artifact": "flags.json"}])
        path = source / "submission.json"
        write_json(path, submission)
        imported = import_execution_eligibility(self.run, self.sid, path)
        self.assertFalse(imported["eligible"])
        self.assertIn("attempt_1_backend_model_unverified", imported["reasons"])
        self.assertIn("attempt_ledger_unverified", imported["reasons"])
        self.assertFalse(verify_execution_eligibility(self.run)["slots"][self.sid]["eligible"])

    def test_missing_actual_backend_fields_are_unknown_despite_matching_requested_values(self):
        previous = None
        for field in ("provider", "model", "reasoning_effort"):
            with self.subTest(field=field):
                source = self.source("unknown-" + field)
                rewrite_source(source, "raw/attempt-1-metadata.json",
                               lambda x: x.update({field: None}))
                result = import_execution_eligibility(self.run, self.sid, source,
                                                       revise=previous is not None,
                                                       expected_snapshot=previous)
                previous = result["audit_snapshot"]["sha256"]
                self.assertFalse(result["eligible"])
                self.assertIn("attempt_1_backend_observation_unknown", result["reasons"])

    def test_request_echo_and_operator_metadata_cannot_be_reclassified_as_provider_return(self):
        for origin in ("request", "operator", "client"):
            with self.subTest(origin=origin):
                source = self.source("echo-" + origin)
                submission = read_json(source)
                descriptor = next(x for x in submission["artifacts"] if x["kind"] == "provider-metadata")
                descriptor["origin"] = origin
                write_json(source, submission)
                with self.assertRaisesRegex(ValueError, "origin|provider"):
                    import_execution_eligibility(self.run, self.sid, source)

    def test_rehashed_missing_actual_worker_or_this_runs_review_probes_is_rejected(self):
        mutations = {
            "worker-report": lambda x: x["pid_checks"].pop(),
            "worker-parent": lambda x: x["processes"][1].update(ppid=9999),
            "review-probe": lambda x: x["probe_manifest"]["negative"][0].update(
                path="/synthetic-protected/unrelated-reference.md"),
            "probe-absent": lambda x: x["probe_manifest"]["negative"][0].update(exists_before_run=False),
            "probe-enoent": lambda x: x["open_probe"]["checks"][1].update(errno=2),
            "positive-hash": lambda x: x["open_probe"]["checks"][0].update(observed_sha256="0" * 64),
        }
        for name, mutate in mutations.items():
            with self.subTest(name=name):
                source = self.source(name)
                rewrite_source(source, "raw/attempt-1-isolation.json", mutate)
                with self.assertRaises(ValueError):
                    import_execution_eligibility(self.run, self.sid, source)

    def test_boolean_counts_exit_codes_and_prebirth_pid_reports_are_rejected(self):
        mutations = (
            ("count", "invocation", lambda x: x.update(request_count=True)),
            ("exit", "invocation", lambda x: x.update(exit_code=False)),
            ("errno", "isolation", lambda x: x["open_probe"]["checks"][1].update(errno=True)),
            ("ledger-count", None, lambda x: x["attempts"][0].update(request_count=True)),
            ("pid-time", "isolation", lambda x: x["pid_checks"][1].update(
                utc=(datetime.fromisoformat(x["processes"][1]["started_at"])
                     - timedelta(seconds=1)).isoformat())),
        )
        for name, kind, mutate in mutations:
            with self.subTest(name=name):
                source = self.source(name)
                rewrite_source(source, "raw/ledger.json" if kind is None
                               else "raw/attempt-1-" + kind + ".json", mutate)
                with self.assertRaises(ValueError):
                    import_execution_eligibility(self.run, self.sid, source)

    def test_runtime_tools_cannot_overrule_frozen_plan_no_tool_policy(self):
        for field in ("allowed_tools", "internal_tools"):
            with self.subTest(field=field):
                requirements = frozen_requirements()
                requirements[field] = ["search_web"]
                suite = Suite.load(ROOT / "cases")
                profile = BenchmarkProfile.load(ROOT / "protocol/benchmark-profile.json", suite)
                runtime = dict(self.meta["plan"]["runtime"], execution_requirements=requirements)
                with self.assertRaises(ValueError):
                    build_plan(profile, suite, runtime=runtime)

    def test_peer_attempt_disclosure_and_actual_network_process_binding_are_required(self):
        mutations = (
            ("peer-attempts", "raw/ledger.json", lambda x: x.update(peer_provenance=[])),
            ("origin-attempts", "raw/origin-manifest.json", lambda x: x.update(budget_evidence={})),
            ("network-pid", "raw/attempt-1-network-worker.json", lambda x: x.update(pid=999999)),
        )
        for name, artifact, mutate in mutations:
            with self.subTest(name=name):
                source = self.source(name)
                rewrite_source(source, artifact, mutate)
                with self.assertRaises(ValueError):
                    import_execution_eligibility(self.run, self.sid, source)

    def test_actual_event_registry_and_calls_override_no_tools_assertion(self):
        for field, value in (("effective_tools", [{"name": "search_web", "classification": "candidate",
                                                   "permission": "allowed"}]),
                             ("tool_calls", [{"name": "search_web", "arguments": {}}])):
            with self.subTest(field=field):
                source = self.source("events-" + field)
                submission = read_json(source)
                descriptor = next(x for x in submission["artifacts"] if x["kind"] == "cli-events")
                path = source.parent / descriptor["path"]
                event = json.loads(path.read_bytes())
                event[field] = value
                raw = (json.dumps(event) + "\n").encode()
                path.write_bytes(raw)
                descriptor.update(bytes=len(raw), sha256=digest_bytes(raw))
                write_json(source, submission)
                rewrite_source(source, "raw/attempt-1-invocation.json", lambda x: x.update(events_sha256=digest_bytes(raw)))
                with self.assertRaisesRegex(ValueError, "registry|tool|Tool"):
                    import_execution_eligibility(self.run, self.sid, source)

    def test_reuse_keeps_original_audit_and_generation_but_conflicting_revision_cannot_merge(self):
        source = self.source()
        accepted = import_execution_eligibility(self.run, self.sid, source)
        destination = self.root / "reused"
        with patch("math_gauge.reliability.invoke_conversation", side_effect=AssertionError(
                "reused slots must not generate another answer")):
            execute_reliability_run(self.meta["plan"], Suite.load(ROOT / "cases"), destination,
                                    command=self.meta["command"], reuse_runs=[self.run])
        _, reused = inspect_reliability_run(destination)
        copied = verify_execution_eligibility(destination)["slots"][self.sid]
        self.assertEqual(reused[self.sid]["evidence_id"], self.records[self.sid]["evidence_id"])
        self.assertEqual(reused[self.sid]["evidence_origin_run_id"], self.meta["run_id"])
        self.assertEqual(copied["receipt_sha256"], accepted["receipt_sha256"])
        self.assertTrue(copied["eligible"])
        submission = read_json(source)
        submission["audit"]["decision"] = "reject"
        submission["audit"]["checks"]["external_authenticity"].update(
            decision="rejected", rationale="Synthetic later provenance withdrawal.")
        write_json(source, submission)
        import_execution_eligibility(self.run, self.sid, source, revise=True,
                                     expected_snapshot=accepted["audit_snapshot"]["sha256"])
        with self.assertRaisesRegex(ValueError, "[Cc]onflicting.*audit"):
            score_runs([self.run, destination])

    def test_reused_original_audit_remains_checkable_after_source_directories_are_deleted(self):
        source = self.source()
        accepted = import_execution_eligibility(self.run, self.sid, source)
        destination = self.root / "independent-copy"
        with patch("math_gauge.reliability.invoke_conversation", side_effect=AssertionError(
                "exact dependency reuse must not make another request")):
            execute_reliability_run(self.meta["plan"], Suite.load(ROOT / "cases"), destination,
                                    command=self.meta["command"], reuse_runs=[self.run])
        shutil.rmtree(self.run)
        shutil.rmtree(source.parent)
        evidence = verify_execution_eligibility(destination)["slots"][self.sid]
        self.assertTrue(evidence["eligible"])
        self.assertEqual(evidence["receipt_sha256"], accepted["receipt_sha256"])
        report = score_runs([destination])
        self.assertIsNone(report["metrics"]["overall"]["formal_score"])
        self.assertIn(self.records[self.sid]["evidence_id"], {x["evidence_id"] for x in report["evidence"]})

    def test_cross_shard_session_state_and_request_reuse_is_rejected_for_distinct_generations(self):
        suite = Suite.load(ROOT / "cases")
        profile = BenchmarkProfile.load(ROOT / "protocol/benchmark-profile.json", suite)
        plan = build_plan(profile, suite, runtime=self.meta["plan"]["runtime"])

        def transport(command, projected, workspace, timeout, **kwargs):
            return {"stdout": "synthetic response" if len(projected["messages"]) == 1
                    else "KEEP\nsynthetic rationale", "stderr": b"", "exit_code": 0,
                    "status": "ok", "usage": {"total_tokens": 1}}

        for dimension in ("session", "state", "request"):
            with self.subTest(dimension=dimension):
                first, second = self.root / (dimension + "-neutral"), self.root / (dimension + "-stance")
                with patch("math_gauge.reliability.invoke_conversation", side_effect=transport):
                    execute_reliability_run(plan, suite, first, command=self.meta["command"], targets=["neutral"])
                    execute_reliability_run(plan, suite, second, command=self.meta["command"], targets=["stance"],
                                            reuse_runs=[first])
                cid = "MG-GR002"
                a = synthetic_submission(first, cid + ":neutral:1", self.root / (dimension + "-a"))
                b = synthetic_submission(second, cid + ":affirm:1", self.root / (dimension + "-b"))
                first_invocation = read_json(a.parent / "raw/attempt-1-invocation.json")
                if dimension == "session":
                    for kind in ("invocation", "context"):
                        rewrite_source(b, "raw/attempt-1-" + kind + ".json", lambda x: x.update(
                            session_id=first_invocation["session_id"]))
                elif dimension == "state":
                    state = read_json(a.parent / "raw/attempt-1-isolation.json")["fresh_state"]["path"]
                    rewrite_source(b, "raw/attempt-1-isolation.json", lambda x: x["fresh_state"].update(path=state))
                else:
                    shared = first_invocation["request_id"]
                    for kind in ("request", "metadata", "response", "invocation"):
                        rewrite_source(b, "raw/attempt-1-" + kind + ".json",
                                       lambda x: x.update(request_id=shared))
                    submission = read_json(b)
                    artifact = next(x for x in submission["artifacts"] if x["kind"] == "cli-events")
                    path = b.parent / artifact["path"]
                    event = json.loads(path.read_bytes())
                    event["request_id"] = shared
                    raw = (json.dumps(event) + "\n").encode()
                    path.write_bytes(raw)
                    events_hash = digest_bytes(raw)
                    artifact.update(bytes=len(raw), sha256=events_hash)
                    write_json(b, submission)
                    rewrite_source(b, "raw/attempt-1-invocation.json", lambda x: x.update(events_sha256=events_hash))
                import_execution_eligibility(first, cid + ":neutral:1", a)
                import_execution_eligibility(second, cid + ":affirm:1", b)
                with self.assertRaisesRegex(ValueError, "[Rr]eused|[Cc]ollis|[Dd]uplicate"):
                    score_runs([first, second])

    def test_merge_can_resolve_missing_ancestor_audit_from_same_original_generation(self):
        suite = Suite.load(ROOT / "cases")
        profile = BenchmarkProfile.load(ROOT / "protocol/benchmark-profile.json", suite)
        plan = build_plan(profile, suite, runtime=self.meta["plan"]["runtime"])
        parent_run, child_run = self.root / "parent-shard", self.root / "child-shard"

        def transport(command, projected, workspace, timeout, **kwargs):
            return {"stdout": "synthetic response" if len(projected["messages"]) == 1
                    else "KEEP\nsynthetic rationale", "stderr": b"", "exit_code": 0,
                    "status": "ok", "usage": {"total_tokens": 1}}

        with patch("math_gauge.reliability.invoke_conversation", side_effect=transport):
            execute_reliability_run(plan, suite, parent_run, command=self.meta["command"], targets=["neutral"])
            execute_reliability_run(plan, suite, child_run, command=self.meta["command"], targets=["stance"],
                                    reuse_runs=[parent_run])
        root_sid, child_sid = "MG-GR002:A1", "MG-GR002:affirm:1"
        child_source = synthetic_submission(child_run, child_sid, self.root / "child-evidence")
        child = import_execution_eligibility(child_run, child_sid, child_source)
        self.assertFalse(child["eligible"])
        self.assertIn("ancestor_execution_ineligible", child["reasons"])
        before = next(x for x in reliability_score_inputs(child_run)["slots"] if x["slot_id"] == child_sid)
        parent_source = synthetic_submission(parent_run, root_sid, self.root / "parent-evidence")
        import_execution_eligibility(parent_run, root_sid, parent_source)
        report = score_runs([parent_run, child_run])
        merged = next(x for x in report["evidence"] if x["slot_id"] == child_sid)
        self.assertTrue(merged["comparison_eligible"])
        self.assertTrue(merged["execution_eligibility"]["eligible"])
        self.assertEqual(merged["execution_receipt_sha256"], before["execution_receipt_sha256"])
        self.assertEqual(merged["evidence_id"], before["evidence_id"])
        self.assertIsNone(report["metrics"]["overall"]["formal_score"])

    def test_withdrawn_audit_has_bound_historical_report_and_no_current_formal_upgrade(self):
        source = self.source()
        accepted = import_execution_eligibility(self.run, self.sid, source)
        snapshot = accepted["audit_snapshot"]["sha256"]
        submission = read_json(source)
        submission["audit"]["decision"] = "reject"
        write_json(source, submission)
        with self.assertRaisesRegex(ValueError, "expected snapshot"):
            import_execution_eligibility(self.run, self.sid, source, revise=True,
                                         expected_snapshot="0" * 64)
        import_execution_eligibility(self.run, self.sid, source, revise=True, expected_snapshot=snapshot)
        current = reliability_score_inputs(self.run)
        historical = score_runs([self.run], audit_snapshot=snapshot)
        self.assertFalse(next(x for x in current["slots"] if x["slot_id"] == self.sid)["comparison_eligible"])
        self.assertEqual(historical["result_kind"], "historical")
        self.assertTrue(historical["execution_audit_snapshots"][0]["audit_snapshot"]["historical"])
        for metric in historical["metrics"].values():
            self.assertIsNone(metric["formal_score"])
        self.assertIn("execution_audit_superseded", historical["metrics"]["overall"]["formal_eligibility"]["reasons"])

    def test_edited_plan_cannot_upgrade_real_draft_case_approval(self):
        plan = copy.deepcopy(self.meta["plan"])
        plan["case_index"][0]["case_approved"] = True
        plan["plan_sha256"] = identity({k: v for k, v in plan.items() if k != "plan_sha256"})
        with patch("math_gauge.reliability.invoke_conversation", side_effect=AssertionError(
                "invalid paper approval must be rejected before candidate transport")):
            with self.assertRaisesRegex(ValueError, "approval|approved|review"):
                execute_reliability_run(plan, Suite.load(ROOT / "cases"), self.root / "upgraded",
                                        command=self.meta["command"])

    def test_temporary_approved_manifest_and_parsed_audits_unlock_only_complete_proof_component(self):
        """Exercise the positive reader path using explicitly synthetic temporary approvals."""
        repository = self.root / "SYNTHETIC-APPROVAL-FIXTURE"
        cases_root = repository / "cases"
        cid = "MG-GR002"
        ids = {cid, "MG-GF101", "MG-GF102", "MG-C002"}
        metadata = read_json(ROOT / "cases/suite.json")
        metadata.update(id="SYNTHETIC-SOFTWARE-TEST-ONLY", title="Temporary software approval fixture",
                        cases=[name for name in metadata["cases"] if Path(name).parent.name in ids])
        for name in metadata["cases"]:
            directory = Path(name).parent
            shutil.copytree(ROOT / "cases" / directory, cases_root / directory)
            if directory.name == cid:
                case = read_json(cases_root / name)
                case.update(status="approved", test_fixture_only=True)
                case["review"]["human"] = "approved"
                write_json(cases_root / name, case)
        write_json(cases_root / "suite.json", metadata)
        shutil.copy2(ROOT / "cases/sources.json", cases_root / "sources.json")
        suite = Suite.load(cases_root)
        packet = repository / "protocol/reliability"
        for name in ("selection", "prompts", "schedule"):
            value = read_json(ROOT / "protocol/reliability" / (name + ".json"))
            if name == "selection":
                value["cases"] = [x for x in value["cases"] if x["case_id"] == cid]
                value.update(source_suite_sha256=suite.sha256, case_count=1,
                             truth_counts={value["cases"][0]["expected_truth"]: 1}, category_counts={"written": 1})
            elif name == "prompts":
                value["messages"] = [x for x in value["messages"] if x["case_id"] == cid]
            else:
                value["slots"] = [x for x in value["slots"] if x["case_id"] in ids
                                  and (x["kind"] == "independent" or x["case_id"] == cid)]
                for number, slot in enumerate(value["slots"], 1):
                    slot["ordinal_per_model"] = number
                value.update(planned_slots_per_model=18, planned_independent_slots_per_model=12,
                             planned_followup_slots_per_model=6)
            write_json(packet / (name + ".json"), value)
        profile_data = read_json(ROOT / "protocol/benchmark-profile.json")
        profile_data.update(id="SYNTHETIC-SOFTWARE-TEST-PROFILE", suite={
            "id": suite.metadata["id"], "version": suite.metadata["version"], "sha256": suite.sha256})
        for component in profile_data["components"]:
            component["case_ids"] = [x for x in component["case_ids"] if x in ids]
        profile_path = repository / "protocol/benchmark-profile.json"
        write_json(profile_path, profile_data)
        profile = BenchmarkProfile.load(profile_path, suite, repository_root=repository)
        plan = build_plan(profile, suite, ["proofs"], runtime=self.meta["plan"]["runtime"])
        run = self.root / "approved-component-run"
        with patch("math_gauge.reliability.invoke_conversation", return_value={
                "stdout": "SYNTHETIC UNASSESSED BODY", "stderr": b"", "exit_code": 0,
                "status": "ok", "usage": {"total_tokens": 1}}):
            execute_reliability_run(plan, suite, run, command=self.meta["command"])
        source_paths = []
        for label in ("A1", "A2", "A3"):
            sid = cid + ":" + label
            source = synthetic_submission(run, sid, self.root / ("approved-sources-" + label))
            source_paths.append(source)
            self.assertTrue(import_execution_eligibility(run, sid, source)["eligible"])

        def pass_axis(axis):
            axis.update(decision="pass", assumption_fidelity="clean", proof_validity="valid",
                        scope_accuracy="correct", unnecessary_restriction=False, reasons=[],
                        notes="SYNTHETIC HUMAN-SHAPED SOFTWARE TEST; not an actual mathematical judgment.")

        entries = reliability_review_templates(run)
        for entry in entries:
            entry.update(reviewer="SYNTHETIC HUMAN-SHAPED SOFTWARE TEST", reviewer_kind="human")
            pass_axis(entry)
            entry["format_review"].update(decision="valid", notes="Synthetic software fixture material.")
            for stage in entry["stages"]:
                pass_axis(stage)
                stage["failure_category"] = "none"
                pass_axis(stage["math_review"])
            pass_axis(entry["focus_review"])
            entry["focus_review"]["verdict"] = plan["reliability"]["selection"]["cases"][0]["expected_truth"]
        apply_reliability_reviews(run, entries)
        positive = score_runs([run])
        self.assertEqual(positive["metrics"]["proofs"]["formal_score"], 100)
        self.assertIsNone(positive["metrics"]["overall"]["formal_score"])
        self.assertEqual(positive["metrics"]["proofs"]["coverage"]["formal_eligible_slots"], 3)
        self.assertTrue(all(x["case_approval_evidence_verified"] for x in reliability_score_inputs(run)["slots"]))
        snapshot = verify_execution_eligibility(run)["audit_snapshot"]["sha256"]
        withdrawn = read_json(source_paths[0])
        withdrawn["audit"]["decision"] = "reject"
        write_json(source_paths[0], withdrawn)
        import_execution_eligibility(run, cid + ":A1", source_paths[0], revise=True, expected_snapshot=snapshot)
        self.assertIsNone(score_runs([run])["metrics"]["proofs"]["formal_score"])
        historical = score_runs([run], audit_snapshot=snapshot)
        self.assertIsNone(historical["metrics"]["proofs"]["formal_score"])
        self.assertEqual(historical["metrics"]["proofs"]["historical_formal_score"], 100)
        public = Suite.load(ROOT / "cases")
        self.assertTrue(all(x["status"] == "draft" and x["review"]["human"] == "pending"
                            for x in public.cases.values()))


if __name__ == "__main__":
    unittest.main()
