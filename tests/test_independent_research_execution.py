"""Synthetic wire events and queue boundaries, without a model or private case."""

import copy
import json
import unittest

from math_gauge import independent_research_execution as runner
import test_taste_v130 as case_fixture


class FixtureTransport:
    def __init__(self, case, model, control, work, *, stop=None, attachment=False):
        self.case, self.model, self.control, self.work = case, model, control, work
        self.stop, self.attachment = stop, attachment

    def __enter__(self):
        self.case.assertFalse(self.case.active)
        self.case.active = True
        return self

    def __exit__(self, *_):
        self.case.active = False

    def start(self):
        return f"synthetic-{self.model['id']}"

    def turn(self, request, rid):
        self.case.dispatched.append((self.model["id"], rid))
        index = runner.ROUNDS.index(rid)
        prompt_names = sorted(path.name for path in (self.work / "rounds").iterdir())
        self.case.assertEqual(prompt_names, [f"{r}.md" for r in runner.ROUNDS[:index + 1]])
        self.case.assertFalse((self.work / "evaluator").exists())
        if index:
            self.case.assertTrue((self.control / "state" / f"{runner.ROUNDS[index - 1]}.seal.json").is_file())
        text = request["params"]["input"]
        self.case.assertEqual(text[0]["text"], f"{rid}: Synthetic invitation.\n")
        if rid == "R1":
            self.case.assertEqual(text[1]["text"], "Synthetic source. ![figure](./figures/fixture.png)\n")
            self.case.assertEqual(text[2], {"type": "localImage", "path": str(self.work / "packet/figures/fixture.png")})
        else:
            self.case.assertEqual(len(text), 1)
        self.case.assertNotIn("EVALUATOR-ONLY-SENTINEL", json.dumps(request))
        sent = runner.utc()
        thread, turn = self.start(), f"synthetic-turn-{index}"
        events = [{"id": request["id"], "result": {"turn": {"id": turn}}}]

        def notice(method, **payload):
            events.append({"method": method, "params": {"threadId": thread, "turnId": turn, **payload}})

        def message(phase, text):
            notice("item/completed", item={"type": "agentMessage", "id": str(len(events)),
                                         "phase": phase, "text": text})

        message("commentary", "Synthetic commentary.")
        cutoff = "deadline" if (rid, "deadline") == self.stop else "native-terminal"
        if cutoff != "deadline":
            final = f"Synthetic final {rid}.\n"
            if rid == "R1" and self.attachment:
                (self.work / "scratch").mkdir()
                (self.work / "scratch/delivered.md").write_bytes(b"Explicitly delivered original.\n")
                (self.work / "scratch/appendix.md").write_bytes(b"Explicitly delivered appendix.\n")
                (self.work / "scratch/extra.md").write_bytes(b"Unsubmitted local scratch.\n")
                final += "[Manuscript](scratch/delivered.md)\n"
                final += "Attached appendix `scratch/appendix.md`.\n[Missing](scratch/missing.md)\n"
            message("final_answer", final)
            message("final_answer", "Later alternate final.")
            notice("thread/tokenUsage/updated", tokenUsage={"last": {"inputTokens": 4, "outputTokens": 2}})
            status = "failed" if (rid, "failed") == self.stop else "completed"
            notice("turn/completed", turn={"id": turn, "status": status})
        at = runner.utc()
        return {"lines": [runner.json_bytes(event) for event in events], "received_at": [at] * len(events),
                "sent_at": sent, "boundary_at": at, "cutoff": cutoff, "pids": {"fixture": True}}


class ResearchExecutionFixture(unittest.TestCase):
    def setUp(self):
        case = case_fixture.ProtocolFixture()
        case.setUp()
        self.addCleanup(case.doCleanups)
        self.root, self.registration = case.root, case.registration
        self.public = self.root / "public"
        self.public.mkdir()
        (self.public / "base.json").write_bytes(b"Historical synthetic baseline")
        cohort = []
        for identifier, effort in (("fixture-one", "max"), ("fixture-two", "xhigh")):
            path = self.public / f"{identifier}.json"
            runner.write_json(path, {"model": {"requested_model": "synthetic-model", "requested_reasoning_effort": effort}})
            cohort.append({"id": identifier, "model": "synthetic-model", "effort": effort,
                           "prior_selected_source": runner.descriptor(self.public, path), "status": "not-started"})
        plan = {"schema": runner.PLAN_SCHEMA, "edition": "1.3.0", "status": "authorized-preparation-not-started",
                "rounds": list(runner.ROUNDS), "candidate_model_calls": 0, "maximum_initial_math_dispatches": 6,
                "cohort": cohort, "registration": runner.descriptor(self.registration.parent, self.registration),
                "baseline": {"edition": "1.2.0", **runner.descriptor(self.public, self.public / "base.json")},
                "budgets": {**runner.BUDGETS, "outer_grace_is_answer_time": False},
                "conditions": {"commit_before_candidate_dispatch": True, "preflight_before_candidate_dispatch": True,
                    "fresh_native_session": True, "same_session_three_rounds": True, "local_tools": True,
                    "tool_network": False, "external_materials": False, "extra_feedback": False,
                    "fourth_round": False, "seal_first_normal_final_before_next_round": True,
                    "automatic_quality_retry": False, "unconfirmed_failure_retry": False}}
        self.plan_path = self.registration.parent / "plan.json"
        runner.write_json(self.plan_path, plan)
        self.plan, self.active, self.dispatched = plan, False, []
        self.run_root = runner.prepare(self.plan_path, self.public, self.root / "run", fixture=True)

    def test_serial_three_round_runs_bind_first_finals_and_explicit_artifacts(self):
        result = runner.execute_queue(self.run_root,
            lambda *args: FixtureTransport(self, *args, attachment=True), fixture=True)
        self.assertEqual(self.dispatched, [(name, rid) for name in ("fixture-one", "fixture-two") for rid in runner.ROUNDS])
        for row in result["cohort"]:
            data = runner.validate_execution(self.run_root, row["execution"], self.plan, allow_fixture=True)
            state = self.run_root / data["state"]
            self.assertEqual(data["outcome"], "normal-finals")
            self.assertEqual((state / "R1.md").read_bytes(), b"Synthetic final R1.\n[Manuscript](scratch/delivered.md)\n"
                             b"Attached appendix `scratch/appendix.md`.\n[Missing](scratch/missing.md)\n")
            self.assertEqual((state / "R1.files/scratch/delivered.md").read_bytes(), b"Explicitly delivered original.\n")
            self.assertEqual((state / "R1.files/scratch/appendix.md").read_bytes(), b"Explicitly delivered appendix.\n")
            self.assertFalse((state / "R1.files/scratch/extra.md").exists())
            self.assertEqual(data["rounds"][0]["attachment_diagnostics"][0]["status"], "missing-regular-file")
            (self.run_root / "workspaces" / row["model_id"] / "scratch/appendix.md").write_bytes(b"Later scratch edit\n")
            runner.validate_execution(self.run_root, row["execution"], self.plan, allow_fixture=True)
            self.assertEqual(data["rounds"][0]["usage_events"][0]["last"]["outputTokens"], 2)
            with self.assertRaisesRegex(ValueError, "Fixture"):
                runner.validate_execution(self.run_root, row["execution"], self.plan)

    def test_native_error_after_a_body_neither_freezes_it_nor_starts_next_model(self):
        result = runner.execute_queue(self.run_root,
            lambda *args: FixtureTransport(self, *args, stop=("R2", "failed")), fixture=True)
        self.assertEqual(self.dispatched, [("fixture-one", "R1"), ("fixture-one", "R2")])
        self.assertEqual([r["outcome"] for r in result["cohort"]], ["unresolved", "not-started"])
        self.assertFalse((self.run_root / "control/fixture-one/state/R2.md").exists())
        with self.assertRaisesRegex(ValueError, "unresolved"):
            runner.validate_execution(self.run_root, result["cohort"][0]["execution"], self.plan, allow_fixture=True)

    def test_deadline_stops_only_the_current_trajectory_without_pretending_r3_was_dispatched(self):
        result = runner.execute_queue(self.run_root,
            lambda *args: FixtureTransport(self, *args, stop=("R2", "deadline")), fixture=True)
        self.assertEqual(self.dispatched, [(name, rid) for name in ("fixture-one", "fixture-two") for rid in ("R1", "R2")])
        data = runner.validate_execution(self.run_root, result["cohort"][0]["execution"], self.plan, allow_fixture=True)
        self.assertEqual(data["outcome"], "delivery-failed")
        self.assertIsNone(data["rounds"][1]["terminal"])

    def test_tampered_final_or_wire_events_break_adoption(self):
        result = runner.execute_queue(self.run_root, lambda *args: FixtureTransport(self, *args), fixture=True)
        ref = result["cohort"][0]["execution"]
        data = runner.validate_execution(self.run_root, ref, self.plan, allow_fixture=True)
        wire = self.run_root / data["rounds"][0]["wire_events"]["path"]
        wire.write_bytes(wire.read_bytes().replace(b"Synthetic final", b"Fabricated final"))
        with self.assertRaisesRegex(ValueError, "hash mismatch"):
            runner.validate_execution(self.run_root, ref, self.plan, allow_fixture=True)
        false_plan = copy.deepcopy(self.plan)
        false_plan["cohort"].reverse()
        with self.assertRaisesRegex(ValueError, "different plan"):
            runner.validate_execution(self.run_root, ref, false_plan, allow_fixture=True)


if __name__ == "__main__":
    unittest.main()
