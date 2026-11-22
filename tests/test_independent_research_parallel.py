"""Four-way admission and continuation checks using only synthetic worker evidence."""

from concurrent.futures import ThreadPoolExecutor
from copy import deepcopy
from pathlib import Path
import tempfile
from threading import Event, Lock
import unittest
from unittest.mock import patch

from math_gauge import independent_research_execution as execution
from scripts import run_independent_research_parallel as parallel


class ParallelContractTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name).resolve()
        for tree in ("control", "workspaces", "runtime"):
            (self.root / tree).mkdir()
        self.plan = {"cohort": [{"id": model_id} for model_id in (parallel.FIRST, *reversed(parallel.PRIORITY))]}
        plan_path = self.root / "control/plan.json"
        execution.write_json(plan_path, self.plan)
        serial = self.root / parallel.SERIAL_TRANSITION
        execution.write_json(serial, {
            "schema": "math-gauge.operator-dispatch-transition/v1", "first_model": parallel.FIRST,
            "gate_path": "control/sol-6.1-xhigh", "candidate_inputs_changed": False,
            "new_candidate_calls_by_this_gate": 0,
        })
        self.authorization = {
            "schema": parallel.AUTH_SCHEMA, "recorded_at": execution.utc(),
            "user_instructions": ["Synthetic four-way authorization"],
            "source_plan_sha256": execution.sha256(plan_path.read_bytes()),
            "serial_transition": execution.descriptor(self.root, serial), "workers": parallel.WORKERS,
            "remaining_priority": list(parallel.PRIORITY),
        }
        self.gate = self.root / parallel.ARCHIVED_GATE
        self.gate.parent.mkdir(parents=True)
        execution.write_json(self.gate, {"kind": "operator-gate-not-candidate", "source": "../serial-to-parallel-transition.json"})

    def auth(self, value):
        path = self.root / parallel.AUTH_PATH
        path.write_bytes(execution.json_bytes(value))
        return execution.descriptor(self.root, path)

    def test_fixed_cover_and_max_xhigh_priority_are_bound_to_the_authorized_bytes(self):
        ref = self.auth(self.authorization)
        self.assertEqual(parallel.load_authorization(self.root, self.plan, ref["sha256"]), ref)
        with self.assertRaisesRegex(ValueError, "exact parallel authorization"):
            parallel.load_authorization(self.root, self.plan, "0" * 64)
        for changed in (dict(workers=3), dict(remaining_priority=list(reversed(parallel.PRIORITY))),
                        dict(remaining_priority=[parallel.PRIORITY[0]] * len(parallel.PRIORITY))):
            changed_ref = self.auth(dict(self.authorization, **changed))
            with self.assertRaisesRegex(ValueError, "Invalid four-way"):
                parallel.load_authorization(self.root, self.plan, changed_ref["sha256"])
        ref = self.auth(self.authorization)
        invalid_plan = {"cohort": self.plan["cohort"][:-1]}
        with self.assertRaisesRegex(ValueError, "retained ten"):
            parallel.load_authorization(self.root, invalid_plan, ref["sha256"])

    def test_first_requires_validated_complete_native_evidence_and_a_closed_process(self):
        preflight = {"path": "control/preflight.json", "sha256": "synthetic"}
        with self.assertRaisesRegex(ValueError, "first configuration must finish"):
            parallel.verified_first(self.root, self.plan, preflight)
        first = self.root / "control" / parallel.FIRST
        first.mkdir()
        execution.write_json(first / "execution.json", {"synthetic": True})
        exit_path = first / "process-exit.json"
        exit_path.write_bytes(b'{"returncode": -15}\n')
        original = {
            "model_id": parallel.FIRST, "origin": execution.NATIVE_ORIGIN, "outcome": "normal-finals",
            "preflight": preflight, "artifacts": {"process-exit.json": execution.descriptor(self.root, exit_path)},
        }
        with patch.object(execution, "validate_execution", return_value=original) as validate:
            value, ref = parallel.verified_first(self.root, self.plan, preflight)
            self.assertIs(value, original)
            validate.assert_called_once_with(self.root, ref, self.plan)
        with patch.object(execution, "validate_execution", return_value=dict(original, outcome="delivery-failed")):
            with self.assertRaisesRegex(ValueError, "complete validated serial"):
                parallel.verified_first(self.root, self.plan, preflight)
        exit_path.write_bytes(b'{"returncode": null}\n')
        changed = deepcopy(original)
        changed["artifacts"]["process-exit.json"] = execution.descriptor(self.root, exit_path)
        with patch.object(execution, "validate_execution", return_value=changed):
            with self.assertRaisesRegex(ValueError, "exit is unconfirmed"):
                parallel.verified_first(self.root, self.plan, preflight)

    def test_every_continuing_path_is_fresh_and_old_gate_is_preserved(self):
        self.assertEqual(parallel.verify_new_paths(self.root), execution.descriptor(self.root, self.gate))
        for suffix in ("control/sol-6.1-xhigh", "runtime/astra-6.2-max", "workspaces/terra-6.1-xhigh"):
            path = self.root / suffix
            path.mkdir()
            with self.assertRaisesRegex(ValueError, "reuse existing evidence"):
                parallel.verify_new_paths(self.root)
            path.rmdir()
        self.gate.write_bytes(b'{"kind":"synthetic-other-gate"}\n')
        with self.assertRaisesRegex(ValueError, "precise noncandidate operator gate"):
            parallel.verify_new_paths(self.root)


class FourWaySchedulerTests(unittest.TestCase):
    def exercise(self, *, failed=None):
        started = {model_id: Event() for model_id in parallel.PRIORITY}
        finish = {model_id: Event() for model_id in parallel.PRIORITY}
        active, sends = set(), []
        lock = Lock()
        paused = Event()

        class ObservableAdmission(parallel.Admissions):
            def pause(self, model_id):
                super().pause(model_id)
                paused.set()

        admission = ObservableAdmission("actual-serial-first-thread")

        def worker(model, dispatch):
            model_id = model["id"]
            admission.register_thread("synthetic-thread-" + model_id)

            def send():
                with lock:
                    active.add(model_id)
                    self.assertLessEqual(len(active), parallel.WORKERS)
                    sends.append(model_id)
                started[model_id].set()

            dispatch(send)
            try:
                self.assertTrue(finish[model_id].wait(10), "Controller did not release fixture worker")
                return {"model_id": model_id, "outcome": "unresolved" if model_id == failed else "normal-finals"}
            finally:
                with lock:
                    active.remove(model_id)

        with ThreadPoolExecutor(max_workers=1) as controller:
            future = controller.submit(parallel.run_scheduled,
                ({"id": model_id} for model_id in parallel.PRIORITY), worker, admission)
            try:
                for model_id in parallel.PRIORITY[:4]:
                    self.assertTrue(started[model_id].wait(5))
                self.assertEqual(sends, list(parallel.PRIORITY[:4]))
                if failed is None:
                    # Allow a later xhigh lane to finish while earlier Max lanes are active.
                    finish[parallel.PRIORITY[2]].set()
                    self.assertTrue(started[parallel.PRIORITY[4]].wait(5))
                    self.assertFalse(finish[parallel.PRIORITY[0]].is_set())
                else:
                    finish[failed].set()
                    self.assertTrue(paused.wait(5))
            finally:
                for gate in finish.values():
                    gate.set()
            rows = future.result(timeout=10)
        return rows, sends, admission

    def test_four_lanes_refill_in_order_without_effort_barrier_or_duplicate_sends(self):
        rows, sends, admission = self.exercise()
        self.assertEqual(sends, list(parallel.PRIORITY))
        self.assertCountEqual([row["model_id"] for row in rows], parallel.PRIORITY)
        self.assertIsNone(admission.paused)

    def test_unresolved_config_stops_new_admissions_and_already_running_lanes_drain(self):
        failed = parallel.PRIORITY[2]
        rows, sends, admission = self.exercise(failed=failed)
        self.assertEqual(sends, list(parallel.PRIORITY[:4]))
        self.assertEqual(admission.paused, failed)
        self.assertEqual(sum(row["outcome"] == "normal-finals" for row in rows), 3)

    def test_presend_pause_and_duplicate_send_are_rejected(self):
        admission = parallel.Admissions("serial-first")
        with self.assertRaisesRegex(ValueError, "unique native thread"):
            admission.register_thread("serial-first")
        sent = Event()
        writes = []
        admission.request(sent, lambda: writes.append("first"))
        with self.assertRaisesRegex(ValueError, "already sent"):
            admission.request(sent, lambda: writes.append("duplicate"))
        admission.pause("unresolved-config")
        with self.assertRaisesRegex(RuntimeError, "paused"):
            admission.request(Event(), lambda: writes.append("after pause"))
        self.assertEqual(writes, ["first"])


if __name__ == "__main__":
    unittest.main()
