"""Continue the existing private research batch with its authorized four-way order."""

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import json
from pathlib import Path
import re
import subprocess
import sys
from threading import Event, Lock


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from math_gauge import independent_research_execution as execution
from math_gauge import taste_v130 as flow
from scripts import run_independent_research_batch as native


FIRST = "sol-6.1-max"
PRIORITY = (
    "astra-6.2-max", "astra-6-max", "astra-6.2-xhigh", "astra-6-xhigh",
    "sol-6.2-max", "sol-6.2-xhigh", "sol-6.1-xhigh", "terra-6.1-max", "terra-6.1-xhigh",
)
WORKERS = 4
AUTH_SCHEMA = "math-gauge.independent-research-parallel-authorization/v1"
AUTH_PATH = "control/parallel-authorization.json"
SERIAL_TRANSITION = "control/serial-to-parallel-transition.json"
ARCHIVED_GATE = "control/operator-gates/sol-6.1-xhigh/operator-dispatch-gate.json"
ENGINE = "math_gauge/independent_research_execution.py"
PAUSE_STATES = frozenset({"unresolved", "not-started"})


def _require(condition, message):
    if not condition:
        raise ValueError(message)


def load_authorization(root, plan, expected_sha256):
    ref = execution.descriptor(root, flow._contained(root, AUTH_PATH))
    _require(ref["sha256"] == expected_sha256, "Select the exact parallel authorization bytes")
    authorization = json.loads(flow._read(root, ref))
    cohort = [row["id"] for row in plan["cohort"]]
    _require(len(cohort) == len(PRIORITY) + 1 and set(cohort) == {FIRST, *PRIORITY},
             "Continuation must cover precisely the retained ten configurations")
    _require(set(authorization) == {"schema", "recorded_at", "user_instructions", "source_plan_sha256",
             "serial_transition", "workers", "remaining_priority"}
             and authorization["schema"] == AUTH_SCHEMA
             and authorization["source_plan_sha256"] == execution.sha256((root / "control/plan.json").read_bytes())
             and authorization["workers"] == WORKERS and authorization["remaining_priority"] == list(PRIORITY)
             and isinstance(authorization["user_instructions"], list) and authorization["user_instructions"]
             and all(isinstance(text, str) and text.strip() for text in authorization["user_instructions"]),
             "Invalid four-way parallel authorization")
    execution._stamp(authorization["recorded_at"])
    serial_ref = authorization["serial_transition"]
    _require(serial_ref["path"] == SERIAL_TRANSITION, "Preserve the original serial transition binding")
    serial = json.loads(flow._read(root, serial_ref))
    _require(serial["schema"] == "math-gauge.operator-dispatch-transition/v1"
             and serial["first_model"] == FIRST and serial["gate_path"] == "control/sol-6.1-xhigh"
             and serial["candidate_inputs_changed"] is False and serial["new_candidate_calls_by_this_gate"] == 0,
             "Original operator gate does not match the frozen first configuration")
    return ref


def verified_first(root, plan, preflight_ref):
    path = flow._contained(root, f"control/{FIRST}/execution.json")
    _require(path.is_file(), "The first configuration must finish and close its native process")
    ref = execution.descriptor(root, path)
    first = execution.validate_execution(root, ref, plan)
    _require(first["model_id"] == FIRST and first["origin"] == execution.NATIVE_ORIGIN
             and first["outcome"] == "normal-finals" and first["preflight"] == preflight_ref
             and "parallel_dispatch" not in first,
             "First configuration needs a complete validated serial native result")
    exit_status = json.loads(flow._read(root, first["artifacts"]["process-exit.json"]))
    _require(type(exit_status["returncode"]) is int, "First native process exit is unconfirmed")
    return first, ref


def verify_new_paths(root):
    for model_id in PRIORITY:
        for tree in ("control", "runtime", "workspaces"):
            path = root / tree / model_id
            _require(not path.exists() and not path.is_symlink(),
                     f"Continuation would reuse existing evidence or the operator gate: {tree}/{model_id}")
    _require(not (root / "batch-summary.json").exists(), "Batch summary already exists")
    _require(not (root / "control/parallel-dispatch-freeze.json").exists(), "Parallel dispatch was already frozen")
    gate_ref = execution.descriptor(root, flow._contained(root, ARCHIVED_GATE))
    gate = json.loads(flow._read(root, gate_ref))
    _require(gate == {"kind": "operator-gate-not-candidate", "source": "../serial-to-parallel-transition.json"},
             "Archive the precise noncandidate operator gate before continuing")
    return gate_ref


def check_continuation(run_root, authorization_sha256):
    root, prepared, plan, registration = execution.prepared(run_root)
    _require(prepared["fixture_only"] is False, "Continuation requires the frozen native plan")
    authorization = load_authorization(root, plan, authorization_sha256)
    preflight = execution.descriptor(root, flow._contained(root, "control/preflight.json"))
    serial_freeze = execution.descriptor(root, flow._contained(root, "control/dispatch-freeze.json"))
    original = json.loads(flow._read(root, serial_freeze))
    probe = json.loads(flow._read(root, preflight))
    _require(original["preflight"] == preflight and original["budgets"] == execution.BUDGETS
             and original["binary"] == probe["binary"] and probe["status"] == "passed"
             and probe["native_model_list_matches"] is True and probe["plan_sha256"] == prepared["plan_sha256"],
             "The original native isolation proof or serial freeze changed")
    for artifact in probe["artifacts"]:
        flow._read(root, artifact)
    first, first_ref = verified_first(root, plan, preflight)
    gate = verify_new_paths(root)
    bindings = {"authorization": authorization, "preflight": preflight, "serial_dispatch_freeze": serial_freeze,
                "first_execution": first_ref, "archived_operator_gate": gate}
    return root, prepared, plan, registration, original, probe, first, bindings


class Admissions:
    def __init__(self, first_thread):
        self.lock = Lock()
        self.seen_threads = {first_thread}
        self.paused = None

    def register_thread(self, thread):
        with self.lock:
            _require(thread not in self.seen_threads, "Expected a fresh, unique native thread")
            self.seen_threads.add(thread)

    def request(self, ready, write):
        with self.lock:
            if self.paused is not None:
                raise RuntimeError(f"Parallel admissions paused after {self.paused}")
            _require(not ready.is_set(), "First native request was already sent")
            write()
            ready.set()

    def pause(self, model_id):
        with self.lock:
            if self.paused is None:
                self.paused = model_id


def run_scheduled(models, run_one, admission):
    """Refill open slots in order after each prior first native send succeeds."""
    rows, active = [], set()

    def collect(done):
        for future in done:
            rows.append(future.result())
            active.remove(future)

    def run(model, ready):
        try:
            row = run_one(model, lambda write: admission.request(ready, write))
            if row["outcome"] in PAUSE_STATES:
                admission.pause(model["id"])
            else:
                _require(row["outcome"] in {"normal-finals", "delivery-failed"} and ready.is_set(),
                         "Configuration lacks a recognized settlement and first dispatch marker")
            return row
        except BaseException:
            admission.pause(model["id"])
            raise
        finally:
            ready.set()

    with ThreadPoolExecutor(max_workers=WORKERS) as pool:
        for model in models:
            collect({future for future in active if future.done()})
            if len(active) == WORKERS:
                collect(wait(active, return_when=FIRST_COMPLETED).done)
            if admission.paused is not None:
                break
            ready = Event()
            active.add(pool.submit(run, model, ready))
            # A later configuration cannot overtake this configuration's actual first send.
            ready.wait()
        while active:
            collect(wait(active, return_when=FIRST_COMPLETED).done)
    return rows


class OrderedCandidate(native.CandidateServer):
    def __init__(self, first_dispatch, *args):
        self.first_dispatch = first_dispatch
        super().__init__(*args)

    def send(self, data, deadline=None):
        write = super().send
        if data.get("method") == "turn/start" and data.get("id") == 100:
            self.first_dispatch(lambda: write(data, deadline=deadline))
        else:
            write(data, deadline=deadline)


def _freeze(root, prepared, registration, original, probe, bindings):
    sources = native.source_hashes()
    expected = probe["runner_sha256"]
    _require(set(sources) == set(expected) and ENGINE in expected
             and all(digest == expected[path] for path, digest in sources.items() if path != ENGINE),
             "The native launcher or isolation helper changed after the first examination")
    _require(sources[ENGINE] != expected[ENGINE], "Verify and commit the shared single-configuration extraction first")
    old_head = original["public_head"]
    _require(isinstance(old_head, str) and re.fullmatch(r"[0-9a-f]{40}|[0-9a-f]{64}", old_head),
             "Original serial freeze lacks its exact committed controller")
    old_engine = subprocess.run(["git", "show", f"{old_head}:{ENGINE}"], cwd=ROOT,
                                check=True, capture_output=True, timeout=15).stdout
    _require(execution.sha256(old_engine) == expected[ENGINE], "Original shared controller binding changed")
    cli = probe["binary"]
    _require(native.identity(cli["path"]) == cli
             and native.runtime_installation(cli["path"])[1] == probe["local_code_mode_host"]
             and native.model_service_proxy() == probe["model_service_proxy"],
             "CLI, code-mode host or model-service route changed after native preflight")
    driver = Path(__file__).resolve()
    sources[driver.relative_to(ROOT).as_posix()] = execution.sha256(driver.read_bytes())
    public_head = native.committed(ROOT, driver)
    case_runner = flow.load_case(registration)[2]["runner"]["files"]
    for path in {*sources, *(ref["path"] for ref in case_runner)}:
        _require(native.committed(ROOT, ROOT / path) == public_head, "Public HEAD changed during parallel freeze")
    private = flow._source_tree(registration)
    private_head = native.committed(private, Path(prepared["plan_path"]))
    _require(native.committed(private, registration) == private_head, "Private HEAD changed during parallel freeze")
    freeze_path = root / "control/parallel-dispatch-freeze.json"
    execution.write_json(freeze_path, {
        "schema": execution.PARALLEL_DISPATCH_SCHEMA, **bindings,
        "source_plan_sha256": prepared["plan_sha256"], "workers": WORKERS, "remaining_priority": list(PRIORITY),
        "public_head": public_head, "private_head": private_head, "runner_sha256": sources,
        "preflight_scope": "retained native capability proof; verifies neither this scheduler nor its dispatches",
        "binary": cli, "local_code_mode_host": probe["local_code_mode_host"], "model_service_proxy": probe["model_service_proxy"],
        "budgets": execution.BUDGETS, "candidate_dispatches_before_this_freeze": 0, "frozen_at": execution.utc(),
    })
    return execution.descriptor(root, freeze_path)


def run_parallel(run_root, authorization_sha256):
    if sys.platform != "darwin":
        raise ValueError("Native continuation requires macOS Seatbelt")
    import fcntl

    root = flow._safe_absolute(run_root)
    with (root / "control/run.lock").open("a+b") as lock:
        fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        root, prepared, plan, registration, original, probe, first, bindings = check_continuation(root, authorization_sha256)
        freeze = _freeze(root, prepared, registration, original, probe, bindings)
        by_id = {row["id"]: row for row in plan["cohort"]}
        admission = Admissions(first["native_context_id"])

        def run_one(model, dispatch):
            def factory(row, control, work):
                return OrderedCandidate(dispatch, root, prepared, registration, probe["binary"], row, control, work)
            return execution.execute_one(root, prepared, plan, registration, model, factory,
                register_thread=admission.register_thread, preflight_ref=bindings["preflight"], parallel_dispatch=freeze)

        rows = run_scheduled((by_id[model_id] for model_id in PRIORITY), run_one, admission)
        initial = {"model_id": FIRST, "outcome": first["outcome"], "execution": bindings["first_execution"]}
        return execution.write_batch_summary(root, prepared, plan, [initial, *rows])


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("check", "execute"), help="Read-only gate check, or explicitly send model turns")
    parser.add_argument("--run-root", required=True)
    parser.add_argument("--authorization-sha256", required=True)
    args = parser.parse_args(argv)
    try:
        if args.mode == "check":
            bundle = check_continuation(args.run_root, args.authorization_sha256)
            print(json.dumps({"status": "ready-for-dispatch-freeze", "first_execution": bundle[-1]["first_execution"],
                              "remaining_priority": PRIORITY, "workers": WORKERS, "new_dispatches": 0}))
            return 0
        result = run_parallel(args.run_root, args.authorization_sha256)
        outcomes = {row["model_id"]: row["outcome"] for row in result["cohort"]}
        print(json.dumps({"summary": str(Path(args.run_root) / "batch-summary.json"), "outcomes": outcomes}))
        return 0 if all(status == "normal-finals" for status in outcomes.values()) else 1
    except (OSError, ValueError, RuntimeError, KeyError, TypeError, subprocess.SubprocessError) as error:
        print(f"parallel independent-research: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
