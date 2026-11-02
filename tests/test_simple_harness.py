"""Portable answer returns use synthetic bytes only, with no candidate/Lean calls."""

import copy
import contextlib
import io
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
import zipfile

from benchmark_fixtures import legacy_suite, legacy_profile, legacy_root

from math_gauge.benchmarks import BenchmarkProfile, build_plan, identity
from math_gauge.catalog import Suite, candidate_message, digest_bytes, read_json, write_json
from math_gauge.cli import main
from math_gauge.harness import (
    SIMPLE_DATASET_SCHEMA, export_simple_release_dataset, freeze_release_runtime,
    inspect_release_dataset, inspect_release_run, release_candidate_request, make_release_anchor,
)
from math_gauge.harness_answers import (
    inspect_answer_collection, issue_answer_request, record_answer_attempt,
    skip_answer_slot, pack_answer_archive,
)
from math_gauge.harness_import import import_answer_archive
from math_gauge.reliability import inspect_reliability_run

ROOT = Path(__file__).resolve().parents[1]
RUNTIME = {"model_label": "synthetic-simple-fixture", "adapter_identity": {"kind": "fixture"},
           "candidate_parameters": {"model": "synthetic-no-model-calls"},
           "budget": {"timeout_seconds": 2, "output_tokens": 1234}, "fresh_context": True}


class SimpleHarnessTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.suite = legacy_suite()
        cls.plan = build_plan(legacy_profile(cls.suite),
                              cls.suite, ["all"])
        cls.shared_temp = tempfile.TemporaryDirectory()
        cls.addClassCleanup(cls.shared_temp.cleanup)
        cls.shared = Path(cls.shared_temp.name).resolve() / "dataset"
        cls.manifest = export_simple_release_dataset(cls.plan, cls.suite, cls.shared,
            release_version="0.2.0", readme=b"# Standalone fixture guide\n",
            extra_files={"LICENSE": (ROOT / "LICENSE").read_bytes(),
                         "THIRD_PARTY_NOTICES.md": b"Synthetic fixture notice\n"})
        cls.anchor = make_release_anchor(cls.plan, cls.manifest)

    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.dataset = self.root / "download"
        shutil.copytree(self.shared, self.dataset)
        self.run = self.root / "run"
        self.responses = self.root / "responses"
        self.archive = self.root / "answers.zip"
        self.output = self.root / "imported"
        self.request_number = 0

    def freeze(self, targets=("chapters",), runtime=None):
        return freeze_release_runtime(self.dataset, runtime or RUNTIME, self.run, targets=list(targets))

    def issue(self, sid, **kwargs):
        self.request_number += 1
        out = self.root / f"request-{self.request_number}.json"
        value = issue_answer_request(self.run, self.responses, sid, out, **kwargs)
        return out, value

    def record(self, sid, request, raw=b"Synthetic answer\r\n", *, status="ok", usage=None, metadata=None,
               recovery_policy=None):
        response = self.root / "current-response.bin"
        response.write_bytes(raw)
        usage_path = self.root / "current-usage.json" if usage is not None else None
        if usage_path:
            write_json(usage_path, usage)
        metadata_path = self.root / "current-metadata.json" if metadata is not None else None
        if metadata_path:
            write_json(metadata_path, metadata)
        return record_answer_attempt(self.run, self.responses, sid, request, response, status=status,
                                     usage_path=usage_path, metadata_path=metadata_path,
                                     recovery_policy=recovery_policy)

    def packed(self, **kwargs):
        return pack_answer_archive(self.run, self.responses, self.archive, **kwargs)

    def archive_contents(self):
        with zipfile.ZipFile(self.archive) as archive:
            return {info.filename: archive.read(info) for info in archive.infolist()}

    def rewrite_archive(self, contents, output):
        with zipfile.ZipFile(output, "w") as archive:
            for name, raw in contents.items():
                archive.writestr(name, raw)

    def test_compact_projection_has_one_guide_and_exact_complete_canonical_inputs(self):
        self.assertEqual(self.manifest["schema"], SIMPLE_DATASET_SCHEMA)
        self.assertEqual(self.manifest["release_version"], self.manifest["suite"]["version"])
        self.assertEqual(self.manifest["planned"]["all_slots"], 177)
        self.assertEqual(len(self.manifest["cases"]), 43)
        self.assertEqual({p.name for p in self.dataset.iterdir()},
                         {"README.md", "manifest.json", "cases", "tools", "LICENSE", "THIRD_PARTY_NOTICES.md"})
        self.assertFalse(any(p.name in {"request.json", "candidate-message.md", "instruction.txt", "CONTROLLER.md",
                                      "plan.json", "reference.md", "rubric.json", "case.json"}
                             for p in self.dataset.rglob("*")))
        self.freeze()
        for row in self.manifest["cases"]:
            original = self.suite.request(self.suite.cases[row["case_id"]])
            self.assertEqual((self.dataset / row["task_path"]).read_bytes(), original["task"].encode())
            self.assertEqual(row["instruction"], original["instruction"])
            for descriptor, item in zip(row["files"], original["files"]):
                self.assertEqual((self.dataset / descriptor["path"]).read_bytes(), item["content"].encode())
        for sid in inspect_release_run(self.run)["selected_slot_ids"]:
            request = release_candidate_request(self.run, sid)
            self.assertEqual(request["messages"], [{"role": "user", "content": candidate_message(
                self.suite.request(self.suite.cases[sid.split(":")[0]]))}])
        inspect_release_dataset(self.dataset, plan=self.plan, suite=self.suite)
        with self.assertRaisesRegex(ValueError, "versions must match"):
            export_simple_release_dataset(self.plan, self.suite, self.root / "wrong", release_version="0.1.0",
                readme=b"guide", extra_files={"LICENSE": b"x", "THIRD_PARTY_NOTICES.md": b"y"})

    def test_relocated_stdlib_helper_and_trusted_single_archive_cli_import(self):
        helper = self.dataset / "tools/benchmark.py"
        runtime = self.root / "runtime.json"
        write_json(runtime, RUNTIME)
        command = [sys.executable, "-I", str(helper)]
        for arguments in (["check"], ["prepare", "--runtime", str(runtime), "--target", "chapters", "--out", str(self.run)]):
            result = subprocess.run(command + arguments, cwd=self.root, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stderr)
        shutil.rmtree(self.dataset)
        helper = self.run / "tools/benchmark.py"
        sid = inspect_release_run(self.run)["selected_slot_ids"][0]
        request = self.root / "issued.json"
        result = subprocess.run([sys.executable, "-I", str(helper), "request", "--run", str(self.run),
            "--responses", str(self.responses), "--slot", sid, "--out", str(request)],
            cwd=self.root, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.record(sid, request, "Synthetic 原始答卷\r\n".encode(), status="timeout",
                    metadata={"provider": "synthetic-declared-only"})
        self.packed()
        plan_path = self.root / "trusted-plan.json"
        write_json(plan_path, self.anchor)
        with patch("subprocess.Popen", side_effect=AssertionError("Importer executed downloaded code")), \
                patch("math_gauge.execution.invoke_conversation", side_effect=AssertionError("Candidate called")), \
                contextlib.redirect_stdout(io.StringIO()) as output:
            result = main(["benchmark-import", "--input", str(self.archive), "--plan", str(plan_path),
                           "--suite", str(legacy_suite().root), "--out", str(self.output)])
        self.assertEqual(result, 0, output.getvalue())
        self.assertEqual((self.output / "external-import/answers.zip").read_bytes(), self.archive.read_bytes())
        meta, records = inspect_reliability_run(self.output)
        self.assertTrue(meta["fixture_only"])
        self.assertFalse(meta["model_identity_verified"])
        self.assertEqual(meta["candidate_calls"], 0)
        self.assertEqual(meta["external_candidate_calls_declared"], 0)
        self.assertEqual(records[sid]["status"], "responded")
        self.assertEqual((self.output / records[sid]["response_path"]).read_bytes(), "Synthetic 原始答卷\r\n".encode())
        self.assertEqual(len(meta["unrun_slots"]), 5)

    def test_omitted_output_cap_roundtrips_through_portable_helper_without_inventing_a_limit(self):
        runtime = copy.deepcopy(RUNTIME)
        runtime["budget"].pop("output_tokens")
        runtime["adapter_identity"]["output_limit"] = "platform-default; maximum unknown"
        runtime["candidate_parameters"]["reasoning_effort"] = "max"
        runtime_path = self.root / "platform-default-runtime.json"
        write_json(runtime_path, runtime)
        helper = self.dataset / "tools/benchmark.py"

        def portable(*arguments):
            result = subprocess.run([sys.executable, "-I", "-S", "-B", str(helper), *map(str, arguments)],
                                    cwd=self.root, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            return json.loads(result.stdout)

        portable("prepare", "--runtime", runtime_path, "--target", "chapters", "--out", self.run)
        frozen = inspect_release_run(self.run)
        self.assertEqual(frozen["runtime"], runtime)
        self.assertNotIn("output_tokens", frozen["execution"]["budget"])
        self.assertNotIn("max_output_tokens", frozen["execution"]["parameters"])
        sid = frozen["selected_slot_ids"][0]
        request = self.root / "platform-default-request.json"
        portable("request", "--run", self.run, "--responses", self.responses, "--slot", sid, "--out", request)
        projected = read_json(request)
        self.assertEqual(projected["parameters"], runtime["candidate_parameters"])
        raw = "Synthetic fixture with unknown platform output limit。\r\n".encode()
        response = self.root / "platform-default-response.md"
        response.write_bytes(raw)
        portable("record", "--run", self.run, "--responses", self.responses, "--slot", sid,
                 "--request", request, "--response", response, "--status", "ok")
        portable("pack", "--run", self.run, "--responses", self.responses, "--out", self.archive)
        meta = import_answer_archive(self.archive, self.anchor, self.suite, self.output)
        checked, records = inspect_reliability_run(self.output)
        self.assertEqual(checked["plan"]["runtime"], runtime)
        self.assertNotIn("output_tokens", checked["execution_contract"]["budget"])
        self.assertNotIn("max_output_tokens", checked["execution_contract"]["parameters"])
        self.assertEqual((self.output / records[sid]["response_path"]).read_bytes(), raw)
        self.assertEqual(meta["candidate_calls"], 0)
        self.assertTrue(meta["fixture_only"])

    def test_provided_output_cap_remains_exact_and_malformed_caps_are_rejected(self):
        frozen = self.freeze()
        self.assertEqual(frozen["execution"]["budget"]["output_tokens"], 1234)
        self.assertEqual(frozen["execution"]["parameters"]["max_output_tokens"], 1234)
        for number, cap in enumerate((None, 0, -1, True, 1234.0, "1234")):
            with self.subTest(cap=cap):
                runtime = copy.deepcopy(RUNTIME)
                runtime["budget"]["output_tokens"] = cap
                destination = self.root / f"malformed-cap-{number}"
                with self.assertRaisesRegex(ValueError, "positive integer"):
                    freeze_release_runtime(self.dataset, runtime, destination)
                self.assertFalse(destination.exists())
        runtime = copy.deepcopy(RUNTIME)
        runtime["candidate_parameters"]["max_output_tokens"] = 1235
        with self.assertRaisesRegex(ValueError, "contradict"):
            freeze_release_runtime(self.dataset, runtime, self.root / "contradictory-cap")

    def test_complete_small_target_retains_retry_failure_usage_and_fixed_denominators(self):
        run = self.freeze()
        for number, sid in enumerate(run["selected_slot_ids"]):
            request, initial = self.issue(sid)
            if number == 0:
                self.record(sid, request, b"\xff\r\n", status="transient_error")
                retry, projected = self.issue(sid)
                self.assertEqual(initial, projected)
                request = retry
            self.record(sid, request, f"Synthetic independent {number}\r\n".encode(), usage={"total_tokens": 3})
        state = inspect_answer_collection(self.run, self.responses)
        self.assertEqual({s["state"] for s in state["slots"]}, {"responded"})
        self.assertEqual(state["budget"]["transport_attempts"], 7)
        self.assertIsNone(state["budget"]["total_tokens"])
        self.packed()
        meta = import_answer_archive(self.archive, self.anchor, self.suite, self.output)
        checked, records = inspect_reliability_run(self.output)
        self.assertEqual(meta["unrun_slots"], [])
        self.assertEqual(checked["plan"]["planned"]["all_slots"], 177)
        self.assertEqual(len(records), 6)
        first = records[run["selected_slot_ids"][0]]
        self.assertEqual([a["status"] for a in first["attempts"]], ["transient_error", "ok"])
        self.assertEqual((self.output / first["attempts"][0]["response_path"]).read_bytes(), b"\xff\r\n")

    def test_followup_history_comes_from_exact_recorded_branch_and_missing_parents_remain_blocked(self):
        run = self.freeze(targets=("neutral", "stance"))
        target = "MG-GR002"
        delivered = {target + ":A1": b"Synthetic initial\r\n", target + ":neutral:1": b"KEEP\r\nsynthetic rationale\r\n",
                     target + ":neutral:2": b"FULL\r\nSynthetic full\r\n"}
        for sid in run["selected_slot_ids"]:
            if sid in delivered:
                request_path, request = self.issue(sid)
                if sid.endswith(":neutral:2"):
                    self.assertEqual([m["content"] for m in request["messages"] if m["role"] == "assistant"],
                                     [delivered[target + ":A1"].decode(), delivered[target + ":neutral:1"].decode()])
                    self.assertNotIn("affirm", json.dumps(request))
                self.record(sid, request_path, delivered[sid])
            else:
                state = next(s for s in inspect_answer_collection(self.run, self.responses)["slots"] if s["slot_id"] == sid) \
                    if self.responses.exists() else None
                if state is None or state["state"] != "blocked":
                    skip_answer_slot(self.run, self.responses, sid, "Explicit synthetic omission")
        packed = self.packed()
        self.assertTrue(any(s["state"] == "blocked" for s in packed["slots"]))
        import_answer_archive(self.archive, self.anchor, self.suite, self.output)
        _, records = inspect_reliability_run(self.output)
        self.assertEqual(records[target + ":neutral:2"]["status"], "responded")
        self.assertEqual(records[target + ":affirm:2"]["status"], "blocked")
        self.assertTrue(any(row["status"] == "blocked" for row in records.values()))

    def test_recording_requires_exact_issued_request_and_first_readable_reply_locks(self):
        run = self.freeze()
        first, second = run["selected_slot_ids"][:2]
        with self.assertRaisesRegex(ValueError, "frozen"):
            self.issue(second)
        request, value = self.issue(first)
        bad = self.root / "changed-request.json"
        write_json(bad, dict(value, parameters={"model": "different"}))
        with self.assertRaisesRegex(ValueError, "exact issued request"):
            self.record(first, bad)
        self.record(first, request, b"Readable even on timeout\r\n", status="timeout")
        with self.assertRaisesRegex(ValueError, "cannot be overwritten"):
            self.record(first, request, b"Replacement")
        with self.assertRaisesRegex(ValueError, "frozen"):
            self.issue(first)
        with self.assertRaisesRegex(ValueError, "frozen"):
            skip_answer_slot(self.run, self.responses, first, "Cannot discard a readable reply")
        original = next(self.responses.rglob("response.md"))
        self.assertEqual(original.read_bytes(), b"Readable even on timeout\r\n")

    def test_unknown_usage_stops_total_budget_and_external_call_counts_are_explicit(self):
        runtime = copy.deepcopy(RUNTIME)
        runtime["budget"]["max_total_tokens"] = 100
        run = self.freeze(runtime=runtime)
        first, second = run["selected_slot_ids"][:2]
        request, _ = self.issue(first)
        self.record(first, request)
        state = inspect_answer_collection(self.run, self.responses)
        self.assertEqual(state["budget"]["stop_reason"], "usage_unavailable_for_total_token_budget")
        with self.assertRaisesRegex(ValueError, "budget"):
            self.issue(second)
        with self.assertRaisesRegex(ValueError, "explicitly observed"):
            self.packed(origin="external")
        self.assertFalse(self.archive.exists())
        # This is a declared test value, never an actual provider claim. The
        # controller must preserve it, rather than infer it from attempt count.
        packed = self.packed(origin="external", declared_external_calls=0)
        self.assertEqual(packed["declared_external_calls"], 0)
        self.assertFalse(packed["fixture_only"])
        meta = import_answer_archive(self.archive, self.anchor, self.suite, self.output)
        self.assertEqual(meta["external_candidate_calls_declared"], 0)
        self.assertFalse(meta["external_origin_verified"])
        self.assertFalse(meta["token_usage_complete"])

    def test_explicit_network_recovery_preserves_unknown_and_roundtrips_retry(self):
        runtime = copy.deepcopy(RUNTIME)
        runtime["budget"].update(max_total_tokens=100, max_transport_attempts=10)
        run = self.freeze(runtime=runtime)
        first, second = run["selected_slot_ids"][:2]
        request, original = self.issue(first)
        original_metadata = {"status": "permanent_error", "error": "Synthetic network interruption",
                             "reclassification": "transient_error; original classification retained"}
        self.record(first, request, b"", status="transient_error", usage={}, metadata=original_metadata)
        metadata = self.responses / "slots" / first.replace(":", "/") / "attempts/1/metadata.json"
        policy = {"schema": "math-gauge.local-transport-recovery/v1", "run_sha256": run["run_sha256"],
                  "unknown_usage": "retain-unknown-use-known-lower-bound",
                  "frozen_runner_sha256": self.plan["runner_sha256"], "installed_runner_sha256": "b" * 64,
                  "attempts": [{"slot_id": first, "number": 1, "response_sha256": digest_bytes(b""),
                                "metadata_sha256": digest_bytes(metadata.read_bytes())}]}
        self.assertTrue(inspect_answer_collection(self.run, self.responses)["budget"]["stopped"])
        wrong = copy.deepcopy(policy)
        wrong["attempts"][0]["metadata_sha256"] = "a" * 64
        self.assertTrue(inspect_answer_collection(self.run, self.responses,
                                                recovery_policy=wrong)["budget"]["stopped"])
        state = inspect_answer_collection(self.run, self.responses, recovery_policy=policy)
        self.assertFalse(state["budget"]["stopped"])
        self.assertIsNone(state["budget"]["total_tokens"])
        retry, projected = self.issue(first, recovery_policy=policy)
        self.assertEqual(projected, original)
        self.record(first, retry, b"Synthetic successful retry\r\n", usage={"total_tokens": 7}, recovery_policy=policy)
        request, _ = self.issue(second, recovery_policy=policy)
        self.record(second, request, usage={"total_tokens": 5}, recovery_policy=policy)
        self.packed(recovery_policy=policy)
        with self.assertRaisesRegex(ValueError, "budget stopped"):
            import_answer_archive(self.archive, self.anchor, self.suite, self.output)
        with patch("math_gauge.harness_import.runner_fingerprint", return_value="c" * 64):
            with self.assertRaisesRegex(ValueError, "Runner source changed"):
                import_answer_archive(self.archive, self.anchor, self.suite, self.output, recovery_policy=policy)
        with patch("math_gauge.harness_import.runner_fingerprint", return_value="b" * 64):
            meta = import_answer_archive(self.archive, self.anchor, self.suite, self.output, recovery_policy=policy)
        checked, records = inspect_reliability_run(self.output)
        self.assertFalse(meta["token_usage_complete"])
        self.assertIsNone(meta["total_tokens"])
        self.assertEqual(meta["known_total_tokens"], 12)
        self.assertEqual(meta["local_transport_recovery"], policy)
        self.assertEqual(records[first]["locked_attempt"], 2)
        self.assertEqual(records[first]["attempts"][0]["usage"], {})
        self.assertEqual(checked["plan"]["planned"]["all_slots"], 177)
        self.assertEqual(json.loads(metadata.read_bytes()), original_metadata)

    def test_explicit_network_recovery_does_not_waive_transport_limit(self):
        runtime = copy.deepcopy(RUNTIME)
        runtime["budget"].update(max_total_tokens=100, max_transport_attempts=1)
        run = self.freeze(runtime=runtime)
        first = run["selected_slot_ids"][0]
        request, _ = self.issue(first)
        self.record(first, request, b"", status="transient_error", usage={}, metadata={"fixture": True})
        metadata = self.responses / "slots" / first.replace(":", "/") / "attempts/1/metadata.json"
        policy = {"schema": "math-gauge.local-transport-recovery/v1", "run_sha256": run["run_sha256"],
                  "unknown_usage": "retain-unknown-use-known-lower-bound",
                  "frozen_runner_sha256": self.plan["runner_sha256"], "installed_runner_sha256": self.plan["runner_sha256"],
                  "attempts": [{"slot_id": first, "number": 1, "response_sha256": digest_bytes(b""),
                                "metadata_sha256": digest_bytes(metadata.read_bytes())}]}
        state = inspect_answer_collection(self.run, self.responses, recovery_policy=policy)
        self.assertEqual(state["budget"]["stop_reason"], "cumulative_budget_exhausted")
        with self.assertRaisesRegex(ValueError, "budget"):
            self.issue(first, recovery_policy=policy)

    def test_archive_rejects_unknown_paths_aliases_symlinks_and_oversized_files(self):
        self.freeze()
        self.packed()
        original = self.archive_contents()
        for number, name in enumerate(("../escape", "/absolute", "run/../escape", "run\\escape", "run./escape",
                                       "RUN/extra", "run/CON.txt", "extra.txt")):
            with self.subTest(name=name):
                contents = dict(original, **{name: b"unlisted"})
                archive = self.root / f"bad-path-{number}.zip"
                self.rewrite_archive(contents, archive)
                with self.assertRaises(ValueError):
                    import_answer_archive(archive, self.anchor, self.suite, self.output)
                self.assertFalse(self.output.exists())
        symbolic = self.root / "symlink.zip"
        with zipfile.ZipFile(symbolic, "w") as archive:
            for name, raw in original.items():
                archive.writestr(name, raw)
            info = zipfile.ZipInfo("run/link")
            info.create_system, info.external_attr = 3, 0o120777 << 16
            archive.writestr(info, b"/tmp")
        with self.assertRaisesRegex(ValueError, "regular files"):
            import_answer_archive(symbolic, self.anchor, self.suite, self.output)
        with patch("math_gauge.harness_import.MAX_ANSWERS_FILE_BYTES", 32):
            with self.assertRaisesRegex(ValueError, "size limit"):
                import_answer_archive(self.archive, self.anchor, self.suite, self.output)

    def test_archive_binds_version_dataset_inventory_and_recorded_original_bytes(self):
        run = self.freeze()
        sid = run["selected_slot_ids"][0]
        request, _ = self.issue(sid)
        self.record(sid, request)
        self.packed()
        original = self.archive_contents()
        for key, replacement in (("release_version", "0.1.0"), ("dataset_sha256", "0" * 64),
                                 ("run_sha256", "1" * 64), ("base_plan_sha256", "2" * 64)):
            with self.subTest(key=key):
                contents = dict(original)
                envelope = json.loads(contents["answers.json"])
                envelope[key] = replacement
                contents["answers.json"] = json.dumps(envelope).encode()
                archive = self.root / (key + ".zip")
                self.rewrite_archive(contents, archive)
                with self.assertRaisesRegex(ValueError, "different version|trusted dataset"):
                    import_answer_archive(archive, self.anchor, self.suite, self.output)
                self.assertFalse(self.output.exists())
        contents = dict(original)
        response_name = next(name for name in contents if name.startswith("submission/") and name.endswith("response.md"))
        contents[response_name] = b"Changed original"
        envelope = json.loads(contents["answers.json"])
        envelope["files"][response_name] = {"bytes": len(contents[response_name]), "sha256": digest_bytes(contents[response_name])}
        contents["answers.json"] = json.dumps(envelope).encode()
        archive = self.root / "changed-original.zip"
        self.rewrite_archive(contents, archive)
        with self.assertRaisesRegex(ValueError, "original file changed"):
            import_answer_archive(archive, self.anchor, self.suite, self.output)
        self.assertFalse(self.output.exists())

    def test_self_rehashed_helper_and_provenance_cannot_replace_the_trusted_dataset(self):
        changed = read_json(self.dataset / "manifest.json")
        helper = self.dataset / "tools/benchmark.py"
        helper.write_bytes(b"raise RuntimeError('untrusted code must never execute')\n")
        changed["release_provenance"] = {"kind": "self-rehashed-untrusted-declaration"}
        changed["files_sha256"]["tools/benchmark.py"] = digest_bytes(helper.read_bytes())
        changed.pop("dataset_sha256")
        changed["dataset_sha256"] = identity(changed)
        write_json(self.dataset / "manifest.json", changed)
        # The altered package is internally consistent and its mathematical
        # projection still matches the original base plan. That is insufficient.
        inspect_release_dataset(self.dataset, plan=self.plan, suite=self.suite)
        self.freeze()
        self.packed()
        with patch("subprocess.Popen", side_effect=AssertionError("Downloaded helper executed")):
            with self.assertRaisesRegex(ValueError, "trusted dataset identity"):
                import_answer_archive(self.archive, self.anchor, self.suite, self.output)
            with self.assertRaisesRegex(ValueError, "anchor"):
                import_answer_archive(self.archive, self.plan, self.suite, self.output)
        self.assertFalse(self.output.exists())


if __name__ == "__main__":
    unittest.main()
