"""Portable candidate/controller boundaries; offline fixtures only."""

import copy
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from math_gauge.benchmarks import BenchmarkProfile, build_plan, identity, validate_plan
from math_gauge.catalog import Suite, candidate_message, digest_bytes, read_json, write_json
from math_gauge.harness import (candidate_request_from_bundle, export_harness_bundle,
                                inspect_harness_bundle)

ROOT = Path(__file__).resolve().parents[1]


class HarnessExportTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.suite = Suite.load(ROOT / "cases")
        cls.profile = BenchmarkProfile.load(ROOT / "protocol/benchmark-profile.json", cls.suite)

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()

    def plan(self, targets=None, *, preparation=False, **runtime):
        settings = {"model_label": "offline-fixture", "adapter_identity": "export-test-v1",
                    "budget": {"timeout_seconds": 3, "output_tokens": 1234},
                    "candidate_parameters": {"model": "declared-model", "temperature": 0},
                    "system_prompt": "Frozen system text.\r\n"}
        settings.update(runtime)
        return build_plan(self.profile, self.suite, targets, runtime=None if preparation else settings)

    def export(self, plan=None, *, name="bundle", targets=None):
        plan = self.plan() if plan is None else plan
        destination = self.root / name
        manifest = export_harness_bundle(plan, self.suite, destination, targets=targets)
        return destination, manifest

    def rehash(self, root, manifest, *, update_files=False):
        if update_files:
            manifest["files_sha256"] = {
                name: digest_bytes((root / name).read_bytes()) for name in manifest["files_sha256"]}
        manifest["bundle_sha256"] = identity({k: v for k, v in manifest.items() if k != "bundle_sha256"})
        write_json(root / "manifest.json", manifest)

    def controller(self, root, *arguments):
        return subprocess.run([sys.executable, "-I", str(root / "controller.py"), *arguments],
                              cwd=self.root, capture_output=True, check=False)

    def test_full_bundle_exact_inventory_and_evaluator_sidecar(self):
        plan = self.plan()
        with patch("math_gauge.execution.invoke_conversation", side_effect=AssertionError("No model calls")):
            root, manifest = self.export(plan)
            checked = inspect_harness_bundle(root, plan=plan, suite=self.suite)
        self.assertEqual(checked, manifest)
        self.assertEqual(manifest["exported_slots"], 177)
        self.assertEqual(len(manifest["cases"]), 43)
        self.assertEqual(len(manifest["prompts"]), 48)
        self.assertEqual(manifest["planned"], plan["planned"])
        self.assertFalse(manifest["preparation_only"])
        self.assertEqual(set(manifest["files_sha256"]) | {"manifest.json"},
                         {p.relative_to(root).as_posix() for p in root.rglob("*") if p.is_file()})
        evaluator = Path(str(root) + ".evaluator")
        self.assertEqual(read_json(evaluator / "plan.json"), plan)
        receipt = read_json(evaluator / "receipt.json")
        self.assertEqual(receipt["bundle_sha256"], manifest["bundle_sha256"])
        self.assertEqual(receipt["candidate_calls"], 0)
        self.assertFalse(any("evaluator" in p.parts or p.name in {"plan.json", "reference.md", "rubric.json"}
                             for p in root.rglob("*")))
        template = read_json(root / "submission-template.json")
        self.assertIsNone(template["bundle_sha256"])
        self.assertEqual(template["slots"], [])
        self.assertTrue(template["fixture_only"])

    def test_partial_projection_keeps_full_denominator_and_dependency_closure(self):
        plan = self.plan()
        root, manifest = self.export(plan, targets=["neutral"])
        self.assertEqual(manifest["targets"], ["neutral"])
        self.assertEqual(manifest["exported_slots"], 24)
        self.assertEqual(manifest["planned"]["all_slots"], 177)
        self.assertEqual(manifest["planned"]["selected_slots"], 177)
        self.assertEqual(len(manifest["cases"]), 8)
        self.assertEqual(len(manifest["prompts"]), 16)
        earlier = set()
        for slot in manifest["slots"]:
            self.assertIn(slot["kind"], {"independent", "followup"})
            if slot["kind"] == "independent":
                self.assertEqual(slot["attempt_label"], "A1")
            else:
                self.assertEqual(slot["arm"], "neutral")
                self.assertIn(slot["parent_slot"], earlier)
            earlier.add(slot["slot_id"])
        inspect_harness_bundle(root, plan=plan)
        narrowed = self.plan(["neutral"])
        with self.assertRaisesRegex(ValueError, "exceed"):
            self.export(narrowed, name="widened", targets=["stance"])
        self.assertFalse((self.root / "widened").exists())

    def test_chapter_attachment_bytes_and_intentionally_supplied_lean_are_unchanged(self):
        root, manifest = self.export()
        for cid in ("MG-C002", "MG-GF101"):
            source = self.suite.request(self.suite.cases[cid])
            case = next(c for c in manifest["cases"] if c["case_id"] == cid)
            self.assertEqual((root / case["candidate_message_path"]).read_bytes(),
                             candidate_message(source).encode("utf-8"))
            for attachment, descriptor in zip(source["files"], case["files"]):
                self.assertEqual((root / descriptor["path"]).read_bytes(), attachment["content"].encode("utf-8"))
        chapter = self.suite.request(self.suite.cases["MG-C002"])
        source_chapter = next(x for x in chapter["files"] if x["name"] == "source/02-operator-bounds.md")
        self.assertIn("**证明**", source_chapter["content"])
        request = candidate_request_from_bundle(root, "MG-C002:A1")
        self.assertIn(source_chapter["content"], request["messages"][-1]["content"])
        self.assertEqual(len(chapter["files"]), 8)

    def test_recursive_projection_drops_evaluator_metadata_and_operator_paths(self):
        secret = "PRIVATE-EVALUATOR-SENTINEL-74932"
        plan = self.plan(adapter_identity={"path": "/private/operator/config", "metadata": {"expected_truth": secret}},
                         operator={"review": {"answer": secret}},
                         budget={"timeout_seconds": 3, "output_tokens": 1234,
                                 "metadata": {"selection_rationale": secret}})
        plan["profile"]["data"]["private_metadata"] = {"rubric": secret}
        plan["profile"]["data_sha256"] = identity(plan["profile"]["data"])
        plan["case_index"][0]["review"] = {"reference": secret}
        plan["slots"][0]["selection_rationale"] = secret
        plan["reliability"]["selection"]["cases"][0]["private_rationale"] = secret
        plan["plan_sha256"] = identity({k: v for k, v in plan.items() if k != "plan_sha256"})
        validate_plan(plan)
        root, manifest = self.export(plan)
        for path in root.rglob("*"):
            if path.is_file():
                raw = path.read_bytes()
                self.assertNotIn(secret.encode(), raw, str(path))
                self.assertNotIn(b"/private/operator/config", raw, str(path))
        self.assertIn(secret, json.dumps(read_json(Path(str(root) + ".evaluator") / "plan.json")))
        self.assertNotIn("profile", manifest)
        self.assertNotIn("review", manifest["cases"][0])

    def test_nested_generation_values_cannot_smuggle_metadata(self):
        plan = self.plan(candidate_parameters={"model": {"expected_truth": "secret"}})
        with self.assertRaisesRegex(ValueError, "scalar"):
            self.export(plan)
        self.assertFalse((self.root / "bundle").exists())

    def test_preparation_without_runtime_is_explicit_and_never_a_trial(self):
        plan = self.plan(preparation=True)
        root, manifest = self.export(plan, targets=["chapters"])
        self.assertTrue(manifest["preparation_only"])
        self.assertFalse(manifest["runtime_frozen"])
        self.assertEqual(manifest["execution"]["parameters"], {})
        self.assertEqual(manifest["execution"]["budget"], {})
        self.assertEqual(candidate_request_from_bundle(root, "MG-C002:A1")["parameters"], {})
        self.assertEqual(read_json(Path(str(root) + ".evaluator") / "receipt.json")["candidate_calls"], 0)

    def test_helper_and_library_build_exact_branch_history_and_case_parameters(self):
        plan = self.plan(budget={"timeout_seconds": 3, "output_tokens": 1234,
                                "case_parameters": {"MG-GF101": {"max_output_tokens": 4321, "seed": 9}}})
        root, manifest = self.export(plan, targets=["neutral"])
        cid = manifest["slots"][0]["case_id"]
        a1, first, second = f"{cid}:A1", f"{cid}:neutral:1", f"{cid}:neutral:2"
        answers = {a1: "原始答卷。\r\n```lean filename=Main.lean\r\n-- exact\r\n```\r\n",
                   first: "KEEP\r\n本轮原始理由。\r\n"}
        request = candidate_request_from_bundle(root, second, answers)
        self.assertEqual([m["role"] for m in request["messages"]],
                         ["system", "user", "assistant", "user", "assistant", "user"])
        self.assertEqual(request["messages"][2]["content"], answers[a1])
        self.assertEqual(request["messages"][4]["content"], answers[first])
        self.assertEqual(request["parameters"], {"model": "declared-model", "temperature": 0,
                                                "max_output_tokens": 4321, "seed": 9})
        answer_file = self.root / "answers.json"
        write_json(answer_file, answers)
        process = self.controller(root, "request", "--slot", second, "--answers", str(answer_file))
        self.assertEqual(process.returncode, 0, process.stderr)
        self.assertEqual(json.loads(process.stdout), request)
        with self.assertRaisesRegex(ValueError, "exactly"):
            candidate_request_from_bundle(root, second, {a1: answers[a1]})
        with self.assertRaisesRegex(ValueError, "unrelated"):
            candidate_request_from_bundle(root, second, dict(answers, **{f"{cid}:deny:1": "other branch"}))
        with self.assertRaisesRegex(ValueError, "unrelated"):
            candidate_request_from_bundle(root, a1, {a1: "previous attempt"})
        with self.assertRaisesRegex(ValueError, "UTF-8"):
            candidate_request_from_bundle(root, first, {a1: b"\xff"})

    def test_controller_renderer_uses_canonical_message_with_unusual_attachments(self):
        root, _ = self.export(targets=["chapters"])
        spec = importlib.util.spec_from_file_location("portable_fixture", root / "controller.py")
        module = importlib.util.module_from_spec(spec)
        # Importing a main helper normally creates a cache file. Disable that
        # in this fixture so the immutable packet's allowlist remains intact.
        with patch.object(sys, "dont_write_bytecode", True):
            spec.loader.exec_module(module)
        for instruction in ("", "Keep all conditions.\r\n"):
            request = {"schema": "math-gauge.request/v1", "case_id": "PARITY", "case_version": "1",
                       "track": "alignment", "instruction": instruction, "task": "Task.\r\n",
                       "files": [{"name": "input.lean", "content": "-- ``` inner ````` fence\r\ndef x := 1"},
                                 {"name": "source/text.md", "content": "Proof.\r\n"}]}
            self.assertEqual(module._h_message(request), candidate_message(request))
        inspect_harness_bundle(root)

    def test_relocation_works_without_repository_or_evaluator_sidecar(self):
        plan = self.plan()
        root, manifest = self.export(plan, targets=["chapters"])
        moved = self.root / "remote-host" / "packet"
        moved.parent.mkdir()
        shutil.move(root, moved)
        shutil.rmtree(Path(str(root) + ".evaluator"))
        with patch("math_gauge.harness.Suite.load", side_effect=AssertionError("No source repository")):
            self.assertEqual(inspect_harness_bundle(moved, plan=plan), manifest)
            request = candidate_request_from_bundle(moved, "MG-C002:A1")
        process = self.controller(moved, "check", "--bundle", str(moved))
        self.assertEqual(process.returncode, 0, process.stderr)
        self.assertEqual(json.loads(process.stdout)["bundle_sha256"], manifest["bundle_sha256"])
        process = self.controller(moved, "request", "--bundle", str(moved), "--slot", "MG-C002:A1")
        self.assertEqual(process.returncode, 0, process.stderr)
        self.assertEqual(json.loads(process.stdout), request)
        self.assertNotIn(str(ROOT).encode(), (moved / "controller.py").read_bytes())

    def test_manifest_file_and_candidate_bytes_tampering_are_detected(self):
        root, manifest = self.export(targets=["chapters"])
        original = copy.deepcopy(manifest)
        manifest["preparation_only"] = True
        write_json(root / "manifest.json", manifest)
        with self.assertRaisesRegex(ValueError, "manifest changed"):
            inspect_harness_bundle(root)
        write_json(root / "manifest.json", original)
        case = original["cases"][0]
        attachment = root / case["files"][0]["path"]
        attachment.write_bytes(attachment.read_bytes() + b" edited")
        with self.assertRaisesRegex(ValueError, "attachment bytes"):
            inspect_harness_bundle(root)

    def test_rehashed_extra_metadata_and_wrong_plan_are_rejected(self):
        plan = self.plan()
        root, original = self.export(plan, targets=["neutral"])
        for mutate in (
            lambda m: m.update({"profile": {"expected_truth": "secret"}}),
            lambda m: m["execution"].update({"metadata": {"reference": "secret"}}),
            lambda m: m["slots"][0].update({"review": {"rubric": "secret"}}),
            lambda m: m["cases"][0].update({"expected_truth": "false"}),
        ):
            value = copy.deepcopy(original)
            mutate(value)
            self.rehash(root, value)
            with self.assertRaisesRegex(ValueError, "Unexpected fields"):
                inspect_harness_bundle(root)
        self.rehash(root, original)
        another = self.plan()
        with self.assertRaisesRegex(ValueError, "different frozen plan"):
            inspect_harness_bundle(root, plan=another)

    def test_rehashed_frozen_prompt_change_is_bound_to_the_plan(self):
        plan = self.plan()
        root, manifest = self.export(plan, targets=["neutral"])
        manifest["prompts"][0]["content"] += " evaluator feedback"
        manifest["prompts"][0]["content_sha256"] = digest_bytes(manifest["prompts"][0]["content"].encode())
        self.rehash(root, manifest)
        # Self-consistent hashes do not establish authority; evaluator binding
        # supplies the independent original plan identity.
        inspect_harness_bundle(root)
        with self.assertRaisesRegex(ValueError, "prompts differ"):
            inspect_harness_bundle(root, plan=plan)

    def test_unlisted_files_empty_directories_and_symlinks_are_rejected(self):
        root, manifest = self.export(targets=["chapters"])
        extra = root / "private-review.json"
        extra.write_text("secret", encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "Unlisted"):
            inspect_harness_bundle(root)
        extra.unlink()
        (root / "unlisted-empty").mkdir()
        with self.assertRaisesRegex(ValueError, "Unlisted"):
            inspect_harness_bundle(root)
        (root / "unlisted-empty").rmdir()
        path = root / manifest["cases"][0]["files"][0]["path"]
        saved = self.root / "original-bytes"
        saved.write_bytes(path.read_bytes())
        path.unlink()
        path.symlink_to(saved)
        with self.assertRaisesRegex(ValueError, "Symlink|symlink"):
            inspect_harness_bundle(root)

    def test_unsafe_output_paths_fail_before_any_bundle_is_created(self):
        plan = self.plan()
        existing = self.root / "existing"
        existing.mkdir()
        link = self.root / "link"
        link.symlink_to(self.root, target_is_directory=True)
        pairs = [(existing, None), (self.root / "one", existing),
                 (self.root / "two", self.root / "two" / "evaluator"),
                 (self.root / "three" / "candidate", self.root / "three"),
                 (self.root / "same", self.root / "same"),
                 (self.suite.root / "bad-harness", self.root / "suite-sidecar"),
                 (link / "escaped", self.root / "sidecar")]
        for destination, evaluator in pairs:
            with self.subTest(destination=destination), self.assertRaises(ValueError):
                export_harness_bundle(plan, self.suite, destination, evaluator_destination=evaluator)
        self.assertEqual(list(existing.iterdir()), [])
        self.assertFalse((self.root / "one").exists())
        self.assertFalse((self.root / "two").exists())
        self.assertFalse((self.root / "three").exists())
        self.assertFalse((self.suite.root / "bad-harness").exists())

    def test_safe_macos_system_aliases_and_arbitrary_root_symlinks(self):
        with tempfile.TemporaryDirectory(dir="/tmp") as temporary:
            destination = Path(temporary) / "bundle"
            manifest = export_harness_bundle(self.plan(["chapters"]), self.suite, destination)
            self.assertEqual(inspect_harness_bundle(destination)["bundle_sha256"], manifest["bundle_sha256"])
            process = self.controller(destination, "check", "--bundle", str(destination))
            self.assertEqual(process.returncode, 0, process.stderr)
        root, _ = self.export(targets=["chapters"])
        link = self.root / "root-link"
        link.symlink_to(root, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "symlink"):
            inspect_harness_bundle(link)
        nested = self.root / "parent-link"
        nested.symlink_to(self.root, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "symlink"):
            inspect_harness_bundle(nested / root.name)

    def test_traversal_manifest_and_request_output_inside_bundle_are_rejected(self):
        root, manifest = self.export(targets=["chapters"])
        original = copy.deepcopy(manifest)
        manifest["cases"][0]["files"][0]["path"] = "../outside"
        self.rehash(root, manifest)
        with self.assertRaisesRegex(ValueError, "target changed"):
            inspect_harness_bundle(root)
        self.rehash(root, original)
        process = self.controller(root, "request", "--slot", "MG-C002:A1", "--out", str(root / "generated.json"))
        self.assertNotEqual(process.returncode, 0)
        self.assertFalse((root / "generated.json").exists())
        inspect_harness_bundle(root)

    def test_new_export_rejects_runner_drift_but_old_bundle_is_inspectable(self):
        plan = self.plan()
        root, manifest = self.export(plan, targets=["chapters"])
        with patch("math_gauge.execution.runner_fingerprint", return_value="0" * 64):
            self.assertEqual(inspect_harness_bundle(root, plan=plan), manifest)
            with self.assertRaisesRegex(ValueError, "Runner source changed"):
                self.export(plan, name="stale")
        self.assertFalse((self.root / "stale").exists())


if __name__ == "__main__":
    unittest.main()
