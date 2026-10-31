"""Synthetic preparation checks; these tests never launch a model CLI."""

import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]


def module(name):
    spec = importlib.util.spec_from_file_location(
        name, ROOT / "scripts/isolated_cli" / (name + ".py")
    )
    loaded = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(loaded)
    return loaded


helper = module("prepare")
probe = module("probe")


class IsolatedCLIPreparationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.private = self.root / "private-data"
        self.private.mkdir()
        self.prompt = self.root / "task.md"
        self.prompt.write_bytes("只含题面。\r\n保留字节。\r\n".encode())
        for name in ("reference", "history", "prior_run"):
            (self.private / name).write_text("not candidate input")
        self.binary = self.root / "fake-cli"
        flags = sorted(set(sum((list(x) for x in helper.REQUIRED_FLAGS.values()), [])))
        self.binary.write_text(
            "#!" + sys.executable + "\nimport sys\n"
            "print('synthetic-cli 0' if '--version' in sys.argv else "
            + repr(" ".join(flags)) + ")\n"
        )
        self.binary.chmod(0o700)

    def config(self, client="agy", name="run"):
        inspection = self.root / (name + "-inspection")
        helper.inspect_cli(client, str(self.binary), inspection)
        return {
            "schema": "math-gauge.isolated-cli/v1", "client": client,
            "cli_identity": str(inspection / "identity.json"),
            "prompt": str(self.prompt), "run_dir": str(self.root / name),
            "model": "synthetic-model", "effort": "synthetic-effort",
            "deny_read_roots": [str(self.private)], "sandbox_exec": sys.executable,
            "probes": [
                {"category": kind, "path": str(self.private / kind)}
                for kind in ("reference", "history", "prior_run")
            ],
        }

    def test_agy_plan_preserves_bytes_and_uses_fresh_explicit_state(self):
        config = self.config()
        with mock.patch.object(helper.subprocess, "run", side_effect=AssertionError("prepare may not run a CLI")):
            plan = helper.prepare(config)
        root = Path(config["run_dir"])
        self.assertEqual((root / "input/task.md").read_bytes(), self.prompt.read_bytes())
        request = (root / "runtime/request.ndjson").read_bytes()
        self.assertEqual(len(request.splitlines()), 1)
        self.assertEqual(json.loads(request)["message"]["content"].encode(), self.prompt.read_bytes())
        self.assertEqual(set((root / "input").iterdir()), {root / "input/task.md"})
        self.assertEqual(list((root / "state").iterdir()), [])
        self.assertEqual(plan["status"], "prepared-not-executed")
        for flag, value in (("--gemini_dir", str(root / "state")), ("--app_data_dir", "antigravity-cli"), ("--agent", "text-only"), ("--model", "synthetic-model"), ("--effort", "synthetic-effort"), ("--input-format", "stream-json"), ("--output-format", "stream-json")):
            self.assertEqual(plan["argv"][plan["argv"].index(flag) + 1], value)
        agent = (root / "work/.agents/agents/text-only.md").read_text()
        self.assertEqual(agent, helper.TEXT_ONLY_AGENT)
        self.assertEqual(agent.split("---", 2)[2].strip(), "")
        audit = helper.audit(root)
        self.assertTrue(audit["artifact_checks_passed"])
        self.assertFalse(audit["runtime_reports_complete"])
        self.assertFalse(audit["isolation_certified"])

    def test_codex_plan_preserves_auth_home_and_disables_context_tools(self):
        config = self.config("codex")
        plan = helper.prepare(config)
        self.assertEqual(plan["stdin_file"], str(Path(config["run_dir"]) / "input/task.md"))
        for flag in ("--ignore-user-config", "--ignore-rules", "--strict-config", "--ephemeral"):
            self.assertIn(flag, plan["argv"])
        self.assertEqual(plan["argv"][-1], "-")
        self.assertFalse(any("agy strict" in gate for gate in plan["manual_gates"]))
        settings = helper.load(Path(config["run_dir"]) / "runtime/codex-settings.json")
        self.assertEqual(settings["web_search"], "disabled")
        self.assertFalse(settings["features.memories"])
        self.assertFalse(settings["features.multi_agent"])
        with mock.patch.dict(os.environ, {"HOME": "/preserved-home", "CODEX_HOME": "/preserved-auth", "EXTRA_SECRET": "never-copy"}, clear=True):
            env = helper.environment(Path(config["run_dir"]))
        self.assertEqual(env["HOME"], "/preserved-home")
        self.assertEqual(env["CODEX_HOME"], "/preserved-auth")
        self.assertNotIn("EXTRA_SECRET", env)

    def test_missing_flags_and_changed_binary_fail_closed(self):
        self.binary.write_text("#!" + sys.executable + "\nprint('no supported flags')\n")
        with self.assertRaisesRegex(ValueError, "inspection failed"):
            helper.inspect_cli("agy", str(self.binary), self.root / "unsupported")
        self.setUp_fake_binary_again()
        config = self.config()
        self.binary.write_text(self.binary.read_text() + "# changed\n")
        with self.assertRaisesRegex(ValueError, "identity"):
            helper.prepare(config)
        self.assertFalse(Path(config["run_dir"]).exists())

    def test_agy_unadvertised_directory_flags_require_separate_preflight(self):
        flags = " ".join(x for x in helper.REQUIRED_FLAGS["agy"] if x not in helper.UNADVERTISED_AGY_FLAGS)
        self.binary.write_text("#!" + sys.executable + "\nimport sys\nprint('synthetic 1' if '--version' in sys.argv else " + repr(flags) + ")\n")
        config = self.config()
        identity = helper.load(config["cli_identity"])
        self.assertEqual(set(identity["unadvertised_directory_flags"]), helper.UNADVERTISED_AGY_FLAGS)
        self.assertFalse(identity["directory_overrides_verified"])
        helper.prepare(config)
        self.assertFalse(helper.audit(config["run_dir"])["agy_directory_preflight_complete"])

    def synthetic_open_report(self, root):
        manifest = helper.load(root / "runtime/probes.json")
        paths = [manifest["positive"]] + [x["path"] for x in manifest["negative"]]
        helper.save(root / "runtime/open-probe.json", {"kind": "actual-file-open", "role": None, "pid": 999999, "passed": True, "prompt_sha256": manifest["sha256"], "checks": [{"path": path, "passed": True} for path in paths], "test_fixture_only": True})

    def test_inventory_has_closed_stdin_and_requires_app_data_at_requested_root(self):
        config = self.config()
        helper.prepare(config)
        root = Path(config["run_dir"])
        self.synthetic_open_report(root)

        def fake_inventory(argv, **kwargs):
            self.assertEqual(argv[-1], "models")
            self.assertEqual(kwargs["stdin"], helper.subprocess.DEVNULL)
            self.assertEqual(argv[argv.index("--gemini_dir") + 1], str(root / "state"))
            self.assertEqual(argv[argv.index("--app_data_dir") + 1], "antigravity-cli")
            generated = root / "state/antigravity-cli/inventory-cache"
            generated.parent.mkdir()
            generated.write_text("synthetic cache, not real CLI evidence")
            kwargs["stdout"].write(b"synthetic-model\n")
            return SimpleNamespace(returncode=0)

        with mock.patch.object(helper.subprocess, "run", side_effect=fake_inventory):
            result = helper.inventory_agy(root)
        self.assertTrue(result["directory_overrides_verified"])
        self.assertEqual(result["request_count"], 0)
        self.assertFalse(result["model_inference_requested"])
        audit = helper.audit(root)
        self.assertTrue(audit["artifact_checks_passed"])
        self.assertTrue(audit["agy_directory_preflight_complete"])
        self.assertFalse(audit["isolation_certified"])
        self.assertEqual(audit["attempt_ledger"]["attempts"][0]["request_count"], 0)

    def test_inventory_without_state_location_evidence_is_preserved_as_failed(self):
        config = self.config()
        helper.prepare(config)
        root = Path(config["run_dir"])
        with self.assertRaisesRegex(ValueError, "real-open probe"):
            helper.inventory_agy(root)
        self.synthetic_open_report(root)
        with mock.patch.object(helper.subprocess, "run", return_value=SimpleNamespace(returncode=0)):
            with self.assertRaisesRegex(ValueError, "preflight failed"):
                helper.inventory_agy(root)
        report = helper.load(root / "runtime/preflight/report.json")
        self.assertEqual(report["exit_code"], 0)
        self.assertFalse(report["directory_overrides_verified"])
        self.assertEqual(helper.load(root / "runtime/attempt-ledger.json")["attempts"][0]["status"], "failed")

    def setUp_fake_binary_again(self):
        flags = " ".join(helper.REQUIRED_FLAGS["agy"])
        self.binary.write_text("#!" + sys.executable + "\nimport sys\nprint('synthetic 1' if '--version' in sys.argv else " + repr(flags) + ")\n")

    def test_negative_probe_categories_and_policy_coverage_are_required(self):
        config = self.config()
        config["probes"] = config["probes"][:2]
        with self.assertRaisesRegex(ValueError, "prior_run"):
            helper.prepare(config)
        config = self.config(name="other")
        config["probes"][0]["path"] = str(self.prompt)
        with self.assertRaisesRegex(ValueError, "deny root"):
            helper.prepare(config)

    def test_read_exceptions_may_not_expose_negative_probes(self):
        config = self.config()
        config["read_exceptions"] = [{"path": str(self.private), "kind": "subpath", "purpose": "too broad"}]
        with self.assertRaisesRegex(ValueError, "expose a negative probe"):
            helper.prepare(config)

    def test_credentials_are_only_linked_and_state_is_excluded(self):
        config = self.config()
        auth = self.private / "oauth"
        secret = "CREDENTIAL_CONTENT_MUST_NEVER_ENTER_EVIDENCE_69393"
        auth.write_text(secret)
        config["credential_links"] = [{"source": str(auth), "target": "antigravity-cli/antigravity-oauth-token"}]
        helper.prepare(config)
        root = Path(config["run_dir"])
        self.assertFalse((root / "state/antigravity-cli").exists())
        helper.auth_links(root)
        link = root / "state/antigravity-cli/antigravity-oauth-token"
        self.assertTrue(link.is_symlink())
        self.assertEqual(link.resolve(), auth)
        (root / "state/private-runtime-data").write_text(secret)
        helper.auth_links(root, remove=True)
        self.assertFalse(link.exists())
        self.assertEqual(auth.read_text(), secret)
        audit = helper.audit(root)
        self.assertFalse(audit["state_included"])
        self.assertEqual(audit["credential_links_remaining"], [])
        self.assertTrue(all(not x["path"].startswith("state/") for x in audit["files"]))
        self.assertNotIn(secret, json.dumps(audit))
        for path in (root / "runtime").iterdir():
            if path.is_file():
                self.assertNotIn(secret, path.read_text())

    def test_audit_detects_input_and_profile_tampering(self):
        config = self.config()
        helper.prepare(config)
        root = Path(config["run_dir"])
        (root / "input/task.md").write_bytes(b"altered")
        (root / "runtime/outer.sb").write_text("(allow default)")
        audit = helper.audit(root)
        self.assertFalse(audit["artifact_checks_passed"])
        self.assertEqual(len(audit["errors"]), 2)

    def test_modified_manifest_cannot_add_state_to_delivery_whitelist(self):
        config = self.config()
        helper.prepare(config)
        root = Path(config["run_dir"])
        (root / "state/private-token").write_text("never read this state file")
        hashes = helper.load(root / "runtime/prepared-hashes.json")
        hashes["state/private-token"] = "untrusted digest"
        (root / "runtime/prepared-hashes.json").write_text(json.dumps(hashes))
        audit = helper.audit(root)
        self.assertFalse(audit["artifact_checks_passed"])
        self.assertTrue(all(not item["path"].startswith("state/") for item in audit["files"]))

    def test_existing_run_is_never_overwritten(self):
        config = self.config()
        helper.prepare(config)
        with self.assertRaisesRegex(ValueError, "must be new"):
            helper.prepare(config)

    def test_real_open_probe_fails_on_allowed_or_missing_negative_file(self):
        manifest = {"positive": str(self.prompt), "sha256": helper.sha256(self.prompt), "negative": [{"path": str(self.private / "reference"), "exists_before_run": True}]}
        result = probe.probe(manifest)
        self.assertFalse(result["passed"])
        self.assertEqual(result["checks"][1]["outcome"], "UNEXPECTED_ALLOWED")
        manifest["negative"][0]["path"] = str(self.private / "missing")
        self.assertEqual(probe.probe(manifest)["checks"][1]["outcome"], "OTHER_ERROR")

    def test_denial_probe_requires_permission_error_and_exact_positive_hash(self):
        manifest = {"positive": str(self.prompt), "sha256": helper.sha256(self.prompt), "negative": [{"path": str(self.private / "reference"), "exists_before_run": True}]}
        with mock.patch("builtins.open", side_effect=PermissionError(1, "synthetic denied")):
            result = probe.probe(manifest)
            self.assertTrue(result["passed"])
            self.assertEqual(result["checks"][0]["observed_sha256"], helper.sha256(self.prompt))
            manifest["sha256"] = "wrong"
            result = probe.probe(manifest)
            self.assertFalse(result["passed"])
            self.assertEqual(result["checks"][0]["observed_sha256"], helper.sha256(self.prompt))

    def test_positive_open_failure_retains_unknown_observed_hash(self):
        manifest = {"positive": str(self.root / "missing-task.md"), "sha256": helper.sha256(self.prompt),
                    "negative": [{"path": str(self.private / "reference"), "exists_before_run": True}]}
        result = probe.probe(manifest)
        self.assertFalse(result["passed"])
        self.assertIsNone(result["checks"][0]["observed_sha256"])
        self.assertEqual(result["checks"][0]["errno"], 2)


if __name__ == "__main__":
    unittest.main()
