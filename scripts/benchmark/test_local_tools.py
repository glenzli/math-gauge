"""Local computation is opt-in and never grants search or reference access."""

import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock, patch
import subprocess

from common import load, save
from local_tools import TRACK, AGY_LOCAL_TOOLS, allowed_event_tool, configure_local_tools
import isolation


class LocalToolsTests(unittest.TestCase):
    def test_provider_aliases_do_not_duplicate_exposed_file_tools(self):
        canonical = {'view_file': 'read_file', 'write_to_file': 'write_file'}
        names = [canonical.get(name, name) for name in AGY_LOCAL_TOOLS]
        self.assertEqual(len(names), len(set(names)))

    def test_exited_children_are_transient_but_live_identity_failures_still_fail(self):
        library = Mock()
        library.proc_pidpath.return_value = 0
        for state in ('Z', ''):
            with patch.object(isolation.ctypes, 'CDLL', return_value=library), patch.object(
                    isolation.subprocess, 'run', return_value=subprocess.CompletedProcess([], 0, state, '')):
                with self.assertRaises(ProcessLookupError):
                    isolation.executable(123)
        with patch.object(isolation.ctypes, 'CDLL', return_value=library), patch.object(
                isolation.subprocess, 'run', return_value=subprocess.CompletedProcess([], 0, 'SN', '')):
            with self.assertRaisesRegex(RuntimeError, 'Cannot identify'):
                isolation.executable(123)

    def test_worker_path_is_captured_before_policy_query_without_a_late_race(self):
        with patch.object(isolation, 'executable', return_value='/bin/sh') as identity, patch.object(
                isolation, 'process_tree', return_value={123: {}}), patch.object(
                isolation.subprocess, 'run', return_value=subprocess.CompletedProcess([], 0, b'', b'')), patch.object(
                isolation, 'load', return_value={'passed': True}):
            result = isolation.check_pid(Path('/tmp/fixture'), 123, 'worker')
            self.assertEqual(result['executable'], '/bin/sh')
            identity.assert_called_once_with(123)

    def test_event_contract_preserves_no_tools_and_rejects_remote_tools(self):
        for client in ("codex", "agy"):
            plain = {"client": client}
            local = {**plain, "local_tool_policy": TRACK}
            command = "command_execution" if client == "codex" else "run_command"
            self.assertFalse(allowed_event_tool(plain, command))
            self.assertTrue(allowed_event_tool(local, command))
            for forbidden in ("web_search", "search_web", "mcp_tool_call", "browser_action", "invoke_subagent"):
                self.assertFalse(allowed_event_tool(local, forbidden))
            self.assertFalse(allowed_event_tool(local, command, allow_search=True))
        self.assertTrue(allowed_event_tool({"client": "agy"}, "finish"))
        self.assertTrue(allowed_event_tool({"client": "codex"}, "web_search", allow_search=True))

    def test_codex_compute_permissions_leave_history_and_network_closed(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            original = {"features.shell_tool": False, "features.unified_exec": False, "features.code_mode_host": False,
                        "permissions.isolated-cli.filesystem": {":minimal": "read"},
                        "permissions.isolated-cli.network.enabled": False, "web_search": "disabled",
                        "features.memories": False}
            save(root / "runtime/codex-settings.json", original)
            (root / 'runtime/outer.sb').write_text('(version 1)(allow default)')
            plan = {"client": "codex", "argv": ["codex", "--cd", str(root / "input")]}
            for key, value in original.items():
                plan["argv"] += ["--config", key + "=" + json.dumps(value)]
            extension = {"changes": []}
            configure_local_tools(root, plan, extension)
            settings = load(root / "runtime/codex-settings.json")
            self.assertTrue(settings["features.shell_tool"])
            self.assertTrue(settings["features.code_mode_host"])
            self.assertFalse(settings["features.memories"])
            self.assertFalse(settings["permissions.isolated-cli.network.enabled"])
            self.assertEqual(settings["web_search"], "disabled")
            fs = settings["permissions.isolated-cli.filesystem"]
            self.assertEqual(fs[str(root / "work")], "write")
            self.assertNotIn(str(Path.home()), fs)
            self.assertEqual({p for p, access in fs.items() if access == 'write'},
                             {str(root / name) for name in ('work', 'output', 'runtime/tmp')})
            self.assertIn('features.shell_tool=true', plan['argv'])
            self.assertEqual(plan['cwd'], str(root / 'work'))

    def test_agy_local_profile_denies_network_and_mcp_without_blocking_commands(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'work/.agents/agents').mkdir(parents=True)
            (root / 'runtime').mkdir()
            (root / 'runtime/outer.sb').write_text('(version 1)(allow default)')
            plan = {'client': 'agy', 'argv': []}
            configure_local_tools(root, plan, {'changes': []})
            settings = load(root / 'runtime/task-settings.json')
            self.assertEqual(settings, load(root / 'state/antigravity-cli/settings.json'))
            self.assertEqual(settings['toolPermission'], 'proceed-in-sandbox')
            self.assertTrue(settings['enableTerminalSandbox'])
            self.assertNotIn('command(*)', settings['permissions']['deny'])
            self.assertNotIn('command(*)', settings['permissions']['allow'])
            self.assertIn('read_url(*)', settings['permissions']['deny'])
            self.assertIn('mcp(*)', settings['permissions']['deny'])
            agent = (root / 'work/.agents/agents/text-only.md').read_text()
            self.assertIn('  - run_command\n', agent)
            self.assertIn('commandExecutionPolicy: sandbox', agent)
            self.assertNotIn('search_web', agent)
            self.assertEqual(plan['local_tool_policy'], TRACK)


if __name__ == '__main__':
    unittest.main()
