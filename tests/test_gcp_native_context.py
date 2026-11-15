"""Native compaction admission, without model calls or private fixtures."""
import copy
from pathlib import Path
import tempfile
import unittest

from scripts.gcp_native_context import NativeContextGuard


class NativeContextTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.session = Path(self.temp.name) / 'session'
        (self.session / 'input').mkdir(parents=True)
        self.task = self.session / 'input/task.md'
        self.task.write_text('Complete original task and all supplied files.')
        self.guard = NativeContextGuard(self.task)
        self.original = self.request(self.task.read_text())

    def request(self, text, *, conversation='same-native-context', work=None):
        return {'systemInstruction': {'parts': [{'text': '<user_information>\n'
            'Command Working Directory: ' + str(work or self.session / 'work')
            + '\nConversation ID: ' + conversation + '\n</user_information>'}]},
            'contents': [{'role': 'user', 'parts': [{'text': text}]}],
            'tools': [{'functionDeclarations': [{'name': 'command'}]}]}

    def summary(self, text='Native summary of this same conversation.'):
        return self.request('<CONTEXT_SUMMARY>\n' + text + '\n</CONTEXT_SUMMARY>')

    def test_native_compaction_preserves_payload_and_original_task_binding(self):
        self.guard.validate(self.original)
        incoming = self.summary()
        before = copy.deepcopy(incoming)
        receipt = self.guard.validate(incoming, expected_tools={'command'})
        self.assertEqual(incoming, before)
        self.assertEqual(receipt['mode'], 'native-compaction')
        self.assertTrue(receipt['tool_response_check_waived_for_new_native_summary'])
        self.assertEqual(receipt['task_sha256'], self.guard.prompt_sha256)

    def test_summary_cannot_be_a_fresh_or_foreign_context(self):
        with self.assertRaisesRegex(ValueError, 'fresh native context'):
            self.guard.validate(self.summary())
        self.guard.validate(self.original)
        for payload in [self.request(self.task.read_text(), conversation='other'),
                        self.request(self.task.read_text(), work=self.session / 'other')]:
            with self.assertRaisesRegex(ValueError, 'scope mismatch|changed within'):
                self.guard.validate(payload)

    def test_repeating_summary_does_not_erase_required_tool_results(self):
        self.guard.validate(self.original)
        incoming = self.summary()
        self.guard.validate(incoming, expected_tools={'command'})
        with self.assertRaisesRegex(ValueError, 'Missing original tool responses'):
            self.guard.validate(incoming, expected_tools={'command'})
        incoming['contents'].append({'role': 'user', 'parts': [
            {'functionResponse': {'name': 'command', 'response': {'output': 'own result'}}}]})
        self.assertEqual(self.guard.validate(incoming, expected_tools={'command'})['mode'],
                         'native-summary-followup')
        self.assertEqual(self.guard.validate(self.summary('Next native compaction'),
                                           expected_tools={'command'})['mode'], 'native-compaction')

    def test_frozen_task_and_native_scope_stay_required(self):
        self.guard.validate(self.original)
        with self.assertRaisesRegex(ValueError, 'Missing frozen task'):
            self.guard.validate(self.request('Unrelated task'))
        self.task.write_text('Changed task')
        with self.assertRaisesRegex(ValueError, 'Frozen native task file changed'):
            self.guard.validate(self.summary())

    def test_malformed_or_model_authored_summary_does_not_qualify(self):
        self.guard.validate(self.original)
        with self.assertRaisesRegex(ValueError, 'Incomplete native context-summary'):
            self.guard.validate(self.request('<CONTEXT_SUMMARY>not closed'))
        payload = self.summary()
        payload['contents'][0]['role'] = 'model'
        with self.assertRaisesRegex(ValueError, 'Missing frozen task'):
            self.guard.validate(payload)
