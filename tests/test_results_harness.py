"""Harness notes are a page-local projection of retained source metadata."""
import copy
import unittest

from scripts.results_harness import render_harness_notes, scoped_harness_notes


class ScopedHarnessNotesTests(unittest.TestCase):
    def setUp(self):
        self.dot = {'id': 'dot', 'record_kind': 'native_harness',
                    'harness_display_name': 'Unknown¹', 'harness': {'name': 'Dot native harness'}}
        self.deepseek = {'id': 'deepseek', 'harness_display_name': 'Codex CLI²',
                         'harness': {'name': 'Codex CLI', 'note_marker': '²',
                                     'note_text': '此前使用DeepSeek Harness（DSH）时，旧说明。'}}
        self.glm = {'id': 'glm', 'harness_display_name': 'Claude Code³',
                    'harness': {'name': 'Claude Code', 'note_marker': '³',
                                'note_text': '保留运行方式说明。', 'note_text_en': 'Retained harness explanation.'}}
        self.gemini = {'id': 'gemini', 'harness_display_name': 'AGY CLI⁴',
                       'harness': {'name': 'AGY CLI', 'note_marker': '⁴', 'note_text': '原运行重试说明。'}}

    def test_current_cohort_has_deepseek_first_and_no_agy_note(self):
        names, notes = scoped_harness_notes([self.gemini, self.deepseek])
        self.assertEqual(names, {'gemini': 'AGY CLI', 'deepseek': 'Codex CLI¹'})
        self.assertEqual([note['marker'] for note in notes], ['¹'])
        self.assertEqual(notes[0]['model_ids'], ['deepseek'])
        self.assertIn('因此改用Codex CLI执行', notes[0]['text']['zh'])
        self.assertIn('DSH', notes[0]['text']['en'])
        self.assertIn('Codex CLI', notes[0]['text']['en'])
        self.assertNotEqual(notes[0]['text']['zh'], notes[0]['text']['en'])

    def test_historical_cohort_numbers_retained_notes_in_source_order(self):
        names, notes = scoped_harness_notes([self.glm, self.gemini, self.deepseek, self.dot])
        self.assertEqual([note['marker'] for note in notes], ['¹', '²', '³'])
        self.assertEqual(names, {'glm': 'Claude Code³', 'gemini': 'AGY CLI',
                                 'deepseek': 'Codex CLI²', 'dot': 'Unknown¹'})
        # An individual model page has its own visible scope.
        names, notes = scoped_harness_notes([self.glm])
        self.assertEqual(names['glm'], 'Claude Code¹')
        self.assertEqual(notes[0]['text']['en'], 'Retained harness explanation.')

    def test_shared_note_is_deduplicated_and_source_metadata_is_immutable(self):
        second = copy.deepcopy(self.deepseek)
        second['id'] = 'another-deepseek'
        models = [self.deepseek, self.gemini, second]
        original = copy.deepcopy(models)
        names, notes = scoped_harness_notes(models)
        self.assertEqual(models, original)
        self.assertEqual(len(notes), 1)
        self.assertEqual(notes[0]['model_ids'], ['another-deepseek', 'deepseek'])
        self.assertEqual(names['another-deepseek'], 'Codex CLI¹')

    def test_static_notes_escape_both_languages(self):
        value = render_harness_notes([{'marker': '¹', 'text': {'zh': '<script>&', 'en': '<img>&'}}])
        self.assertIn('data-lang-content="zh">&lt;script&gt;&amp;', value)
        self.assertIn('data-lang-content="en" hidden>&lt;img&gt;&amp;', value)
        self.assertNotIn('<script>', value)


if __name__ == '__main__':
    unittest.main()
