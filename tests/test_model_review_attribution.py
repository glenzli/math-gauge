"""Keep explicit model-level reviewer and human-review provenance separate."""
import unittest

from scripts.results_details import review_status


class ModelReviewAttributionTests(unittest.TestCase):
    def setUp(self):
        self.process = {'primary_ai_reviewer': 'Sol 6.1 Max',
                        'cross_check_reviewers': ['Astra 6 Max', 'Dot']}
        self.attribution = {'reviewer_kind': 'ai', 'human_review': 'pending',
                            'detail_zh': 'Sol 与 Root：分别审核；人工待审',
                            'detail_en': 'Sol and Root reviewed separately; human review pending <unapproved>'}

    def test_explicit_model_attribution_does_not_claim_a_human_spot_check(self):
        page = review_status({'review_process': self.process,
            'model': {'harness': {'review_attribution': self.attribution}}}, '../../method.html')
        self.assertIn('AI 审核 · 人工数学审核待完成', page)
        self.assertIn('AI reviewed · Human mathematical review pending', page)
        self.assertIn('Sol 与 Root', page)
        self.assertIn('&lt;unapproved&gt;', page)
        self.assertNotIn('部分人工抽审', page)
        self.assertNotIn('Astra 6 Max', page)

    def test_other_model_and_global_status_keep_the_original_output(self):
        expected = ('<div class="statusline"><span class="status-dot" aria-hidden="true"></span>'
            '<span title="全审：Sol 6.1 Max；抽审核对：Astra 6 Max + Dot">AI 审核 · 部分人工抽审</span>'
            '<a data-context-link href="method.html">审核方式 →</a></div>')
        self.assertEqual(review_status({'review_process': self.process}, 'method.html'), expected)
        self.assertEqual(review_status({'review_process': self.process,
            'model': {'harness': {'name': 'Codex CLI'}}}, 'method.html'), expected)

    def test_an_override_cannot_invent_another_human_review_status(self):
        self.attribution['human_review'] = 'approved'
        with self.assertRaisesRegex(ValueError, 'human-pending'):
            review_status({'review_process': self.process,
                'model': {'harness': {'review_attribution': self.attribution}}}, 'method.html')


if __name__ == '__main__':
    unittest.main()
