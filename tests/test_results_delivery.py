import copy
import unittest

from scripts.results_delivery import delivery_progress


class AnswerDeliveryTests(unittest.TestCase):
    def setUp(self):
        self.result = {'whole_task_counts': {'planned': 39, 'unknown': 0}, 'coverage': {}}

    def test_paper_failure_is_settled_but_not_delivered(self):
        self.result['coverage'].update(source_reviewed_tasks=38, observed_delivery_failures=1)
        self.assertEqual(delivery_progress({}, self.result, record_sha256='source'),
                         {'planned': 39, 'delivered': 38, 'undelivered': 1, 'pending': 0})

    def test_unrun_is_separate_from_failed_delivery_and_mathematical_errors(self):
        self.result['whole_task_counts']['unknown'] = 16
        record = {'execution_summary': {'delivered_initial_tasks': 19}}
        original = copy.deepcopy(self.result)
        progress = delivery_progress(record, self.result, record_sha256='source')
        self.assertEqual((progress['delivered'], progress['undelivered'], progress['pending']), (19, 4, 16))
        self.assertEqual(self.result, original)

    def test_zero_is_known_and_missing_delivery_evidence_is_unknown(self):
        progress = delivery_progress({'execution_summary': {'delivered_initial_tasks': 0}}, self.result, record_sha256='source')
        self.assertEqual(progress['delivered'], 0)
        self.assertIsNone(delivery_progress({}, self.result, record_sha256='source')['delivered'])

    def test_legacy_counts_bind_the_selected_record_and_denominator(self):
        projection = {'record_sha256': 'source', 'planned': 39, 'delivered': 39}
        self.assertEqual(delivery_progress({}, self.result, record_sha256='source', projection=projection)['delivered'], 39)
        with self.assertRaises(ValueError):
            delivery_progress({}, self.result, record_sha256='different', projection=projection)
        with self.assertRaises(ValueError):
            delivery_progress({}, self.result, record_sha256='source', projection={**projection, 'planned': 25})

    def test_native_count_does_not_depend_on_strict_passes(self):
        self.result['whole_task_counts'].update(passed=0, failed=39)
        self.assertEqual(delivery_progress({'delivery_counts': {'initial': 39}}, self.result, record_sha256='source')['delivered'], 39)

    def test_delivered_but_ungraded_answers_are_not_missing(self):
        self.result['whole_task_counts']['unknown'] = 3
        progress = delivery_progress({'execution_summary': {'delivered_initial_tasks': 39}}, self.result, record_sha256='source')
        self.assertEqual((progress['delivered'], progress['pending'], progress['undelivered']), (39, 0, 0))
