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

    def test_recovered_source_status_does_not_change_delivery_or_math(self):
        self.result.update(submission_method_version='0.1.0', submission_summary={
            'planned':39, 'active_final':21, 'forced_content':5, 'blank':13, 'pending':0,
            'pending_original_record_review':3})
        original = copy.deepcopy(self.result)
        progress = delivery_progress({}, self.result, record_sha256='source',
                                     review_completion={'resolved_pending_count':3})
        self.assertEqual((progress['delivered'],progress['forced_content'],progress['blank']), (21,5,13))
        self.assertEqual(progress['pending_original_record_review'],0)
        self.assertEqual(self.result, original)
        with self.assertRaisesRegex(ValueError, 'another submission population'):
            delivery_progress({},self.result,record_sha256='source',
                              review_completion={'resolved_pending_count':2})

    def test_browser_recovery_hides_old_pending_note_without_rewriting_scores(self):
        from scripts.results_presentation import model_view
        result = {'metrics':{'earned':{'confirmed':41.48,'exact':None}},'contributions':{},
                  'submission_summary':{'planned':39,'active_final':21,'forced_content':5,
                      'blank':13,'pending':0,'pending_original_record_review':3}}
        model = {'combined':result,'retry':{'combined':result},'content_rates':None,
                 'capability':{'nonlogical_retry_3':result},'strict':{'nonlogical_retry_3':result},
                 'answer_delivery':{'source_review_status':'complete'}}
        before=copy.deepcopy(model)
        projected=model_view(model)
        self.assertEqual(projected['retry']['combined']['submission_summary']['pending_original_record_review'],0)
        self.assertEqual(projected['retry']['combined']['metrics'],result['metrics'])
        self.assertEqual(model,before)
