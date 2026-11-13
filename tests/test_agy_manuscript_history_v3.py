"""Two synthetic AGY ledger regressions; no private task or candidate bytes."""
import copy
import json
import unittest

import test_agy_native_evidence as native_tests
from math_gauge.records import evidence_bytes, validate_agy_manuscript_history


class AgyManuscriptHistoryV3Tests(unittest.TestCase):
    def fixture(self, excluded=False):
        f = native_tests.AgyEvidenceTests()
        f.setUp()
        self.addCleanup(f.doCleanups)
        freeze = dict(benchmark_version='1.0.0', requested_model='argon', requested_effort='high',
            maximum_effective_attempts=3, first_normal_final_locks_selection=True,
            mathematical_errors_never_retry=True, proven_pure_system_failures_excluded_separately=True)
        freeze_source = f.put('freeze.json', freeze)
        success = copy.deepcopy(f.data)
        success['physical_request'] = 2
        success_source = f.put('p2-native.json', success)
        terminal = dict(event='result', result=dict(status='ERROR', error='Synthetic native failure'))
        terminal_source = f.put('p1-terminal.json', terminal)
        events = f.put('p1-events.ndjson', (json.dumps(terminal)+'\n').encode())
        execution = copy.deepcopy(f.execution)
        execution['artifact_hashes']['output/events.ndjson'] = events['sha256']
        failure = dict(copy.deepcopy(f.data), physical_request=1, outcome='delivery_failed',
            mathematical_judgment='not_adjudicated', additional_mathematical_penalty=0,
            native_execution=f.put('p1-execution.json', execution), native_events=events,
            native_terminal_event=terminal_source, response=None,
            native_terminal_seal=f.put('p1-seal.json', dict(native_status='ERROR',
                normal_complete_delivery=False, raw_terminal_sha256=terminal_source['sha256'])))
        failure_source = f.put('p1-native.json', failure)
        attempts = []
        for number, source in [(1, failure_source), (2, success_source)]:
            result = f.put(f'p{number}-result.json', dict(schema='math-gauge.argon-physical-result/v1',
                case_id='S', physical_request_number=number, freeze_sha256=freeze_source['sha256'],
                requested_model='argon', requested_effort='high', normal_complete_delivery=number == 2))
            attempts.append(dict(physical_request=number, agy_native_evidence=source,
                execution_result=result, excluded_pure_system_failure=excluded if number == 1 else False,
                effective_model_attempt=(None if excluded else 1) if number == 1 else (1 if excluded else 2),
                first_normal_final=number == 2))
        if excluded:
            attempts[0]['exclusion_admission'] = f.put('exclusion.json', dict(
                schema='math-gauge.source-bound-service-failure-admission/v1',
                affected_physical_requests=[dict(case_id='S', physical_request_number=1,
                    adjudicated_pure_service_failure=True, effective_attempt_consumed=False,
                    terminal_evidence=terminal_source,
                    original_result_sha256=attempts[0]['execution_result']['sha256'])]))
        effective = 1 if excluded else 2
        ledger = dict(schema='math-gauge.agy-manuscript-request-history/v3', case_id='S',
            first_normal_final_selected=True, selection_depends_on_mathematical_quality=False,
            source_raw_bytes_rewritten=False, pre_call_freeze=freeze_source, attempts=attempts,
            selected_physical_request=2, consumed_effective_attempts=effective, effective_model_attempt=effective)
        row = dict(case_id='S', selected_physical_request=2, effective_model_attempt=effective,
            agy_native_evidence=success_source, execution=success['native_execution'],
            execution_plan=success['native_plan'], native_events=success['native_events'],
            native_request=success['native_request'], candidate_input=success['candidate_input'], response=success['response'])
        return f, freeze, ledger, row, dict(case_id='S', original_task=success['candidate_input'])

    def check(self, f, ledger, row, case):
        row['physical_request_ledger'] = f.put('history-v3.json', ledger)
        return validate_agy_manuscript_history(f.root, row, case)

    def test_consumed_failure_cannot_disappear_or_hide_an_earlier_normal_final(self):
        f, freeze, ledger, row, case = self.fixture()
        self.assertEqual(self.check(f, ledger, row, case)['consumed_effective_attempts'], 2)
        erased = copy.deepcopy(ledger)
        erased['attempts'][0]['effective_model_attempt'] = None
        with self.assertRaisesRegex(ValueError, 'erased or renumbered'):
            self.check(f, erased, row, case)
        hidden = copy.deepcopy(ledger)
        first = json.loads(evidence_bytes(f.root, hidden['attempts'][1]['agy_native_evidence']))
        first['physical_request'] = 1
        hidden['attempts'][0]['agy_native_evidence'] = f.put('hidden-success.json', first)
        with self.assertRaises(ValueError):
            self.check(f, hidden, row, case)

    def test_pure_exclusion_requires_actual_admission_and_same_request_identity(self):
        f, freeze, ledger, row, case = self.fixture(excluded=True)
        self.assertEqual(self.check(f, ledger, row, case)['consumed_effective_attempts'], 1)
        bad = copy.deepcopy(ledger)
        bad['attempts'][0]['exclusion_admission'] = f.put('unadmitted.json', dict(
            schema='math-gauge.source-bound-service-failure-admission/v1', affected_physical_requests=[]))
        with self.assertRaisesRegex(ValueError, 'original admitted'):
            self.check(f, bad, row, case)
        for field in ('requested_model', 'requested_effort'):
            for location in ('freeze', 'execution_result'):
                with self.subTest(field=field, location=location):
                    f, freeze, bad, row, case = self.fixture()
                    if location == 'freeze':
                        freeze[field] = 'another-request'
                        bad['pre_call_freeze'] = f.put('other-freeze.json', freeze)
                        for attempt in bad['attempts']:
                            result = json.loads(evidence_bytes(f.root, attempt['execution_result']))
                            result['freeze_sha256'] = bad['pre_call_freeze']['sha256']
                            attempt['execution_result'] = f.put(f"result-{attempt['physical_request']}.json", result)
                    else:
                        result = json.loads(evidence_bytes(f.root, bad['attempts'][1]['execution_result']))
                        result[field] = 'another-request'
                        bad['attempts'][1]['execution_result'] = f.put('other-result.json', result)
                    with self.assertRaisesRegex(ValueError, 'model or effort'):
                        self.check(f, bad, row, case)


if __name__ == '__main__':
    unittest.main()
