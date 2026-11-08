"""Synthetic operational failure bindings; no candidate or mathematical judgments."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from math_gauge.records import descriptor, validate_native_delivery_failure, validate_unavailable_engineering_native_bindings


class NativeDeliveryFailureTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(); self.addCleanup(temp.cleanup); self.root = Path(temp.name)
        def put(name, value):
            path = self.root / name
            path.write_bytes(value if isinstance(value, bytes) else (json.dumps(value) + '\n').encode())
            return descriptor(self.root, path)
        self.put = put
        task = put('task.md', b'SYNTHETIC TASK')
        request = put('request.ndjson', {'event':'user','message':{'content':'SYNTHETIC TASK'}})
        event = {'event': 'result', 'result': {'status': 'ERROR', 'response': 'READABLE FAILED TEXT'}}
        terminal = put('terminal.json', event); events = put('events.ndjson', (json.dumps(event)+'\n').encode())
        seal = put('seal.json', dict(native_status='ERROR', normal_complete_delivery=False, raw_terminal_sha256=terminal['sha256']))
        execution = put('execution.json', dict(kind='math', request_count=1, stdin_bytes_written=request['bytes'], stdin_write_calls=1,
            artifact_hashes={'input/task.md': task['sha256'], 'output/events.ndjson': events['sha256']}))
        slot = put('slot.json', dict(slot_id='SYNTHETIC:A1', case_id='SYNTHETIC', started=True,
            status='execution_error', response_sha256=None, locked_attempt=None, attempts=[{'status':'permanent_error'}]))
        self.data = dict(schema='math-gauge.native-delivery-failure-adjudication/v1', case_id='SYNTHETIC',
            slot_id='SYNTHETIC:A1', post_observation=True, outcome='delivery_failed', mathematical_judgment='not_adjudicated',
            source_raw_bytes_rewritten=False, native_request=request,
            additional_mathematical_penalty=0, native_execution=execution, native_events=events,
            native_terminal_event=terminal, native_terminal_seal=seal, native_plan=put('plan.json', dict(client='agy', stdin_sha256=request['sha256'], prompt_sha256=task['sha256'])),
            candidate_input=task, slot_record=slot, retained_failed_physical_requests=[])
        self.row = dict(id='SYNTHETIC:A1', case_id='SYNTHETIC', response=None, review=None,
            source=dict(candidate_input=task, slot_record=slot), evaluation=dict(completion={'lower':0,'upper':0,'exact':0}, strict_pass=False))
        self.save()
    def save(self): self.row['delivery_failure'] = self.put('adjudication.json', self.data)
    def test_error_remains_operational_zero_without_math_review_or_success(self):
        self.assertEqual(validate_native_delivery_failure(self.root, self.row)['mathematical_judgment'], 'not_adjudicated')
        self.row['response'] = self.put('answer.md', b'READABLE FAILED TEXT')
        with self.assertRaises(ValueError): validate_native_delivery_failure(self.root, self.row)
    def test_private_error_receipt_must_match_opaque_engineering_projection(self):
        self.row['delivery_status'] = 'delivery_failed'
        case = dict(case_id='SYNTHETIC', slot_id='SYNTHETIC:A1', source_kind='not_available',
            delivery_status='delivery_failed', source_slot_record=self.row['source']['slot_record'])
        evidence = dict(native_failure_adjudication_sha256=self.row['delivery_failure']['sha256'])
        case['unavailable_evidence'] = self.put('unavailable.json', evidence)
        record, review = {'records':[self.row]}, {'cases':[case]}
        validate_unavailable_engineering_native_bindings(self.root, record, review, engineering_root=self.root)
        evidence['native_failure_adjudication_sha256'] = 'a' * 64
        case['unavailable_evidence'] = self.put('unavailable.json', evidence)
        with self.assertRaisesRegex(ValueError, 'another native ERROR'):
            validate_unavailable_engineering_native_bindings(self.root, record, review, engineering_root=self.root)

    def test_unrun_projection_cannot_hide_a_started_original_slot(self):
        self.row.pop('delivery_failure'); self.row['delivery_status'] = 'not_run'
        original = dict(slot_id='SYNTHETIC:A1',case_id='SYNTHETIC',started=False,status='not_run',
            response_sha256=None,locked_attempt=None,attempts=[])
        self.row['source']['slot_record'] = self.put('slot.json',original)
        case = dict(case_id='SYNTHETIC',slot_id='SYNTHETIC:A1',source_kind='not_available',delivery_status='not_run',
            source_slot_record=self.row['source']['slot_record'],unavailable_evidence=self.put('unavailable.json',{}))
        record, review = {'records':[self.row]}, {'cases':[case]}
        validate_unavailable_engineering_native_bindings(self.root,record,review,engineering_root=self.root)
        original['started']=True
        case['source_slot_record']=self.row['source']['slot_record']=self.put('slot.json',original)
        with self.assertRaisesRegex(ValueError,'private original slot'):
            validate_unavailable_engineering_native_bindings(self.root,record,review,engineering_root=self.root)

    def test_unbound_terminal_or_fabricated_math_penalty_is_rejected(self):
        original = copy.deepcopy(self.data)
        self.data['additional_mathematical_penalty'] = 5; self.save()
        with self.assertRaises(ValueError): validate_native_delivery_failure(self.root, self.row)
        self.data = original
        self.data['native_terminal_event'] = self.put('different.json', {'event':'result','result':{'status':'SUCCESS'}}); self.save()
        with self.assertRaises(ValueError): validate_native_delivery_failure(self.root, self.row)


if __name__ == '__main__': unittest.main()
