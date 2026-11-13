"""Recovered visible replies never become fabricated native success receipts."""
from copy import deepcopy
from datetime import datetime, timezone
import base64
import hashlib
import json
from pathlib import Path
import shutil
import tempfile
import unittest

from math_gauge.result_corrections import _field, load_selected, verify_native_recovery


def integer(value):
    result = bytearray()
    while value > 127:
        result.append((value & 127) | 128)
        value >>= 7
    return bytes(result + bytes([value]))


def scalar(key, value):
    return integer(key << 3) + integer(value)


def message(key, value):
    return integer((key << 3) | 2) + integer(len(value)) + value


class HarnessCorrectionTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.folder = Path(self.temporary.name)

    def keep(self, name, value):
        raw = value if isinstance(value, bytes) else (json.dumps(value) + '\n').encode()
        (self.folder / name).write_bytes(raw)
        return {'path': name, 'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}

    def fixture(self, *, completion=60, field=1, original_status='ERROR'):
        start = 1_800_000_000
        stamp = message(8, scalar(1, start + completion))
        payload = message(20, message(field, b'Original visible final.'))
        witness = {'post_observation': True, 'not_an_execution_time_seal': True,
            'conversation_id': 'original-context', 'rows': [
                {'idx': 0, 'step_type': 14}, {'idx': 1, 'step_type': 15,
                 'payload_sha256': hashlib.sha256(payload).hexdigest(),
                 'original_metadata_b64': base64.b64encode(stamp).decode(),
                 'metadata_sha256': hashlib.sha256(stamp).hexdigest()}]}
        return {'post_observation': True, 'original_native_status': 'ERROR',
            'native_status_rewritten': False, 'new_candidate_calls': 0,
            'original_terminal_seal': self.keep('seal.json', {'native_status': original_status,
                'normal_complete_delivery': False,
                'utc': datetime.fromtimestamp(start + 120, timezone.utc).isoformat()}),
            'step_payload': self.keep('step.pb', payload),
            'response': self.keep('answer.txt', b'Original visible final.'),
            'clock_witness': self.keep('clock.json', witness),
            'conversation_id': 'original-context', 'step_index': 1,
            'started_at': datetime.fromtimestamp(start, timezone.utc).isoformat(),
            'completed_at': datetime.fromtimestamp(start + completion, timezone.utc).isoformat(),
            'original_timeout_seconds': 120}

    def test_original_error_is_preserved_and_visible_bytes_are_bound(self):
        proof = self.fixture()
        result = verify_native_recovery(self.folder, proof)
        self.assertEqual(result['original_native_status'], 'ERROR')
        changed = deepcopy(proof)
        changed['response'] = self.keep('edited.txt', b'Repaired or substituted final.')
        with self.assertRaisesRegex(ValueError, 'exact original visible reply'):
            verify_native_recovery(self.folder, changed)

    def test_hidden_reasoning_is_not_a_recovered_reply(self):
        with self.assertRaises(ValueError):
            verify_native_recovery(self.folder, self.fixture(field=3))

    def test_after_deadline_or_success_relabeling_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'deadline'):
            verify_native_recovery(self.folder, self.fixture(completion=121))
        with self.assertRaisesRegex(ValueError, 'native success'):
            verify_native_recovery(self.folder, self.fixture(original_status='SUCCESS'))

    def test_ambiguous_native_fields_are_not_treated_as_missing(self):
        with self.assertRaisesRegex(ValueError, 'ambiguous'):
            _field(scalar(2, 1) + scalar(2, 2), 2, default=0)

    def test_unselected_file_does_not_change_current_results(self):
        self.keep('benchmark.json', {'version': '1.0.0'})
        self.keep('unselected-correction.json', {'score': 100})
        self.assertIsNone(load_selected(self.folder, 'fixture', self.folder))


class SelectedCorrectionTests(unittest.TestCase):
    """Exercise the public consumer against independently retained source files."""

    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        source_root = Path(__file__).resolve().parents[1]
        edition = json.loads((source_root / 'benchmark.json').read_bytes())
        self.selection = edition['result_corrections']['gemini-4-argon']
        manifest_source = source_root / self.selection['path']
        self.manifest = json.loads(manifest_source.read_bytes())
        self.folder = self.root / manifest_source.parents[2].relative_to(source_root)
        source_folder = manifest_source.parents[2]
        self.folder.mkdir(parents=True)
        for name in ('record.json', 'public-task-scores.json'):
            shutil.copyfile(source_folder / name, self.folder / name)
        record = json.loads((source_folder / 'record.json').read_bytes())
        descriptors = [self.manifest[key] for key in ('answer', 'math_review', 'claim_review', 'public_tasks', 'rates')]
        descriptors.extend(self.manifest['scores'].values())
        descriptors.extend(record[key]['nonlogical_retry_3'] for key in
                           ('capability_results', 'assessment_results', 'strict_results'))
        for descriptor in descriptors:
            target = self.folder / descriptor['path']
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source_folder / descriptor['path'], target)
        self.edition = {'version': edition['version'],
                        'result_corrections': {'gemini-4-argon': self.selection}}
        self.select()

    def select(self):
        raw = (json.dumps(self.manifest, ensure_ascii=False) + '\n').encode()
        path = self.root / self.selection['path']
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)
        self.selection.update(bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())
        (self.root / 'benchmark.json').write_text(json.dumps(self.edition))

    def load(self):
        return load_selected(self.root, 'gemini-4-argon', self.folder)

    def test_selected_original_sources_are_consumable(self):
        correction = self.load()
        self.assertEqual(set(correction['_scores']), {'capability', 'partial', 'strict'})
        self.assertFalse(correction['native_status_rewritten'])

    def test_adoption_cannot_change_scoring_rules(self):
        self.manifest['scoring_rules_changed'] = True
        self.select()
        with self.assertRaisesRegex(ValueError, 'Invalid selected'):
            self.load()

    def test_selected_source_cannot_be_silently_repaired(self):
        with (self.folder / self.manifest['answer']['path']).open('ab') as output:
            output.write(b'\nRepaired proof.')
        with self.assertRaises(ValueError):
            self.load()

    def test_unrelated_task_cannot_change_through_erratum(self):
        descriptor = self.manifest['public_tasks']
        path = self.folder / descriptor['path']
        tasks = json.loads(path.read_bytes())
        rows = tasks['views']['partial']['nonlogical_retry_3']['tasks']
        next(row for row in rows if row['case_id'] != 'HCH02')['response_sha256'] = '0' * 64
        raw = (json.dumps(tasks) + '\n').encode()
        path.write_bytes(raw)
        descriptor.update(bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())
        self.select()
        with self.assertRaisesRegex(ValueError, 'unrelated answer'):
            self.load()


if __name__ == '__main__':
    unittest.main()
