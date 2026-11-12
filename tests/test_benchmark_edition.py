"""Edition reuse preserves source bytes, complete score views and safe paths."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from math_gauge.editions import result_archive, verify_compatibility


class EditionCompatibilityTests(unittest.TestCase):
    def fixture(self, root):
        edition = dict(version='1.0.0', selected_result_record_ids={'model': 'snapshot'},
            result_compatibility=dict(source_benchmark_version='0.6.0',
                archive_root='results/v0.6.0', path='releases/v1.0.0/compatibility.json',
                new_candidate_calls=0, mathematical_judgments_changed=False))
        records, bindings = [], []
        for model, rid in [('model', 'snapshot'), ('dot-underlying-model-20261108', '20261108')]:
            parent = f'results/v0.6.0/{model}/{rid}/'
            names = [parent + 'record.json'] + [parent + f'view{n}.json' for n in range(6)]
            for name in names:
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(b'original source bytes')
                bindings.append(dict(path=name, sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
            records.append(dict(model_id=model, record_id=rid, record_path=names[0], score_paths=names[1:]))
        manifest = dict(schema='math-gauge.edition-compatibility/v1', benchmark_version='1.0.0',
            source_benchmark_version='0.6.0', archive_root='results/v0.6.0', new_candidate_calls=0,
            mathematical_judgments_changed=False,
            counts=dict(public_a1=25, private_a1=14, combined_a1=39, mathematical_families=35, c003_rounds=3),
            selected_records=records, source_bindings=bindings)
        (root / 'releases/v1.0.0').mkdir(parents=True)
        (root / 'benchmark.json').write_text(json.dumps(edition))
        path = root / edition['result_compatibility']['path']
        path.write_text(json.dumps(manifest))
        return edition, manifest, path

    def test_original_archive_identity_survives_the_new_edition(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            edition, _, _ = self.fixture(root)
            self.assertEqual(verify_compatibility(root), edition)
            self.assertEqual(result_archive(edition), 'results/v0.6.0')
            self.assertEqual(result_archive(dict(version='0.6.0')), 'results/v0.6.0')

    def test_reuse_rejects_changed_original_bytes_and_missing_score_views(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            _, manifest, path = self.fixture(root)
            source = root / manifest['source_bindings'][0]['path']
            source.write_bytes(b'changed answer')
            with self.assertRaisesRegex(ValueError, 'source changed'):
                verify_compatibility(root)
            source.write_bytes(b'original source bytes')
            manifest['selected_records'][0]['score_paths'].pop()
            path.write_text(json.dumps(manifest))
            with self.assertRaisesRegex(ValueError, 'six views'):
                verify_compatibility(root)

    def test_unbound_selection_and_unsafe_adoption_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            edition, _, _ = self.fixture(root)
            edition['selected_result_record_ids']['model'] = 'another-answer'
            (root / 'benchmark.json').write_text(json.dumps(edition))
            with self.assertRaisesRegex(ValueError, 'every selected record'):
                verify_compatibility(root)
            edition['result_compatibility']['archive_root'] = '../private'
            with self.assertRaisesRegex(ValueError, 'compatibility boundary'):
                result_archive(edition)
