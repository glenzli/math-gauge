"""New execution editions coexist with byte-bound adopted result archives."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from math_gauge.editions import result_archive, verify_compatibility
from math_gauge.records import selected_cli_records


class SelectedSourceEditionTests(unittest.TestCase):
    def fixture(self, root):
        edition = dict(version='1.0.0', selected_result_models=['legacy', 'fresh'],
            selected_result_record_ids={'legacy': 'old', 'fresh': 'new'},
            selected_result_source_versions={'fresh': '1.0.0'},
            result_compatibility=dict(source_benchmark_version='0.6.0',
                archive_root='results/v0.6.0', path='releases/v1.0.0/compatibility.json',
                new_candidate_calls=0, mathematical_judgments_changed=False))
        adopted, bindings = [], []
        for model, rid in [('legacy', 'old'), ('dot-underlying-model-20261108', '20261108')]:
            parent = f'results/v0.6.0/{model}/{rid}/'
            names = [parent + 'record.json'] + [parent + f'view{n}.json' for n in range(6)]
            for name in names:
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(json.dumps({'benchmark_version': '0.6.0'}))
                bindings.append(dict(path=name, sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
            adopted.append(dict(model_id=model, record_id=rid, record_path=names[0], score_paths=names[1:]))
        fresh = root / 'results/v1.0.0/fresh/new/record.json'
        fresh.parent.mkdir(parents=True)
        fresh.write_text(json.dumps({'benchmark_version': '1.0.0'}))
        manifest = dict(schema='math-gauge.edition-compatibility/v1', benchmark_version='1.0.0',
            source_benchmark_version='0.6.0', archive_root='results/v0.6.0', new_candidate_calls=0,
            mathematical_judgments_changed=False,
            counts=dict(public_a1=25, private_a1=14, combined_a1=39, mathematical_families=35, c003_rounds=3),
            selected_records=adopted, source_bindings=bindings)
        path = root / edition['result_compatibility']['path']
        path.parent.mkdir(parents=True)
        path.write_text(json.dumps(manifest))
        (root / 'benchmark.json').write_text(json.dumps(edition))
        return edition, fresh, path

    def test_new_run_uses_current_archive_without_rewriting_adoption_manifest(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            edition, _, path = self.fixture(root)
            original = path.read_bytes()
            self.assertEqual(verify_compatibility(root), edition)
            self.assertEqual(result_archive(edition, 'legacy'), 'results/v0.6.0')
            self.assertEqual(result_archive(edition, 'fresh'), 'results/v1.0.0')
            selected = dict(selected_cli_records(root))
            self.assertEqual(selected['fresh'], root / 'results/v1.0.0/fresh/new')
            self.assertEqual(path.read_bytes(), original)

    def test_new_source_mapping_cannot_relocate_legacy_or_escape_edition(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            edition, fresh, _ = self.fixture(root)
            for value in ('0.6.0', '../private', '1.0.1'):
                changed = dict(edition, selected_result_source_versions={'fresh': value})
                with self.subTest(value=value), self.assertRaises(ValueError):
                    result_archive(changed, 'fresh')
            edition['selected_result_source_versions']['legacy'] = '1.0.0'
            (root / 'benchmark.json').write_text(json.dumps(edition))
            with self.assertRaisesRegex(ValueError, 'every selected record'):
                verify_compatibility(root)
            del edition['selected_result_source_versions']['legacy']
            (root / 'benchmark.json').write_text(json.dumps(edition))
            fresh.write_text(json.dumps({'benchmark_version': '0.6.0'}))
            with self.assertRaisesRegex(ValueError, 'selected source edition'):
                verify_compatibility(root)
