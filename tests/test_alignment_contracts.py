"""Alignment case identifiers retain the shared formal evidence contract."""
import importlib.util
import json
from pathlib import Path
import unittest


_spec = importlib.util.spec_from_file_location(
    'alignment_formal_fixtures', Path(__file__).with_name('test_formal_verifier.py'))
_fixtures = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_fixtures)
V = _fixtures.V


class AlignmentFormalContracts(_fixtures.FixtureMixin, unittest.TestCase):
    def test_alignment_identifier_keeps_frozen_input_and_source_checks(self):
        path, data = self.fixture()
        data['case_id'] = 'MG-F101'
        path.write_text(json.dumps(data))
        manifest, *_ = V.validate_case(path)
        self.assertEqual(manifest['case_id'], 'MG-F101')
        (self.root/'Example.lean').write_text('namespace MathGauge.Fixture\ndef value := 2\nend MathGauge.Fixture\n')
        with self.assertRaisesRegex(V.VerificationError, 'Source SHA256 mismatch'):
            V.validate_case(path)

    def test_alignment_identifier_cannot_escape_its_output_directory(self):
        path, data = self.fixture()
        for identifier in ('MG-F101/other', '../MG-F101', 'MG-F101..', 'MG-F101\\other'):
            with self.subTest(identifier=identifier):
                data['case_id'] = identifier
                path.write_text(json.dumps(data))
                with self.assertRaisesRegex(V.VerificationError, 'Invalid case id'):
                    V.validate_case(path)


if __name__ == '__main__':
    unittest.main()
