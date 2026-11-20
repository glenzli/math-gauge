"""Neutral revision source projections and portable return contracts; no models."""

import copy
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
import zipfile

from math_gauge.catalog import Suite, candidate_message
from math_gauge.records import descriptor
from math_gauge.revision_harness import (
    build_revision_request, collect_revision_attempt, export_revision_bundle,
    import_revision_return, inspect_revision_bundle, pack_revision_return,
)

ROOT = Path(__file__).resolve().parents[1]


class NeutralRevisionHarnessTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.public = self.root / 'public'
        self.private = self.root / 'private'
        self.private.mkdir()
        shutil.copytree(ROOT / 'tests/fixtures/runner-suite', self.public / 'cases')
        (self.public / 'protocol').mkdir()
        for name in ('standards', 'invitation'):
            shutil.copyfile(ROOT / f'protocol/neutral-revision-candidate-{name}.md',
                self.public / f'protocol/neutral-revision-candidate-{name}.md')
        self.suite = Suite.load(self.public / 'cases')
        self.reply = self.private / 'first-answer.md'
        self.reply.write_bytes(b'\r\nOriginal answer.\r\nSelf assessment: uncertain.\r\n')
        self.attachment = self.private / 'original-manuscript.md'
        self.attachment.write_bytes(b'Original explicitly delivered file.\r\n')
        case = self.suite.cases['TEST-D001']
        self.selection = dict(model_id='synthetic-fixture', record_id='fixture-only', source_record=None,
            selection=[dict(case_id=case['id'], family_id='fixture-family', subcategory='written-argument',
                source_case=dict(scope='public', **descriptor(self.public, self.suite.case_file(case, case['task']))),
                original_answer=dict(scope='private', **descriptor(self.private, self.reply)),
                original_submission_status='active_final',
                original_answer_attachments=[dict(name=self.attachment.name,
                    source=dict(scope='private', **descriptor(self.private, self.attachment)))],
                response_sha256=descriptor(self.private, self.reply)['sha256'],
                loss_modes=['partial'], first_scores={'partial': 0.9},
                operator_note='PRIVATE-OLD-GRADE-AND-REVIEW-REASON', completed_adoption=None)])
        self.bundle = self.root / 'package'
        self.collection = self.root / 'returns'

    def export(self, selection=None, **kwargs):
        return export_revision_bundle(selection or self.selection, self.public, self.private, self.bundle, **kwargs)

    def request(self, **kwargs):
        value = build_revision_request(self.bundle, 'R001', runtime={'model_label': 'synthetic-fixture',
            'backend_sku': None, 'parameters': {}}, **kwargs)
        path = self.root / 'request.json'
        path.write_text(json.dumps(value, ensure_ascii=False))
        return path, value

    def test_complete_candidate_projection_retains_original_self_assessment_and_files(self):
        manifest = self.export()
        row = manifest['tasks'][0]
        request = build_revision_request(self.bundle, 'R001')
        content = request['messages'][0]['content']
        original = candidate_message(self.suite.request(self.suite.cases['TEST-D001']))
        self.assertIn(original, content)
        self.assertIn(self.reply.read_bytes().decode(), content)
        self.assertIn(self.attachment.read_bytes().decode(), content)
        self.assertEqual((self.bundle / row['previous_answer']['path']).read_bytes(), self.reply.read_bytes())
        candidate_raw = b''.join(path.read_bytes() for path in (self.bundle / 'candidate').rglob('*') if path.is_file())
        self.assertNotIn(b'PRIVATE-OLD-GRADE-AND-REVIEW-REASON', candidate_raw)
        self.assertNotIn(b'loss_modes', candidate_raw)
        self.assertTrue(request['preparation_only'])
        self.assertEqual(request['context_mode'], 'source-bound-replay')
        self.assertEqual(manifest['counts']['ready'], 1)
        self.assertNotIn('path', manifest.get('source_record_sha256') or '')
        self.assertNotIn('original_answer', row['source_selection'])
        self.assertNotIn('first_scores', row['source_selection'])
        with self.assertRaisesRegex(ValueError, 'session identifier'):
            build_revision_request(self.bundle, 'R001', context_mode='native-session-continuation')
        native = build_revision_request(self.bundle, 'R001', context_mode='native-session-continuation',
            source_session_id='fixture-source-session')
        self.assertEqual(native['source_session_id'], 'fixture-source-session')
        self.assertNotIn(self.reply.read_bytes().decode(), native['messages'][0]['content'])

    def test_raw_return_and_attachment_round_trip_is_importable_pending_review(self):
        self.export()
        request, _ = self.request()
        raw = b'\r\nComplete actual final.\r\nSelf assessment: incomplete.\r\n'
        reply = self.root / 'actual-final.md'
        reply.write_bytes(raw)
        delivered = self.root / 'delivered.md'
        delivered.write_bytes(b'Complete delivered file\r\n')
        evidence = self.root / 'native.json'
        evidence.write_bytes(b'{"status":"actual-native-terminal"}\n')
        collect_revision_attempt(self.bundle, self.collection, request, status='normal_final',
            response_path=reply, attachments=[delivered], evidence=[evidence],
            metadata={'backend_sku': None, 'elapsed_seconds': 12})
        archive = self.root / 'return.zip'
        pack_revision_return(self.bundle, self.collection, archive)
        imported = import_revision_return(self.bundle, archive, self.root / 'imported')
        self.assertEqual(imported['returned_tasks'], 1)
        self.assertFalse(imported['scores_changed'])
        self.assertFalse(imported['runtime_certification'])
        self.assertFalse(imported['human_mathematical_approval'])
        record = imported['records'][0]
        self.assertEqual(record['case_id'], 'TEST-D001')
        self.assertEqual(record['review_status'], 'pending_mathematical_and_operational_review')
        base = self.root / 'imported/original-return'
        self.assertEqual((base / record['normal_final']['path']).read_bytes(), raw)
        self.assertEqual((base / record['attempts'][0]['attachments'][0]['source']['path']).read_bytes(), delivered.read_bytes())
        with self.assertRaisesRegex(ValueError, 'first effective attempt'):
            collect_revision_attempt(self.bundle, self.collection, request, status='normal_final', response_path=reply)

    def test_cutoff_history_remains_nonfinal_and_output_exhaustion_cannot_retry(self):
        selection = copy.deepcopy(self.selection)
        selection['selection'][0]['original_submission_status'] = 'forced_content'
        selection['selection'][0]['response_sha256'] = None
        self.export(selection)
        request, value = self.request()
        self.assertIn('原请求没有正常最终交卷', value['messages'][0]['content'])
        self.assertIsNone(value['source_response_sha256'])
        self.assertEqual(value['source_original_text_sha256'], descriptor(self.private, self.reply)['sha256'])
        attempt = collect_revision_attempt(self.bundle, self.collection, request, status='maximum_output_exhausted')
        self.assertIsNone(attempt['response'])
        with self.assertRaisesRegex(ValueError, 'maximum-output retry'):
            collect_revision_attempt(self.bundle, self.collection, request, status='cutoff_without_final')

    def test_proven_system_failure_keeps_physical_number_then_one_effective_attempt(self):
        self.export()
        request, _ = self.request()
        with self.assertRaisesRegex(ValueError, 'confirmation and native evidence'):
            collect_revision_attempt(self.bundle, self.collection, request, status='system_only_failure')
        evidence = self.root / 'failure.json'
        evidence.write_bytes(b'{"source":"synthetic-confirmed-system-only"}')
        failed = collect_revision_attempt(self.bundle, self.collection, request, status='system_only_failure',
            evidence=[evidence], metadata={'pure_system_failure_confirmed': True})
        self.assertIsNone(failed['effective_attempt_number'])
        final = collect_revision_attempt(self.bundle, self.collection, request, status='normal_final', response_path=self.reply)
        self.assertEqual(final['physical_request_number'], 2)
        self.assertEqual(final['effective_attempt_number'], 1)

    def test_missing_original_completed_and_excluded_tasks_do_not_create_new_requests(self):
        selection = copy.deepcopy(self.selection)
        missing = selection['selection'][0]
        missing['original_answer'] = None
        completed = copy.deepcopy(self.selection['selection'][0])
        completed['completed_adoption'] = {'path': 'opaque-existing-adoption'}
        selection['selection'].append(completed)
        manifest = self.export(selection)
        self.assertEqual(manifest['counts']['source_unavailable'], 1)
        self.assertEqual(manifest['counts']['completed_reused'], 1)
        self.assertFalse((self.bundle / 'candidate/tasks').exists())
        with self.assertRaisesRegex(ValueError, 'not ready'):
            build_revision_request(self.bundle, 'R001')
        other = self.root / 'excluded'
        excluded = export_revision_bundle(self.selection, self.public, self.private, other, exclude=True)
        self.assertEqual(excluded['counts']['excluded_partial'], 1)

    def test_source_binding_and_private_output_boundary_are_enforced(self):
        selection = copy.deepcopy(self.selection)
        selection['selection'][0]['source_case']['sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'bytes changed'):
            self.export(selection)
        with self.assertRaisesRegex(ValueError, 'public repository'):
            export_revision_bundle(self.selection, self.public, self.private, self.public / 'private-package')

    def test_known_blank_failure_can_continue_without_fabricating_original_text(self):
        selection = copy.deepcopy(self.selection)
        row = selection['selection'][0]
        row.update(original_answer=None, response_sha256=None, original_submission_status='blank',
            original_answer_attachments=[])
        manifest = self.export(selection)
        self.assertEqual(manifest['counts']['ready'], 1)
        self.assertIsNone(manifest['tasks'][0]['previous_answer'])
        self.assertFalse((self.bundle / 'candidate/tasks/R001/previous-answer.md').exists())
        request = build_revision_request(self.bundle, 'R001')
        self.assertIn('没有可提供的原答正文', request['messages'][0]['content'])
        self.assertIsNone(request['source_response_sha256'])

    def test_missing_delivered_attachment_never_exports_partial_original_context(self):
        self.attachment.unlink()
        manifest = self.export()
        self.assertEqual(manifest['counts']['source_unavailable'], 1)
        self.assertFalse((self.bundle / 'candidate/tasks').exists())

    def test_relocated_stdlib_controller_checks_requests_collects_and_imports(self):
        self.export()
        moved = self.root / 'moved'
        shutil.move(self.bundle, moved)
        self.bundle = moved
        helper = self.bundle / 'tools/revision.py'
        command = [sys.executable, '-I', str(helper)]
        runtime = self.root / 'runtime.json'
        runtime.write_text('{"model_label":"synthetic-fixture","backend_sku":null}')
        request = self.root / 'issued.json'
        archive = self.root / 'portable-return.zip'
        imported = self.root / 'portable-import'
        actions = [
            ['check'],
            ['request', '--task', 'R001', '--runtime', str(runtime), '--out', str(request)],
            ['collect', '--returns', str(self.collection), '--request', str(request), '--status', 'normal_final', '--response', str(self.reply)],
            ['pack', '--returns', str(self.collection), '--out', str(archive)],
            ['import', '--archive', str(archive), '--out', str(imported)],
        ]
        for action in actions:
            result = subprocess.run(command + action, cwd=self.root, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads((imported / 'import.json').read_bytes())['returned_tasks'], 1)
        inspect_revision_bundle(self.bundle)

    def test_archive_paths_and_missing_normal_final_are_rejected(self):
        self.export()
        request, _ = self.request()
        with self.assertRaisesRegex(ValueError, 'full actual text'):
            collect_revision_attempt(self.bundle, self.collection, request, status='normal_final')
        archive = self.root / 'unsafe.zip'
        with zipfile.ZipFile(archive, 'x') as stream:
            stream.writestr('../outside.md', b'not permitted')
        with self.assertRaises(ValueError):
            import_revision_return(self.bundle, archive, self.root / 'rejected')
        self.assertFalse((self.root / 'outside.md').exists())


if __name__ == '__main__':
    unittest.main()
