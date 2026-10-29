import copy
import json
import os
import shutil
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from math_gauge.catalog import (Suite, candidate_message, digest_bytes, read_json,
                                validate_alignment_manifest, write_json)
from math_gauge.execution import (extract_candidate_alignment, run,
                                  validate_alignment_audit, verify_candidate_lean)
from math_gauge.review import apply_reviews, report, templates

ROOT = Path(__file__).resolve().parents[1]


class QuestionGroupContracts(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.suite_path = self.root / 'suite'
        shutil.copytree(ROOT / 'archive/legacy-v0/public', self.suite_path)
        self.cid = 'MG-D001'
        self.case_path = self.suite_path / self.cid / 'case.json'
        self.case = read_json(self.case_path)
        self.case['group_contract'] = self.cid + '/group.json'
        self.contract_path = self.suite_path / self.case['group_contract']
        self.contract = {
            'schema': 'math-gauge.group-contract/v1', 'id': self.cid,
            'kind': 'progressive', 'stages': [
                {'id': 'S' + str(i), 'title': 'fixture', 'kind': 'decide',
                 'depends_on': ['S' + str(i-1)] if i > 1 else [],
                 'assumptions': ['finite set'], 'expected': 'true',
                 'required_evidence': ['an explicit proof'],
                 'critical_errors': ['changing the quantified set'],
                 'points': 20, 'lean_required': False}
                for i in range(1, 6)],
            'turns': [{'stage_id': 'S4', 'earlier_stage_ids': ['S3'],
                       'changed_assumptions': 'test fixture change', 'expected_truth': 'true',
                       'mechanism': 'test fixture', 'tempting_invalid_transfer': 'test fixture',
                       'correct_boundary': 'test fixture'}]}
        self.save()

    def save(self):
        write_json(self.case_path, self.case)
        write_json(self.contract_path, self.contract)

    def replay(self, response='This is a transport fixture, not a model answer.'):
        self.save()
        suite = Suite.load(self.suite_path)
        responses = self.root / 'responses.json'
        write_json(responses, {self.cid: response})
        self.run_path = self.root / 'run'
        run(suite, self.run_path, [self.cid], replay=responses)
        return self.run_path

    def passing(self):
        e = templates(self.run_path)[0]
        e.update(reviewer='unit fixture', reviewer_kind='fixture', decision='pass',
                 assumption_fidelity='clean', proof_validity='valid', scope_accuracy='correct',
                 notes='Synthetic transport checks only, not a mathematical review.')
        for s in e['stages']:
            s.update(decision='pass', assumption_fidelity='clean', proof_validity='valid',
                     scope_accuracy='correct', failure_category='none', notes='Synthetic fixture proof.')
        return e

    def alignment(self):
        self.contract.update(alignment_manifest_required=True, version=self.case['version'])
        for stage in self.contract['stages']:
            stage['lean_required'] = True
        return {'case_id': self.cid, 'version': self.case['version'], 'items': [
            {'id': s['id'], 'status': 'complete',
             'declarations': [{'file': 'Main.lean', 'name': 'groupAnswer'}],
             'representation': 'Synthetic fixture mapping.', 'dependencies': []}
            for s in self.contract['stages']]}

    def alignment_response(self, manifest):
        return ('```lean filename=Main.lean\ntheorem groupAnswer : True := True.intro\n```\n'
                '```json filename=alignment.json\n' + json.dumps(manifest) + '\n```\n')

    def alignment_receipt_fixture(self, response):
        """Synthetic bookkeeping evidence only; excluded from model comparisons."""
        record = read_json(self.run_path/self.cid/'record.json')
        manifest, span, _ = extract_candidate_alignment(response)
        receipt = {'schema': 'math-gauge.candidate-lean/v1', 'case_id': self.cid,
                   'response_sha256': record['response_sha256'], 'request_sha256': record['request_sha256'],
                   'group_contract_sha256': record['group_contract_sha256'],
                   'status': 'passed', 'source_repaired': False, 'fixture_only': True,
                   'files_sha256': {'Main.lean': 'fixture'},
                   'audit': {'declarations': [{'module': 'Main', 'name': 'groupAnswer'},
                                               {'module': 'Main', 'name': 'otherAnswer'}]},
                   'alignment_manifest': manifest, 'alignment_source_span': span,
                   'alignment_manifest_sha256': span['sha256'], 'alignment_inventory_validated': True}
        path = self.run_path/'lean-fixture.json'; write_json(path, receipt)
        e = self.passing()
        for row in e['stages']:
            row.update(lean_status='passed', declarations=[{'file': 'Main.lean', 'name': 'groupAnswer'}])
        e.update(candidate_lean_report='lean-fixture.json', candidate_lean_report_sha256=digest_bytes(path.read_bytes()))
        return e, receipt, path

    def test_alignment_requires_exact_coverage_and_identity(self):
        manifest = self.alignment()
        for mutate in [lambda x: x.update(case_id='another'), lambda x: x.update(version='another'),
                       lambda x: x['items'].pop(), lambda x: x['items'].__setitem__(1, x['items'][0]),
                       lambda x: x['items'][0].update(status='proved'),
                       lambda x: x['items'][0].update(declarations=[]),
                       lambda x: x['items'][0].update(dependencies=['unknown'])]:
            broken = copy.deepcopy(manifest); mutate(broken)
            with self.assertRaises(ValueError):
                validate_alignment_manifest(broken, self.contract)
        manifest['items'].reverse()  # No compulsory reference proof order.
        validate_alignment_manifest(manifest, self.contract)

    def test_alignment_extraction_is_exact_and_ignores_nested_fences(self):
        manifest = self.alignment()
        body = json.dumps(manifest, ensure_ascii=False) + '\n'
        response = '前言\n````text\n```json filename=alignment.json\n{}\n```\n````\n'
        response += '```json filename=alignment.json\n' + body + '```\n'
        parsed, span, raw = extract_candidate_alignment(response)
        self.assertEqual(parsed, manifest)
        self.assertEqual(raw, body.encode())
        self.assertEqual(response.encode()[span['start_byte']:span['end_byte']], raw)
        for broken in [response + response,
                       '```json filename=alignment.json\n{"items":[],"items":[]}\n```\n',
                       '```json filename=alignment.json\n{}']:
            with self.assertRaises(ValueError):
                extract_candidate_alignment(broken)

    def test_missing_alignment_is_rejected_before_compilation(self):
        self.alignment()
        self.replay('```lean filename=Main.lean\ndef answer := 1\n```\n')
        receipt = verify_candidate_lean(self.run_path/self.cid, self.root/'verify', dependency_root=self.root/'absent')
        self.assertEqual(receipt['status'], 'format_error')
        self.assertIn('alignment.json', receipt['reason'])
        self.assertNotIn('engine_identity', receipt)

    def test_incomplete_alignment_cannot_be_promoted_by_reviewer(self):
        manifest = self.alignment(); manifest['items'][-1]['status'] = 'incomplete'
        response = self.alignment_response(manifest); self.replay(response)
        e, _, _ = self.alignment_receipt_fixture(response)
        with self.assertRaisesRegex(ValueError, 'incomplete'):
            apply_reviews(self.run_path, [e])
        e['decision'] = 'partial'
        e['stages'][-1].update(decision='partial', failure_category='unresolved')
        apply_reviews(self.run_path, [e])
        self.assertEqual(report(self.run_path)[0]['group_diagnostics'][self.cid]['stage_passes'], 4)

    def test_alignment_cannot_be_replaced_by_a_different_reviewer_mapping(self):
        manifest = self.alignment(); response = self.alignment_response(manifest); self.replay(response)
        e, receipt, path = self.alignment_receipt_fixture(response)
        e['stages'][-1]['declarations'][0]['name'] = 'otherAnswer'  # Audited, but not the candidate mapping.
        with self.assertRaisesRegex(ValueError, 'differ from candidate'):
            apply_reviews(self.run_path, [e])
        e['stages'][-1]['declarations'][0]['name'] = 'groupAnswer'
        receipt['alignment_manifest']['items'][-1]['representation'] = 'Changed after extraction'
        write_json(path, receipt); e['candidate_lean_report_sha256'] = digest_bytes(path.read_bytes())
        with self.assertRaisesRegex(ValueError, 'bind the candidate'):
            apply_reviews(self.run_path, [e])

    def test_alignment_claims_must_exist_in_the_compiled_inventory(self):
        manifest = self.alignment()
        receipt = {'files_sha256': {'Main.lean': 'fixture'},
                   'audit': {'declarations': [{'module': 'Main', 'name': 'otherAnswer'}]}}
        with self.assertRaisesRegex(ValueError, 'not audited'):
            validate_alignment_audit(manifest, self.contract, receipt)

    def test_lean_receipt_cannot_cross_group_contracts(self):
        manifest = self.alignment()
        response = self.alignment_response(manifest)
        self.replay(response)
        old_record = read_json(self.run_path/self.cid/'record.json')
        self.contract['required_output_files'] = ['Main.lean']
        self.save()
        self.run_path = self.root/'stronger-contract-run'
        run(Suite.load(self.suite_path), self.run_path, [self.cid],
            replay=self.root/'responses.json')
        record = read_json(self.run_path/self.cid/'record.json')
        self.assertEqual(record['request_sha256'], old_record['request_sha256'])
        self.assertEqual(record['response_sha256'], old_record['response_sha256'])
        self.assertNotEqual(record['group_contract_sha256'], old_record['group_contract_sha256'])
        entry, receipt, path = self.alignment_receipt_fixture(response)
        for value in (old_record['group_contract_sha256'], None):
            with self.subTest(contract_hash=value):
                if value is None:
                    receipt.pop('group_contract_sha256', None)
                else:
                    receipt['group_contract_sha256'] = value
                write_json(path, receipt)
                entry['candidate_lean_report_sha256'] = digest_bytes(path.read_bytes())
                with self.assertRaisesRegex(ValueError, 'group contract'):
                    apply_reviews(self.run_path, [entry])
                self.assertFalse((self.run_path/'reviews.json').exists())
        receipt['group_contract_sha256'] = record['group_contract_sha256']
        write_json(path, receipt)
        entry['candidate_lean_report_sha256'] = digest_bytes(path.read_bytes())
        apply_reviews(self.run_path, [entry])
        self.assertEqual(report(self.run_path)[0]['group_diagnostics'][self.cid]['stage_passes'], 5)

    def test_candidate_manifest_freezes_group_contract_before_compilation(self):
        manifest = self.alignment()
        self.replay(self.alignment_response(manifest))
        record = read_json(self.run_path/self.cid/'record.json')
        with patch('math_gauge.execution.sys.platform', 'unsupported'):
            receipt = verify_candidate_lean(self.run_path/self.cid, self.root/'verify',
                                            dependency_root=self.root/'absent')
        self.assertEqual(receipt['status'], 'infrastructure_error')
        self.assertEqual(receipt['group_contract_sha256'], record['group_contract_sha256'])
        artifact = read_json(self.root/'verify/manifest.json')
        self.assertEqual(artifact['group_contract_sha256'], record['group_contract_sha256'])
        self.assertEqual(receipt['artifact_sha256'], digest_bytes((self.root/'verify/manifest.json').read_bytes()))

    def test_nested_projection_is_exact_and_contract_is_hidden(self):
        source = self.suite_path / self.cid / 'Background.lean'
        source.write_text('def backgroundValue := 1\n')
        self.case['solver_files'] = [{'source': self.cid+'/Background.lean', 'target': 'Math/Background.lean'}]
        self.save()
        suite = Suite.load(self.suite_path)
        request = suite.prepare(suite.cases[self.cid], self.root/'solver')
        self.assertEqual((self.root/'solver/Math/Background.lean').read_bytes(), source.read_bytes())
        self.assertIn('Math/Background.lean', candidate_message(request))
        self.assertNotIn('tempting_invalid_transfer', json.dumps(request))
        self.case['solver_files'].append({'source': self.case['group_contract'], 'target': 'leak.json'})
        self.save()
        with self.assertRaisesRegex(ValueError, 'rubric'):
            Suite.load(self.suite_path)

    def test_nested_target_collisions_and_traversal_are_rejected(self):
        for name in ['prompt.md/sub.lean', '../Escape.lean', '.', 'request.json/file']:
            with self.subTest(name=name):
                self.case['solver_files'] = [{'source': self.case['task'], 'target': name}]
                self.save()
                with self.assertRaises(ValueError):
                    Suite.load(self.suite_path)
        for targets in [('a', 'a/b'), ('A/B.lean', 'a/b.lean')]:
            self.case['solver_files'] = [{'source': self.case['task'], 'target': name} for name in targets]
            self.save()
            with self.assertRaises(ValueError):
                Suite.load(self.suite_path)

    def test_forward_dependencies_and_wrong_turn_truth_are_rejected(self):
        self.contract['stages'][0]['depends_on'] = ['S5']
        self.save()
        with self.assertRaisesRegex(ValueError, 'earlier'):
            Suite.load(self.suite_path)
        self.contract['stages'][0]['depends_on'] = []
        self.contract['turns'][0]['expected_truth'] = 'false'
        self.save()
        with self.assertRaisesRegex(ValueError, 'truth'):
            Suite.load(self.suite_path)
        self.contract['turns'][0].update(scope='subclaim')
        self.save()
        with self.assertRaisesRegex(ValueError, 'explicit target'):
            Suite.load(self.suite_path)
        self.contract['turns'][0]['target_claim'] = 'The stage also asks whether an extra converse is valid.'
        self.save()
        Suite.load(self.suite_path)

    def test_missing_stage_cannot_be_hidden_by_overall_pass(self):
        self.replay(); e = self.passing(); e['stages'].pop()
        with self.assertRaisesRegex(ValueError, 'every frozen stage'):
            apply_reviews(self.run_path, [e])
        self.assertFalse((self.run_path/'reviews.json').exists())

    def test_stage_drift_prevents_pass_and_saved_reviews_are_rechecked(self):
        self.replay(); e = self.passing()
        e['stages'][3]['assumption_fidelity'] = 'drift'
        with self.assertRaisesRegex(ValueError, 'contradicts'):
            apply_reviews(self.run_path, [e])
        e['stages'][3]['assumption_fidelity'] = 'clean'
        apply_reviews(self.run_path, [e])
        saved = read_json(self.run_path/'reviews.json')
        saved[self.cid]['stages'][3]['assumption_fidelity'] = 'drift'
        write_json(self.run_path/'reviews.json', saved)
        with self.assertRaisesRegex(ValueError, 'contradicts'):
            report(self.run_path)

    def test_group_contract_is_frozen_and_cannot_be_removed(self):
        self.replay()
        self.contract['stages'][0]['points'] = 200
        self.save()  # Later suite edits must not alter the run's contract.
        self.assertEqual(len(templates(self.run_path)[0]['stages']), 5)
        meta = read_json(self.run_path/'run.json')
        del meta['cases'][0]['group_contract']
        write_json(self.run_path/'run.json', meta)
        with self.assertRaisesRegex(ValueError, 'binding'):
            templates(self.run_path)

    def test_group_cannot_drop_candidate_message_bindings(self):
        self.replay()
        for path, nested in ((self.run_path/'run.json', True),
                             (self.run_path/self.cid/'record.json', False)):
            saved = read_json(path)
            changed = copy.deepcopy(saved)
            descriptor = changed['cases'][0] if nested else changed
            descriptor.pop('candidate_message_sha256')
            write_json(path, changed)
            with self.subTest(path=path), self.assertRaisesRegex(ValueError, 'message binding'):
                templates(self.run_path)
            write_json(path, saved)
        self.assertEqual(len(templates(self.run_path)[0]['stages']), 5)

    def test_changed_frozen_contract_and_stale_review_are_rejected(self):
        self.replay(); e = self.passing()
        e['group_contract_sha256'] = '0'*64
        with self.assertRaisesRegex(ValueError, 'different group'):
            apply_reviews(self.run_path, [e])
        path = self.run_path/self.cid/'review-contract.json'
        path.write_text(path.read_text()+' ')
        with self.assertRaisesRegex(ValueError, 'contract changed'):
            templates(self.run_path)

    def test_lean_pass_requires_bound_unrepaired_evidence(self):
        self.contract['stages'][-1]['lean_required'] = True
        self.replay(); e = self.passing(); e['stages'][-1]['lean_status'] = 'passed'
        with self.assertRaises(ValueError):
            apply_reviews(self.run_path, [e])
        record = read_json(self.run_path/self.cid/'record.json')
        receipt = {'schema': 'math-gauge.candidate-lean/v1', 'case_id': self.cid,
                   'response_sha256': record['response_sha256'], 'request_sha256': record['request_sha256'],
                   'group_contract_sha256': record['group_contract_sha256'],
                   'status': 'passed', 'source_repaired': True, 'fixture_only': True}
        path = self.run_path/'lean-fixture.json'
        write_json(path, receipt)
        e.update(candidate_lean_report='lean-fixture.json', candidate_lean_report_sha256=digest_bytes(path.read_bytes()))
        with self.assertRaisesRegex(ValueError, 'unrepaired'):
            apply_reviews(self.run_path, [e])
        receipt['source_repaired'] = False; receipt['request_sha256'] = '0'*64
        write_json(path, receipt); e['candidate_lean_report_sha256'] = digest_bytes(path.read_bytes())
        with self.assertRaisesRegex(ValueError, 'unrepaired'):
            apply_reviews(self.run_path, [e])

    def test_immutable_background_cannot_be_replaced_before_compiling(self):
        source = self.suite_path/self.cid/'Background.lean'; source.write_text('def a := 1\n')
        self.case['solver_files'] = [{'source': self.cid+'/Background.lean', 'target': 'Base/Background.lean'}]
        self.contract['immutable_input_files'] = ['Base/Background.lean']
        self.replay('```lean filename=Base/Background.lean\ndef a := 2\n```\n')
        result = verify_candidate_lean(self.run_path/self.cid, self.root/'verify', dependency_root=self.root/'absent')
        self.assertEqual(result['status'], 'format_error')
        self.assertIn('cannot be replaced', result['reason'])

    def test_stage_maps_only_to_audited_submitted_declarations(self):
        self.contract['stages'][-1]['lean_required'] = True
        self.replay(); e = self.passing(); row = e['stages'][-1]
        row['lean_status'] = 'passed'
        record = read_json(self.run_path/self.cid/'record.json')
        receipt = {'schema': 'math-gauge.candidate-lean/v1', 'case_id': self.cid,
                   'response_sha256': record['response_sha256'], 'request_sha256': record['request_sha256'],
                   'group_contract_sha256': record['group_contract_sha256'],
                   'status': 'passed', 'source_repaired': False, 'fixture_only': True,
                   'files_sha256': {'Main.lean': 'fixture'},
                   'audit': {'declarations': [{'module': 'Main', 'name': 'Fixture.answer'}]}}
        path = self.run_path/'lean-fixture.json'; write_json(path, receipt)
        e.update(candidate_lean_report='lean-fixture.json', candidate_lean_report_sha256=digest_bytes(path.read_bytes()))
        row['declarations'] = [{'file': 'Main.lean', 'name': 'Fixture.missing'}]
        with self.assertRaisesRegex(ValueError, 'not audited'):
            apply_reviews(self.run_path, [e])
        row['declarations'] = [{'file': 'Main.lean', 'name': 'Fixture.answer'}]
        apply_reviews(self.run_path, [e])
        self.assertEqual(report(self.run_path)[0]['group_diagnostics'][self.cid]['stage_passes'], 5)

    def test_required_project_entrypoint_is_enforced_before_compiling(self):
        self.contract['required_output_files'] = ['Main.lean']
        self.replay('```lean filename=Other.lean\ndef a := 2\n```\n')
        result = verify_candidate_lean(self.run_path/self.cid, self.root/'verify', dependency_root=self.root/'absent')
        self.assertEqual(result['status'], 'format_error')
        self.assertIn('Main.lean', result['reason'])

    def test_diagnostics_separate_root_failure_and_dependents(self):
        self.replay(); e = self.passing(); e['decision'] = 'partial'
        for i in (1, 2):
            e['stages'][i].update(decision='fail', proof_validity='invalid', failure_category='mathematical')
        e['stages'][2]['inherited_from'] = ['S2']
        apply_reviews(self.run_path, [e]); result, _ = report(self.run_path)
        d = result['group_diagnostics'][self.cid]
        self.assertEqual(d['root_failures'], ['S2'])
        self.assertEqual(d['completed_weight'], 60)
        self.assertEqual(result['tracks']['determinate']['eligible_for_model_comparison'], 0)

    def test_passed_stage_cannot_be_labeled_a_failure_source(self):
        self.replay(); e = self.passing(); e['decision'] = 'partial'
        e['stages'][1].update(decision='fail', proof_validity='invalid', failure_category='mathematical', inherited_from=['S1'])
        with self.assertRaisesRegex(ValueError, 'passed stage'):
            apply_reviews(self.run_path, [e])

    @unittest.skipUnless(sys.platform == 'darwin' and os.environ.get('MATH_GAUGE_CANDIDATE_DEPENDENCIES'),
                         'Set candidate dependency root for the isolated group compiler acceptance test')
    def test_nested_group_compiles_and_review_binds_real_audit(self):
        source = self.suite_path/self.cid/'Background.lean'
        source.write_text('def backgroundValue : Nat := 7\n')
        self.case['solver_files'] = [{'source': self.cid+'/Background.lean', 'target': 'Base/Background.lean'}]
        self.contract.update(immutable_input_files=['Base/Background.lean'], required_output_files=['Main.lean'])
        manifest = self.alignment()
        self.contract['stages'][-2].update(lean_required=True, allow_background_declarations=True)
        manifest['items'][-2]['declarations'] = [{'file': 'Base/Background.lean', 'name': 'backgroundValue'}]
        self.replay('```lean filename=Main.lean\nimport Base.Background\ntheorem groupAnswer : backgroundValue = 7 := rfl\n```\n'
                    '```json filename=alignment.json\n' + json.dumps(manifest) + '\n```\n')
        receipt = verify_candidate_lean(self.run_path/self.cid, self.run_path/'candidate-validation',
                                        dependency_root=os.environ['MATH_GAUGE_CANDIDATE_DEPENDENCIES'], timeout=60)
        self.assertEqual(receipt['status'], 'passed', receipt)
        self.assertEqual(receipt['group_contract_sha256'],
                         read_json(self.run_path/self.cid/'record.json')['group_contract_sha256'])
        self.assertEqual(read_json(self.run_path/'candidate-validation/manifest.json')['group_contract_sha256'],
                         receipt['group_contract_sha256'])
        e = self.passing()
        for row in e['stages']:
            row.update(lean_status='passed', declarations=[{'file': 'Main.lean', 'name': 'groupAnswer'}])
        e['stages'][-2].update(lean_status='passed', declarations=[{'file': 'Base/Background.lean', 'name': 'backgroundValue'}])
        e.update(candidate_lean_report='candidate-validation/report.json',
                 candidate_lean_report_sha256=digest_bytes((self.run_path/'candidate-validation/report.json').read_bytes()))
        apply_reviews(self.run_path, [e])
        result, _ = report(self.run_path)
        self.assertEqual(result['group_diagnostics'][self.cid]['stage_passes'], 5)
        self.assertEqual(result['tracks']['determinate']['eligible_for_model_comparison'], 0)


if __name__ == '__main__':
    unittest.main()
