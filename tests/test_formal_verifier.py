"""Focused contracts for source identity, dependency boundaries and real kernel audits."""
from pathlib import Path
import hashlib
import importlib.util
import json
import os
import shutil
import sys
import tempfile
import unittest
from copy import deepcopy
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('formal_verifier', ROOT/'scripts/formal/verify.py')
V = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(V)
with patch.dict(sys.modules, {'verify': V}):
    E_SPEC = importlib.util.spec_from_file_location('formal_evidence', ROOT/'scripts/formal/check_evidence.py')
    E = importlib.util.module_from_spec(E_SPEC)
    E_SPEC.loader.exec_module(E)
    S_SPEC = importlib.util.spec_from_file_location('formal_suite', ROOT/'scripts/formal/verify_suite.py')
    S = importlib.util.module_from_spec(S_SPEC)
    S_SPEC.loader.exec_module(S)

class FixtureMixin:
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='math-gauge-formal-')
        self.case = Path(self.temp.name)/'case'
        self.root = self.case/'formal';self.root.mkdir(parents=True)
        for name in ('task.md','reference.md','rubric.json'):(self.case/name).write_text('dummy '+name+'\n')
        (self.root/'COVERAGE.md').write_text('Fixture coverage only.\n')
    def tearDown(self):
        self.temp.cleanup()
    def fixture(self, text='namespace MathGauge.Fixture\ndef value : Nat := 1\nend MathGauge.Fixture\n', profile=V.DEFAULT_PROFILE):
        p=self.root/'Example.lean';p.write_text(text)
        audit=self.root/'CurrentAudit.lean';audit.write_text(V.render_audit(['Example'],profile))
        data={'schema':'math-gauge.formal-case/v1','case_id':'MG-TEST-Example','lean_toolchain':V.TOOLCHAIN,'mathlib_revision':V.MATHLIB_REV,'frozen_inputs':{name:V.digest(self.case/name) for name in ('task.md','reference.md','rubric.json')},'coverage':{'source':'COVERAGE.md','sha256':V.digest(self.root/'COVERAGE.md')},'modules':[{'module':'Example','source':p.name,'sha256':V.digest(p),'imports':V.source_imports(text)}],'audit':{'module':'CurrentAudit','source':audit.name,'sha256':V.digest(audit)}}
        if profile != V.DEFAULT_PROFILE:
            config=V.profile_config(profile)
            data.update(verification_profile=profile,lean_toolchain=config['toolchain'],mathlib_revision=config['mathlib_revision'],tauceti_revision=config['tauceti_revision'])
        manifest=self.root/'manifest.json';manifest.write_text(json.dumps(data));return manifest,data
class ManifestTests(FixtureMixin, unittest.TestCase):
    def author_fixture(self, cid='MG-GR001'):
        path, manifest = self.fixture()
        case = {'schema':'math-gauge.case/v1','id':cid,'version':'0.1.1',
                'task':'case/task.md','reference':'case/reference.md',
                'rubric':'case/rubric.json','group_contract':'case/contract.json',
                'solver_files':[{'source':'case/input.lean','target':'Input.lean'}]}
        V.save(self.case/'case.json',case)
        (self.case/'input.lean').write_text('def frozenBackground := 0\n')
        V.save(self.case/'contract.json',{'id':cid,'version':'0.1.1','stages':[{'id':'S1'}]})
        alignment={'schema':'math-gauge.author-alignment/v1','case_id':cid,'case_version':'0.1.1',
                   'items':[{'id':'S1','status':'complete','declarations':[{'module':'Example','name':'MathGauge.Fixture.value'}],
                             'assumptions':'No extra assumptions','quantifiers':'No parameters','domains':'Nat',
                             'conclusions':'Value is one','representation':'Direct natural number definition',
                             'dependencies':[],'gaps':[]}]}
        V.save(self.root/'alignment.json',alignment)
        manifest.update(schema='math-gauge.formal-case/v2',case_id=cid,case_version='0.1.1',
                        frozen_inputs=V.author_frozen_inputs(self.case)[1],
                        alignment={'source':'alignment.json','sha256':V.digest(self.root/'alignment.json')})
        audit=self.root/'CurrentAudit.lean'
        audit.write_text(V.render_audit(['Example'],all_case_declarations=True))
        manifest['audit']['sha256']=V.digest(audit)
        V.save(path,manifest)
        return path,manifest,alignment
    def test_new_paper_binds_contract_and_all_candidate_attachments(self):
        path,_,_=self.author_fixture()
        V.validate_case(path)
        (self.case/'input.lean').write_text('def frozenBackground := 1\n')
        with self.assertRaisesRegex(V.VerificationError,'complete case'):V.validate_case(path)
    def test_new_paper_cannot_use_legacy_contract_or_drop_an_obligation(self):
        path,manifest,alignment=self.author_fixture()
        manifest['schema']='math-gauge.formal-case/v1';V.save(path,manifest)
        with self.assertRaisesRegex(V.VerificationError,'v2 author contract'):V.validate_case(path)
        manifest['schema']='math-gauge.formal-case/v2'
        alignment['items']=[];V.save(self.root/'alignment.json',alignment)
        manifest['alignment']['sha256']=V.digest(self.root/'alignment.json');V.save(path,manifest)
        with self.assertRaisesRegex(V.VerificationError,'every stage'):V.validate_case(path)
    def test_complete_author_stage_cannot_keep_a_known_gap(self):
        path,manifest,alignment=self.author_fixture()
        alignment['items'][0]['gaps']=['Reverse implication missing']
        V.save(self.root/'alignment.json',alignment)
        manifest['alignment']['sha256']=V.digest(self.root/'alignment.json');V.save(path,manifest)
        with self.assertRaisesRegex(V.VerificationError,'no known gaps'):V.validate_case(path)
    def test_chapter_task_path_and_obligation_input_are_bound(self):
        path,manifest,_=self.author_fixture('MG-C002')
        (self.case/'candidate').mkdir()
        (self.case/'task.md').rename(self.case/'candidate/task.md')
        case=V.load(self.case/'case.json');case['task']='case/candidate/task.md';V.save(self.case/'case.json',case)
        manifest['frozen_inputs']=V.author_frozen_inputs(self.case)[1];V.save(path,manifest)
        V.validate_case(path)
        self.assertIn('candidate/task.md',manifest['frozen_inputs'])
        self.assertNotIn('task.md',manifest['frozen_inputs'])
    def test_case_relative_author_contract_and_invalid_path_base(self):
        path, manifest, _ = self.author_fixture()
        case = V.load(self.case/'case.json')
        case['path_base'] = 'case'
        for key in ('task', 'reference', 'rubric', 'group_contract'):
            case[key] = case[key].removeprefix('case/')
        for row in case['solver_files']:
            row['source'] = row['source'].removeprefix('case/')
        V.save(self.case/'case.json', case)
        manifest['frozen_inputs'] = V.author_frozen_inputs(self.case)[1]
        V.save(path, manifest)
        V.validate_case(path)
        case['path_base'] = 'guess'; V.save(self.case/'case.json', case)
        with self.assertRaisesRegex(V.VerificationError, 'path_base'):
            V.author_frozen_inputs(self.case)
    def test_new_audit_includes_non_mathgauge_local_namespaces(self):
        for profile in V.PROFILES:
            audit=V.render_audit(['Example'],profile,all_case_declarations=True)
            self.assertIn('expectedModules.contains origin',audit)
            self.assertNotIn('startsWith "MathGauge."',audit)
    def test_public_extraction_keeps_frozen_input_contract(self):
        p,d=self.fixture();d['case_id']='MG-P001';p.write_text(json.dumps(d))
        manifest,*_=V.validate_case(p)
        self.assertEqual(manifest['case_id'],'MG-P001')
        (self.case/'reference.md').write_text('changed reference')
        with self.assertRaisesRegex(V.VerificationError,'Frozen case input'):V.validate_case(p)
    def test_case_id_cannot_select_an_output_subdirectory(self):
        p,d=self.fixture();d['case_id']='MG-P001/other';p.write_text(json.dumps(d))
        with self.assertRaisesRegex(V.VerificationError,'Invalid case id'):V.validate_case(p)
    def test_bad_hash_is_rejected(self):
        p,d=self.fixture();(self.root/'Example.lean').write_text('namespace MathGauge.Fixture\ndef changed := 2\n')
        with self.assertRaisesRegex(V.VerificationError,'SHA256'):V.validate_case(p)
    def test_frozen_case_bytes_are_bound(self):
        p,_=self.fixture();(self.case/'task.md').write_text('changed task')
        with self.assertRaisesRegex(V.VerificationError,'Frozen case input'):V.validate_case(p)
    def test_missing_dependency_is_rejected(self):
        with self.assertRaisesRegex(V.VerificationError,'lake-manifest'):V.inspect_dependencies(self.root)
    def test_current_audit_cannot_be_replaced_by_a_claim(self):
        p,d=self.fixture();audit=self.root/'CurrentAudit.lean';audit.write_text('import Example\n-- pretend audit succeeded\n');d['audit']['sha256']=V.digest(audit);p.write_text(json.dumps(d))
        with self.assertRaisesRegex(V.VerificationError,'shared generator'):V.validate_case(p)
    def test_missing_local_dependency_is_not_silently_imported(self):
        p,d=self.fixture('import Later\nnamespace MathGauge.Fixture\ndef value := 1\nend MathGauge.Fixture\n')
        later=self.root/'Later.lean';later.write_text('def later := 0\n');d['modules'].append({'module':'Later','source':later.name,'sha256':V.digest(later),'imports':[]});p.write_text(json.dumps(d))
        with self.assertRaisesRegex(V.VerificationError,'later in module order'):V.validate_case(p)
    def test_sorry_is_rejected_but_comment_is_not_a_placeholder(self):
        p,_=self.fixture('namespace MathGauge.Fixture\n-- No sorry is used.\ntheorem ok : True := by trivial\nend MathGauge.Fixture\n');V.validate_case(p)
        p,_=self.fixture('namespace MathGauge.Fixture\ntheorem unfinished : False := by sorry\nend MathGauge.Fixture\n')
        with self.assertRaisesRegex(V.VerificationError,'placeholder'):V.validate_case(p)
    def test_legacy_audit_bytes_are_unchanged(self):
        # This golden identity predates profile selection and binds historical audits.
        self.assertEqual(hashlib.sha256(V.render_audit(['Example']).encode()).hexdigest(),
                         'fb52b90a58cc89498df7097b2d0e189d44044d95e9b0685f8988c06be2b3f035')
        self.assertEqual(V.render_audit(['Example']),V.render_audit(['Example'],V.DEFAULT_PROFILE))
    def test_new_profile_binds_all_revisions_and_its_own_template(self):
        p,d=self.fixture(profile=V.TAUCETI_PROFILE)
        self.assertEqual(V.manifest_profile(V.validate_case(p)[0]),V.TAUCETI_PROFILE)
        audit=self.root/'CurrentAudit.lean';audit.write_text(V.render_audit(['Example']))
        d['audit']['sha256']=V.digest(audit);p.write_text(json.dumps(d))
        with self.assertRaisesRegex(V.VerificationError,'shared generator'):V.validate_case(p)
    def test_unknown_profile_and_partial_profile_migration_are_rejected(self):
        for field,value,reason in [('verification_profile','arbitrary','Unknown verification profile'),
                                   ('lean_toolchain',V.TOOLCHAIN,'toolchain'),
                                   ('mathlib_revision',V.MATHLIB_REV,'Mathlib'),
                                   ('tauceti_revision','0'*40,'TauCeti')]:
            with self.subTest(field=field):
                p,d=self.fixture(profile=V.TAUCETI_PROFILE);d[field]=value;p.write_text(json.dumps(d))
                with self.assertRaisesRegex(V.VerificationError,reason):V.validate_case(p)
        p,d=self.fixture(profile=V.TAUCETI_PROFILE);del d['tauceti_revision'];p.write_text(json.dumps(d))
        with self.assertRaisesRegex(V.VerificationError,'TauCeti'):V.validate_case(p)
    def test_legacy_profile_cannot_gain_tauceti_by_manifest_field(self):
        p,d=self.fixture();d['tauceti_revision']=V.PROFILES[V.TAUCETI_PROFILE]['tauceti_revision'];p.write_text(json.dumps(d))
        with self.assertRaisesRegex(V.VerificationError,'fixed verification profile'):V.validate_case(p)
    def test_case_cannot_use_another_profiles_dependency_receipt(self):
        p,_=self.fixture(profile=V.TAUCETI_PROFILE)
        with self.assertRaisesRegex(V.VerificationError,'profiles differ'):
            V.verify_case(p,{'mathlib_revision':V.MATHLIB_REV},self.root/'out')
        config=V.PROFILES[V.TAUCETI_PROFILE]
        with self.assertRaisesRegex(V.VerificationError,'Dependency TauCeti revision'):
            V.verify_case(p,{'verification_profile':V.TAUCETI_PROFILE,'mathlib_revision':config['mathlib_revision'],
                             'tauceti_revision':'0'*40},self.root/'out')
    def test_one_invocation_cannot_mix_profiles(self):
        legacy,_=self.fixture();legacy_copy=self.root/'legacy.json';legacy_copy.write_bytes(legacy.read_bytes())
        modern,d=self.fixture(profile=V.TAUCETI_PROFILE);d['case_id']='MG-TEST-Modern';modern.write_text(json.dumps(d))
        # Separate source trees preserve each audit identity before CLI prevalidation.
        modern_case=self.case.with_name('modern');shutil.copytree(self.case,modern_case)
        modern=modern_case/'formal/manifest.json'
        self.fixture();out=self.root/'mixed-out'
        with patch.object(V,'inspect_dependencies') as inspect:
            self.assertEqual(V.main(['--manifest',str(legacy_copy),'--manifest',str(modern),
                                    '--dependency-root',str(self.root),'--out',str(out)]),1)
        inspect.assert_not_called()
        self.assertIn('Cannot mix verification profiles',V.load(out/'report.json')['error'])

class RetainedEvidenceTests(FixtureMixin, unittest.TestCase):
    """Synthetic saved output tests receipt integrity without claiming a Lean run."""
    def setUp(self):
        super().setUp()
        _, manifest, alignment = ManifestTests.author_fixture(self)
        cid = manifest['case_id']
        old_case = V.load(self.case/'case.json')
        for key in ('task', 'reference', 'rubric', 'group_contract'):
            old_case[key] = old_case[key].replace('case/', cid + '/')
        old_case['solver_files'][0]['source'] = cid + '/input.lean'
        old_case['review'] = {'mathematical': 'fixture-ai-review', 'human': 'pending'}
        old_case['evaluator_files'] = [cid + '/provenance.json', 'reviews/old-shared.json']
        V.save(self.case/'case.json', old_case)
        V.save(self.case/'provenance.json', {'kind': 'synthetic-test-fixture'})
        self.repo = Path(self.temp.name)/'export'
        new_case = self.repo/'cases/proofs'/cid
        new_case.parent.mkdir(parents=True)
        self.case.rename(new_case); self.case = new_case; self.root = new_case/'formal'
        manifest['frozen_inputs'] = V.author_frozen_inputs(self.case)[1]
        V.save(self.root/'manifest.json', manifest)
        shutil.copyfile(self.case/'case.json', self.root/'checked-case.json')
        shutil.copyfile(self.root/'manifest.json', self.root/'checked-manifest.json')
        declarations = [{'module': 'Example', 'name': 'MathGauge.Fixture.value',
                         'user_name': 'MathGauge.Fixture.value', 'kind': 'definition'}]
        summary = {'passed': True, 'unexpected_axioms': [], 'axiom_union': [], 'declaration_count': 1}
        (self.root/'logs').mkdir()
        (self.root/'logs/Example.log').write_text('')
        (self.root/'logs/CurrentAudit.log').write_text(
            'MATH_GAUGE_DECL ' + json.dumps(declarations[0]) + '\n' +
            'MATH_GAUGE_AUDIT_SUMMARY ' + json.dumps(summary) + '\n')

        def command(row):
            name = row['module']; log = 'logs/' + name + '.log'
            return {'module': name, 'source_sha256': row['sha256'], 'exit_code': 0,
                    'log': log, 'log_sha256': V.digest(self.root/log)}

        report = {
            'schema': 'math-gauge.formal-verification/v1', 'case_id': cid, 'status': 'passed',
            'manifest_sha256': V.digest(self.root/'manifest.json'),
            'started_utc': '2000-01-01T00:00:00+00:00', 'finished_utc': '2000-01-01T00:00:01+00:00',
            'frozen_inputs': manifest['frozen_inputs'], 'alignment': manifest['alignment'],
            'coverage': manifest['coverage'], 'fresh_output': True,
            'source_side_oleans_reused': False, 'sibling_case_outputs_used': False,
            'semantic_alignment_inferred': False, 'local_declaration_audit_scope': 'all-explicit-case-modules',
            'dependency': {'mathlib_revision': V.MATHLIB_REV, 'lean_version': 'Lean 4.29.1 fixture',
                           'ambient_lean_path_excluded': True, 'dependency_project_build_excluded': True},
            'modules': [command(manifest['modules'][0])],
            'audit': {'command': command(manifest['audit']), 'declarations': declarations,
                      'summary': summary, 'allowed_axioms': sorted(V.ALLOWED_AXIOMS)},
        }
        V.save(self.root/'verification-report.json', report)
        V.save(self.root/'declarations.json', declarations)
        evidence = self.repo/'verification/author'; (evidence/'semantic-reviews').mkdir(parents=True)
        review_path = evidence/'semantic-reviews'/f'{cid}.json'
        hashes = {name: V.digest(self.case/name) for name in manifest['frozen_inputs']}
        hashes['formal/manifest.json'] = V.digest(self.root/'checked-manifest.json')
        hashes['formal/Example.lean'] = V.digest(self.root/'Example.lean')
        review = {'case_id': cid, 'case_version': manifest['case_version'],
                  'reviewer': 'fixture-independent-reviewer', 'status': 'passed',
                  'files': hashes, 'items': [{'id': 'S1', 'status': 'passed'}]}
        V.save(review_path, review)
        self.mapping = {'id': cid, 'previous': 'drafts/fixture/' + cid,
                        'current': 'cases/proofs/' + cid}
        self.layout = {
            'schema': E.LAYOUT_SCHEMA, 'baseline_commit': '6a48027baa33e06e913a554fb8bac9394a82b480',
            'case_paths': [self.mapping],
            'path_prefixes': [{'previous': 'results/author-fixture', 'current': 'verification/author'}],
        }
        V.save(self.repo/'verification/layout.json', self.layout)
        self.baseline = {
            'id': cid, 'case_version': manifest['case_version'], 'case_path': self.mapping['previous'],
            'manifest_sha256': V.digest(self.root/'checked-manifest.json'),
            'verification_report_sha256': V.digest(self.root/'verification-report.json'),
            'declarations_sha256': V.digest(self.root/'declarations.json'),
            'compile_started_utc': report['started_utc'], 'compile_finished_utc': report['finished_utc'],
            'complete_items': ['S1'], 'incomplete_items': [],
            'independent_semantic_review': {
                'path': 'results/author-fixture/semantic-reviews/' + cid + '.json',
                'sha256': V.digest(review_path), 'reviewer': review['reviewer'], 'status': 'passed',
                'bound_files_rechecked': len(hashes), 'stage_ids': ['S1'],
            },
        }
        V.save(evidence/'checked-ledger.json', {
            'schema': 'math-gauge.author-evidence-ledger/v1', 'baseline_commit': '1'*40,
            'counts': {'papers': 1, 'fully_formalized_papers': 1, 'items': 1, 'complete_items': 1,
                       'modules': 1, 'declarations_with_per_case_repetition': 1},
            'cases': [self.baseline],
        })
        self.layout['migration'] = {'checked_ledger_sha256': V.digest(evidence/'checked-ledger.json')}
        V.save(self.repo/'verification/layout.json', self.layout)
        V.save(self.repo/'cases/suite.json', {'schema': 'math-gauge.suite/v1',
                                           'cases': ['proofs/' + cid + '/case.json']})
        current = deepcopy(old_case); current['path_base'] = 'case'
        for key in ('task', 'reference', 'rubric', 'group_contract'):
            current[key] = current[key].removeprefix(cid + '/')
        current['solver_files'][0]['source'] = 'input.lean'
        current['evaluator_files'] = ['provenance.json'] + sorted(E.REQUIRED_EVALUATOR_FILES)
        current['review']['formalization'] = E.canonical_formalization(alignment)
        V.save(self.case/'case.json', current)
        manifest['frozen_inputs'] = V.author_frozen_inputs(self.case)[1]
        V.save(self.root/'manifest.json', manifest)
        E.check_case(self.repo, self.layout, self.mapping, self.baseline, write_binding=True)

    def check(self, **kwargs):
        return E.check_case(self.repo, self.layout, self.mapping, self.baseline, **kwargs)

    def update_current_manifest(self):
        manifest = V.load(self.root/'manifest.json')
        manifest['frozen_inputs'] = V.author_frozen_inputs(self.case)[1]
        V.save(self.root/'manifest.json', manifest)

    def test_metadata_reroute_uses_checked_inputs_and_preserves_original_compile_time(self):
        report = (self.root/'verification-report.json').read_bytes()
        with patch.object(V, 'command', side_effect=AssertionError('Offline checks cannot invoke tools')):
            row = self.check()
            ledger = E.check_all(self.repo)
        self.assertEqual(row['compile_started_utc'], '2000-01-01T00:00:00+00:00')
        self.assertNotEqual(row['manifest_sha256'], row['checked_manifest_sha256'])
        self.assertNotEqual(row['case_sha256'], row['checked_case_sha256'])
        self.assertEqual((self.root/'verification-report.json').read_bytes(), report)
        self.assertEqual(ledger['counts']['fully_formalized_papers'], 1)
        self.assertFalse(ledger['fresh_compilation_repeated'])

    def test_human_version_and_unlisted_metadata_changes_are_rejected_even_after_rehash(self):
        original = V.load(self.case/'case.json')
        for field, value in [('version', '9.9.9'), ('title', 'Unapproved metadata'),
                             ('injected', True), ('review', {'human': 'approved'})]:
            with self.subTest(field=field):
                current = deepcopy(original); current[field] = value
                V.save(self.case/'case.json', current); self.update_current_manifest()
                with self.assertRaises(V.VerificationError): self.check(write_binding=True)
        V.save(self.case/'case.json', original); self.update_current_manifest()
        self.check()

    def test_checked_ledger_cannot_be_replaced_during_binding_refresh(self):
        path = self.repo/'verification/author/checked-ledger.json'
        baseline = V.load(path)
        baseline['baseline_commit'] = '9' * 40
        V.save(path, baseline)
        binding = (self.root/'input-binding.json').read_bytes()
        with self.assertRaisesRegex(V.VerificationError, 'recorded migration identity'):
            E.check_all(self.repo, write_bindings=True)
        self.assertEqual((self.root/'input-binding.json').read_bytes(), binding)
        with self.assertRaisesRegex(V.VerificationError, 'recorded migration identity'):
            E.original_row(self.repo, self.layout, self.mapping['id'])

    def test_mathematical_inputs_cannot_be_changed_and_rehashed_as_a_relocation(self):
        original_manifest = (self.root/'manifest.json').read_bytes()
        for name in ('task.md', 'reference.md', 'rubric.json', 'contract.json', 'input.lean'):
            with self.subTest(name=name):
                path = self.case/name; original = path.read_bytes()
                path.write_bytes(original + b'\n')
                self.update_current_manifest()
                with self.assertRaisesRegex(V.VerificationError, 'Only the current case.json hash'):
                    self.check(write_binding=True)
                path.write_bytes(original); (self.root/'manifest.json').write_bytes(original_manifest)

    def test_lean_source_and_coverage_cannot_be_rebound(self):
        for name, field in [('Example.lean', 'modules'), ('COVERAGE.md', 'coverage')]:
            with self.subTest(name=name):
                path = self.root/name; original = path.read_bytes()
                manifest = V.load(self.root/'manifest.json'); original_manifest = deepcopy(manifest)
                path.write_bytes(original + b'\n')
                if field == 'modules': manifest[field][0]['sha256'] = V.digest(path)
                else: manifest[field]['sha256'] = V.digest(path)
                V.save(self.root/'manifest.json', manifest)
                with self.assertRaisesRegex(V.VerificationError, 'Only the current case.json hash'):
                    self.check(write_binding=True)
                path.write_bytes(original); V.save(self.root/'manifest.json', original_manifest)

    def test_original_report_and_checked_manifest_tampering_is_rejected(self):
        for filename in ('verification-report.json', 'checked-manifest.json'):
            with self.subTest(filename=filename):
                path = self.root/filename; original = path.read_bytes()
                path.write_bytes(original + b'\n')
                with self.assertRaisesRegex(V.VerificationError, 'Original compiler evidence|Checked manifest'):
                    self.check(write_binding=True)
                path.write_bytes(original)

    def test_stale_review_hash_and_binding_tampering_are_not_ignored(self):
        path = self.repo/'verification/author/semantic-reviews/MG-GR001.json'
        original = path.read_bytes(); path.write_bytes(original + b'\n')
        with self.assertRaisesRegex(V.VerificationError, 'Original independent semantic review changed'):
            self.check()
        path.write_bytes(original)
        binding = V.load(self.root/'input-binding.json'); binding['current_case']['sha256'] = '0'*64
        V.save(self.root/'input-binding.json', binding)
        with self.assertRaisesRegex(V.VerificationError, 'Input binding differs'): self.check()

    def test_recorded_review_source_hash_is_checked_after_path_translation(self):
        path = self.repo/'verification/author/semantic-reviews/MG-GR001.json'
        review = V.load(path)
        # An original review can itself contain a stale hash. Retaining and
        # correctly hashing that document must not make its source claim true.
        review['files']['task.md'] = '0'*64
        V.save(path, review)
        baseline = deepcopy(self.baseline)
        baseline['independent_semantic_review']['sha256'] = V.digest(path)
        with self.assertRaisesRegex(V.VerificationError, 'source hash is stale'):
            E.check_review(self.repo, self.layout, self.case, baseline)

    def test_missing_mapped_declaration_is_rejected_despite_valid_compiler_summary(self):
        manifest = V.load(self.root/'checked-manifest.json')
        alignment = V.load(self.root/'alignment.json')
        alignment['items'][0]['declarations'][0]['name'] = 'MathGauge.Fixture.absent'
        V.save(self.root/'alignment.json', alignment)
        manifest['alignment']['sha256'] = V.digest(self.root/'alignment.json')
        # Exercise report validation directly: its source binding is internally
        # consistent, but the mapped theorem is absent from actual audit output.
        report = V.load(self.root/'verification-report.json'); report['alignment'] = manifest['alignment']
        V.save(self.root/'verification-report.json', report)
        with self.assertRaisesRegex(V.VerificationError, 'Mapped declaration missing'):
            E.check_compiler_report(self.root, manifest, manifest, self.baseline)

    def test_local_axiom_is_rejected_even_if_summary_claims_allowed_union(self):
        report = V.load(self.root/'verification-report.json')
        report['audit']['declarations'][0]['kind'] = 'axiom'
        V.save(self.root/'verification-report.json', report)
        V.save(self.root/'declarations.json', report['audit']['declarations'])
        checked = V.load(self.root/'checked-manifest.json')
        with self.assertRaisesRegex(V.VerificationError, 'local axiom'):
            E.check_compiler_report(self.root, checked, checked, self.baseline)

    def test_compiler_log_and_audit_inventory_must_match(self):
        log = self.root/'logs/Example.log'; log.write_text('different compiler output')
        checked = V.load(self.root/'checked-manifest.json')
        with self.assertRaisesRegex(V.VerificationError, 'Saved compiler log changed'):
            E.check_compiler_report(self.root, checked, checked, self.baseline)

    def test_reported_audit_inventory_must_match_the_log_even_after_log_rehash(self):
        report = V.load(self.root/'verification-report.json')
        log = self.root/'logs/CurrentAudit.log'
        log.write_text('MATH_GAUGE_AUDIT_SUMMARY ' + json.dumps(report['audit']['summary']) + '\n')
        report['audit']['command']['log_sha256'] = V.digest(log)
        V.save(self.root/'verification-report.json', report)
        checked = V.load(self.root/'checked-manifest.json')
        with self.assertRaisesRegex(V.VerificationError, 'audit log and reported inventory'):
            E.check_compiler_report(self.root, checked, checked, self.baseline)

    def test_partial_coverage_stays_partial_in_derived_metadata(self):
        alignment = {'items': [{'status': 'complete'}, {'status': 'partial'}, {'status': 'pending'}]}
        self.assertEqual(E.canonical_formalization(alignment), {
            'status': 'partial', 'complete_obligations': 1, 'total_obligations': 3,
            'evidence': 'formal/manifest.json'})

    def test_canonical_suite_resolves_author_manifests_without_a_second_catalog(self):
        manifests = S.indexed_manifests(self.repo/'cases/suite.json')
        self.assertEqual(manifests, [(self.root/'manifest.json').resolve()])
        suite = self.repo/'cases/suite.json'; data = V.load(suite); data['cases'] *= 2; V.save(suite, data)
        with self.assertRaisesRegex(V.VerificationError, 'Duplicate'): S.indexed_manifests(suite)

    def test_suite_selects_exact_profile_before_inspecting_dependencies(self):
        modern = self.case.with_name('MG-GP001'); shutil.copytree(self.case, modern)
        case = V.load(modern/'case.json'); case['id'] = 'MG-GP001'; V.save(modern/'case.json', case)
        contract = V.load(modern/'contract.json'); contract['id'] = 'MG-GP001'; V.save(modern/'contract.json', contract)
        alignment = V.load(modern/'formal/alignment.json'); alignment['case_id'] = 'MG-GP001'
        V.save(modern/'formal/alignment.json', alignment)
        manifest = V.load(modern/'formal/manifest.json'); config = V.profile_config(V.TAUCETI_PROFILE)
        manifest.update(case_id='MG-GP001', verification_profile=V.TAUCETI_PROFILE,
                        lean_toolchain=config['toolchain'], mathlib_revision=config['mathlib_revision'],
                        tauceti_revision=config['tauceti_revision'])
        manifest['frozen_inputs'] = V.author_frozen_inputs(modern)[1]
        manifest['alignment']['sha256'] = V.digest(modern/'formal/alignment.json')
        audit = modern/'formal/CurrentAudit.lean'
        audit.write_text(V.render_audit(['Example'], V.TAUCETI_PROFILE, all_case_declarations=True))
        manifest['audit']['sha256'] = V.digest(audit); V.save(modern/'formal/manifest.json', manifest)
        suite = self.repo/'cases/suite.json'; data = V.load(suite)
        data['cases'].append('proofs/MG-GP001/case.json'); V.save(suite, data)

        def compile_stub(path, dependency, out):
            current = V.load(path)
            return {'case_id': current['case_id'], 'status': 'passed', 'modules': current['modules'],
                    'audit': {'summary': {}}, 'manifest_sha256': V.digest(path)}

        for profile, selected, excluded in [(V.DEFAULT_PROFILE, 'MG-GR001', 'MG-GP001'),
                                             (V.TAUCETI_PROFILE, 'MG-GP001', 'MG-GR001')]:
            with self.subTest(profile=profile):
                output = self.repo/('output-' + profile)
                with patch.object(V, 'inspect_dependencies', return_value={}) as inspect, \
                     patch.object(V, 'verify_case', side_effect=compile_stub) as compile_case:
                    self.assertEqual(S.main(['--suite', str(suite), '--profile', profile,
                                             '--dependency-root', str(self.repo/'unused'),
                                             '--out', str(output)]), 0)
                self.assertEqual(inspect.call_args.args[2], profile)
                self.assertEqual(compile_case.call_count, 1)
                report = V.load(output/'report.json')
                self.assertEqual(report['suite_case_count'], 2)
                self.assertEqual(report['selected_case_count'], 1)
                self.assertEqual(report['cases'][0]['case_id'], selected)
                self.assertEqual(report['excluded_cases'], [excluded])


class DependencyProfileTests(FixtureMixin, unittest.TestCase):
    def dependency_fixture(self):
        dep=self.root/'dependencies';dep.mkdir()
        config=V.PROFILES[V.TAUCETI_PROFILE]
        packages=[{'name':name,'rev':rev} for name,rev in config['packages'].items()]
        V.save(dep/'lake-manifest.json',{'packagesDir':'.lake/packages','packages':packages})
        (dep/'lean-toolchain').write_text(config['toolchain']+'\n')
        prefix=self.root/'toolchain';binary=prefix/'bin/lean';binary.parent.mkdir(parents=True);binary.write_bytes(b'fixture lean')
        audit=prefix/'lib/lean/Lean/Util/CollectAxioms.olean';audit.parent.mkdir(parents=True);audit.write_bytes(b'fixture audit')
        for name in config['packages']:(dep/'.lake/packages'/name/'.lake/build/lib/lean').mkdir(parents=True)
        (dep/'.lake/build/lib/lean').mkdir(parents=True)
        def invoke(argv,**kwargs):
            args=list(map(str,argv))
            if args[-1]=='--version':return 'Lean (version 4.36.0-rc1, fixture)'
            if args[-1]=='--print-prefix':return str(prefix)
            package=Path(args[3]);name=package.name
            if args[-1]=='--show-toplevel':return str(package.resolve())
            if args[-1]=='HEAD' and 'rev-parse' in args:return config['packages'][name]
            if 'status' in args or 'diff' in args:return ''
            raise AssertionError(args)
        return dep,binary,invoke
    def inspect(self,dep,binary,invoke):
        with patch.object(V,'command',side_effect=invoke):
            return V.inspect_dependencies(dep,binary,V.TAUCETI_PROFILE)
    def test_pinned_packages_are_clean_and_dependency_project_build_is_excluded(self):
        dep,binary,invoke=self.dependency_fixture();report=self.inspect(dep,binary,invoke)
        self.assertEqual(report['verification_profile'],V.TAUCETI_PROFILE)
        self.assertEqual(len(report['packages']),10)
        self.assertTrue(all(p['tracked_state']['clean'] for p in report['packages']))
        self.assertNotIn(str(dep/'.lake/build/lib/lean'),report['search_paths'])
        self.assertTrue(report['ambient_lean_path_excluded'])
    def test_untrusted_extra_missing_duplicate_and_mixed_revision_packages_are_rejected(self):
        dep,binary,invoke=self.dependency_fixture();lock=dep/'lake-manifest.json';original=V.load(lock)
        variants=[original['packages']+[{'name':'foreign','rev':'0'*40}],
                  [p for p in original['packages'] if p['name']!='TauCeti'],
                  original['packages']+[original['packages'][0]],
                  [dict(p,rev=V.MATHLIB_REV) if p['name']=='mathlib' else p for p in original['packages']]]
        for packages in variants:
            with self.subTest(packages=len(packages)):
                V.save(lock,dict(original,packages=packages))
                with self.assertRaises(V.VerificationError):self.inspect(dep,binary,invoke)
    def test_dirty_tauceti_source_is_rejected_even_at_the_correct_head(self):
        dep,binary,invoke=self.dependency_fixture()
        def dirty(argv,**kwargs):
            if 'status' in argv and Path(argv[3]).name=='TauCeti':return ' M TauCeti/Changed.lean'
            return invoke(argv,**kwargs)
        with self.assertRaisesRegex(V.VerificationError,'TauCeti tracked sources are modified'):self.inspect(dep,binary,dirty)
    def test_dependency_root_and_binary_toolchains_must_both_match_profile(self):
        dep,binary,invoke=self.dependency_fixture();toolchain=dep/'lean-toolchain'
        toolchain.write_text(V.TOOLCHAIN)
        with self.assertRaisesRegex(V.VerificationError,'root toolchain'):self.inspect(dep,binary,invoke)
        toolchain.write_text(V.PROFILES[V.TAUCETI_PROFILE]['toolchain'])
        def old_binary(argv,**kwargs):
            if argv[-1]=='--version':return 'Lean (version 4.29.1, fixture)'
            return invoke(argv,**kwargs)
        with self.assertRaisesRegex(V.VerificationError,'Expected Lean 4.36.0-rc1'):self.inspect(dep,binary,old_binary)
    def test_package_checkout_head_and_ownership_are_checked(self):
        dep,binary,invoke=self.dependency_fixture()
        for operation,reply,reason in [('HEAD','0'*40,'checkout differs'),
                                       ('--show-toplevel',str(dep),'own pinned checkout')]:
            with self.subTest(operation=operation):
                def wrong(argv,**kwargs):
                    if argv[-1]==operation:return reply
                    return invoke(argv,**kwargs)
                with self.assertRaisesRegex(V.VerificationError,reason):self.inspect(dep,binary,wrong)

@unittest.skipUnless(os.environ.get('MATH_GAUGE_TEST_DEPENDENCY_ROOT'),'Set MATH_GAUGE_TEST_DEPENDENCY_ROOT for pinned live Lean tests')
class LiveKernelTests(FixtureMixin, unittest.TestCase):
    profile=V.DEFAULT_PROFILE
    @classmethod
    def setUpClass(cls):
        cls.dependency=V.inspect_dependencies(os.environ['MATH_GAUGE_TEST_DEPENDENCY_ROOT'],os.environ.get('MATH_GAUGE_TEST_LEAN'))
    def compile_fixture(self,text):
        manifest,_=self.fixture(text,self.profile);out=self.root/'out';out.mkdir();return V.verify_case(manifest,self.dependency,out)
    def test_all_constants_include_private_helpers(self):
        report=self.compile_fixture('namespace MathGauge.Fixture\nprivate def hidden : Nat := 7\ndef value : Nat := hidden\ntheorem value_eq : value = 7 := rfl\nend MathGauge.Fixture\n')
        self.assertEqual(report['status'],'passed',report)
        declarations=report['audit']['declarations']
        self.assertTrue(any(d['user_name']=='MathGauge.Fixture.hidden' and d['name'].startswith('_private.') for d in declarations))
        self.assertTrue({'definition','theorem'} <= {d['kind'] for d in declarations})
    def test_source_side_compiled_output_is_not_reused(self):
        manifest,_=self.fixture(profile=self.profile)
        stale=self.root/'Example.olean';stale.write_bytes(b'untrusted stale source-side artifact')
        out=self.root/'out';out.mkdir();report=V.verify_case(manifest,self.dependency,out)
        self.assertEqual(report['status'],'passed',report)
        self.assertFalse(report['source_side_oleans_reused'])
        self.assertNotIn(str(self.root),report['lean_path'].split(os.pathsep))
        self.assertNotEqual(report['modules'][0]['olean_sha256'],V.digest(stale))
    def test_nonstandard_axiom_is_rejected_by_the_kernel_audit(self):
        report=self.compile_fixture('namespace MathGauge.Fixture\naxiom extra : False\ntheorem invalid : False := extra\nend MathGauge.Fixture\n')
        self.assertEqual(report['modules'][0]['exit_code'],0)
        self.assertEqual(report['status'],'failed')
        self.assertIn('MathGauge.Fixture.extra',report['audit']['summary']['unexpected_axioms'])
    def test_ambient_olean_path_is_ignored(self):
        manifest,_=self.fixture('import UnlistedForeign\nnamespace MathGauge.Fixture\ndef value := 1\nend MathGauge.Fixture\n',self.profile)
        foreign=self.root/'foreign';foreign.mkdir();(foreign/'UnlistedForeign.olean').write_bytes(b'not a trusted dependency')
        old=os.environ.get('LEAN_PATH');os.environ['LEAN_PATH']=str(foreign)
        try:
            out=self.root/'out';out.mkdir();report=V.verify_case(manifest,self.dependency,out)
        finally:
            if old is None:os.environ.pop('LEAN_PATH',None)
            else:os.environ['LEAN_PATH']=old
        self.assertEqual(report['status'],'failed');self.assertIn('Missing compiled external import',report['error'])

@unittest.skipUnless(os.environ.get('MATH_GAUGE_TEST_DEPENDENCY_ROOT'),'Set MATH_GAUGE_TEST_DEPENDENCY_ROOT for pinned live Lean tests')
class LiveAuthorKernelTests(FixtureMixin, unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.dependency=V.inspect_dependencies(os.environ['MATH_GAUGE_TEST_DEPENDENCY_ROOT'],os.environ.get('MATH_GAUGE_TEST_LEAN'))
    def author_compile(self,text,name):
        path,manifest,alignment=ManifestTests.author_fixture(self)
        (self.root/'Example.lean').write_text(text)
        manifest['modules'][0]['sha256']=V.digest(self.root/'Example.lean')
        alignment['items'][0]['declarations'][0]['name']=name
        V.save(self.root/'alignment.json',alignment)
        manifest['alignment']['sha256']=V.digest(self.root/'alignment.json')
        V.save(path,manifest)
        out=self.root/'out';out.mkdir()
        return V.verify_case(path,self.dependency,out)
    def test_unused_non_mathgauge_private_axiom_is_rejected(self):
        report=self.author_compile('namespace OtherAuthor\nprivate axiom unused : False\ndef value : Nat := 1\nend OtherAuthor\n','OtherAuthor.value')
        self.assertEqual(report['modules'][0]['exit_code'],0)
        self.assertEqual(report['status'],'failed')
        self.assertTrue(any(d['user_name']=='OtherAuthor.unused' for d in report['audit']['declarations']))
        self.assertTrue(any('unused' in n for n in report['audit']['summary']['unexpected_axioms']))
    def test_named_stage_evidence_must_exist_in_compiled_inventory(self):
        report=self.author_compile('namespace OtherAuthor\ndef value : Nat := 1\nend OtherAuthor\n','OtherAuthor.missing')
        self.assertEqual(report['modules'][0]['exit_code'],0)
        self.assertEqual(report['status'],'failed')
        self.assertIn('missing from kernel inventory',report['error'])

@unittest.skipUnless(os.environ.get('MATH_GAUGE_TEST_TAUCETI_ROOT'),'Set MATH_GAUGE_TEST_TAUCETI_ROOT for pinned Lean 4.36 live tests')
class LiveTauCetiKernelTests(LiveKernelTests):
    # The legacy class may be disabled independently of this profile's fixtures.
    __unittest_skip__=False
    profile=V.TAUCETI_PROFILE
    @classmethod
    def setUpClass(cls):
        cls.dependency=V.inspect_dependencies(os.environ['MATH_GAUGE_TEST_TAUCETI_ROOT'],os.environ.get('MATH_GAUGE_TEST_TAUCETI_LEAN'),cls.profile)
    def test_module_system_unused_private_axiom_is_still_audited(self):
        report=self.compile_fixture('module\nnamespace MathGauge.Fixture\nprivate axiom unused : False\npublic theorem ok : True := by trivial\nend MathGauge.Fixture\n')
        self.assertEqual(report['modules'][0]['exit_code'],0)
        self.assertEqual(report['status'],'failed')
        self.assertTrue(any(d['user_name']=='MathGauge.Fixture.unused' for d in report['audit']['declarations']))
        self.assertTrue(any('unused' in name for name in report['audit']['summary']['unexpected_axioms']))

if __name__=='__main__':unittest.main()
