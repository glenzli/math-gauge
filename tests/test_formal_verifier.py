"""Focused contracts for source identity, dependency boundaries and real kernel audits."""
from pathlib import Path
import hashlib
import importlib.util
import json
import os
import shutil
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('formal_verifier', ROOT/'scripts/formal/verify.py')
V = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(V)

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
