"""Focused contracts for source identity, dependency boundaries and real kernel audits."""
from pathlib import Path
import importlib.util
import json
import os
import tempfile
import unittest

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
    def fixture(self, text='namespace MathGauge.Fixture\ndef value : Nat := 1\nend MathGauge.Fixture\n'):
        p=self.root/'Example.lean';p.write_text(text)
        audit=self.root/'CurrentAudit.lean';audit.write_text(V.render_audit(['Example']))
        data={'schema':'math-gauge.formal-case/v1','case_id':'MG-TEST-Example','lean_toolchain':V.TOOLCHAIN,'mathlib_revision':V.MATHLIB_REV,'frozen_inputs':{name:V.digest(self.case/name) for name in ('task.md','reference.md','rubric.json')},'coverage':{'source':'COVERAGE.md','sha256':V.digest(self.root/'COVERAGE.md')},'modules':[{'module':'Example','source':p.name,'sha256':V.digest(p),'imports':V.source_imports(text)}],'audit':{'module':'CurrentAudit','source':audit.name,'sha256':V.digest(audit)}}
        manifest=self.root/'manifest.json';manifest.write_text(json.dumps(data));return manifest,data
class ManifestTests(FixtureMixin, unittest.TestCase):
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

@unittest.skipUnless(os.environ.get('MATH_GAUGE_TEST_DEPENDENCY_ROOT'),'Set MATH_GAUGE_TEST_DEPENDENCY_ROOT for pinned live Lean tests')
class LiveKernelTests(FixtureMixin, unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.dependency=V.inspect_dependencies(os.environ['MATH_GAUGE_TEST_DEPENDENCY_ROOT'],os.environ.get('MATH_GAUGE_TEST_LEAN'))
    def compile_fixture(self,text):
        manifest,_=self.fixture(text);out=self.root/'out';out.mkdir();return V.verify_case(manifest,self.dependency,out)
    def test_all_constants_include_private_helpers(self):
        report=self.compile_fixture('namespace MathGauge.Fixture\nprivate def hidden : Nat := 7\ndef value : Nat := hidden\ntheorem value_eq : value = 7 := rfl\nend MathGauge.Fixture\n')
        self.assertEqual(report['status'],'passed',report)
        declarations=report['audit']['declarations']
        self.assertTrue(any(d['user_name']=='MathGauge.Fixture.hidden' and d['name'].startswith('_private.') for d in declarations))
        self.assertTrue({'definition','theorem'} <= {d['kind'] for d in declarations})
    def test_nonstandard_axiom_is_rejected_by_the_kernel_audit(self):
        report=self.compile_fixture('namespace MathGauge.Fixture\naxiom extra : False\ntheorem invalid : False := extra\nend MathGauge.Fixture\n')
        self.assertEqual(report['modules'][0]['exit_code'],0)
        self.assertEqual(report['status'],'failed')
        self.assertIn('MathGauge.Fixture.extra',report['audit']['summary']['unexpected_axioms'])
    def test_ambient_olean_path_is_ignored(self):
        manifest,_=self.fixture('import UnlistedForeign\nnamespace MathGauge.Fixture\ndef value := 1\nend MathGauge.Fixture\n')
        foreign=self.root/'foreign';foreign.mkdir();(foreign/'UnlistedForeign.olean').write_bytes(b'not a trusted dependency')
        old=os.environ.get('LEAN_PATH');os.environ['LEAN_PATH']=str(foreign)
        try:
            out=self.root/'out';out.mkdir();report=V.verify_case(manifest,self.dependency,out)
        finally:
            if old is None:os.environ.pop('LEAN_PATH',None)
            else:os.environ['LEAN_PATH']=old
        self.assertEqual(report['status'],'failed');self.assertIn('Missing compiled external import',report['error'])

if __name__=='__main__':unittest.main()
