"""Candidate transport/artifact contracts, plus opt-in isolated kernel checks.

No model requests. Set MATH_GAUGE_CANDIDATE_DEPENDENCIES for real Lean fixtures.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

from math_gauge.catalog import Suite, candidate_message, digest_bytes, write_json
from math_gauge.execution import (
    extract_candidate_lean, verify_candidate_lean, _candidate_sources,
    _candidate_policy, _missing_cached_source, _candidate_engine,
    _override_extraction,
    run,
)


class CandidateArtifactTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def request(self, files=()):
        return {"task": "题面\r\n原样保留。\r\n", "instruction": "", "files": list(files),
                "case_id": "TEST", "track": "alignment", "secret_evaluator_field": "NOT_VISIBLE"}

    def case(self, response, files=()):
        case = self.root / "case"; (case / "solver").mkdir(parents=True)
        request = self.request(files)
        write_json(case / "solver/request.json", request)
        (case / "response.md").write_bytes(response.encode())
        write_json(case / "record.json", {
            "response_sha256": digest_bytes(response.encode()),
            "request_sha256": digest_bytes(json.dumps(request, ensure_ascii=False, sort_keys=True).encode()),
            "status": "ok"})
        return case

    def test_empty_attachments_preserve_exact_task(self):
        request = self.request()
        self.assertEqual(candidate_message(request).encode(), request["task"].encode())
        request["instruction"] = "legacy"
        self.assertEqual(candidate_message(request), "legacy\n\n" + request["task"])

    def test_neutral_attachment_serialization_has_dynamic_fence(self):
        content = '/- ```inside\n```` end -/\r\ndef α := 1'
        request = self.request([{"name": "Core.lean", "content": content}])
        message = candidate_message(request)
        self.assertTrue(message.startswith(request["task"]))
        self.assertIn("`````lean\n" + content + "\n`````", message)
        self.assertNotIn("NOT_VISIBLE", message)
        self.assertNotIn('"case_id"', message)
        self.assertIn(content.encode(), message.encode())

    def test_duplicate_or_escaping_input_attachment_rejected(self):
        with self.assertRaises(ValueError):
            candidate_message(self.request([{"name": "../Core.lean", "content": ""}]))
        with self.assertRaises(ValueError):
            candidate_message(self.request([{"name": "Core.lean", "content": ""}] * 2))

    def test_suite_preparation_preserves_real_attachment_crlf(self):
        target=self.root/'suite'
        shutil.copytree(Path(__file__).resolve().parents[1]/'tests/fixtures/runner-suite',target)
        suite=Suite.load(target);case=suite.cases['TEST-F004']
        body=b'-- attachment\r\ntheorem answer : True := True.intro\r\n'
        (target/case['solver_files'][0]['source']).write_bytes(body)
        suite=Suite.load(target)
        request=suite.prepare(suite.cases['TEST-F004'],self.root/'solver')
        item=request['files'][0]
        self.assertEqual(item['content'].encode(),body)
        self.assertEqual((self.root/'solver'/item['name']).read_bytes(),body)
        self.assertIn(body,candidate_message(request).encode())

    def test_runner_freezes_message_and_default_family(self):
        suite=Suite.load(Path(__file__).resolve().parents[1]/'tests/fixtures/runner-suite')
        replay=self.root/'replay.json';write_json(replay,{'TEST-D001':'fixture only'})
        result=run(suite,self.root/'run',['TEST-D001'],replay=replay)
        item=result['cases'][0]
        self.assertEqual(item['task_kind'],'exploration')
        self.assertEqual(item['family_id'],'TEST-D001')
        message=candidate_message(suite.request(suite.cases['TEST-D001']))
        self.assertEqual(item['candidate_message_sha256'],digest_bytes(message.encode()))
        self.assertRegex(result['run_id'],r'^[0-9a-f]{32}$')
        self.assertEqual(json.loads((self.root/'run/run.json').read_text())['run_id'],result['run_id'])

    def test_runner_freezes_raw_adapter_stdout(self):
        suite=Suite.load(Path(__file__).resolve().parents[1]/'tests/fixtures/runner-suite')
        body=b'\xe8\xaf\x81\xe6\x98\x8e\r\n```lean filename=Solution.lean\r\ntheorem answer : True := True.intro\r\n```\r\n'
        command=[sys.executable,'-c','import sys;sys.stdin.buffer.read();sys.stdout.buffer.write('+repr(body)+')']
        run(suite,self.root/'run',['TEST-D001'],command=command,model='synthetic-local-fixture')
        self.assertEqual((self.root/'run/TEST-D001/response.md').read_bytes(),body)

    def test_extract_preserves_source_bytes_and_offsets(self):
        source = '-- 中文\r\ntheorem answer : True := by trivial\r\n'
        response = '说明\r\n```lean filename=Solution.lean\r\n' + source + '```\r\n'
        item = extract_candidate_lean(response)[0]
        self.assertEqual(item["content"], source)
        self.assertEqual(response.encode()[item['start_byte']:item['end_byte']], source.encode())

    def test_unicode_filename_is_not_rejected(self):
        self.assertEqual(extract_candidate_lean('```lean filename=证明.lean\ntheorem answer : True := True.intro\n```')[0]['name'], '证明.lean')

    def test_explicit_reviewed_extraction_keeps_whole_fenced_body(self):
        response='Explanation snippet:\n```lean\n#check Nat\n```\nThe complete file:\n```lean\ntheorem answer : True := True.intro\n```\n'
        raw=response.encode();body=b'theorem answer : True := True.intro\n';start=raw.index(body)
        override={'reviewer':'independent fixture','reviewer_kind':'ai','reason':'Second fence is explicitly identified as complete file; first is an explanatory snippet.',
                  'files':[{'name':'Solution.lean','start_byte':start,'end_byte':start+len(body)}]}
        files=_override_extraction(response,override)
        self.assertEqual(files[0]['content'].encode(),body)
        override['files'][0]['start_byte']+=1
        with self.assertRaises(ValueError):_override_extraction(response,override)

    def test_override_cannot_supply_repaired_content(self):
        override={'reviewer':'test','reviewer_kind':'human','reason':'test',
                  'files':[{'name':'Solution.lean','start_byte':0,'end_byte':0,'content':'fixed code'}]}
        with self.assertRaises(ValueError):_override_extraction('',override)

    def test_existing_heading_and_info_formats(self):
        for heading in ('Solution.lean', '`Solution.lean`', '### Solution.lean', '文件：`Solution.lean`', 'File: Solution.lean'):
            with self.subTest(heading=heading):
                self.assertEqual(extract_candidate_lean(heading + '\n\n```lean\ndef x := 1\n```')[0]['name'], 'Solution.lean')
        for info in ('lean filename="Solution.lean"', 'lean Solution.lean', 'lean4 filename=Solution.lean'):
            self.assertEqual(extract_candidate_lean('```'+info+'\ndef x := 1\n```')[0]['name'], 'Solution.lean')

    def test_duplicate_unsafe_unnamed_and_unclosed_files_fail(self):
        inputs = [
            '```lean\ndef x := 1\n```',
            '```lean filename=../Escape.lean\ndef x := 1\n```',
            '```lean filename=/Escape.lean\ndef x := 1\n```',
            '```lean filename=Foo.lean\ndef x := 1',
            '```lean filename=Foo.lean\ndef x := 1\n```\n```lean filename=foo.lean\ndef y := 2\n```',
        ]
        for response in inputs:
            with self.subTest(response=response), self.assertRaises(ValueError):
                extract_candidate_lean(response)

    def test_non_lean_and_quoted_fragments_are_not_deliveries(self):
        with self.assertRaises(ValueError):
            extract_candidate_lean('```text\n```lean filename=Foo.lean\n```\n')
        with self.assertRaises(ValueError):
            extract_candidate_lean('No code, only a proof outline.')

    def test_source_closure_replaces_inputs_and_omits_unused_inputs(self):
        engine, _ = _candidate_engine()
        submitted = {'Solution.lean': 'import Core\ntheorem answer : True := True.intro\n'}
        inputs = {'Core.lean': 'def core := 1\n', 'Candidate.lean': 'import Core\n'}
        sources, external = _candidate_sources(submitted, inputs, engine['source_imports'])
        self.assertEqual([x[0] for x in sources], ['Core.lean', 'Solution.lean'])
        self.assertEqual(external, set())
        sources, _ = _candidate_sources({'Core.lean':'def core := 2\n'}, inputs, engine['source_imports'])
        self.assertEqual(sources, [('Core.lean','def core := 2\n')])

    def test_local_cycles_and_case_collisions_fail(self):
        engine, _ = _candidate_engine()
        with self.assertRaisesRegex(ValueError, 'Cyclic'):
            _candidate_sources({'A.lean':'import B\n','B.lean':'import A\n'}, {}, engine['source_imports'])
        with self.assertRaisesRegex(ValueError, 'colliding'):
            _candidate_sources({'core.lean':''}, {'Core.lean':''}, engine['source_imports'])

    def test_no_code_is_not_an_empty_success(self):
        case = self.case('I did not complete the proof.')
        report = verify_candidate_lean(case, self.root/'out', dependency_root='/unused')
        self.assertEqual(report['status'], 'format_error')
        self.assertEqual(report['response_sha256'], digest_bytes((case/'response.md').read_bytes()))
        self.assertFalse(report['semantic_alignment_inferred'])

    def test_tampered_response_is_rejected_before_extraction(self):
        case = self.case('original')
        (case/'response.md').write_text('changed')
        report = verify_candidate_lean(case,self.root/'out',dependency_root='/unused')
        self.assertEqual(report['status'],'infrastructure_error')

    def test_required_filename_only_when_caller_supplies_task_contract(self):
        case = self.case('```lean filename=Other.lean\ntheorem answer : True := True.intro\n```')
        report = verify_candidate_lean(case,self.root/'out',dependency_root='/unused',required_files=('Solution.lean',))
        self.assertEqual(report['status'],'format_error')
        self.assertIn('Task-required',report['reason'])

    def test_isolation_unavailable_never_falls_back_to_host_compile(self):
        case = self.case('```lean filename=Solution.lean\ntheorem answer : True := True.intro\n```')
        with patch('math_gauge.execution.sys.platform','unsupported'):
            report = verify_candidate_lean(case,self.root/'out',dependency_root='/unused')
        self.assertEqual(report['status'],'infrastructure_error')
        self.assertTrue(report['artifact_sha256'])
        self.assertEqual((self.root/'out/submitted/Solution.lean').read_bytes(),b'theorem answer : True := True.intro\n')

    def test_policy_has_no_network_or_host_write_allow(self):
        dep={'lean':'/pinned/bin/lean','search_paths':['/pinned/lib/lean']}
        policy = _candidate_policy(Path('/work/sources'),Path('/work/build'),Path('/work/scratch'),dep)
        self.assertIn('(deny default)',policy)
        self.assertNotIn('(allow network',policy)
        self.assertNotIn('(allow process-fork',policy)
        self.assertNotIn('(subpath "/Users")',policy)

    def test_cached_source_missing_is_distinct_from_nonexistent_module(self):
        package=self.root/'mathlib';library=package/'.lake/build/lib/lean';library.mkdir(parents=True)
        (package/'Known.lean').write_text('')
        dep={'search_paths':[str(library)]}
        self.assertTrue(_missing_cached_source('Known',dep))
        self.assertFalse(_missing_cached_source('Typo',dep))


@unittest.skipUnless(sys.platform == 'darwin' and os.environ.get('MATH_GAUGE_CANDIDATE_DEPENDENCIES'),
                     'requires explicitly selected Lean dependency cache and macOS isolation')
class CandidateKernelTests(unittest.TestCase):
    setUp = CandidateArtifactTests.setUp
    request = CandidateArtifactTests.request
    case = CandidateArtifactTests.case

    def check_source(self, source):
        case=self.case('```lean filename=Solution.lean\n'+source+'\n```')
        return verify_candidate_lean(case,self.root/'verified',
            dependency_root=os.environ['MATH_GAUGE_CANDIDATE_DEPENDENCIES'],
            lean=os.environ.get('MATH_GAUGE_CANDIDATE_LEAN'),timeout=60)

    def test_arbitrary_namespace_and_private_declarations_are_audited(self):
        report=self.check_source('namespace Unrelated\nprivate theorem hidden : True := True.intro\ntheorem visible : True := hidden\nend Unrelated')
        self.assertEqual(report['status'],'passed',report)
        self.assertEqual(report['audit']['summary']['unexpected_axioms'],[])
        self.assertTrue(any('hidden' in x['name'] for x in report['audit']['declarations']))

    def test_unused_axiom_outside_mathgauge_rejected(self):
        report=self.check_source('namespace Other\naxiom unused : False\ntheorem ordinary : True := True.intro\nend Other')
        self.assertEqual(report['status'],'axiom_rejected',report)

    def test_sorry_outside_mathgauge_rejected(self):
        report=self.check_source('theorem incomplete : False := by sorry')
        self.assertEqual(report['status'],'axiom_rejected',report)

    def test_source_cannot_read_host_file(self):
        secret=self.root/'secret.txt';secret.write_text('PRIVATE_CANDIDATE_PROBE_CONTENT')
        report=self.check_source('#eval IO.FS.readFile '+json.dumps(str(secret))+'\ntheorem answer : True := True.intro')
        self.assertEqual(report['status'],'compile_error',report)
        self.assertNotIn('PRIVATE_CANDIDATE_PROBE_CONTENT', ''.join(p.read_text() for p in (self.root/'verified/logs').glob('*.log')))

    def test_mathlib_and_frozen_background_dependency(self):
        background = 'import Mathlib\nnamespace Background\ndef increment (n : ℕ) := n + 1\nend Background\n'
        source = 'import Core\nnamespace Alternate\ntheorem answer : Background.increment 2 = 3 := by norm_num [Background.increment]\nend Alternate\n'
        case=self.case('```lean filename=Solution.lean\n'+source+'```',
                       [{'name':'Core.lean','content':background},
                        {'name':'Unused.lean','content':'axiom unused : False\n'}])
        report=verify_candidate_lean(case,self.root/'verified',
            dependency_root=os.environ['MATH_GAUGE_CANDIDATE_DEPENDENCIES'],
            lean=os.environ.get('MATH_GAUGE_CANDIDATE_LEAN'),timeout=60)
        self.assertEqual(report['status'],'passed',report)
        self.assertEqual([x['module'] for x in report['modules'][:-1]],['Core','Solution'])
        self.assertTrue((self.root/'verified/inputs/Unused.lean').exists())
        self.assertEqual(report['input_files_sha256']['Core.lean'],digest_bytes(background.encode()))


if __name__ == '__main__':
    unittest.main()
