"""Parallel collector contracts with synthetic responses; no candidate/Lean calls."""
import copy
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
import zipfile

from benchmark_fixtures import fixture_profile, fixture_suite
from math_gauge.benchmarks import build_plan
from math_gauge.catalog import read_json, write_json
from math_gauge.harness import (
    COMPACT_CONTROLLER, LEGACY_COMPACT_CONTROLLER, SIMPLE_CONTROLLER, _h_identity,
    export_simple_release_dataset, freeze_release_runtime, inspect_release_run,
    make_release_anchor,
)
from math_gauge.harness_answers import (
    inspect_answer_collection, issue_answer_request, record_answer_attempt,
    skip_answer_slot, pack_answer_archive,
)
from math_gauge.harness_import import import_answer_archive, import_harness_submission
from math_gauge.reliability import inspect_reliability_run

RUNTIME = {'model_label': 'synthetic-parallel-fixture', 'adapter_identity': {'kind': 'fixture'},
           'candidate_parameters': {'model': 'no-model-calls'},
           'budget': {'timeout_seconds': 2}, 'fresh_context': True}


class ParallelHarnessTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.suite = fixture_suite()
        cls.plan = build_plan(fixture_profile(cls.suite), cls.suite, ['all'])
        cls.shared_temp = tempfile.TemporaryDirectory()
        cls.addClassCleanup(cls.shared_temp.cleanup)
        cls.shared = Path(cls.shared_temp.name).resolve() / 'dataset'
        cls.manifest = export_simple_release_dataset(cls.plan, cls.suite, cls.shared,
            release_version=cls.suite.metadata['version'], readme=b'Synthetic software fixture, no candidate calls.\n',
            extra_files={'LICENSE': b'fixture\n', 'THIRD_PARTY_NOTICES.md': b'fixture\n'})
        cls.anchor = make_release_anchor(cls.plan, cls.manifest)

    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name).resolve()
        self.dataset = self.root / 'dataset'
        shutil.copytree(self.shared, self.dataset)
        self.run, self.responses = self.root / 'run', self.root / 'responses'
        self.number = 0

    def freeze(self, runtime=None, targets=('lean-formalization',)):
        return freeze_release_runtime(self.dataset, runtime or RUNTIME, self.run, targets=list(targets))

    def issue(self, sid):
        self.number += 1
        path = self.root / f'request-{self.number}.json'
        request = issue_answer_request(self.run, self.responses, sid, path)
        return path, request

    def record(self, sid, request, raw, status='ok'):
        self.number += 1
        path = self.root / f'raw-{self.number}.md'
        path.write_bytes(raw)
        return record_answer_attempt(self.run, self.responses, sid, request, path, status=status)

    def test_independent_jobs_return_out_of_order_and_one_exhaustion_does_not_stop_batch(self):
        slots = self.freeze()['selected_slot_ids']
        first, second, third = slots[:3]
        second_path, second_request = self.issue(second)
        first_path, _ = self.issue(first)
        state = inspect_answer_collection(self.run, self.responses)
        self.assertEqual(sum(r['state'] == 'awaiting_response' for r in state['slots']), 2)
        self.record(first, first_path, b'', 'budget_exhausted')
        raw = 'Synthetic 原始答卷\r\n'.encode()
        self.record(second, second_path, raw)
        third_path, third_request = self.issue(third)
        self.assertNotIn(raw.decode(), json.dumps(third_request))
        self.assertEqual(third_request['parameters'], second_request['parameters'])
        self.record(third, third_path, b'Third independent fixture\r\n')
        skip_answer_slot(self.run, self.responses, slots[-1], 'Synthetic explicit omission')
        self.assertFalse(inspect_answer_collection(self.run, self.responses)['budget']['stopped'])
        with self.assertRaisesRegex(ValueError, 'locked'):
            self.issue(second)
        archive = self.root / 'answers.zip'
        pack_answer_archive(self.run, self.responses, archive, origin='fixture', declared_external_calls=0)
        direct_source = self.root / 'direct-submission'
        with zipfile.ZipFile(archive) as zipped:
            for name in zipped.namelist():
                if name.startswith('submission/'):
                    path = direct_source / name.removeprefix('submission/')
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_bytes(zipped.read(name))
        submitted = read_json(direct_source / 'submission.json')
        self.assertEqual([row['slot_id'] for row in submitted['slots']], [first, second, third])
        # Both ingestion routes use the same v4 per-slot exhaustion semantics.
        for direct in (False, True):
            out = self.root / ('direct' if direct else 'portable')
            if direct:
                import_harness_submission(self.run, direct_source / 'submission.json', self.plan, self.suite, out)
            else:
                import_answer_archive(archive, self.anchor, self.suite, out)
            meta, records = inspect_reliability_run(out)
            self.assertEqual(meta['candidate_calls'], 0)
            self.assertIsNone(meta['budget_stop_reason'])
            self.assertEqual(records[first]['status'], 'execution_error')
            self.assertEqual(records[second]['status'], 'responded')
            self.assertEqual((out / records[second]['response_path']).read_bytes(), raw)
            self.assertEqual(records[third]['status'], 'responded')

    def test_followup_requires_only_its_own_parents_and_cannot_skip_an_outstanding_reply(self):
        run = self.freeze(targets=('lean-formalization', 'neutral'))
        dataset = read_json(self.run / 'dataset/manifest.json')
        indexed = {s['slot_id']: s for s in dataset['slots']}
        followup = next(sid for sid in run['selected_slot_ids'] if indexed[sid]['kind'] == 'followup')
        parent = indexed[followup]['parent_slot']
        unrelated = next(sid for sid in run['selected_slot_ids']
                         if indexed[sid]['kind'] == 'independent' and sid != parent)
        with self.assertRaisesRegex(ValueError, 'parent'):
            self.issue(followup)
        other_path, _ = self.issue(unrelated)
        parent_path, _ = self.issue(parent)
        own = b'ONLY_THIS_BRANCH_PARENT\r\n'
        self.record(parent, parent_path, own)
        _, request = self.issue(followup)
        self.assertEqual([m['content'] for m in request['messages'] if m['role'] == 'assistant'], [own.decode()])
        self.assertEqual(next(s['state'] for s in inspect_answer_collection(self.run, self.responses)['slots']
                              if s['slot_id'] == unrelated), 'awaiting_response')
        with self.assertRaisesRegex(ValueError, 'outstanding'):
            skip_answer_slot(self.run, self.responses, unrelated, 'Cannot discard an issued answer')
        self.record(unrelated, other_path, b'Unrelated branch content\r\n')

    def test_shared_cumulative_caps_keep_manifest_order_and_one_outstanding_request(self):
        for key in ('max_total_tokens', 'max_transport_attempts'):
            with self.subTest(cap=key):
                runtime = copy.deepcopy(RUNTIME)
                runtime['budget'][key] = 100
                run = freeze_release_runtime(self.dataset, runtime, self.root / key, targets=['lean-formalization'])
                responses = self.root / (key + '-responses')
                first, second = run['selected_slot_ids'][:2]
                with self.assertRaisesRegex(ValueError, 'frozen slot order'):
                    issue_answer_request(self.root / key, responses, second, self.root / (key + '-early.json'))
                issued = self.root / (key + '-first.json')
                issue_answer_request(self.root / key, responses, first, issued)
                with self.assertRaisesRegex(ValueError, 'frozen slot order'):
                    issue_answer_request(self.root / key, responses, second, self.root / (key + '-pending.json'))

    def test_legacy_controller_revisions_keep_original_order_and_global_exhaustion(self):
        for version in (SIMPLE_CONTROLLER, LEGACY_COMPACT_CONTROLLER):
            with self.subTest(controller=version):
                root = self.root / version.rsplit('/', 1)[-1]
                dataset = root / 'dataset'
                shutil.copytree(self.shared, dataset)
                legacy = read_json(dataset / 'manifest.json')
                legacy['controller_version'] = version
                legacy['dataset_sha256'] = _h_identity({k: v for k, v in legacy.items() if k != 'dataset_sha256'})
                write_json(dataset / 'manifest.json', legacy)
                run = freeze_release_runtime(dataset, RUNTIME, root / 'run', targets=['lean-formalization'])
                responses = root / 'responses'
                first, second = run['selected_slot_ids'][:2]
                with self.assertRaisesRegex(ValueError, 'frozen slot order'):
                    issue_answer_request(root / 'run', responses, second, root / 'early.json')
                request = root / 'first.json'
                issue_answer_request(root / 'run', responses, first, request)
                raw = root / 'empty.md'; raw.write_bytes(b'')
                record_answer_attempt(root / 'run', responses, first, request, raw, status='budget_exhausted')
                self.assertEqual(inspect_answer_collection(root / 'run', responses)['budget']['stop_reason'], 'adapter_budget_exhausted')
                with self.assertRaisesRegex(ValueError, 'budget'):
                    issue_answer_request(root / 'run', responses, second, root / 'after-stop.json')

    def test_generated_neutral_helper_collects_parallel_returns_and_imports_without_execution(self):
        from scripts.release import release_plan
        plan, suite = release_plan()
        dataset = self.root / 'neutral'
        manifest = export_simple_release_dataset(plan, suite, dataset, release_version=suite.metadata['version'],
            readme=b'Neutral synthetic software check\n',
            extra_files={'LICENSE': b'fixture\n', 'THIRD_PARTY_NOTICES.md': b'fixture\n'},
            release_provenance={'candidate_projection': plan['candidate_projection']})
        helper = dataset / 'tools/benchmark.py'
        runtime = self.root / 'runtime.json'; write_json(runtime, RUNTIME)
        run, responses = self.root / 'neutral-run', self.root / 'neutral-responses'
        def command(*args):
            completed = subprocess.run([sys.executable, '-I', '-S', '-B', str(helper), *map(str, args)],
                                       cwd=self.root, capture_output=True)
            self.assertEqual(completed.returncode, 0, completed.stderr)
            return json.loads(completed.stdout)
        prepared = command('prepare', '--runtime', runtime, '--target', 'proofs', '--out', run)
        self.assertEqual(inspect_release_run(run)['controller_version'], COMPACT_CONTROLLER.replace('math-gauge.', 'benchmark.'))
        first, second = prepared['selected_slot_ids'][:2]
        requests = {}
        for sid in (second, first):
            path = self.root / (sid.replace(':', '-') + '.json')
            command('request', '--run', run, '--responses', responses, '--slot', sid, '--out', path)
            requests[sid] = path
        for sid, raw, status in [(second, b'Neutral fixture\r\n', 'ok'), (first, b'', 'budget_exhausted')]:
            response = self.root / (sid.replace(':', '-') + '.md'); response.write_bytes(raw)
            command('record', '--run', run, '--responses', responses, '--slot', sid,
                    '--request', requests[sid], '--response', response, '--status', status)
        archive = self.root / 'neutral-answers.zip'
        command('pack', '--run', run, '--responses', responses, '--out', archive, '--origin', 'fixture', '--declared-external-calls', 0)
        out = self.root / 'neutral-imported'
        import_answer_archive(archive, make_release_anchor(plan, manifest), suite, out)
        meta, records = inspect_reliability_run(out)
        self.assertEqual(meta['candidate_calls'], 0)
        self.assertEqual((out / records[second]['response_path']).read_bytes(), b'Neutral fixture\r\n')


if __name__ == '__main__':
    unittest.main()
