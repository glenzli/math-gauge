"""Fresh source assessments bind current policy and delivered trajectory identities."""
import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

import test_current_record_scoring as current_record_tests
import test_alignment_scoring as alignment_tests
from math_gauge import submission_evidence
from math_gauge.scoring import (
    _alignment_trajectory, formalization_substitutions, score_assessment_inputs,
    score_assessment_record_inputs, strict_alignment_trajectory,
)

ROOT = current_record_tests.ROOT


def descriptor(name, raw):
    return dict(path=name, bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())


class SelectedFinalRecordScoringTests(unittest.TestCase):
    def setUp(self):
        self.fixture = current_record_tests.FreshRecordScoringTests()
        self.fixture.setUp()
        f = self.fixture
        self.assessment = json.loads((ROOT/'protocol/scoring-policy.json').read_bytes())
        self.submission_policy = json.loads((ROOT/'protocol/submission-scoring-policy.json').read_bytes())
        alignment = f.alignment
        alignment.update(primary_source_kind='submission_selected',
            source_selection_component_version='0.1.0',
            attempt_conditions=['single_attempt', 'nonlogical_retry_3'])
        alignment['baseline'].update(source_kind='original_final', source_sha256='b'*64,
            source_response_sha256='b'*64)
        for row, kind in zip(alignment['rounds'],
                             ('original_final', 'sealed_workspace', 'original_final')):
            snapshot = row['snapshot']
            snapshot['source_kind'] = kind
            snapshot['source_response_sha256'] = ('8'*64 if kind == 'sealed_workspace'
                                                   else snapshot['source_sha256'])
        # A synthetic false-complete diagnosis makes MC and RMC distinct, so
        # using the wrong positive-only trajectory cannot pass by coincidence.
        alignment['rounds'][1]['diagnosis'].update(claims_complete=True, accurate=False,
                                                 global_points=0, localization_points=0)
        self.submission = dict(schema=submission_evidence.REVIEW_SCHEMA, version='0.1.0',
            model_label=f.inputs['model_label'], attempt_condition='nonlogical_retry_3',
            initials=[dict(case_id=c['case_id'], classification='active_final',
                source_response_sha256='b'*64, scored_math_is_delivered=True,
                reason='Synthetic selected normal final', evidence=[descriptor('final.md', b'final')])
                for c in f.inputs['plan']['case_index']],
            rounds=[dict(round=r['round'], classification='active_final',
                source_response_sha256=r['snapshot']['source_response_sha256'],
                mathematical_source_sha256=r['snapshot']['source_sha256'],
                scored_math_is_delivered=True, reason='Synthetic selected round final',
                evidence=[descriptor('round.md', b'round')]) for r in alignment['rounds']],
            normal_alignment=alignment)

    def score(self, mode='partial', **changes):
        f = self.fixture
        kwargs = dict(formalization_review=f.formal, assessment_policy=self.assessment,
            strict_policy=f.data['strict_policy'], mode=mode,
            capability_policy=f.capability if mode == 'capability' else None,
            submission_review=self.submission, submission_policy=self.submission_policy)
        kwargs.update(changes)
        return score_assessment_record_inputs(f.inputs, f.alignment, f.policy, **kwargs)

    def test_mixed_normal_trajectory_matches_direct_scorer_in_all_modes(self):
        f = self.fixture
        original = copy.deepcopy((f.inputs, f.alignment, f.formal, self.submission))
        substitutions = formalization_substitutions(f.inputs, f.formal)
        strict = strict_alignment_trajectory(f.alignment, f.policy, allow_submission_sources=True)
        self.assertEqual([r['snapshot']['source_kind'] for r in f.alignment['rounds']],
                         ['original_final', 'sealed_workspace', 'original_final'])
        reports = {}
        for mode in ('capability', 'partial', 'strict'):
            with self.subTest(mode=mode):
                trajectory = _alignment_trajectory(f.alignment, f.policy,
                    positive_only=mode == 'capability', allow_submission_sources=True)[0]
                expected = score_assessment_inputs(f.inputs, self.assessment, f.data['strict_policy'],
                    mathematical_substitutions=substitutions, alignment_summary=trajectory,
                    strict_trajectory=strict, mode=mode,
                    capability_policy=f.capability if mode == 'capability' else None,
                    submission_review=self.submission, submission_policy=self.submission_policy)
                actual = self.score(mode)
                reports[mode] = actual
                for key in ('metrics', 'contributions', 'tasks', 'alignment_selfcheck',
                            'strict_alignment_selfcheck', 'submission_summary'):
                    self.assertEqual(actual[key], expected[key])
                self.assertEqual(actual['capacity']['total'], 100)
                counts = {r['case_id']: (r['complete_count'], r['total'])
                          for r in actual['lean_formalization_breakdown']['cases']}
                self.assertEqual(counts, {'LCH01': (8, 8), 'LCH02': (20, 20),
                                         'HCH02': (40, 40), 'MG-C003': (24, 92)})
        self.assertGreater(reports['capability']['metrics']['lean-selfcheck']['exact'],
                           reports['partial']['metrics']['lean-selfcheck']['exact'])
        self.assertEqual((f.inputs, f.alignment, f.formal, self.submission), original)

    def test_current_selected_source_requires_complete_policy_evidence(self):
        for changes in ({'submission_policy': None}, {'submission_review': None},
                        {'assessment_policy': self.fixture.data['assessment_policy']}):
            with self.subTest(changes=tuple(changes)), self.assertRaisesRegex(
                    ValueError, 'matching current submission evidence'):
                self.score(**changes)
        invalid = copy.deepcopy(self.submission_policy)
        invalid['version'] = '0.2.0'
        with self.assertRaisesRegex(ValueError, 'Unsupported active-submission'):
            self.score(submission_policy=invalid)

    def test_selected_source_rejects_model_condition_and_round_raw_hash_mismatch(self):
        mutations = (
            ('alignment_model', lambda: self.fixture.alignment.update(model_label='OTHER MODEL')),
            ('submission_model', lambda: self.submission.update(model_label='OTHER MODEL')),
            ('attempt_condition', lambda: self.fixture.alignment.update(attempt_conditions=['single_attempt'])),
            ('round_raw', lambda: self.submission['rounds'][1].update(source_response_sha256='9'*64)),
        )
        for name, mutate in mutations:
            self.setUp()
            mutate()
            with self.subTest(mutation=name), self.assertRaises(ValueError):
                self.score()

    def test_selected_baseline_requires_original_response_and_same_obligation_map(self):
        self.fixture.alignment['baseline']['source_response_sha256'] = '9'*64
        with self.assertRaisesRegex(ValueError, 'original engineering judgment'):
            self.score()
        self.setUp()
        obligations = self.fixture.alignment['baseline']['obligations']
        obligations[0]['complete'] = False
        obligations[-1]['complete'] = True
        self.assertEqual(sum(r['complete'] for r in obligations), 24)
        with self.assertRaisesRegex(ValueError, 'original engineering judgment'):
            self.score()

    def test_modern_four_engineering_source_rejects_older_alignment_policies(self):
        for version in ('0.1.0', '0.3.0'):
            self.setUp()
            if version == '0.1.0':
                policy = alignment_tests.alignment_policy(self.fixture.policy['obligation_ids'])
            else:
                policy = dict(self.fixture.policy, version=version)
            # Reject the old method, rather than an invalid policy fixture.
            from math_gauge.scoring import _alignment_policy
            _alignment_policy(policy)
            self.fixture.policy = policy
            self.fixture.alignment['scoring_version'] = version
            with self.subTest(source_policy=version), self.assertRaises(ValueError):
                self.score()

    def test_selected_baseline_cannot_borrow_another_engineering_or_final_source(self):
        for kind in ('sealed_workspace', 'original_final'):
            self.setUp()
            baseline = self.fixture.alignment['baseline']
            chapter = next(c for c in self.fixture.formal['cases'] if c['case_id'] == 'MG-C003')
            baseline.update(source_kind=kind, source_sha256=(chapter['source_sha256']
                if kind == 'sealed_workspace' else baseline['source_response_sha256']))
            self.score()
            baseline['source_sha256'] = '9'*64
            with self.subTest(source_kind=kind), self.assertRaises(ValueError):
                self.score()

    def test_legacy_sealed_workspace_path_keeps_existing_direct_results(self):
        f = current_record_tests.FreshRecordScoringTests()
        f.setUp()
        substitutions = formalization_substitutions(f.inputs, f.formal)
        strict = strict_alignment_trajectory(f.alignment, f.policy)
        for mode in ('capability', 'partial', 'strict'):
            with self.subTest(mode=mode):
                trajectory = _alignment_trajectory(f.alignment, f.policy,
                    positive_only=mode == 'capability')[0]
                expected = score_assessment_inputs(f.inputs, f.data['assessment_policy'],
                    f.data['strict_policy'], mathematical_substitutions=substitutions,
                    alignment_summary=trajectory, strict_trajectory=strict, mode=mode,
                    capability_policy=f.capability if mode == 'capability' else None)
                actual = f.score(mode)
                self.assertEqual(actual['metrics'], expected['metrics'])
                self.assertEqual(actual['alignment_selfcheck'], expected['alignment_selfcheck'])


class FirstAssessmentSourceTests(unittest.TestCase):
    @staticmethod
    def git_oid(kind, raw):
        return hashlib.sha1(kind.encode()+b' '+str(len(raw)).encode()+b'\0'+raw).hexdigest()

    def fixture(self, folder, *, policy=None, tree_mode=b'100644', embedded_policy=None):
        current = json.loads((ROOT/'protocol/scoring-policy.json').read_bytes())
        policy = copy.deepcopy(current if policy is None else policy)
        def keep(name, raw):
            if not isinstance(raw, bytes):
                raw = (json.dumps(raw, sort_keys=True)+'\n').encode()
            (folder/name).write_bytes(raw)
            return descriptor(name, raw)
        policy_raw = (json.dumps(policy, sort_keys=True)+'\n').encode()
        protocol = tree_mode+b' scoring-policy.json\0'+bytes.fromhex(self.git_oid('blob', policy_raw))
        profile_raw = None
        if embedded_policy is not None:
            profile_raw = (json.dumps({'assessment_policy': embedded_policy}, sort_keys=True)+'\n').encode()
            protocol = (b'100644 benchmark-profile.json\0'
                        + bytes.fromhex(self.git_oid('blob', profile_raw)) + protocol)
        root = b'40000 protocol\0'+bytes.fromhex(self.git_oid('tree', protocol))
        commit = (f"tree {self.git_oid('tree', root)}\n"
                  'author Synthetic Test <fixture@example.invalid> 0 +0000\n'
                  'committer Synthetic Test <fixture@example.invalid> 0 +0000\n\n'
                  'Synthetic policy source only\n').encode()
        freeze = dict(benchmark_version='1.0.0', utc='2026-11-13T00:00:00Z',
            all_initials_fresh=True, historical_answers_reused=0, mathematical_requests=0,
            public_commit=self.git_oid('commit', commit))
        proof = dict(schema='math-gauge.first-assessment-source/v1', kind='fresh_source',
            assessment_method_version='0.9.0', source_benchmark_version='1.0.0',
            model_id='synthetic-fresh-source', new_candidate_calls=0,
            source_freeze=keep('freeze.json', freeze),
            source_commit_object=keep('commit.object', commit),
            source_root_tree=keep('root.tree', root),
            source_protocol_tree=keep('protocol.tree', protocol),
            source_assessment_policy=keep('policy.json', policy_raw))
        if profile_raw is not None:
            proof['source_benchmark_profile'] = keep('profile.json', profile_raw)
        proof['first_dispatch'] = keep('first-dispatch.json', dict(
            utc='2026-11-13T00:00:01Z', freeze_sha256=proof['source_freeze']['sha256']))
        record = dict(model_id='synthetic-fresh-source', benchmark_version='1.0.0',
                      first_assessment_source=keep('first-assessment-source.json', proof))
        return record, proof, current

    def rebind(self, folder, record, proof, key, value):
        item = proof[key]
        raw = value if isinstance(value, bytes) else (json.dumps(value, sort_keys=True)+'\n').encode()
        (folder/item['path']).write_bytes(raw)
        proof[key] = descriptor(item['path'], raw)
        raw = (json.dumps(proof, sort_keys=True)+'\n').encode()
        (folder/'first-assessment-source.json').write_bytes(raw)
        record['first_assessment_source'] = descriptor('first-assessment-source.json', raw)

    def test_fresh_policy_source_is_verified_without_invented_score_history(self):
        with tempfile.TemporaryDirectory() as temp:
            folder = Path(temp)
            record, proof, current = self.fixture(folder)
            self.assertNotIn('score_history', record)
            self.assertEqual(submission_evidence.validate_first_assessment_source(folder, record, current), current)
            self.assertEqual(submission_evidence.original_assessment_policy(folder, record, current), current)
            self.assertEqual(len(list(folder.iterdir())), 7)

    def test_real_older_profile_labels_need_same_tree_and_identical_math(self):
        current = json.loads((ROOT/'protocol/scoring-policy.json').read_bytes())
        old = dict(current, version='0.8.0', capability_policy_version='0.2.0')
        old.pop('submission_policy_version')
        with tempfile.TemporaryDirectory() as temp:
            folder = Path(temp)
            record, proof, _ = self.fixture(folder, embedded_policy=old)
            self.assertEqual(submission_evidence.original_assessment_policy(folder, record, current), old)
            changed = dict(old, fixture_changed_metadata='unbound profile')
            self.rebind(folder, record, proof, 'source_benchmark_profile',
                        {'assessment_policy': changed})
            with self.assertRaisesRegex(ValueError, 'frozen source commit'):
                submission_evidence.original_assessment_policy(folder, record, current)
        with tempfile.TemporaryDirectory() as temp:
            folder = Path(temp)
            record, _, _ = self.fixture(folder, embedded_policy=dict(old, fixture_changed_metadata='changed math'))
            with self.assertRaisesRegex(ValueError, 'frozen mathematical policy'):
                submission_evidence.original_assessment_policy(folder, record, current)

    def test_complete_git_chain_cannot_substitute_another_current_policy(self):
        with tempfile.TemporaryDirectory() as temp:
            folder = Path(temp)
            current = json.loads((ROOT/'protocol/scoring-policy.json').read_bytes())
            altered = dict(current, fixture_changed_metadata='a different original policy')
            record, proof, _ = self.fixture(folder, policy=altered)
            with self.assertRaisesRegex(ValueError, 'original source policy'):
                submission_evidence.validate_first_assessment_source(folder, record, current)

    def test_changed_object_or_executable_policy_mode_breaks_git_provenance(self):
        for mutation in ('commit', 'protocol', 'policy_mode'):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as temp:
                folder = Path(temp)
                record, proof, current = self.fixture(folder,
                    tree_mode=b'100755' if mutation == 'policy_mode' else b'100644')
                if mutation != 'policy_mode':
                    key = 'source_commit_object' if mutation == 'commit' else 'source_protocol_tree'
                    raw = (folder/proof[key]['path']).read_bytes()
                    changed = raw+b'changed' if mutation == 'commit' else raw[:-1]+bytes([raw[-1] ^ 1])
                    self.rebind(folder, record, proof, key, changed)
                with self.assertRaisesRegex(ValueError, 'actual frozen source commit'):
                    submission_evidence.validate_first_assessment_source(folder, record, current)

    def test_first_dispatch_must_follow_and_bind_actual_fresh_source_freeze(self):
        for mutation in ('dispatch_hash', 'dispatch_before', 'dispatch_equal',
                         'freeze_edition', 'reused_answers', 'already_dispatched'):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as temp:
                folder = Path(temp)
                record, proof, current = self.fixture(folder)
                key = 'first_dispatch' if mutation.startswith('dispatch') else 'source_freeze'
                value = json.loads((folder/proof[key]['path']).read_bytes())
                if mutation == 'dispatch_hash': value['freeze_sha256'] = '0'*64
                elif mutation == 'dispatch_before': value['utc'] = '2026-11-12T23:59:59Z'
                elif mutation == 'dispatch_equal': value['utc'] = '2026-11-13T00:00:00Z'
                elif mutation == 'freeze_edition': value['benchmark_version'] = '0.6.0'
                elif mutation == 'reused_answers': value['historical_answers_reused'] = 1
                else: value['mathematical_requests'] = 1
                self.rebind(folder, record, proof, key, value)
                # A refreshed descriptor must not make a changed freeze authentic.
                if key == 'source_freeze':
                    dispatch = json.loads((folder/proof['first_dispatch']['path']).read_bytes())
                    dispatch['freeze_sha256'] = proof['source_freeze']['sha256']
                    self.rebind(folder, record, proof, 'first_dispatch', dispatch)
                with self.assertRaisesRegex(ValueError, 'pre-call fresh source freeze'):
                    submission_evidence.validate_first_assessment_source(folder, record, current)

    def test_fresh_source_rejects_older_edition_method_model_and_dual_history(self):
        for mutation in ('record_edition', 'proof_edition', 'old_method', 'model', 'dual_history'):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as temp:
                folder = Path(temp)
                record, proof, current = self.fixture(folder)
                if mutation == 'record_edition': record['benchmark_version'] = '0.6.0'
                elif mutation == 'old_method':
                    current.update(version='0.8.0', capability_policy_version='0.2.0')
                    current.pop('submission_policy_version', None)
                elif mutation == 'dual_history': record['score_history'] = {}
                else:
                    proof['source_benchmark_version' if mutation == 'proof_edition' else 'model_id'] = (
                        '0.6.0' if mutation == 'proof_edition' else 'different-model')
                    raw = (json.dumps(proof, sort_keys=True)+'\n').encode()
                    (folder/'first-assessment-source.json').write_bytes(raw)
                    record['first_assessment_source'] = descriptor('first-assessment-source.json', raw)
                with self.assertRaises(ValueError):
                    submission_evidence.original_assessment_policy(folder, record, current)


if __name__ == '__main__':
    unittest.main()
