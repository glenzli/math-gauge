"""External admission regressions using synthetic manuscripts and operator data only.

No private case, real response, model call, native receipt or historical result is
used. The CLI concurrency tests mock preparation, then exercise the real writer.
"""
from contextlib import redirect_stdout
from copy import deepcopy
from datetime import datetime, timezone
import io
import json
from pathlib import Path
import shutil
import struct
import unittest
from unittest.mock import patch
from zipfile import ZipFile

from math_gauge import independent_research_external as external
from math_gauge import independent_research_handoff as handoff
from math_gauge import independent_research_value as value
from math_gauge import taste_v130 as flow
from scripts import adopt_independent_research_external as cli
from scripts import export_independent_research_handoff as exporter
from test_independent_research_review import write_policy
import test_taste_v130 as fixture_support


MODEL = 'claude-opus-5.5-max'
OTHER = 'claude-opus-5.5-xhigh'
MARKER = 'SYNTHETIC-PRIVATE-EXTERNAL-EVIDENCE'


def absolute_descriptor(path):
    raw = path.read_bytes()
    return dict(path=str(path), bytes=len(raw), sha256=external.digest(raw))


class ExternalAdmissionTests(unittest.TestCase):
    def setUp(self):
        fixture = fixture_support.ProtocolFixture('runTest')
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        self.root, self.registration = fixture.root, fixture.registration
        for name in ('second', 'third', 'fourth'):
            image = fixture.case / f'packet/figures/{name}.png'
            image.write_bytes(f'Synthetic {name} image bytes'.encode())
            fixture.reg['packet'].append(fixture_support.descriptor(image, fixture.case))
        fixture_support.write_json(self.registration, fixture.reg)
        self.review_policy = write_policy(fixture)
        exporter.build(self.registration, self.root / 'built')
        archive = self.root / 'built' / exporter.ARCHIVE_NAME
        self.bundle = self.root / 'operator'
        with ZipFile(archive) as zipped:
            zipped.extractall(self.bundle)

        self.public = self.root / 'public'
        for name in external.POLICY_PATHS.values():
            destination = self.public / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes((flow.POLICY_FILE.parents[3] / name).read_bytes())
        (self.public / 'site').mkdir()
        fixture_support.write_json(self.public / 'site/data.json',
            dict(benchmark_version='1.2.0', models=[dict(id=MODEL), dict(id=OTHER)]))

        self.state = self.root / 'operator-state'
        self.session_id = 'synthetic-operator-session'
        metadata = self.root / 'operator-metadata.json'
        fixture_support.write_json(metadata, dict(synthetic=True,
            model=dict(requested=external.CONFIGURATIONS[MODEL][0], reasoning_effort='max')))
        # These are synthetic operator declarations. No native/model execution is
        # represented by the test, and the absent native evidence is explicit.
        handoff.prepare(self.bundle, self.state, self.session_id, metadata=metadata)
        candidate = self.root / 'candidate-output'
        candidate.mkdir()
        (candidate / 'unsubmitted.md').write_bytes(b'UNSUBMITTED-WORKSPACE-SENTINEL')
        for round_id in handoff.ROUNDS:
            handoff.reveal(self.bundle, self.state, self.session_id, round_id,
                           self.root / f'released-{round_id}')
            capture = self.root / f'capture-{round_id}'
            capture.mkdir()
            (capture / 'final.md').write_bytes(f'See the synthetic {round_id} attachment.\r\n'.encode())
            attachment = f'manuscript-{round_id}.md'
            (candidate / attachment).write_bytes(f'{round_id}: 合成 λ {MARKER}.\r\n'.encode())
            now = datetime.now(timezone.utc).isoformat()
            observation = handoff.new_observation(round_id, self.session_id)
            observation.update(request_id='synthetic-' + round_id, delivery='normal-final',
                dispatched_at=now, boundary=dict(kind='first-normal-final', at=now),
                first_normal_final=True, first_normal_final_at=now, final='final.md',
                attachments=[attachment],
                evidence_gaps=['Synthetic operator fixture; no native model was called.'])
            fixture_support.write_json(capture / 'observation.json', observation)
            handoff.freeze(self.bundle, self.state, self.session_id, round_id, capture,
                           candidate_files=candidate)
        self.checked = external.validate_state(self.state, self.bundle)
        self.capacity = [f'C{i}' for i in range(5)]
        self.autonomy = ['A1', 'A2']
        self.review = self.new_review()
        self.original = self.original_review(self.review)
        self.inputs = self.root / 'private-selection'
        self.inputs.mkdir()
        self.selection = self.inputs / 'selection.json'
        self.review_root = self.root / 'review-sources'
        self.review_root.mkdir()
        archive_copy = self.inputs / archive.name
        shutil.copyfile(archive, archive_copy)
        self.source = dict(schema=external.SELECTION, registration=str(self.registration),
            review_policy=str(self.review_policy), bundle=str(self.bundle),
            source_evidence=[absolute_descriptor(archive_copy)], models=[])
        self.save_reviews()
        self.output = self.root / 'proposals' / 'proposal.json'
        self.output.parent.mkdir()

    def evidence(self, round_id='R1'):
        name = f'{round_id}/delivered/manuscript-{round_id}.md'
        raw = self.checked['files'][name]
        return [dict(round=round_id, file=name, sha256=external.digest(raw),
                     start=0, end=len(raw), quote=raw.decode())]

    def judgment(self, round_id='R1', **fields):
        return dict(reason=MARKER, evidence=self.evidence(round_id), **fields)

    def new_review(self):
        taste = dict(mc_score=90, rmc_score=80,
            directions={name: self.judgment(mc_points=points, verdict=verdict) for name, points, verdict
                        in zip(value.DIMENSIONS, (50, 20, 20), (True, False, True))},
            deductions=[self.judgment(id='shared-root', criterion='selection', points=10)],
            sufficient_choices=self.judgment(verdict=True))
        capacity = dict(mc_score=70, rmc_score=60,
            directions={name: self.judgment(mc_points=points, verdict=verdict) for name, points, verdict
                        in zip(self.capacity, (20, 20, 15, 10, 5), (True, True, True, False, False))},
            deductions=[self.judgment(id='shared-root', criterion=self.capacity[0], points=10)])
        return dict(schema=external.REVIEW, edition='1.3.0', model_id=MODEL,
            reviewer=dict(requested_model='gpt-6.1-sol', requested_effort='max',
                reviewer_id='Synthetic independent reviewer', reviewer_context_id='synthetic-independent-context',
                reviewer_kind='ai', human_review='pending', backend_identity_independently_verified=False),
            sealed_finals=self.checked['seals'], policy_bindings=external.policy_bindings(self.public),
            rounds={r: self.judgment(r) for r in handoff.ROUNDS}, taste=taste, capacity=capacity,
            autonomy=dict(score=100, gates={name: self.judgment(r, verdict=True)
                          for name, r in zip(self.autonomy, ('R1', 'R2'))}),
            extension=dict(self.judgment(), level='E0', assessed_rounds=list(handoff.ROUNDS),
                independent_question=MARKER, outside_core=MARKER, result_and_scope=MARKER, value=MARKER),
            error_roots=[self.judgment(id='shared-root', effects=dict(
                taste='Synthetic failure affects selection.', capacity='Synthetic failure affects a required direction.'))])

    @staticmethod
    def original_review(review):
        taste = review['taste']
        return dict(model_id=review['model_id'], reviewer=deepcopy(review['reviewer']),
            taste=dict(mc_score=taste['mc_score'], rmc_score=taste['rmc_score'],
                aspects={name: dict(mc_points=row['mc_points']) for name, row in taste['directions'].items()},
                gates={name: dict(verdict=row['verdict']) for name, row in taste['directions'].items()},
                sufficient_choices=deepcopy(taste['sufficient_choices']),
                error_deductions=[dict(id=r['id'], dimension=r['criterion'], points=r['points']) for r in taste['deductions']]),
            capacity=dict(mc_score=review['capacity']['mc_score'], rmc_score=review['capacity']['rmc_score'],
                directions=deepcopy(review['capacity']['directions']),
                error_deductions=deepcopy(review['capacity']['deductions'])),
            autonomy=deepcopy(review['autonomy']), extension=deepcopy(review['extension']))

    def save_reviews(self):
        review = self.review_root / 'review.json'
        original = self.review_root / 'original-review.json'
        reviewer = self.review_root / 'reviewer.json'
        review.write_bytes(external.encoded(self.review))
        original.write_bytes(external.encoded(self.original))
        fixture_support.write_json(reviewer, dict(schema='math-gauge.external-reviewer-observation/v1',
            requested_model='gpt-6.1-sol', requested_effort='max',
            reviewer_context_id=self.review['reviewer']['reviewer_context_id'], reviewer_kind='ai',
            human_review='pending', backend_identity_independently_verified=False,
            review_sha256=external.digest(review.read_bytes()), original_review_sha256=external.digest(original.read_bytes())))
        self.source['models'] = [dict(id=self.review['model_id'], state=str(self.state), review=str(review),
            reviewer_observation=str(reviewer), original_review=str(original))]
        self.selection.write_bytes(external.encoded(self.source))

    def validate(self, review=None):
        return external.validate_review(self.review if review is None else review, self.checked,
            model_id=MODEL, policies=external.policy_bindings(self.public),
            capacity_keys=self.capacity, autonomy_keys=self.autonomy)

    def prepare(self):
        return external.prepare(self.selection, self.public)

    def arguments(self, *extra, output=None):
        return ['adopt', '--selection', str(self.selection), '--public-root', str(self.public),
                '--out', str(output or self.output), *extra]

    def test_original_finals_and_declared_attachments_are_the_only_evidence(self):
        result = self.prepare()
        self.assertEqual(result['candidate_calls_by_adoption'], 0)
        self.assertEqual(len(self.checked['files']), 6)
        self.assertTrue(all(f'{r}/first-final.md' in self.checked['files'] for r in handoff.ROUNDS))
        for mutate in (
            lambda r: r['rounds']['R1']['evidence'][0].update(start=1),
            lambda r: r['rounds']['R1']['evidence'][0].update(quote='invented'),
            lambda r: r['rounds']['R1']['evidence'][0].update(sha256='0' * 64),
            lambda r: r['rounds']['R1']['evidence'][0].update(file='R1/delivered/unsubmitted.md'),
        ):
            bad = deepcopy(self.review)
            mutate(bad)
            with self.subTest(evidence=bad['rounds']['R1']['evidence']), self.assertRaises(ValueError):
                self.validate(bad)
        raw = external.encoded(result)
        for private in (MARKER.encode(), b'CASE-FIXTURE', str(self.root).encode(), *[k.encode() for k in self.capacity]):
            self.assertNotIn(private, raw)

    def test_source_cannot_change_between_checked_mirror_and_consumption(self):
        real_check = handoff.check

        def swap_after_check(bundle, mirror):
            result = real_check(bundle, mirror)
            final = self.state / 'R3/first-final.md'
            final.write_bytes(b'Unverified post-check substitute.\n')
            seal_path = self.state / 'R3/seal.json'
            seal = json.loads(seal_path.read_bytes())
            seal['final'] = handoff.descriptor('R3/first-final.md', final.read_bytes())
            seal_path.write_bytes(external.encoded(seal))
            return result

        with patch.object(handoff, 'check', side_effect=swap_after_check), self.assertRaises(ValueError):
            external.validate_state(self.state, self.bundle)

    def test_selected_label_cannot_reassign_a_max_state_to_xhigh(self):
        self.review['model_id'] = self.original['model_id'] = OTHER
        self.save_reviews()
        with self.assertRaises(ValueError):
            self.prepare()

    def test_insufficient_choices_require_unknown_selection_and_score(self):
        bad = deepcopy(self.review)
        bad['taste'].update(mc_score=None, rmc_score=None, deductions=[])
        bad['taste']['sufficient_choices']['verdict'] = False
        for row in bad['taste']['directions'].values():
            row.update(mc_points=None, verdict=True)
        with self.assertRaises(ValueError):
            self.validate(bad)
        bad['taste']['directions']['selection']['verdict'] = None
        result = self.validate(bad)
        self.assertIsNone(result['axes']['taste']['strict'])
        self.assertEqual(result['strict_credit']['taste'], dict(lower=0, upper=100, exact=None))

    def test_only_well_formed_appledouble_transport_metadata_is_ignored(self):
        path = self.state / '._extra.md'
        path.write_bytes(bytes.fromhex('00051607') + b'Additional unlisted manuscript bytes')
        with self.assertRaises(ValueError):
            external.validate_state(self.state, self.bundle)
        header = struct.pack('>II16sH', 0x00051607, 0x00020000, bytes(16), 1)
        path.write_bytes(header + struct.pack('>III', 9, 38, 4) + bytes(4))
        checked = external.validate_state(self.state, self.bundle)
        self.assertEqual([r['path'] for r in checked['ignored_transport_sidecars']], [path.name])
        self.assertTrue(path.exists())  # Original transport container is retained.
        overlap = struct.pack('>II16sH', 0x00051607, 0x00020000, bytes(16), 2)
        path.write_bytes(overlap + struct.pack('>III', 9, 50, 4) + struct.pack('>III', 2, 52, 4) + bytes(6))
        with self.assertRaises(ValueError):
            external.validate_state(self.state, self.bundle)

    def test_normalization_preserves_scores_credit_roots_flags_autonomy_extension_and_context(self):
        external.validate_normalization(self.original, self.review)
        changes = (
            lambda r: r['taste'].update(mc_score=91),
            lambda r: r['capacity'].update(rmc_score=61),
            lambda r: r['taste']['directions']['value'].update(mc_points=51),
            lambda r: r['taste']['directions']['structure'].update(verdict=True),
            lambda r: r['capacity']['directions']['C0'].update(mc_points=19),
            lambda r: r['capacity']['directions']['C4'].update(verdict=True),
            lambda r: r['taste']['deductions'][0].update(points=9),
            lambda r: r['capacity']['deductions'][0].update(criterion='C1'),
            lambda r: r['taste']['deductions'][0].update(id='changed-root'),
            lambda r: r['taste']['sufficient_choices'].update(verdict=False),
            lambda r: r['autonomy'].update(score=99),
            lambda r: r['autonomy']['gates']['A1'].update(verdict=False),
            lambda r: r['extension'].update(level='E1'),
            lambda r: r['reviewer'].update(reviewer_context_id='another-context'),
        )
        for change in changes:
            changed = deepcopy(self.review)
            change(changed)
            with self.subTest(change=change), self.assertRaises(ValueError):
                external.validate_normalization(self.original, changed)

    def test_shared_root_needs_distinct_axis_effects_and_is_charged_once_per_axis(self):
        self.validate()
        bad = deepcopy(self.review)
        bad['taste']['deductions'].append(deepcopy(bad['taste']['deductions'][0]))
        with self.assertRaises(ValueError):
            self.validate(bad)
        bad = deepcopy(self.review)
        bad['error_roots'][0]['effects'].pop('capacity')
        with self.assertRaises(ValueError):
            self.validate(bad)

    def test_shared_projection_uses_two_to_one_and_retains_net_passed_credit(self):
        result = self.prepare()
        row = result['models'][MODEL]
        self.assertEqual(row['criteria']['capacity'], dict(planned=5, passed=3, unknown=0))
        self.assertEqual(row['strict_credit'], dict(taste=dict(lower=60, upper=60, exact=60),
            capacity=dict(lower=45, upper=45, exact=45)))
        policy, _ = value.load_policy()
        policy['item_weights'] = dict(taste=2, capacity=1)
        point = lambda n: dict(lower=n, upper=n, exact=n)
        base = {mode: dict(metrics={key: point(80) for key in ('overall', 'written', 'lean', 'research')})
                for mode in ('MC', 'RMC', 'SMC')}
        projection = external.project_model(base, policy, row)
        self.assertAlmostEqual(projection['score_modes']['MC']['item']['exact'], (2 * 90 + 70) / 3)
        self.assertAlmostEqual(projection['score_modes']['RMC']['item']['exact'], (2 * 80 + 60) / 3)
        self.assertEqual(projection['score_modes']['SMC']['item']['exact'], 55)
        self.assertEqual(projection['composite_by_base']['SMC']['exact'], 77.5)
        all_passed = deepcopy(self.review)
        for direction in all_passed['taste']['directions'].values():
            direction['verdict'] = True
        self.assertEqual(self.validate(all_passed)['strict_credit']['taste']['exact'], 80)

    def test_apply_rejects_a_baseline_changed_after_preparation(self):
        proposal = self.prepare()
        baseline = self.public / 'site/data.json'
        baseline.write_bytes(baseline.read_bytes() + b'\n')
        with self.assertRaises(ValueError):
            cli.apply_index(self.public, proposal, expected=None)
        self.assertFalse((self.public / external.PUBLIC_PATH).exists())

    def test_lock_parent_cannot_redirect_writes_outside_public_root(self):
        proposal = self.prepare()
        outside = self.root / 'outside-lock'
        outside.mkdir()
        (self.public / '.dev-mesh').symlink_to(outside, target_is_directory=True)
        with self.assertRaises(ValueError):
            cli.apply_index(self.public, proposal, expected=None)
        self.assertEqual(list(outside.iterdir()), [])
        self.assertFalse((self.public / external.PUBLIC_PATH).exists())

    def test_check_rereads_installed_bytes_after_a_concurrent_valid_extension(self):
        initial = self.prepare()
        cli.apply_index(self.public, initial, expected=None)
        extended = deepcopy(initial)
        extended['cohort'].append(OTHER)
        extended['models'][OTHER] = deepcopy(extended['models'][MODEL])
        extended['models'][OTHER]['source_sha256'] = 'f' * 64

        def preparation_race(*_args):
            cli.apply_index(self.public, extended, expected=external.encoded(initial))
            return initial

        with patch.object(cli.external, 'prepare', side_effect=preparation_race), \
             patch.object(cli.sys, 'argv', self.arguments('--check')), redirect_stdout(io.StringIO()), \
             self.assertRaises(ValueError):
            cli.main()
        self.assertEqual((self.public / external.PUBLIC_PATH).read_bytes(), external.encoded(extended))
        self.assertFalse(self.output.exists())

    def test_proposal_cannot_add_a_file_to_a_sibling_selected_source_tree(self):
        output = self.state / 'unlisted-proposal.json'
        with patch.object(cli.sys, 'argv', self.arguments(output=output)), redirect_stdout(io.StringIO()), \
             self.assertRaises(ValueError):
            cli.main()
        self.assertFalse(output.exists())
        external.validate_state(self.state, self.bundle)

    def test_atomic_install_rejects_stale_and_settled_changes_without_mutating_index(self):
        initial = self.prepare()
        cli.apply_index(self.public, initial, expected=None)
        target = self.public / external.PUBLIC_PATH
        before = target.read_bytes()
        self.assertEqual(before, external.encoded(initial))
        with self.assertRaises(ValueError):
            cli.apply_index(self.public, initial, expected=None)
        changed = deepcopy(initial)
        changed['models'][MODEL]['axes']['taste']['mc'] = 91
        with self.assertRaises(ValueError):
            cli.apply_index(self.public, changed, expected=before)
        self.assertEqual(target.read_bytes(), before)
        self.assertEqual(list(target.parent.glob('.adoption-*')), [])

    def amended_selection(self):
        prior = self.prepare()
        before_raw = external.encoded(prior)
        parent = self.inputs / 'before-selection.json'
        parent.write_bytes(self.selection.read_bytes())
        index = self.inputs / 'before-index.json'
        index.write_bytes(before_raw)
        old_review = self.review_root / 'review.json'
        self.review_root = self.root / 'fresh-review'
        self.review_root.mkdir()
        self.review['reviewer']['reviewer_context_id'] = 'synthetic-fresh-reaudit-context'
        self.review['error_roots'] = []
        for axis, points, passed in (('taste', (49, 20, 18), (True, True, True)),
                                    ('capacity', (17, 11, 16, 0, 9), (True, False, True, False, True))):
            row = self.review[axis]
            row.update(mc_score=sum(points), rmc_score=sum(points), deductions=[])
            for value, point, flag in zip(row['directions'].values(), points, passed):
                value.update(mc_points=point, verdict=flag)
        sources = [absolute_descriptor(self.state / r / 'first-final.md') for r in handoff.ROUNDS]
        self.original = dict(schema=external.REAUDIT, edition='1.3.0', candidate=MODEL,
            reviewer=dict(kind='ai', requested_model='gpt-6.1-sol', requested_effort='max',
                context=self.review['reviewer']['reviewer_context_id'], human_review='pending',
                backend_identity_independently_verified=False), source_bindings=sources,
            evidence={r: {**self.evidence(r)[0], 'file': str(self.state / self.evidence(r)[0]['file'])}
                      for r in handoff.ROUNDS}, calibration=dict(old_review_read_only_after_blind_freeze=
                          absolute_descriptor(old_review)))
        for axis in external.AXES:
            row = self.review[axis]
            dimensions = [dict(id=key, mc=value['mc_points'], net=value['mc_points'], deductions=0,
                               strict_pass=value['verdict']) for key, value in row['directions'].items()]
            self.original[axis] = dict(MC=row['mc_score'], RMC=row['rmc_score'], dimensions=dimensions,
                SMC_retained_net_credit=sum(r['net'] for r in dimensions if r['strict_pass']),
                all_gates_pass=all(r['strict_pass'] for r in dimensions))
        self.save_reviews()
        snapshots = []
        for number, source in enumerate(sources):
            snapshot = self.review_root / f'source-{number}.md'
            snapshot.write_bytes(Path(source['path']).read_bytes())
            snapshots.append(dict(original_path=source['path'], retained=absolute_descriptor(snapshot)))
        receipt = self.review_root / 'normalization.json'
        receipt.write_text('{}\n')
        amendment = dict(schema=external.AMENDMENT, edition='1.3.0', model_id=MODEL,
            before_index=absolute_descriptor(index), before_selection=absolute_descriptor(parent),
            before_review=absolute_descriptor(old_review), after_review=absolute_descriptor(self.review_root/'review.json'),
            reevaluation=absolute_descriptor(self.review_root/'original-review.json'),
            normalization_receipt=absolute_descriptor(receipt), review_sources=snapshots,
            retained_fields=['rounds','autonomy','extension'], user_selection=dict(source_kind='direct-user-message',
                text='Adopt this full independent re-audit', date='2026-11-24', scope='full-independent-reaudit',
                human_mathematical_approval=False))
        path = self.inputs / 'review-amendment.json'
        path.write_bytes(external.encoded(amendment))
        self.source['review_amendment'] = absolute_descriptor(path)
        self.selection.write_bytes(external.encoded(self.source))
        return prior, before_raw, path

    def test_selected_reaudit_replays_parent_and_only_changes_named_math_review(self):
        prior, before_raw, amendment_path = self.amended_selection()
        cli.apply_index(self.public, prior, expected=None)
        proposal = self.prepare()
        row = proposal['models'][MODEL]
        self.assertEqual(row['axes']['taste']['mc'], 87)
        self.assertEqual(row['strict_credit']['capacity']['exact'], 42)
        self.assertEqual(row['criteria']['capacity']['passed'], 3)
        with self.assertRaises(ValueError):
            cli.apply_index(self.public, proposal, expected=before_raw)
        cli.apply_index(self.public, proposal, expected=before_raw, amendment_selection=self.selection)
        cli.check_index(self.public, self.prepare())
        self.assertEqual((self.public/external.PUBLIC_PATH).read_bytes(), external.encoded(proposal))
        self.assertEqual(Path(json.loads(amendment_path.read_bytes())['before_index']['path']).read_bytes(), before_raw)
        bad = deepcopy(self.review)
        bad['taste']['directions']['selection']['mc_points'] += 1
        with self.assertRaises(ValueError):
            external.validate_normalization(self.original, bad)

    def test_reaudit_cannot_rewrite_retained_axes_or_the_selected_source(self):
        _, _, amendment_path = self.amended_selection()
        proposal = self.prepare()
        bad = deepcopy(proposal)
        bad['models'][MODEL]['extension_level'] = 'E1'
        with self.assertRaises(ValueError):
            external.amendment_parent(self.selection, bad, self.public)
        path = self.review_root/'review.json'
        changed = json.loads(path.read_bytes())
        changed['autonomy']['score'] = 75
        path.write_bytes(external.encoded(changed))
        with self.assertRaises(ValueError):
            self.prepare()
        self.assertTrue(amendment_path.exists())


if __name__ == '__main__':
    unittest.main()
