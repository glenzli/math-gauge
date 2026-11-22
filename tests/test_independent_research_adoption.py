"""Whole-cohort adoption contracts with synthetic manuscripts and a mocked wire boundary."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

from math_gauge import independent_research_adoption as adoption
from math_gauge import taste_v130 as flow
import test_independent_research_review as trajectory_fixture
import test_taste_v130 as fixture_support

descriptor = fixture_support.descriptor
write_json = fixture_support.write_json


class AdoptionTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name).resolve()
        self.run = self.root / 'run'
        (self.run / 'control').mkdir(parents=True)
        self.rows, self.executions, self.reviews = [], {}, {}
        self.registration, self.review_policy = None, None
        for name in ('fixture-a', 'fixture-b'):
            fixture = fixture_support.ProtocolFixture('runTest')
            fixture.setUp()
            self.addCleanup(fixture.doCleanups)
            original_seal = fixture.seal
            # These operator declarations are synthetic. The native-wire owner is
            # explicitly mocked below; no fabricated native request is executed.
            fixture.seal = lambda rid, _seal=original_seal, **kw: _seal(rid, kind='operator-attestation', **kw)
            review = fixture.review()
            fixture_policy = trajectory_fixture.write_policy(fixture)
            if self.registration is None:
                self.registration = fixture.registration
                self.review_policy = fixture_policy
            review = trajectory_fixture.reviewed_trajectory(fixture, review, fixture_policy)
            review['reviewer_id'] = 'Sol 6.1 Max'
            review['reviewer_context_id'] = 'independent-' + name
            control = self.run / 'control' / name
            control.mkdir()
            shutil.copytree(fixture.state, control / 'state')
            execution = dict(origin='codex-app-server', model_id=name, outcome='normal-finals',
                state=f'control/{name}/state', native_context_id='native-' + name,
                rounds=[dict(delivery='normal-final') for _ in range(3)])
            write_json(control / 'execution.json', execution)
            self.executions[name] = execution
            review_path = self.root / (name + '-review.json')
            write_json(review_path, review)
            request_path = self.root / (name + '-request.txt')
            request_path.write_text('Pure synthetic private review marker; no real case or model result.')
            reviewer_path = self.root / (name + '-reviewer.json')
            write_json(reviewer_path, dict(schema='math-gauge.independent-research-reviewer-observation/v1',
                requested_model='gpt-6.1-sol', requested_effort='max', reviewer_kind='ai', human_review='pending',
                reviewer_id=review['reviewer_id'], reviewer_context_id=review['reviewer_context_id'],
                backend_identity_independently_verified=False,
                original_request=descriptor(request_path, self.root),
                original_response=descriptor(review_path, self.root)))
            self.rows.append(dict(id=name, execution=descriptor(control / 'execution.json', self.run),
                review=descriptor(review_path, self.root), reviewer_source=descriptor(reviewer_path, self.root)))
            self.reviews[name] = review
        self.plan = dict(cohort=[dict(id=name) for name in self.executions],
            baseline=dict(edition='1.2.0', path='site/data.json', sha256='a' * 64))
        self.plan_path = self.root / 'plan.json'
        write_json(self.plan_path, self.plan)
        shutil.copyfile(self.plan_path, self.run / 'control/plan.json')
        self.selection = self.root / 'selection.json'
        policy_raw = self.review_policy.read_bytes()
        self.source = dict(schema=adoption.SELECTION, plan=descriptor(self.plan_path, self.root),
            run_root=str(self.run), models=self.rows,
            review_policy=dict(path=str(self.review_policy), bytes=len(policy_raw), sha256=hashlib.sha256(policy_raw).hexdigest()))

    def prepare(self):
        write_json(self.selection, self.source)
        with patch('math_gauge.independent_research_execution.load_plan', return_value=(self.plan, self.registration)), \
             patch('math_gauge.independent_research_execution.validate_execution',
                   side_effect=lambda _root, ref, _plan: self.executions[Path(ref['path']).parent.name]):
            return adoption.prepare(self.selection, flow.POLICY_FILE.parents[3])

    def update_review(self, name):
        row = next(r for r in self.rows if r['id'] == name)
        path = self.root / row['review']['path']
        write_json(path, self.reviews[name])
        row['review'] = descriptor(path, self.root)
        reviewer_path = self.root / row['reviewer_source']['path']
        source = json.loads(reviewer_path.read_bytes())
        source['reviewer_context_id'] = self.reviews[name]['reviewer_context_id']
        source['original_response'] = descriptor(path, self.root)
        write_json(reviewer_path, source)
        row['reviewer_source'] = descriptor(reviewer_path, self.root)

    def test_all_reviews_project_only_allowlisted_grades_and_opaque_bindings(self):
        value = self.prepare()
        self.assertEqual(value['cohort'], ['fixture-a', 'fixture-b'])
        self.assertEqual(value['native_round_dispatches'], 6)
        self.assertEqual(value['models']['fixture-a']['axes']['capacity']['score'], 80)
        self.assertEqual(value['review_policy_sha256'], self.source['review_policy']['sha256'])
        text = adoption.encoded(value).decode()
        for private in ('Pure synthetic private review marker', 'Synthetic assessment', 'CASE-FIXTURE', 'quote',
                        'TRAJECTORY-PRIVATE-RUBRIC-SENTINEL', 'trajectory-review-policy.json', str(self.root)):
            self.assertNotIn(private, text)

    def test_legacy_selection_review_and_aggregate_are_explicitly_rejected(self):
        current = self.prepare()
        old_projection = deepcopy(current)
        old_projection['schema'] = 'math-gauge.independent-research-adoption/v1'
        old_projection.pop('review_policy_sha256')
        with self.assertRaisesRegex(ValueError, 'projection v2'):
            adoption.validate_public(old_projection)
        policy = self.source.pop('review_policy')
        self.source['schema'] = 'math-gauge.independent-research-review-selection/v1'
        with self.assertRaisesRegex(ValueError, 'selection v2'):
            self.prepare()
        self.source.update(schema=adoption.SELECTION, review_policy=policy)
        self.reviews['fixture-a']['schema'] = flow.REVIEW
        self.reviews['fixture-a'].pop('review_policy_sha256')
        self.update_review('fixture-a')
        with self.assertRaisesRegex(ValueError, 'whole-trajectory review'):
            self.prepare()

    def test_policy_descriptor_does_not_accept_replaced_bytes(self):
        self.review_policy.write_bytes(self.review_policy.read_bytes() + b'\n')
        with self.assertRaisesRegex(ValueError, 'source bytes changed'):
            self.prepare()

    def test_no_partial_or_duplicate_cohort_is_adopted(self):
        self.source['models'] = self.rows[:1]
        with self.assertRaisesRegex(ValueError, 'Partial'):
            self.prepare()
        self.source['models'] = [self.rows[0], self.rows[0]]
        with self.assertRaisesRegex(ValueError, 'Partial'):
            self.prepare()

    def test_only_the_requested_independent_reviewer_can_supply_grades(self):
        row = self.rows[0]
        path = self.root / row['reviewer_source']['path']
        value = json.loads(path.read_bytes())
        value['requested_model'] = 'gpt-6.2-sol'
        write_json(path, value)
        row['reviewer_source'] = descriptor(path, self.root)
        with self.assertRaisesRegex(ValueError, 'Sol 6.1 Max'):
            self.prepare()

    def test_fixture_failed_and_unresolved_wire_results_are_never_promoted(self):
        for field, value in [('origin', 'fixture'), ('outcome', 'delivery-failed'), ('outcome', 'unresolved')]:
            prior = deepcopy(self.executions['fixture-a'])
            self.executions['fixture-a'][field] = value
            with self.assertRaisesRegex(ValueError, 'operational adjudication'):
                self.prepare()
            self.executions['fixture-a'] = prior

    def test_original_quote_and_reviewer_response_bytes_must_still_match(self):
        path = self.root / self.rows[0]['review']['path']
        path.write_bytes(path.read_bytes() + b'\n')
        with self.assertRaisesRegex(ValueError, 'source bytes changed'):
            self.prepare()

    def test_review_context_cannot_be_reused_or_equal_the_native_solver(self):
        self.reviews['fixture-b']['reviewer_context_id'] = self.reviews['fixture-a']['reviewer_context_id']
        self.update_review('fixture-b')
        with self.assertRaisesRegex(ValueError, 'independent review context'):
            self.prepare()
        self.reviews['fixture-b']['reviewer_context_id'] = self.executions['fixture-b']['native_context_id']
        self.update_review('fixture-b')
        with self.assertRaisesRegex(ValueError, 'independent review context'):
            self.prepare()

    def test_unknown_and_real_zero_survive_the_public_projection(self):
        review = self.reviews['fixture-a']
        review['axes']['autonomy']['score'] = 0
        review['axes']['taste']['score'] = None
        self.update_review('fixture-a')
        value = self.prepare()['models']['fixture-a']['axes']
        self.assertEqual(value['autonomy']['score'], 0)
        self.assertIsNone(value['taste']['score'])

    def test_confirmed_delivery_failure_needs_its_own_review_and_leaves_math_axes_unknown(self):
        name = 'fixture-a'
        selected = self.rows[0]
        evidence_path = self.run / 'control/fixture-a/failed.native.ndjson'
        evidence_path.write_bytes(b'{"synthetic_cutoff":true}\n')
        native = descriptor(evidence_path, self.run)
        self.executions[name].update(outcome='delivery-failed', context_id='synthetic-candidate',
            rounds=[dict(delivery='normal-final', wire_events=native), dict(delivery='delivery-failed', wire_events=native)])
        old = self.reviews[name]
        self.reviews[name] = dict(schema='math-gauge.independent-research-operational-review/v1',
            execution_sha256=selected['execution']['sha256'], reviewer_kind='ai', human_review='pending',
            reviewer_id=old['reviewer_id'], reviewer_context_id=old['reviewer_context_id'],
            conclusion='confirmed-delivery-failed', reason='Synthetic explicit deadline adjudication.', evidence=[native])
        self.update_review(name)
        value = self.prepare()
        self.assertEqual(value['native_round_dispatches'], 5)
        row = value['models'][name]
        self.assertEqual(row['status'], 'delivery-failed')
        self.assertEqual(row['normal_rounds'], 1)
        self.assertTrue(all(grade == dict(score=None, strict=None) for grade in row['axes'].values()))

    def test_public_boundary_rejects_private_additions(self):
        base = self.prepare()
        for mutate in [lambda x: x.update(evidence='private'),
            lambda x: x['models']['fixture-a'].update(reason='private'),
            lambda x: x['models']['fixture-a']['axes']['capacity'].update(quote='private')]:
            value = deepcopy(base)
            mutate(value)
            with self.assertRaises(ValueError):
                adoption.validate_public(value)

    def baseline_fixture(self):
        def point(v):
            return dict(lower=v, upper=v, exact=v)
        models = []
        for index, name in enumerate(('fixture-a', 'fixture-b', 'fixture-c')):
            report = dict(metrics={key: point(80) for key in ('overall', 'written', 'lean', 'research')})
            models.append(dict(id=name, label='Synthetic ' + name, display_order=index,
                ranking_values=dict(strict=8000, partial=8000, capability=8000),
                capability=dict(nonlogical_retry_3=report), retry=dict(combined=report),
                strict=dict(nonlogical_retry_3=report)))
        data = dict(benchmark_version='1.2.0', models=models)
        raw = json.dumps(data, ensure_ascii=False, indent=2).encode() + b'\n'
        selected = self.prepare()
        selected['source_binding']['sha256'] = hashlib.sha256(raw).hexdigest()
        return data, raw, selected

    def test_display_projects_exactly_the_selected_cohort_and_keeps_others_blank(self):
        from scripts.preview_open_research_v130 import baseline_data
        data, raw, selected = self.baseline_fixture()
        selected['models']['fixture-a']['axes']['autonomy']['score'] = 0
        selected['models']['fixture-a']['axes']['taste']['score'] = None
        board = baseline_data(data, source_bytes=raw, adopted=selected)
        rows = {row['id']: row for row in board['rows']}
        self.assertEqual(board['source_binding']['sha256'], hashlib.sha256(raw).hexdigest())
        self.assertEqual(rows['fixture-a']['components']['autonomy']['value'], 0)
        self.assertEqual(rows['fixture-a']['components']['taste']['state'], 'insufficient-evidence')
        self.assertIsNone(rows['fixture-a']['item']['exact'])
        for axis in rows['fixture-c']['components'].values():
            self.assertEqual(axis, dict(state='not-tested', value=None, strict=None))

    def test_display_refuses_a_changed_baseline_policy_or_unknown_selected_model(self):
        from scripts.preview_open_research_v130 import baseline_data
        data, raw, original = self.baseline_fixture()
        for key in ('baseline', 'policy', 'model'):
            selected = deepcopy(original)
            if key == 'baseline':
                selected['source_binding']['sha256'] = '0' * 64
            elif key == 'policy':
                selected['policy_sha256'] = '0' * 64
            else:
                selected['cohort'][0] = 'missing-model'
                selected['models']['missing-model'] = selected['models'].pop('fixture-a')
            with self.assertRaisesRegex(ValueError, 'different baseline'):
                baseline_data(data, source_bytes=raw, adopted=selected)


if __name__ == '__main__':
    unittest.main()
