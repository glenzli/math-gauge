"""Source fidelity and fixed 1.3 score modes on purely synthetic manuscripts."""

from copy import deepcopy
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from math_gauge import independent_research_adoption as adoption
from math_gauge import independent_research_score_modes as modes
from math_gauge import taste_v130 as flow
from scripts import adopt_independent_research_score_modes as cli
import test_independent_research_adoption as adoption_fixture
from test_taste_v130 import descriptor, write_json


class ScoreModeSources(unittest.TestCase):
    def setUp(self):
        fixture = adoption_fixture.AdoptionTests('runTest')
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        self.fixture, self.root = fixture, fixture.root
        fixture.plan['registration'] = {'sha256': flow._sha(fixture.registration.read_bytes())}
        write_json(fixture.plan_path, fixture.plan)
        write_json(fixture.run / 'control/plan.json', fixture.plan)
        fixture.source['plan'] = descriptor(fixture.plan_path, self.root)
        for identifier, execution in fixture.executions.items():
            execution['context_id'] = json.loads(
                (fixture.run / execution['state'] / 'session.json').read_bytes())['context_id']
            execution_path = fixture.run / 'control' / identifier / 'execution.json'
            write_json(execution_path, execution)
            next(row for row in fixture.rows if row['id'] == identifier)['execution'] = descriptor(
                execution_path, fixture.run)

        before = fixture.reviews['fixture-a']
        before['gates']['capacity']['C4']['verdict'] = False
        before['gates']['capacity']['optional']['verdict'] = True
        before['axes']['capacity']['strict'] = False
        fixture.update_review('fixture-a')
        self.original = fixture.prepare()
        self.base_path = fixture.index_target()
        self.base_raw = adoption.encoded(self.original)
        self.base_path.write_bytes(self.base_raw)
        (self.root / modes.POLICY_PATH).write_bytes(modes.POLICY_FILE.read_bytes())
        self.rows = [dict(id=row['id'], execution=row['execution'], original_review=row['review'],
            original_reviewer_source=row['reviewer_source'], effective_review=row['review'],
            effective_reviewer_source=row['reviewer_source'], recheck=None, mc_review=None, mc_reviewer_source=None)
            for row in fixture.rows[:2]]
        self.source = dict(schema=modes.SELECTION, plan=fixture.source['plan'], run_root=fixture.source['run_root'],
            review_policy=fixture.source['review_policy'], base_adoption=descriptor(self.base_path, self.root),
            models=self.rows)
        self.selection = self.root / 'mode-selection.json'
        self.request = self.root / 'mc-request.txt'
        self.request.write_text('SYNTHETIC-PRIVATE-SUPPLEMENT-MARKER')

    def prepare(self):
        write_json(self.selection, self.source)
        with patch('math_gauge.independent_research_execution.load_plan',
                   return_value=(self.fixture.plan, self.fixture.registration)), \
             patch('math_gauge.independent_research_execution.validate_execution',
                   side_effect=lambda _root, ref, _plan: self.fixture.executions[Path(ref['path']).parent.name]):
            return modes.prepare(self.selection, self.root)

    def reviewer_source(self, path, reviewer, *, purpose=None):
        source = dict(schema='math-gauge.independent-research-reviewer-observation/v1',
            requested_model='gpt-6.1-sol', requested_effort='max', reviewer_kind='ai', human_review='pending',
            reviewer_id=reviewer['reviewer_id'], reviewer_context_id=reviewer['reviewer_context_id'],
            backend_identity_independently_verified=False, original_request=descriptor(self.request, self.root),
            original_response=descriptor(path, self.root))
        if purpose is not None:
            source['purpose'] = purpose
        output = path.with_suffix('.reviewer.json')
        write_json(output, source)
        return descriptor(output, self.root)

    def mc_review(self, row, *, deduction=0):
        review_path = self.root / row['effective_review']['path']
        raw = review_path.read_bytes()
        effective = json.loads(raw)
        axes = {axis: dict(mc_score=grade['score'], rmc_score=grade['score'],
                          reason='Synthetic mathematical evidence', evidence=grade['evidence'])
                for axis, grade in effective['axes'].items()}
        deductions = []
        if deduction:
            axes['capacity']['mc_score'] += deduction
            deductions = [dict(id='synthetic-root', axis='capacity', points=deduction,
                               reason='Synthetic private error witness', evidence=axes['capacity']['evidence'])]
        return dict(schema=modes.MC_REVIEW, reviewer_id='Sol 6.1 Max', reviewer_context_id='shared-mc-calibration',
            reviewer_kind='ai', human_review='pending', source_review_sha256=flow._sha(raw),
            registration_sha256=effective['registration_sha256'], sealed_finals=effective['sealed_finals'],
            axes=axes, error_deductions=deductions, no_mathematical_errors=not deduction)

    def select_mc(self, row, review, *, purpose=modes.MC_PURPOSE):
        path = self.root / (row['id'] + '-mc.json')
        write_json(path, review)
        row['mc_review'] = descriptor(path, self.root)
        row['mc_reviewer_source'] = self.reviewer_source(path, review, purpose=purpose)

    def test_positive_credit_and_required_gate_counts_link_only_public_values(self):
        first, second = self.rows
        self.select_mc(first, self.mc_review(first, deduction=5))
        self.select_mc(second, self.mc_review(second))
        result = self.prepare()
        row = result['models'][first['id']]
        self.assertEqual(row['axes']['capacity'], dict(mc=85, rmc=80, strict=False))
        self.assertEqual(row['criteria']['capacity'], dict(planned=5, passed=4, unknown=0))
        self.assertEqual(result['models'][second['id']]['axes']['capacity']['mc'], 80)
        self.assertIsNone(row['recheck_sha256'])
        self.assertEqual(row['original_source_sha256'], self.original['models'][first['id']]['source_sha256'])
        self.assertEqual(self.base_path.read_bytes(), self.base_raw)
        output = adoption.encoded(result).decode()
        for private in ('SYNTHETIC-PRIVATE', 'synthetic-root', 'CASE-FIXTURE', 'quote', 'optional', str(self.root)):
            self.assertNotIn(private, output)

    def test_invalid_delta_error_root_citation_and_request_attribution_are_rejected(self):
        row = self.rows[0]
        valid = self.mc_review(row, deduction=5)
        for label, mutate in [
            ('no-error', lambda r: r.update(no_mathematical_errors=True)),
            ('selected ordinary', lambda r: r['axes']['capacity'].update(rmc_score=78)),
            ('reconcile', lambda r: r['error_deductions'][0].update(points=4)),
            ('unique ID', lambda r: r['error_deductions'].append(dict(r['error_deductions'][0], axis='taste'))),
            ('quotation', lambda r: r['axes']['capacity']['evidence'][0].update(quote='invented')),
            ('bind the selected', lambda r: r.update(source_review_sha256='a' * 64)),
        ]:
            with self.subTest(label=label):
                review = deepcopy(valid)
                mutate(review)
                self.select_mc(row, review)
                with self.assertRaisesRegex(ValueError, label):
                    self.prepare()
        self.select_mc(row, valid, purpose='something-else')
        with self.assertRaisesRegex(ValueError, 'calibration purpose'):
            self.prepare()
        self.select_mc(row, valid)
        self.request.write_bytes(b'Changed source request')
        with self.assertRaisesRegex(ValueError, 'source bytes changed'):
            self.prepare()

    def test_authorized_recheck_is_additive_and_mc_binds_the_effective_review(self):
        row = self.rows[0]
        selected = self.fixture.reviews[row['id']]
        rechecked = deepcopy(selected)
        rechecked['reviewer_context_id'] = 'new-blind-synthetic-review'
        rechecked['axes']['capacity']['score'] = 74
        path = self.root / 'rechecked.json'
        write_json(path, rechecked)
        row.update(effective_review=descriptor(path, self.root),
                   effective_reviewer_source=self.reviewer_source(path, rechecked))
        with self.assertRaisesRegex(ValueError, 'requires explicit user recheck'):
            self.prepare()
        auth = self.root / 'synthetic-private-authorization.txt'
        auth.write_text('Synthetic user-requested recheck of the same sealed originals.')
        decision = self.root / 'recheck-decision.json'
        write_json(decision, dict(schema=modes.RECHECK, decision='user-requested-recheck',
            reason='Synthetic decision', execution_sha256=row['execution']['sha256'],
            original_review_sha256=row['original_review']['sha256'],
            effective_review_sha256=row['effective_review']['sha256'], authorization=descriptor(auth, self.root)))
        row['recheck'] = descriptor(decision, self.root)
        self.select_mc(row, self.mc_review(row))
        changed = self.prepare()['models'][row['id']]
        self.assertNotEqual(changed['original_source_sha256'], changed['effective_source_sha256'])
        self.assertEqual(changed['axes']['capacity']['rmc'], 74)
        self.assertEqual(changed['axes']['capacity']['mc'], 74)
        self.assertEqual(self.original['models'][row['id']]['axes']['capacity']['score'], 80)
        self.assertEqual(self.base_path.read_bytes(), self.base_raw)

    def test_atomic_local_overlay_fills_pending_without_replacing_selected_rows(self):
        initial = self.prepare()
        target = self.root / modes.PUBLIC_PATH
        cli.apply_index(self.root, initial, expected=None)
        prior = target.read_bytes()
        self.assertEqual(prior, adoption.encoded(initial))
        row = self.rows[0]
        self.select_mc(row, self.mc_review(row, deduction=5))
        complete = self.prepare()
        with patch('scripts.adopt_independent_research_batch.os.replace', side_effect=OSError('interrupted fixture')):
            with self.assertRaisesRegex(OSError, 'interrupted fixture'):
                cli.apply_index(self.root, complete, expected=prior)
        self.assertEqual(target.read_bytes(), prior)
        cli.apply_index(self.root, complete, expected=prior)
        installed = target.read_bytes()
        changed = deepcopy(complete)
        changed['models'][row['id']]['axes']['capacity']['mc'] = 90
        with self.assertRaisesRegex(ValueError, 'retain already selected'):
            cli.apply_index(self.root, changed, expected=installed)
        self.assertEqual(target.read_bytes(), installed)
        self.assertEqual(self.base_path.read_bytes(), self.base_raw)
        policy_path = self.root / modes.POLICY_PATH
        policy, _ = modes.load_policy(policy_path)
        policy['group_weights'].update(written=31, independent_open_research=9)
        write_json(policy_path, policy)
        reweighted = self.prepare()
        self.assertNotEqual(reweighted['policy_sha256'], complete['policy_sha256'])
        self.assertEqual(reweighted['models'], complete['models'])
        cli.apply_index(self.root, reweighted, expected=installed)
        self.assertEqual(target.read_bytes(), adoption.encoded(reweighted))


class FixedScoreModeArithmetic(unittest.TestCase):
    def setUp(self):
        self.policy, _ = modes.load_policy()
        self.base = {mode: dict(metrics={key: dict(exact=v)
            for key, v in zip(('overall', *modes.BASE_GROUPS), values)})
            for mode, values in zip(modes.MODES, [(99, 70, 90, 100), (90, 60, 70, 80), (80, 50, 40, 30)])}
        self.axes = {axis: dict(mc=mc, rmc=rmc, strict=strict)
                     for axis, mc, rmc, strict in zip(modes.AXES, (80, 65, 90), (80, 60, 85), (True, False, False))}
        self.criteria = dict(autonomy=dict(planned=2, passed=2, unknown=0),
                             taste=dict(planned=3, passed=1, unknown=1),
                             capacity=dict(planned=5, passed=4, unknown=0))
        self.adopted = dict(status='reviewed',
            axes={axis: dict(score=grade['rmc'], strict=grade['strict']) for axis, grade in self.axes.items()})
        self.overlay = dict(axes=self.axes, criteria=self.criteria, mc_source_sha256='a' * 64)

    def test_mode_specific_totals_and_partial_strict_keep_their_own_denominators(self):
        result = modes.project_scores(self.base, self.policy, adopted=self.adopted, overlay=self.overlay)
        item = result['score_modes']
        self.assertEqual(item['MC']['item']['exact'], 81.25)
        self.assertEqual(item['RMC']['item']['exact'], 77.5)
        self.assertEqual(item['SMC']['components']['capacity']['exact'], 80)
        self.assertEqual(item['SMC']['components']['taste']['state'], 'insufficient-evidence')
        self.assertEqual(result['item_strict'], 0)
        self.assertEqual(result['composite_by_base']['MC']['exact'], 86.125)
        self.assertEqual(result['composite_by_base']['RMC']['exact'], 70.75)
        self.assertIsNone(result['strict_overall']['exact'])
        self.assertAlmostEqual(result['strict_overall']['lower'], 43 + 1 / 3)
        self.assertAlmostEqual(result['strict_overall']['upper'], 44 + 1 / 6)
        self.assertAlmostEqual(result['strict_confirmed'], 43 + 1 / 3)
        self.criteria['taste']['unknown'] = 0
        settled = modes.project_scores(self.base, self.policy, adopted=self.adopted, overlay=self.overlay)
        self.assertAlmostEqual(settled['strict_overall']['exact'], 43 + 1 / 3)
        self.assertEqual(settled['item_strict'], 0)

    def test_unmeasured_review_pending_and_confirmed_delivery_failure_are_distinct(self):
        unknown = modes.project_scores(self.base, self.policy)
        self.assertIsNone(unknown['score_modes']['RMC']['item']['exact'])
        self.assertEqual(unknown['score_modes']['RMC']['item']['state'], 'not-tested')
        self.assertEqual(unknown['composite_by_base']['RMC'], dict(lower=63, upper=73, exact=None))
        pending = modes.project_scores(self.base, self.policy, adopted=self.adopted)
        self.assertEqual(pending['score_modes']['MC']['item']['state'], 'review-pending')
        self.assertIsNone(pending['score_modes']['MC']['item']['exact'])
        self.assertEqual(pending['score_modes']['RMC']['item']['exact'], 77.5)
        failed = dict(status='delivery-failed', axes={axis: dict(score=None, strict=None) for axis in modes.AXES})
        result = modes.project_scores(self.base, self.policy, adopted=failed)['score_modes']
        self.assertIsNone(result['MC']['item']['exact'])
        for mode in ('RMC', 'SMC'):
            self.assertEqual(result[mode]['item']['exact'], 0)
            self.assertEqual(result[mode]['item']['state'], 'delivery-failed')
            self.assertIsNone(result[mode]['components']['capacity']['exact'])

    def test_signed_rmc_unknown_is_kept_and_only_overall_is_floored(self):
        self.base['RMC']['metrics'].update(written=dict(exact=0), lean=dict(exact=0),
            research=dict(lower=-20, upper=10, exact=None, confirmed=4))
        result = modes.project_scores(self.base, self.policy)
        self.assertEqual(result['composite_by_base']['RMC'], dict(lower=0, upper=13, exact=None))
        self.assertEqual(result['category_points']['RMC']['research'], dict(lower=-6, upper=3, exact=None, confirmed=1.2))
        self.assertEqual(result['confirmed_by_base']['RMC'], 1.2)

    def test_full_task_changes_each_total_by_at_most_its_fixed_ten_points(self):
        def settled(score):
            passed = score == 100
            overlay = dict(axes={axis: dict(mc=score, rmc=score, strict=passed) for axis in modes.AXES},
                criteria={axis: dict(planned=count, passed=count if passed else 0, unknown=0)
                          for axis, count in modes.REQUIRED_CRITERIA.items()}, mc_source_sha256='a' * 64)
            return modes.project_scores(self.base, self.policy, adopted=self.adopted, overlay=overlay)
        zero, full = settled(0), settled(100)
        for mode in modes.MODES:
            self.assertEqual(full['composite_by_base'][mode]['exact'] - zero['composite_by_base'][mode]['exact'], 10)
