"""Synthetic contracts for source-bound strict net credit and its public uses."""

from copy import deepcopy
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from math_gauge import independent_research_adoption as adoption
from math_gauge import independent_research_strict_credit as credit
from math_gauge import independent_research_value as value
from math_gauge.taste_v130 import POLICY_FILE
from scripts.preview_open_research_v130 import baseline_projection
from test_independent_research_value import FINALS, MARKER, SEALS, new_review
from test_research_ability_projection import MEASURED, UNMEASURED, baseline, overlay, point, selection


class StrictResearchCreditTests(unittest.TestCase):
    def setUp(self):
        self.policy, self.digest = credit.load_policy()
        self.source_taste = new_review('g' * 64)['taste']
        self.source_taste['aspects']['value']['mc_points'] = 55
        self.source_taste['aspects']['structure']['mc_points'] = 20
        self.source_taste['aspects']['selection']['mc_points'] = 18
        self.directions = [f'fixture-direction-{i}' for i in range(5)]
        self.grade = dict(taste=dict(mc=93, rmc=88, strict=False), capacity=dict(mc=85, rmc=84, strict=False))
        self.verdicts = dict(taste=dict(value=True, structure=True, selection=False),
                             capacity=dict(zip(self.directions, (True, True, True, True, False))))
        evidence = self.source_taste['rounds']['R1']['evidence']
        def judgment(**fields):
            return dict(reason=MARKER, evidence=evidence, **fields)
        self.review = dict(schema=credit.REVIEW, version=credit.VERSION, edition='1.3.0', model_id=MEASURED,
            reviewer_id='Synthetic reviewer', reviewer_context_id='fixture-fresh', reviewer_kind='ai', human_review='pending',
            source_review_sha256='a' * 64, source_mc_review_sha256='b' * 64, source_value_review_sha256='c' * 64,
            sealed_finals=SEALS.copy(), capacity=dict(directions={name: judgment(mc_points=points) for name, points in
                zip(self.directions, (19, 19, 19, 19, 9))}, deductions={'old-capacity-error': judgment(criterion=self.directions[0])}),
            taste=dict(deductions={'one-repaired-local-error': judgment(criterion='selection')}))
        self.source_mc = dict(error_deductions=[dict(id='old-capacity-error', axis='capacity', points=1),
                                               dict(id='not-capacity', axis='taste', points=7)])

    def validate(self, review=None):
        return credit.validate_allocation(self.review if review is None else review, model_id=MEASURED,
            policy=self.policy, grade=self.grade, verdicts=self.verdicts, effective_sha256='a' * 64,
            mc_sha256='b' * 64, taste_sha256='c' * 64, seals=SEALS, finals=FINALS,
            taste_source=self.source_taste, mc_source=self.source_mc)

    def test_net_pass_credit_excludes_failed_credit_and_does_not_charge_it_twice(self):
        result = self.validate()
        # The taste deduction is already charged inside discarded selection
        # credit. The capacity deduction belongs to a retained direction.
        self.assertEqual(credit._bounds(result['taste']), point(75))
        self.assertEqual(credit._bounds(result['capacity']), point(75))
        self.assertEqual(credit._counts(self.verdicts['capacity']), dict(planned=5, passed=4, unknown=0))
        # 4/5 passed is an 80% diagnostic, while the retained credit is 75.
        self.assertNotEqual(credit._bounds(result['capacity'])['exact'], min(84, 80))
        self.assertEqual(credit._bounds(credit._direct(71, dict(planned=5, passed=5, unknown=0))), point(71))
        self.assertEqual(credit._bounds(credit._direct(0, dict(planned=5, passed=4, unknown=0))), point(0))

    def test_unresolved_direction_keeps_its_original_net_credit_bounds(self):
        self.verdicts['capacity'][self.directions[3]] = None
        self.assertEqual(credit._bounds(self.validate()['capacity']), dict(lower=56, upper=75, exact=None))
        self.assertEqual(credit._bounds(credit._unallocated(84, credit._counts(self.verdicts['capacity']))),
                         dict(lower=0, upper=84, exact=None))
        self.assertEqual(credit._bounds(credit._unallocated(None, dict(planned=5, passed=0, unknown=5))),
                         dict(lower=0, upper=100, exact=None))

    def test_wrong_sources_forged_credit_and_repeated_roots_are_rejected(self):
        changes = (
            lambda r: r.update(source_value_review_sha256='d' * 64),
            lambda r: r['sealed_finals'].update(R1='d' * 64),
            lambda r: r['capacity'].update(rmc_score=100),
            lambda r: r['capacity']['directions'][self.directions[0]].update(mc_points=21),
            lambda r: r['capacity']['directions'][self.directions[0]].update(mc_points=0),
            lambda r: r['capacity']['directions'].update(optional=deepcopy(r['capacity']['directions'][self.directions[0]])),
            lambda r: r['capacity']['deductions'].update(another=deepcopy(r['capacity']['deductions']['old-capacity-error'])),
            lambda r: r['capacity']['deductions']['old-capacity-error'].update(points=0),
            lambda r: r['taste']['deductions']['one-repaired-local-error']['evidence'][0].update(quote='wrong'),
        )
        for change in changes:
            with self.subTest(change=change):
                review = deepcopy(self.review)
                change(review)
                with self.assertRaises(ValueError):
                    self.validate(review)

    def test_current_assembly_changes_only_strict_credit_and_its_two_profile_projections(self):
        data = baseline()
        raw = json.dumps(data).encode()
        adopted = selection(raw, POLICY_FILE.read_bytes())
        adopted_raw = json.dumps(adopted).encode()
        overlay_raw = overlay(adopted_raw)
        old_value_policy, _ = value.load_policy()
        old_value_policy['base_results_sha256'] = credit._hash(overlay_raw)
        with TemporaryDirectory() as dirname:
            root = Path(dirname)
            value_path = root / 'value-policy.json'
            value_raw = adoption.encoded(old_value_policy)
            value_path.write_bytes(value_raw)
            revised_raw = adoption.encoded(dict(schema=value.PUBLIC, version=value.VERSION, edition='1.3.0',
                policy_sha256=credit._hash(value_raw), base_results_sha256=credit._hash(overlay_raw),
                cohort=[MEASURED], candidate_calls_by_adoption=0, models={MEASURED: dict(taste=self.grade['taste'],
                    criteria=dict(planned=3, passed=2, unknown=0), extension_level='E1', source_sha256='a' * 64)}))
            policy = dict(self.policy, value_policy_sha256=credit._hash(value_raw), value_results_sha256=credit._hash(revised_raw),
                          score_modes_results_sha256=credit._hash(overlay_raw))
            policy_path = root / 'strict-credit-policy.json'
            policy_path.write_bytes(adoption.encoded(policy))
            overlay_args = dict(source_bytes=raw, adopted=adopted, adopted_bytes=adopted_raw, overlay_bytes=overlay_raw,
                profile_policy_path=POLICY_FILE.with_name('profile-policy-v2.json'),
                value_policy_path=value_path, value_bytes=revised_raw)
            original, original_profiles, _ = baseline_projection(data, **overlay_args)
            pending, pending_profiles, _ = baseline_projection(data, strict_credit_policy_path=policy_path, **overlay_args)
            result = dict(schema=credit.PUBLIC, version=credit.VERSION, edition='1.3.0',
                policy_sha256=credit._hash(policy_path.read_bytes()), value_results_sha256=policy['value_results_sha256'],
                candidate_calls_by_adoption=0, cohort=[MEASURED],
                models={MEASURED: dict(taste=point(75), capacity=point(70), source_sha256='b' * 64)})
            revised, profiles, category_points = baseline_projection(data, strict_credit_policy_path=policy_path,
                strict_credit_bytes=adoption.encoded(result), **overlay_args)
            result['models'][MEASURED]['taste']['reason'] = MARKER
            with self.assertRaises(ValueError):
                baseline_projection(data, strict_credit_policy_path=policy_path,
                                    strict_credit_bytes=adoption.encoded(result), **overlay_args)

        old, missing, row = [next(row for row in board['rows'] if row['id'] == MEASURED)
                             for board in (original, pending, revised)]
        self.assertEqual(old['score_modes']['SMC']['components']['capacity']['exact'], 100)
        self.assertEqual(row['score_modes']['SMC']['components']['capacity']['exact'], 70)
        self.assertEqual(row['score_modes']['SMC']['components']['taste']['exact'], 75)
        self.assertEqual(missing['score_modes']['SMC']['components']['taste']['upper'], 88)
        self.assertIsNone(missing['score_modes']['SMC']['item']['exact'])
        self.assertEqual(row['criteria'], old['criteria'])
        self.assertEqual(row['task_strict'], old['task_strict'])
        for mode in ('MC', 'RMC'):
            self.assertEqual(row['score_modes'][mode], old['score_modes'][mode])
            self.assertEqual(row['composites'][mode], old['composites'][mode])
        self.assertLess(row['score_modes']['SMC']['item']['exact'], row['score_modes']['RMC']['item']['exact'])
        self.assertAlmostEqual(category_points[MEASURED]['SMC'][value.modes.ITEM]['exact'], (75 + 2*70) / 30)
        modeled, old_modeled = (profile['by_model'][MEASURED] for profile in (profiles, original_profiles))
        self.assertEqual(modeled['completion_v130']['exact'], row['strict_overall']['exact'])
        self.assertEqual(modeled['independent_taste_smc']['exact'], 75)
        self.assertEqual(modeled['independent_taste_smc']['coverage'], old_modeled['independent_taste_smc']['coverage'])
        for stage in modeled['stages']:
            self.assertEqual(modeled['stages'][stage]['mathematical_taste']['lower'], 60)
            for axis in ('initiative_v130', 'depth_v130', 'discernment_v130', 'open_research_v130'):
                self.assertEqual(modeled['stages'][stage][axis], old_modeled['stages'][stage][axis])
        self.assertIsNone(pending_profiles['by_model'][MEASURED]['independent_taste_smc']['exact'])
        unmeasured = next(row for row in revised['rows'] if row['id'] == UNMEASURED)
        self.assertEqual(unmeasured['strict_overall'], dict(lower=72, upper=82, exact=None))
        self.assertEqual(revised['strict_credit_binding'], profiles['strict_credit_binding'])
