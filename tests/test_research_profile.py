"""Fixed profile-route policy and unknown intervals without model execution."""

import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from math_gauge import research_profile as profile
from math_gauge.taste_v130 import POLICY_FILE as SCORE_POLICY


class ResearchProfileTests(unittest.TestCase):
    def setUp(self):
        self.policy, _ = profile.load_policy(profile.POLICY_FILE)
        self.denominators = json.loads(SCORE_POLICY.read_bytes())['new_axis_denominators']
        self.report = dict(subscores=dict(autonomy=None, taste=86, capacity=70),
                           strict_overall=dict(lower=72, upper=72, exact=72), strict_confirmed=72)
        self.taste_smc = dict.fromkeys(('lower', 'upper', 'exact', 'confirmed'), 66.6666666667)
        self.taste_smc['state'] = 'reviewed'
        self.report['score_modes'] = dict(SMC=dict(components=dict(taste=self.taste_smc)))
        self.report['criteria'] = dict(taste=dict(planned=3, passed=2, unknown=0))
        self.report['strict_verdicts'] = dict(taste=False)
        self.data = {'open_research': dict(schema='math-gauge.open-research/v1', benchmark_version='1.2.0',
            models=[dict(id='fixture', first=dict(lower=50, upper=50, exact=50,
                coverage=dict(unit='open_research_family', planned=5, reviewed=5)), revision=None)])}

    def projection(self, policy):
        return profile.project_models(self.data, {'fixture': self.report}, policy, self.denominators)['fixture']

    def test_partial_autonomy_never_renormalizes_capacity_or_implies_an_extra_task(self):
        row = self.projection(self.policy)
        blended = row['stages']['first']['open_research_v130']
        self.assertIsNone(blended['exact'])
        self.assertAlmostEqual(blended['lower'], 49 + 1 / 3)
        self.assertEqual(blended['upper'], 56)
        self.assertEqual(blended['confirmed'], round(49 + 1 / 3, 10))
        self.assertEqual(blended['task_coverage'], dict(unit='independent_open_research_task', planned=1,
                         reviewed=0, components_planned=2, components_reviewed=1))
        self.assertEqual(blended['base_coverage']['planned'], 5)
        self.assertEqual(row['independent_taste']['exact'], 86)

    def test_adjustable_blends_leave_raw_scores_and_official_completion_unchanged(self):
        self.report['subscores']['autonomy'] = 10
        before = self.projection(self.policy)
        self.policy['routes']['open_research_v130'].update(item_percent=40, component_weights=dict(autonomy=1, capacity=1))
        with TemporaryDirectory() as directory:
            path = Path(directory) / 'policy.json'
            path.write_text(json.dumps(self.policy))
            policy, digest = profile.load_policy(path)
            self.assertEqual(len(digest), 64)
            after = self.projection(policy)
            self.assertEqual(before['stages']['first']['open_research_v130']['exact'], 50)
            self.assertEqual(after['stages']['first']['open_research_v130']['exact'], 46)
            for key in ('open_research_autonomy', 'independent_taste', 'independent_taste_smc', 'completion_v130'):
                self.assertEqual(after[key], before[key])
            self.policy['routes']['open_research_v130']['component_weights']['autonomy'] = 0
            path.write_text(json.dumps(self.policy))
            with self.assertRaisesRegex(ValueError, 'fixed independent research profile route'):
                profile.load_policy(path)

    def test_mathematical_taste_uses_only_its_fixed_two_sources_in_each_stage(self):
        def stage(score):
            return dict(exact=score, lower=score, upper=score, confirmed=score,
                        coverage=dict(unit='theorem_extension_family', planned=6, reviewed=6, observed=6))

        source = dict(fixture=dict(first=stage(50), revision=None))
        before = self.projection(self.policy)
        self.policy['mathematical_taste']['legacy_percent'] = 25
        project = profile.project_models(self.data, {'fixture': self.report}, self.policy,
                                         self.denominators, legacy_taste_strict=source)['fixture']
        self.assertEqual(project['independent_taste']['exact'], 86)
        self.assertEqual(project['independent_taste_smc']['exact'], self.taste_smc['exact'])
        self.assertAlmostEqual(project['stages']['first']['mathematical_taste']['exact'], 62.5)
        known = project['stages']['revision']['mathematical_taste']
        self.assertAlmostEqual(known['lower'], 50)
        self.assertAlmostEqual(known['upper'], 75)
        self.assertIsNone(known['exact'])
        self.assertFalse(known['legacy_review_available'])
        self.assertEqual(known['legacy_metric']['coverage']['reviewed'], 0)
        self.assertEqual(known['independent_coverage'], dict(unit='taste_checkpoint', planned=3, reviewed=3))
        for stage_id in ('first', 'revision'):
            for axis in ('initiative_v130', 'depth_v130', 'open_research_v130', 'discernment_v130'):
                self.assertEqual(project['stages'][stage_id][axis], before['stages'][stage_id][axis])

    def test_unresolved_checkpoints_keep_source_bounds_and_zero_is_known(self):
        self.report['criteria']['taste'].update(passed=1, unknown=1)
        self.taste_smc.update(lower=33.3333333333, upper=66.6666666667, exact=None,
                              confirmed=33.3333333333, state='insufficient-evidence')
        blended = self.projection(self.policy)['stages']['first']['mathematical_taste']
        self.assertAlmostEqual(blended['lower'], 80 / 3)
        self.assertAlmostEqual(blended['upper'], 160 / 3 + 20)
        self.assertIsNone(blended['exact'])
        self.assertEqual(blended['independent_coverage']['reviewed'], 2)
        self.assertEqual(blended['independent_metric']['state'], 'insufficient-evidence')
        self.report['criteria']['taste'].update(passed=0, unknown=0)
        self.taste_smc.update(lower=0, upper=0, exact=0, confirmed=0, state='reviewed')
        raw = self.projection(self.policy)['independent_taste_smc']
        self.assertEqual(raw['exact'], 0)
        self.assertEqual(raw['coverage']['reviewed'], 3)
