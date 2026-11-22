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
            for key in ('open_research_autonomy', 'independent_taste', 'completion_v130'):
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
                                         self.denominators, legacy_taste=source)['fixture']
        self.assertEqual(project['stages']['first']['mathematical_taste']['exact'], 77)
        known = project['stages']['revision']['mathematical_taste']
        self.assertEqual((known['lower'], known['upper'], known['exact']), (64.5, 89.5, None))
        self.assertEqual(known['legacy_metric']['coverage']['reviewed'], 0)
        self.assertEqual(known['independent_coverage'], dict(unit='manuscript', planned=3, reviewed=3))
        for stage_id in ('first', 'revision'):
            for axis in ('initiative_v130', 'depth_v130', 'open_research_v130', 'discernment_v130'):
                self.assertEqual(project['stages'][stage_id][axis], before['stages'][stage_id][axis])
