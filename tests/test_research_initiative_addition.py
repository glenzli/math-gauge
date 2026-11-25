from copy import deepcopy
from pathlib import Path
import json
import tempfile
import unittest
from unittest.mock import patch

from math_gauge import research_initiative as owner
from math_gauge import independent_research_admitted_delivery as admitted
from math_gauge import independent_research_external as external


MODEL = 'gemini-4-carbon-medium'


class InitiativeAdditionCase(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.policy_hash = 'a' * 64
        self.policy = {'planned_opportunities': 28, 'private_contract_sha256': 'b' * 64}
        policy_reader = patch.object(owner, 'load_policy', return_value=(self.policy, self.policy_hash))
        self.addCleanup(policy_reader.stop)
        policy_reader.start()
        for path in external.POLICY_PATHS.values():
            self.write(path, {})
        self.aggregate = dict(schema=admitted.SCHEMA, version='0.1.0', edition=owner.EDITION,
            source_kind=admitted.SOURCE_KIND, source_binding=dict(base_edition='1.2.0',
                baseline=dict(path='results/independent-research-baselines/v0.1.0/' + 'd' * 64 + '/data.json',
                              bytes=0, sha256='d' * 64),
                adoption_sha256='e' * 64, admission_sha256='1' * 64, review_sha256='2' * 64,
                authorization_sha256=admitted.AUTHORIZATION_SHA256),
            policy_bindings=external.policy_bindings(self.root), cohort=[MODEL],
            models={MODEL: dict(status='reviewed',
                axes={axis: dict(mc=100, rmc=100, strict=True) for axis in ('taste', 'capacity')},
                criteria={axis: dict(planned=n, passed=n, unknown=0) for axis, n in (('taste', 3), ('capacity', 5))},
                strict_credit={axis: dict(lower=100, upper=100, exact=100) for axis in ('taste', 'capacity')},
                extension_level='E0', autonomy_score=100, normal_rounds=2, forced_rounds=1,
                round_dispatches=3, delivery_kinds=['forced-content', 'normal-final', 'normal-final'], source_sha256='c' * 64)},
            method=dict(selection='post-observation-user-selected-cutoff', native_status_preserved=True,
                forced_content_is_mathematically_reviewed=True, original_round_limit_seconds=2700,
                R1_user_extension_seconds=900, account_condition_changed=True, historical_results_unchanged=True,
                resource_usage_scope='unknown-until-independently-reconciled'),
            reviewer_kind='ai', human_review='pending', candidate_calls_by_adoption=0)
        self.admitted_ref = self.write(admitted.PUBLIC_PATH, self.aggregate)
        self.prepare()

    def write(self, relative, value):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        raw = owner.encoded(value)
        path.write_bytes(raw)
        return dict(path=Path(relative).as_posix(), bytes=len(raw), sha256=owner.digest(raw))

    def prepare(self, *, unknown_legacy=False, old_extension=None):
        self.index = dict(schema='math-gauge.research-initiative-index/v1', version=owner.VERSION,
            edition=owner.EDITION, condition=owner.CONDITION, policy_sha256=self.policy_hash,
            models={}, **owner.BOUNDARIES)
        for mid in [MODEL] + ['model-' + str(n) for n in range(19)]:
            rows = [dict(opportunity_id='case-' + str(n), grade=None if unknown_legacy and n == 0 else 4)
                    for n in range(27)] + [dict(opportunity_id='independent-extension', grade=old_extension)]
            review = dict(model_id=mid, rows=rows)
            material = dict(model_id=mid, source_status='unavailable')
            report = owner.public_projection(review, material, self.policy_hash)
            self.index['models'][mid] = self.write(owner.DIRECTORY + '/' + mid + '/profile.json', report)
            if mid == MODEL:
                self.base, self.base_review = report, review
        self.write(owner.INDEX_PATH, self.index)
        review = deepcopy(self.base_review)
        review['rows'][-1]['grade'] = 0
        self.new_review = review
        report = owner.public_projection(review, dict(model_id=MODEL, source_status='available'), self.policy_hash)
        self.addition = dict(schema='math-gauge.research-initiative-addition/v1', version=owner.VERSION,
            edition=owner.EDITION, model_id=MODEL, condition=owner.CONDITION, policy_sha256=self.policy_hash,
            base_profile=self.index['models'][MODEL], admitted_results=self.admitted_ref,
            admitted_selection_sha256='e' * 64,
            independent_review=dict(primary_ai_review_sha256='3' * 64, coordinator_selection_sha256='4' * 64,
                                    normalization_sha256='5' * 64, grade_0_to_4=0),
            profile=report, **owner.BOUNDARIES)

    def load(self):
        return owner.load_public(self.root, benchmark_version=owner.EDITION)

    def validate(self, addition):
        return owner.validate_addition(addition, self.base, self.index['models'][MODEL],
                                      self.root, self.policy, self.policy_hash)

    def test_absent_addition_preserves_the_unknown_and_original_projection(self):
        result = self.load()
        self.assertNotIn('additions', result)
        row = next(r for r in result['models'] if r['id'] == MODEL)
        self.assertIsNone(row['metric']['exact'])
        self.assertEqual(row['extension_metric']['coverage']['reviewed'], 0)
        self.assertEqual(row['metric']['coverage']['planned'], 28)
        self.assertIsNone(owner.load_public(self.root, benchmark_version='1.2.0'))

    def test_known_zero_preserves_legacy_other_models_and_frozen_source_bytes(self):
        before = self.load()
        old_bytes = {p: (self.root / p).read_bytes() for p in
                     [owner.INDEX_PATH] + [r['path'] for r in self.index['models'].values()]}
        ref = self.write(owner.ADDITIONS[MODEL], self.addition)
        after = self.load()
        old, new = ({r['id']: r for r in view['models']} for view in (before, after))
        self.assertEqual(old[MODEL]['legacy_metric'], new[MODEL]['legacy_metric'])
        self.assertEqual({mid: r for mid, r in old.items() if mid != MODEL},
                         {mid: r for mid, r in new.items() if mid != MODEL})
        self.assertEqual(new[MODEL]['extension_metric']['exact'], 0)
        self.assertEqual(new[MODEL]['metric']['exact'], 96.4285714286)
        self.assertEqual(new[MODEL]['metric']['coverage']['reviewed'], 28)
        self.assertEqual(before['source'], after['source'])
        self.assertEqual(after['additions'], [ref])
        self.assertTrue(all((self.root / p).read_bytes() == raw for p, raw in old_bytes.items()))

    def test_unknown_legacy_keeps_the_full_twenty_eight_denominator(self):
        self.prepare(unknown_legacy=True)
        self.write(owner.ADDITIONS[MODEL], self.addition)
        row = next(r for r in self.load()['models'] if r['id'] == MODEL)
        self.assertIsNone(row['metric']['exact'])
        self.assertEqual(row['metric']['coverage'], dict(unit='research_opportunity', planned=28, reviewed=27))
        self.assertEqual(row['metric']['confirmed'], 92.8571428571)
        self.assertEqual(row['metric']['unknown_weight'], 3.5714285714)
        self.assertEqual(row['legacy_metric'], self.base['legacy_metric'])
        self.assertEqual(row['extension_metric']['exact'], 0)

    def test_a_valid_but_different_legacy_grade_cannot_be_adopted(self):
        changed = deepcopy(self.addition)
        review = deepcopy(self.new_review)
        review['rows'][0]['grade'] = 3
        changed['profile'] = owner.public_projection(review, {'changed': True}, self.policy_hash)
        owner.validate_public(changed['profile'], self.policy, self.policy_hash)
        with self.assertRaises(ValueError):
            self.validate(changed)

    def test_addition_cannot_regrade_an_already_known_extension(self):
        self.prepare(old_extension=1)
        with self.assertRaises(ValueError):
            self.validate(self.addition)

    def test_sources_model_grade_and_public_field_allowlists_are_strict(self):
        changes = (
            lambda a: a['base_profile'].update(sha256='0' * 64),
            lambda a: a['admitted_results'].update(sha256='0' * 64),
            lambda a: a.update(admitted_selection_sha256='0' * 64),
            lambda a: a.update(model_id='another-model'),
            lambda a: a.update(new_candidate_calls=False),
            lambda a: a['independent_review'].update(grade_0_to_4=False),
            lambda a: a['independent_review'].update(grade_0_to_4=1),
            lambda a: a['independent_review'].update(private_path='/private/materials'),
            lambda a: a['profile'].update(quotation='private mathematical text'),
            lambda a: a.update(private_review='/private/materials'),
        )
        for change in changes:
            with self.subTest(change=change):
                addition = deepcopy(self.addition)
                change(addition)
                with self.assertRaises(ValueError):
                    self.validate(addition)

    def test_current_admitted_policy_binding_must_replay(self):
        self.write(next(iter(external.POLICY_PATHS.values())), {'changed': True})
        with self.assertRaises(ValueError):
            self.validate(self.addition)


if __name__ == '__main__':
    unittest.main()
