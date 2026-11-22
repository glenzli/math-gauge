"""Synthetic strict-review amendments, fixed coverage, original-source and privacy contracts."""
import copy
import json
import unittest

from math_gauge import legacy_taste as legacy
from math_gauge import legacy_taste_strict as strict
from math_gauge.open_research import encoded
from tests import test_legacy_taste as fixtures

MARKER = fixtures.MARKER


class StrictTasteTests(unittest.TestCase):
    def setUp(self):
        self.source = fixtures.LegacyTasteTests()
        self.source.setUp()
        self.addCleanup(self.source.doCleanups)
        source = self.source
        for mid, model in source.catalog['models'].items():
            for stage in ('first', 'revision'):
                for cid, material in (model[stage] or {}).items():
                    row = source.judgment(source.families.index(cid), 75, stage=stage, mid=mid)
                    answer = source.root / material['evidence']['answer']['path']
                    row['evidence'] = [dict(quote=answer.read_text().split(MARKER)[0].strip())]
                    source.rows.append(row)
        self.catalog = encoded(source.catalog)
        source.review['source_catalog_sha256'] = legacy.sha256(self.catalog)
        self.previous = copy.deepcopy(source.review)
        self.policy, self.policy_sha = strict.load_policy()
        self.review = dict(self.previous, schema=strict.REVIEW_SCHEMA, version=strict.VERSION,
                           policy_sha256=self.policy_sha,
                           previous_review_sha256=legacy.sha256(encoded(self.previous)))
        self.review['judgments'] = []
        for old in source.rows:
            row = copy.deepcopy(old)
            row.update(score=80, unresolved_kind=None,
                       strict_checks=dict.fromkeys(strict.CHECKS, True),
                       criteria={key: dict(points=points, reason=MARKER, evidence=copy.deepcopy(old['evidence']))
                                 for key, points in [('value', 30), ('conditions', 25), ('support', 25)]})
            self.review['judgments'].append(row)

    def project(self):
        source = self.source
        report = strict.prepare_public(source.roots, self.catalog, [encoded(self.review)],
            [encoded(self.previous)], self.policy, self.policy_sha, source.policy, source.policy_sha)
        return strict.validate_public(report, self.policy_sha, source.baseline, source.baseline_sha,
                                      policy=self.policy)

    def test_full_strict_assessment_uses_new_judgments_and_keeps_originals(self):
        before = encoded(self.previous)
        report = self.project()
        self.assertEqual(report['models']['evaluated']['first']['exact'], 80)
        self.assertEqual(report['models']['evaluated']['revision']['exact'], 80)
        self.assertEqual(report['review_coverage'], dict(planned=20, assessed=20, scored=20,
                                                       source_missing=0, verification_unresolved=0))
        self.assertEqual(encoded(self.previous), before)
        self.assertEqual(report['previous_review_sha256'], [legacy.sha256(before)])
        self.assertEqual(report['review_sha256'], [legacy.sha256(encoded(self.review))])

    def test_previously_unrated_source_can_receive_its_own_actual_choice_judgment(self):
        old = self.previous['judgments'][0]
        old.update(score=None, enough_evidence=False, assessment_status='evidence_insufficient')
        self.review['previous_review_sha256'] = legacy.sha256(encoded(self.previous))
        report = self.project()
        self.assertEqual(report['models']['evaluated']['first']['exact'], 80)

    def test_genuine_zero_and_specific_unresolved_mathematics_have_different_bounds(self):
        row = self.review['judgments'][0]
        row['score'] = 0
        for part in row['criteria'].values():
            part['points'] = 0
        zero = self.project()['models']['evaluated']['first']
        self.assertAlmostEqual(zero['exact'], 400 / 6)
        row.update(score=None, enough_evidence=False, assessment_status='evidence_insufficient',
                   unresolved_kind='verification_unresolved')
        row['strict_checks']['credited_work_closed'] = None
        for part in row['criteria'].values():
            part['points'] = None
        report = self.project()
        unknown = report['models']['evaluated']['first']
        self.assertIsNone(unknown['exact'])
        self.assertAlmostEqual(unknown['lower'], zero['exact'])
        self.assertAlmostEqual(unknown['upper'] - unknown['lower'], 100 / 6)
        self.assertEqual(report['review_coverage']['verification_unresolved'], 1)
        row['unresolved_kind'] = 'no_extra_theorem'
        with self.assertRaisesRegex(ValueError, 'specific missing source'):
            self.project()

    def test_full_support_and_full_score_require_every_strict_check(self):
        row = self.review['judgments'][0]
        for key in strict.DIMENSIONS:
            row['criteria'][key]['points'] = strict.DIMENSIONS[key]
        row['score'] = 100
        row['strict_checks']['credited_work_closed'] = False
        with self.assertRaisesRegex(ValueError, 'Full strict credit'):
            self.project()
        row['score'] = 99
        row['criteria']['value']['points'] = 39
        with self.assertRaisesRegex(ValueError, 'Full strict credit'):
            self.project()
        row['strict_checks']['credited_work_closed'] = True
        row['strict_checks']['no_silent_repair'] = False
        with self.assertRaisesRegex(ValueError, 'rely on repairs'):
            self.project()
        row['strict_checks']['no_silent_repair'] = True
        row['strict_checks']['scope_faithful'] = False
        row['criteria']['conditions']['points'] = 29
        row['criteria']['value']['points'] = 40
        # A scope error is charged to conditions once; independently closed work
        # need not lose the same point again in its proof-support dimension.
        self.assertEqual(self.project()['review_coverage']['scored'], 20)
        row['strict_checks']['credited_work_closed'] = False
        row['criteria']['conditions']['points'] = 30
        row['criteria']['value']['points'] = 37
        row['criteria']['support']['points'] = 20
        row['score'] = 87
        # A proof error does not automatically constitute another assumption error.
        self.assertEqual(self.project()['review_coverage']['scored'], 20)

    def test_dimension_points_and_reasons_are_independent_source_bound_inputs(self):
        row = self.review['judgments'][0]
        row['criteria']['value']['points'] = 41
        with self.assertRaisesRegex(ValueError, 'fixed point budget'):
            self.project()
        row['criteria']['value']['points'] = 31
        with self.assertRaisesRegex(ValueError, 'equal its three'):
            self.project()
        row['criteria']['value']['points'] = 30
        row['criteria']['conditions']['evidence'] = [dict(quote='Not in the actual answer')]
        with self.assertRaisesRegex(ValueError, 'quote differs'):
            self.project()

    def test_missing_duplicate_or_replaced_sources_are_rejected(self):
        original = copy.deepcopy(self.review)
        self.review['judgments'].pop()
        with self.assertRaisesRegex(ValueError, 'every answer'):
            self.project()
        self.review = copy.deepcopy(original)
        self.review['judgments'].append(copy.deepcopy(self.review['judgments'][0]))
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            self.project()
        self.review = copy.deepcopy(original)
        self.review['judgments'][0]['response_sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'original answer identity'):
            self.project()

    def test_new_policy_and_prior_review_cannot_be_swapped(self):
        self.review['policy_sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'prior-review binding'):
            self.project()
        self.review['policy_sha256'] = self.policy_sha
        self.review['previous_review_sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'prior-review binding'):
            self.project()

    def test_private_dimensions_and_scope_never_leave_aggregate_projection(self):
        report = self.project()
        text = json.dumps(report)
        self.assertNotIn(MARKER, text)
        self.assertNotIn('fixture-1', text)
        self.assertNotIn('criteria', text)
        report['review_coverage']['assessed'] -= 1
        with self.assertRaisesRegex(ValueError, 'pending review'):
            strict.validate_public(report, self.policy_sha, self.source.baseline,
                                   self.source.baseline_sha, policy=self.policy)
