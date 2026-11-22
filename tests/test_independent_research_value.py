"""Synthetic contracts for source-bound 1.3 value review and fixed score composition."""

from copy import deepcopy
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from math_gauge import independent_research_adoption as adoption
from math_gauge import independent_research_score_modes as modes
from math_gauge import independent_research_value as value
from math_gauge.research_profile import VALUE_POLICY_PATH, load_policy, project_models
from math_gauge.taste_v130 import POLICY_FILE, ROUNDS
from scripts.adopt_independent_research_value import main
from test_research_ability_projection import MEASURED, baseline, overlay, point, selection


MARKER = 'SYNTHETIC-PRIVATE-VALUE-EVIDENCE'
SEALS = {r: str(i) * 64 for i, r in enumerate(ROUNDS, 1)}
FINALS = {r: f'{r} 数学证据 {MARKER}'.encode() for r in ROUNDS}


def new_review(policy_digest, seals=SEALS, effective='e' * 64, mc_source='d' * 64):
    def record(round_id='R1', **fields):
        raw = FINALS[round_id]
        return dict(reason=MARKER, evidence=[dict(round=round_id, file=round_id+'.md', start=3,
                    end=len(raw), quote=raw[3:].decode())], **fields)

    return dict(schema=value.REVIEW, version=value.VERSION, edition='1.3.0', model_id=MEASURED,
        policy_sha256=policy_digest, source_review_sha256=effective, source_mc_review_sha256=mc_source,
        sealed_finals=seals, reviewer_id='Synthetic value reviewer', reviewer_context_id='fixture-new-context',
        reviewer_kind='ai', human_review='pending',
        taste=dict(mc_score=88, rmc_score=83, aspects={name: record(mc_points=points) for name, points in
                   zip(value.DIMENSIONS, (53, 16, 19))}, gates={name: record(verdict=True) for name in value.DIMENSIONS},
                   rounds={r: record(r) for r in ROUNDS}, sufficient_choices=record(verdict=True),
                   error_deductions=[record(id='one-repaired-local-error', points=5)]),
        extension=dict(record(), level='E2', assessed_rounds=list(ROUNDS), independent_question=MARKER,
                       outside_core=MARKER, result_and_scope=MARKER, value=MARKER))


def write(root, name, raw):
    path = root / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(raw)
    return dict(path=name, bytes=len(raw), sha256=value._hash(raw))


class ValueRevisionTests(unittest.TestCase):
    def setUp(self):
        self.policy, self.digest = value.load_policy()
        self.source = dict(model_id=MEASURED, policy=self.policy, policy_hash=self.digest,
                           effective_sha256='e' * 64, mc_sha256='d' * 64, sealed_finals=SEALS, finals=FINALS)
        self.data = baseline()
        self.old = selection(json.dumps(self.data).encode(), POLICY_FILE.read_bytes())
        self.retained = json.loads(overlay(json.dumps(self.old).encode()))['models'][MEASURED]
        self.reports = {mode: dict(metrics={key: point(80) for key in (*modes.BASE_GROUPS, 'overall')})
                        for mode in modes.MODES}

    def validate(self, review):
        return value.validate_review(review, **self.source)

    def project(self, review=None, *, status='reviewed', retained=True):
        return value.project_scores(self.reports, self.policy, adopted=dict(status=status),
                                    retained=self.retained if retained else None, review=review)

    def test_repaired_local_error_preserves_independent_strict_verdict(self):
        review = new_review(self.digest)
        result = self.validate(review)
        self.assertEqual(result['taste'], dict(mc=88, rmc=83, strict=True))
        projected = self.project(result)
        self.assertAlmostEqual(projected['score_modes']['RMC']['item']['exact'], (83 + 140) / 3)
        self.assertEqual(projected['score_modes']['SMC']['item']['exact'], 100)
        self.assertEqual(projected['item_strict'], 100)
        # A low-value, technically faithful result can fail value independently.
        taste = review['taste']
        taste['aspects']['value']['mc_points'] = 3
        taste['mc_score'], taste['rmc_score'] = 38, 33
        taste['gates']['value']['verdict'] = False
        result = self.project(self.validate(review))
        self.assertEqual(result['criteria']['taste']['passed'], 2)
        self.assertLess(result['score_modes']['SMC']['item']['exact'], 100)
        self.assertEqual(result['item_strict'], 0)

    def test_missing_and_zero_are_distinct_and_denominator_is_fixed(self):
        unmeasured = self.project(status='not-run', retained=False)
        pending = self.project()
        zero = self.project(dict(taste=dict(mc=0, rmc=0, strict=False),
                                 criteria=dict(planned=3, passed=0, unknown=0), extension_level='E0'))
        failed = self.project(status='delivery-failed', retained=False)
        self.assertEqual(unmeasured['strict_overall'], dict(lower=72, upper=82, exact=None))
        self.assertEqual(pending['score_modes']['RMC']['components']['taste']['state'], 'review-pending')
        self.assertEqual(pending['score_modes']['RMC']['components']['capacity']['exact'], 70)
        self.assertIsNone(pending['item_composite']['exact'])
        self.assertEqual(zero['subscores']['taste'], 0)
        self.assertEqual(zero['coverage']['components_reviewed'], 2)
        self.assertEqual(failed['score_modes']['SMC']['item']['exact'], 0)
        self.assertIsNone(failed['score_modes']['MC']['item']['exact'])

    def test_extension_changes_only_initiative_and_old_autonomy_never_enters_scores(self):
        review = self.validate(new_review(self.digest))
        profile_policy = load_policy(POLICY_FILE.parents[3] / VALUE_POLICY_PATH)[0]
        denominators = json.loads(POLICY_FILE.read_bytes())['new_axis_denominators']
        projections, profiles = [], []
        retained_c = adoption.encoded(self.retained['axes']['capacity'])
        for level in ('E0', 'E1', 'E2', 'E3', None):
            projected = self.project(dict(review, extension_level=level))
            profile = project_models(self.data, {MEASURED: projected}, profile_policy, denominators)[MEASURED]
            projections.append(projected)
            profiles.append(profile)
            self.retained['axes']['autonomy']['rmc'] = 100
        for projected in projections:
            self.assertEqual(projected['composite_by_base'], projections[0]['composite_by_base'])
            self.assertEqual(projected['criteria']['capacity'], self.retained['criteria']['capacity'])
            self.assertEqual({mode: projected['score_modes'][mode]['components']['capacity']['exact']
                              for mode in modes.MODES}, dict(MC=76, RMC=70, SMC=100))
        self.assertEqual(adoption.encoded(self.retained['axes']['capacity']), retained_c)
        first = [profile['stages']['first'] for profile in profiles]
        self.assertEqual([row['initiative_v130']['exact'] for row in first], [72, 77, 82, 92, None])
        self.assertEqual(first[-1]['initiative_v130']['upper'], 92)
        self.assertEqual([p['autonomous_extension']['coverage']['reviewed'] for p in profiles], [1, 1, 1, 1, 0])
        for row in first:
            self.assertEqual(row['open_research_v130']['exact'], 22)
            self.assertEqual(row['depth_v130']['exact'], 70)
            self.assertEqual(row['discernment_v130']['exact'], 56.6)
        self.assertEqual(profiles[0]['completion_v130']['exact'], projections[0]['strict_overall']['exact'])
        self.assertNotIn('open_research_autonomy', profiles[0])

    def test_review_rejects_private_contract_substitutions(self):
        mutations = (
            lambda review: review.update(capacity=100),
            lambda review: review.update(source_review_sha256='f' * 64),
            lambda review: review['sealed_finals'].update(R2='f' * 64),
            lambda review: review['taste']['rounds']['R1']['evidence'][0].update(file='R1.files/other.md'),
            lambda review: review['taste']['rounds']['R1']['evidence'][0].update(start=4),
            lambda review: review['taste']['sufficient_choices'].update(verdict=False),
            lambda review: review['taste']['error_deductions'].append(deepcopy(review['taste']['error_deductions'][0])),
            lambda review: review['extension']['assessed_rounds'].pop(),
        )
        for change in mutations:
            with self.subTest(change=change):
                review = new_review(self.digest, seals=SEALS.copy())
                change(review)
                with self.assertRaises(ValueError):
                    self.validate(review)

    def test_adoption_rebuilds_only_from_archived_bytes_and_drops_private_evidence(self):
        with TemporaryDirectory() as temp:
            root = Path(temp).resolve()
            public, replay, reviews = (root / name for name in ('public', 'archived', 'reviews'))
            old_run, state = '/nonexistent/fixture-run', 'control/fixture/state'
            seals, rounds, previous = {}, [], None
            for round_id in ROUNDS:
                final = write(replay, f'{state}/{round_id}.md', FINALS[round_id])
                seal = write(replay, f'{state}/{round_id}.seal.json', adoption.encoded(dict(
                    round=round_id, previous=previous, registration_sha256='f' * 64,
                    delivery='normal-final', raw=dict(final, path=f'{round_id}.md'))))
                previous = seals[round_id] = seal['sha256']
                rounds.append(dict(round=round_id, delivery='normal-final', seal=seal))
            execution = write(replay, 'control/execution.json', adoption.encoded(dict(model_id=MEASURED,
                outcome='normal-finals', state=state, rounds=rounds, registration_sha256='f' * 64,
                context_id='fixture-candidate', native_context_id='fixture-candidate-native')))
            def bound(name, contents):
                ref = write(replay, 'control/' + name, adoption.encoded(contents))
                return dict(ref, path=old_run + '/' + ref['path'])
            effective = bound('effective.json', dict(sealed_finals=seals, registration_sha256='f' * 64,
                axes=dict(capacity=dict(score=70, strict=True)), reviewer_context_id='fixture-old-review'))
            mc = bound('mc.json', dict(sealed_finals=seals, registration_sha256='f' * 64,
                source_review_sha256=effective['sha256'], reviewer_context_id='fixture-old-mc',
                axes=dict(capacity=dict(mc_score=76, rmc_score=70))))
            reviewer, mc_reviewer = (bound(name, {}) for name in ('effective-reviewer.json', 'mc-reviewer.json'))
            preexisting = self.retained
            preexisting['effective_source_sha256'] = value._hash(adoption.encoded(dict(execution=execution['sha256'],
                review=effective['sha256'], reviewer=reviewer['sha256'])))
            preexisting['recheck_sha256'] = 'c' * 64
            preexisting['mc_source_sha256'] = value._hash(adoption.encoded(dict(review=mc['sha256'], reviewer=mc_reviewer['sha256'])))
            old_raw = json.dumps(self.old).encode()
            old = write(public, adoption.PUBLIC_PATH, old_raw)
            retained = json.loads(overlay(old_raw))
            retained['models'][MEASURED] = preexisting
            retained_raw = adoption.encoded(retained)
            write(public, modes.PUBLIC_PATH, retained_raw)
            write(public, modes.POLICY_PATH, modes.POLICY_FILE.read_bytes())
            policy = write(public, value.POLICY_PATH, adoption.encoded(dict(self.policy,
                base_results_sha256=value._hash(retained_raw))))
            chosen = dict(id=MEASURED, execution=execution, original_review=None, original_reviewer_source=None,
                          effective_review=effective, effective_reviewer_source=reviewer, recheck=None,
                          mc_review=mc, mc_reviewer_source=mc_reviewer)
            write(replay, value.SELECTION_PATH, adoption.encoded(dict(schema=modes.SELECTION, plan=None,
                run_root=old_run, review_policy=None, base_adoption=old, models=[chosen])))
            write(reviews, f'{MEASURED}/review.json', adoption.encoded(new_review(policy['sha256'], seals,
                                                                                  effective['sha256'], mc['sha256'])))
            write(reviews, f'{MEASURED}/notes.md', MARKER.encode())
            argv = ['--public-root', str(public), '--replay-root', str(replay), '--reviews', str(reviews), '--out']
            main([*argv, str(root/'proposed.json'), '--apply'])
            main([*argv, str(root/'checked.json'), '--check'])
            installed = (public/value.PUBLIC_PATH).read_bytes()
            self.assertEqual(installed, (root/'checked.json').read_bytes())
            self.assertNotIn(MARKER.encode(), installed)
            self.assertEqual(json.loads(installed)['models'][MEASURED]['taste']['rmc'], 83)
            self.assertEqual((public/modes.PUBLIC_PATH).read_bytes(), retained_raw)
            write(replay, f'{state}/R2.md', b'wrong bytes')
            with self.assertRaises(ValueError):
                value.prepare(replay, reviews, public)
