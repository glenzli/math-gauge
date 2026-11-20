"""Continuation traits preserve source ownership, intervals and fixed weights."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from math_gauge.mathematical_profile_revision import (
    REVIEWED_AXES, RevisionProfileInputs, load_policy, validate_policy,
    validate_task_review, project_public, validate_public, _task_sources,
)
from math_gauge.scoring import score_mathematical_profile, score_mathematical_profile_revisions
from math_gauge.scoring import score_mathematical_profile_baseline_corrections
from math_gauge.mathematical_profile_corrections import BaselineCorrectionInputs
from test_mathematical_profile import arithmetic_fixture, strict_report

ROOT = Path(__file__).resolve().parents[1]


def fixture():
    baseline, _, _ = arithmetic_fixture()
    original = score_mathematical_profile(baseline)
    selected = next(row for row in baseline.contracts['tasks']
                    if row['subcategory'] == 'written-argument' and row['public'])
    inputs = object.__new__(RevisionProfileInputs)
    inputs.base_score = deepcopy(original)
    inputs.base_profile = dict(metrics=deepcopy(original['metrics']))
    inputs.contracts = deepcopy(baseline.contracts)
    inputs.policy = load_policy(ROOT)[0]
    inputs.strict_report = strict_report(94.5)
    inputs.review = dict(model_id='synthetic', tasks=[dict(id=selected['id'],
        axes={axis:dict(grade=4) for axis in REVIEWED_AXES})])
    return inputs, selected['id']


class RevisionProfileArithmeticTests(unittest.TestCase):
    def test_only_selected_slots_blend_and_signed_decreases_are_retained(self):
        inputs, slot = fixture()
        for judgment in inputs.review['tasks'][0]['axes'].values():
            judgment['grade'] = 0
        result = score_mathematical_profile_revisions(inputs)
        for axis in REVIEWED_AXES:
            self.assertAlmostEqual(result['metrics'][axis]['exact'], 100 - 20/35)
        rows = {row['id']:row for row in result['tasks']}
        self.assertEqual(rows[slot]['axes']['proof']['exact'], 3.2)
        for row in inputs.base_score['tasks']:
            if row['id'] != slot:
                self.assertEqual(rows[row['id']]['axes'], row['axes'])
                self.assertFalse(rows[row['id']]['continuation_selected'])
        self.assertEqual(result['revision_coverage'],
                         dict(selected_tasks=1, reviewed_tasks=1, unknown_tasks=0))

    def test_initiative_is_exactly_the_original_and_completion_is_official_12_smc(self):
        inputs, _ = fixture()
        inputs.base_profile['metrics']['initiative']['exact'] = 31.2
        inputs.base_profile['metrics']['initiative']['confirmed'] = 31.2
        for row in inputs.base_score['tasks']:
            row['axes']['initiative'] = dict(lower=0, upper=0, exact=0)
        result = score_mathematical_profile_revisions(inputs)
        self.assertEqual(result['metrics']['initiative'], inputs.base_profile['metrics']['initiative'])
        self.assertEqual(result['metrics']['completion']['exact'], 94.5)
        self.assertNotEqual(result['metrics']['completion'], inputs.base_profile['metrics']['completion'])

    def test_unknown_revision_retains_twenty_percent_weight_without_inheritance(self):
        inputs, _ = fixture()
        inputs.review['tasks'][0]['axes']['proof']['grade'] = None
        result = score_mathematical_profile_revisions(inputs)
        metric = result['metrics']['proof']
        self.assertIsNone(metric['exact'])
        self.assertAlmostEqual(metric['lower'], 100-20/35)
        self.assertEqual(metric['upper'], 100)
        self.assertAlmostEqual(metric['unknown_weight'], 20/35)
        self.assertEqual(metric['coverage'], dict(unit='mathematical_family', planned=35, reviewed=34))
        self.assertEqual(result['revision_coverage'],
                         dict(selected_tasks=1, reviewed_tasks=0, unknown_tasks=1))
        self.assertEqual(result['metrics']['fidelity']['exact'], 100)

    def test_exempt_tasks_keep_actual_old_grades_instead_of_inferred_full_credit(self):
        inputs, slot = fixture()
        other = next(row for row in inputs.base_score['tasks'] if row['id'] != slot
                     and row['id'].startswith('MG-') and row['id'].endswith(':A1'))
        other['axes']['depth'] = dict(lower=2, upper=2, exact=2)
        result = score_mathematical_profile_revisions(inputs)
        output = next(row for row in result['tasks'] if row['id'] == other['id'])
        self.assertEqual(output['axes']['depth']['exact'], 2)
        self.assertLess(result['metrics']['depth']['exact'], 100)

    def test_scorer_requires_validated_owner_type_and_policy_keeps_source_contract(self):
        with self.assertRaises(ValueError):
            score_mathematical_profile_revisions({})
        policy, _ = load_policy(ROOT)
        for key, value in [('initiative', 'blend'), ('revision_weight', '1/2'),
                           ('planned_families', 9), ('main_scores_modified', True)]:
            changed = deepcopy(policy); changed[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                validate_policy(changed)

    def test_source_correction_is_shared_by_both_stages_and_not_a_revision_decline(self):
        inputs, slot = fixture()
        original = deepcopy(inputs.base_score)
        correction = object.__new__(BaselineCorrectionInputs)
        correction.rows = [dict(model_id='synthetic',id=slot,
            axes={axis:dict(**{'from':4,'to':2}) for axis in ('proof','fidelity','discernment')})]
        correction.contracts = inputs.contracts;correction.sha256 = 'a'*64
        baseline = score_mathematical_profile_baseline_corrections(original,correction,model_id='synthetic')
        self.assertEqual(original,inputs.base_score,'the archived original is never mutated')
        for axis in ('proof','fidelity','discernment'):
            self.assertAlmostEqual(baseline['metrics'][axis]['exact'],100-50/35)
            inputs.review['tasks'][0]['axes'][axis]['grade']=2
        for axis in ('depth','closure','initiative','completion'):
            self.assertEqual(baseline['metrics'][axis],original['metrics'][axis])
        inputs.base_score=baseline;inputs.base_profile['metrics']=deepcopy(baseline['metrics'])
        revised=score_mathematical_profile_revisions(inputs)
        for axis in ('proof','fidelity','discernment'):
            self.assertEqual(revised['metrics'][axis],baseline['metrics'][axis])
        correction.rows[0]['axes']['proof']['from']=3
        with self.assertRaises(ValueError):
            score_mathematical_profile_baseline_corrections(original,correction,model_id='synthetic')


class RevisionProfileEvidenceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.raw = b'Exact delivered argument and its boundary.'
        (self.root/'answer.md').write_bytes(self.raw)
        self.source = dict(repository='private', path='answer.md', bytes=len(self.raw),
                           sha256=hashlib.sha256(self.raw).hexdigest())
        self.material = dict(id='case:A1', revision_ref=dict(continuation=dict(status='reviewed')),
                             sources=dict(answer=self.source))
        self.review = dict(id='case:A1', axes={axis:dict(grade=4, assessment_status='reviewed',
            reason='The required core and its stated scope are established.',
            evidence=[dict(source_id='answer', pointer='', quote='Exact delivered argument')])
            for axis in REVIEWED_AXES})
        self.review['axes']['proof']['core_status'] = 'established'
        self.review['axes']['fidelity']['core_scope_failure'] = False

    def validate(self):
        return validate_task_review(self.review, self.material, roots=dict(private=self.root))

    def test_judgments_bind_original_quotes_and_reject_another_task_or_alias(self):
        self.validate()
        for change in ('quote', 'source', 'task', 'bytes'):
            with self.subTest(change=change):
                review, material = deepcopy(self.review), deepcopy(self.material)
                if change == 'quote': review['axes']['proof']['evidence'][0]['quote'] = 'Invented mathematics'
                if change == 'source': review['axes']['proof']['evidence'][0]['source_id'] = 'another-model-answer'
                if change == 'task': review['id'] = 'foreign:A1'
                if change == 'bytes': material['sources']['answer']['sha256'] = '0'*64
                with self.assertRaises(ValueError):
                    validate_task_review(review, material, roots=dict(private=self.root))

    def test_proof_and_fidelity_gates_apply_independently_to_continuations(self):
        self.review['axes']['proof']['core_status'] = 'unresolved_core'
        with self.assertRaises(ValueError): self.validate()
        self.review['axes']['proof']['grade'] = 2
        self.validate()
        self.review['axes']['fidelity']['core_scope_failure'] = True
        with self.assertRaises(ValueError): self.validate()
        self.review['axes']['fidelity']['grade'] = 2
        self.validate()

    def test_unknowns_need_a_missing_evidence_state_and_never_gain_initiative(self):
        judgment = self.review['axes']['proof']
        judgment.update(grade=None, assessment_status='source_unresolved',
                        core_status='source_unresolved', missing_evidence='Missing mathematical source.')
        self.validate()
        del judgment['missing_evidence']
        with self.assertRaises(ValueError): self.validate()
        self.review['axes']['initiative'] = deepcopy(self.review['axes']['depth'])
        with self.assertRaises(ValueError): self.validate()

    def test_task_aliases_only_reference_adopted_delivery_and_actual_attachments(self):
        desc = dict(path='answer.md', bytes=len(self.raw), sha256=self.source['sha256'])
        row = dict(original_task=dict(scope='public', **desc), continuation=dict(
            answer=desc, input=desc, review=desc, attachments=[desc]))
        result = _task_sources(row)
        self.assertEqual(set(result), {'task','input','answer','review','attachment:0'})
        self.assertEqual(result['task']['repository'], 'public')
        self.assertEqual(result['attachment:0']['repository'], 'private')


class RevisionProfilePublicBoundaryTests(unittest.TestCase):
    def test_projection_contains_no_private_case_ids_quotes_or_paths(self):
        inputs, _ = fixture()
        score = score_mathematical_profile_revisions(inputs)
        score['tasks'][0]['secret'] = 'PRIVATE_SENTINEL'
        public = project_public(score, policy_sha256='a'*64,
            private_review_sha256='b'*64, private_materials_sha256='c'*64,
            source_base_profile=dict(path='results/mathematical-profiles/v0.4.0/synthetic/profile.json',
                                     bytes=1, sha256='d'*64),
            source_adoption=dict(path='results/edition-reassessments/v1.2.0/synthetic/public.json',
                                 bytes=1, sha256='e'*64))
        raw = json.dumps(public)
        self.assertNotIn('PRIVATE_SENTINEL', raw)
        self.assertNotIn('case_id', raw)
        self.assertNotIn('tasks', public)
        for key in ('tasks', 'private_source_path'):
            changed = deepcopy(public); changed[key] = 'PRIVATE_SENTINEL'
            with self.assertRaises(ValueError): validate_public(changed, policy_sha256='a'*64)


if __name__ == '__main__':
    unittest.main()
