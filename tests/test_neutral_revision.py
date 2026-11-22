"""Neutral continuation contracts: signed scores, unknowns and source integrity."""
from copy import deepcopy
import json
from pathlib import Path
import tempfile
import unittest

from math_gauge.benchmarks import identity
from math_gauge.neutral_revision import (MODES, CONDITION, RevisionInputs, descriptor,
    select_revision_tasks, load_inputs, load_policy, load_transition, load_public, document)
from math_gauge.scoring import score_neutral_revision_overlay, score_neutral_revision_delta

ROOT = Path(__file__).resolve().parents[1]
POLICY = json.loads((ROOT/'protocol/scoring-policy.json').read_bytes())
ORIGINAL_ADOPTIONS = {
    'sol-6.1-max': dict(path='results/edition-reassessments/v1.2.0/sol-6.1-max/20261109/public.json',
        bytes=5560, sha256='68747743f2b9a71dd293c4ec012315f28b5f5f85777c55351f8188b978b133b7'),
    'sol-6.2-max': dict(path='results/edition-reassessments/v1.2.0/sol-6.2-max/20261118/public.json',
        bytes=5559, sha256='8b84dfd044d8ecb2a1d5bcb0662f74d0c65dc4ef3addfbab259066b77ec21c44'),
    'terra-6.1-max': dict(path='results/edition-reassessments/v1.2.0/terra-6.1-max/20261105/public.json',
        bytes=5596, sha256='cc004a34ca1225cca5bacf677827ae8e568b61698378ea74f19af16dff425de9'),
}


def interval(value):
    return dict(lower=value,upper=value,exact=value)


def fixture_reports(*, category='written-argument', first=(0,0,False), unknown=False):
    reports = {}
    for mode,point in zip(MODES,first):
        tasks = []
        for child in POLICY['subcategories']:
            if child['aggregation'] == 'trajectory':
                continue
            for i in range(child['families']):
                cid = child['id']+'-'+str(i)
                tasks.append(dict(case_id=cid,family_id=cid,subcategory=child['id'],
                    response_sha256='a'*64,review_sha256='b'*64,strict_pass=True,
                    completion=interval(1),submission_assessment=dict(classification='active_final')))
        target = next(t for t in tasks if t['subcategory'] == category)
        target['completion'] = (dict(lower=0,upper=1,exact=None) if unknown else
                                interval(int(point) if mode == 'strict' else point))
        target['strict_pass'] = None if unknown else (point if mode == 'strict' else point == 1)
        metrics,contributions = {},{}
        for child in POLICY['subcategories']:
            value = 100
            metrics[child['id']] = dict(exact=value,confirmed=value,lower=value,upper=value,complete=True)
            contributions[child['id']] = dict(exact=child['weight'],confirmed=child['weight'],
                lower=child['weight'],upper=child['weight'],complete=True)
        for group in POLICY['groups']:
            metrics[group['id']] = dict(exact=100,confirmed=100,lower=100,upper=100,complete=True)
            contributions[group['id']] = dict(exact=group['weight'],confirmed=group['weight'],
                lower=group['weight'],upper=group['weight'],complete=True)
        for key in ('earned','overall'):
            metrics[key] = dict(exact=100,confirmed=100,lower=100,upper=100,complete=True)
        reports[mode] = dict(schema='math-gauge.assessment-score/v1',benchmark_version='1.1.0',
            scoring_method_version='0.9.0',score_mode=mode,attempt_condition=CONDITION,
            model_label='Fixture',tasks=tasks,metrics=metrics,contributions=contributions,
            source_bindings={},whole_task_counts=dict(planned=39,passed=38,failed=1,unknown=0))
    return reports


def inputs(reports, *, scores=None, status='reviewed', cutoff=None):
    selected = select_revision_tasks(reports,model_id='fixture')
    rows = [dict(case_id=r['case_id'],family_id=r['family_id'],subcategory=r['subcategory'],
        continuation=dict(status=status,scores=scores,cutoff_capability=cutoff,
            answer=dict(sha256='c'*64) if status=='reviewed' else None,
            review=dict(sha256='d'*64) if status=='reviewed' else None)) for r in selected]
    data = dict(model_id='fixture',record_id='fixture',rows=rows,
        base_identities={m:identity(reports[m]) for m in MODES},
        base_sha256=dict.fromkeys(MODES,'e'*64),inputs_sha256='f'*64,policy_sha256='1'*64)
    return RevisionInputs(json.dumps(data).encode())


class NeutralScoringTests(unittest.TestCase):
    def test_whole_task_selection_known_loss_unknown_and_lean(self):
        reports = fixture_reports(first=(1,.9,True))
        selected = select_revision_tasks(reports,model_id='fixture')
        self.assertEqual(len(selected),1)
        self.assertEqual(selected[0]['loss_modes'],['partial'])
        # All three modes full are exempt. Unknowns alone are never failures.
        self.assertEqual(select_revision_tasks(fixture_reports(first=(1,1,True))),[])
        self.assertEqual(select_revision_tasks(fixture_reports(unknown=True)),[])
        self.assertEqual(select_revision_tasks(fixture_reports(category='lean-audit')),[])
        self.assertEqual(select_revision_tasks(fixture_reports(category='lean-formalization')),[])

    def test_selected_full_mode_can_decline_and_first_strict_is_retained(self):
        reports = fixture_reports(first=(1,.9,True))
        revision = inputs(reports,scores=dict(capability=.5,partial=.5,strict=0))
        mc = score_neutral_revision_overlay(reports['capability'],POLICY,revision=revision,mode='capability')
        smc = score_neutral_revision_overlay(reports['strict'],POLICY,revision=revision,mode='strict')
        task = next(t for t in mc['tasks'] if 'neutral_revision' in t)
        self.assertEqual(task['completion']['exact'],.9)
        strict = next(t for t in smc['tasks'] if 'neutral_revision' in t)
        self.assertTrue(strict['strict_pass'])
        self.assertTrue(strict['neutral_revision']['first_strict_pass'])
        self.assertFalse(strict['neutral_revision']['revision_strict_pass'])
        self.assertEqual(strict['completion']['exact'],.8)
        self.assertEqual(smc['whole_task_counts'],reports['strict']['whole_task_counts'])

    def test_successful_repair_keeps_historical_loss_and_fixed_weight(self):
        reports = fixture_reports(first=(0,0,False))
        revision = inputs(reports,scores=dict.fromkeys(MODES,1))
        for mode in MODES:
            score = score_neutral_revision_overlay(reports[mode],POLICY,revision=revision,mode=mode)
            task = next(t for t in score['tasks'] if 'neutral_revision' in t)
            self.assertEqual(task['completion']['exact'],.2)
            self.assertAlmostEqual(score['contributions']['written-argument']['confirmed'],25*(11+.2)/12)
            self.assertLess(score['metrics']['earned']['confirmed'],100)
            self.assertEqual(score['metrics']['lean'],reports[mode]['metrics']['lean'])
            self.assertEqual(score['contributions']['lean'],reports[mode]['contributions']['lean'])
        self.assertEqual(reports['strict']['tasks'][0]['completion'],interval(0))

    def test_signed_research_is_blended_without_task_floor(self):
        reports = fixture_reports(category='theorem-extension',first=(0,-2/3,False))
        revision = inputs(reports,scores=dict(capability=0,partial=-1/3,strict=0))
        result = score_neutral_revision_overlay(reports['partial'],POLICY,revision=revision,mode='partial')
        task = next(t for t in result['tasks'] if 'neutral_revision' in t)
        self.assertAlmostEqual(task['completion']['exact'],-.6)
        self.assertAlmostEqual(result['contributions']['theorem-extension']['confirmed'],10*(5-.6)/6)

    def test_unknown_revision_retains_ordinary_penalty_and_fixed_denominator(self):
        reports = fixture_reports(first=(.5,.5,False))
        revision = inputs(reports,status='not_run')
        result = score_neutral_revision_overlay(reports['partial'],POLICY,revision=revision,mode='partial')
        task = next(t for t in result['tasks'] if 'neutral_revision' in t)
        self.assertAlmostEqual(task['completion']['lower'],.36)
        self.assertAlmostEqual(task['completion']['upper'],.6)
        self.assertIsNone(task['completion']['exact'])
        self.assertIsNone(result['metrics']['overall']['exact'])
        self.assertEqual(result['contributions']['written-argument']['coverage']['planned'],12)

    def test_manuscript_unknown_uses_actual_task_floor(self):
        for floor,low in ((None,-.1),(0,0)):
            reports = fixture_reports(category='manuscript-completion')
            if floor is not None:
                for report in reports.values():
                    task = next(t for t in report['tasks'] if t['subcategory']=='manuscript-completion')
                    task['claim_assessment'] = dict(rmc_floor_points=floor)
            revision = inputs(reports,status='not_run')
            result = score_neutral_revision_overlay(reports['partial'],POLICY,revision=revision,mode='partial')
            task = next(t for t in result['tasks'] if 'neutral_revision' in t)
            self.assertEqual(task['completion']['lower'],low)

    def test_failure_mc_waits_for_cutoff_review_rmc_smc_are_zero(self):
        reports = fixture_reports(first=(.5,.5,False))
        pending = inputs(reports,status='delivery_failed')
        mc = score_neutral_revision_overlay(reports['capability'],POLICY,revision=pending,mode='capability')
        self.assertIsNone(next(t for t in mc['tasks'] if 'neutral_revision' in t)['completion']['exact'])
        for mode in ('partial','strict'):
            result = score_neutral_revision_overlay(reports[mode],POLICY,revision=pending,mode=mode)
            self.assertEqual(next(t for t in result['tasks'] if 'neutral_revision' in t)['completion']['exact'],
                             .4 if mode=='partial' else 0)
        reviewed = inputs(reports,status='delivery_failed',cutoff=interval(.5))
        mc = score_neutral_revision_overlay(reports['capability'],POLICY,revision=reviewed,mode='capability')
        self.assertEqual(next(t for t in mc['tasks'] if 'neutral_revision' in t)['completion']['exact'],.5)

    def test_family_variants_average_before_frozen_weight(self):
        reports = fixture_reports()
        for report in reports.values():
            duplicate = deepcopy(report['tasks'][0])
            duplicate.update(case_id='variant',completion=interval(1),strict_pass=True)
            report['tasks'].append(duplicate)
        revision = inputs(reports,scores=dict.fromkeys(MODES,1))
        result = score_neutral_revision_overlay(reports['capability'],POLICY,revision=revision,mode='capability')
        self.assertAlmostEqual(result['contributions']['written-argument']['confirmed'],25*(11+.6)/12)

    def test_mismatched_parent_or_condition_is_rejected(self):
        reports = fixture_reports()
        revision = inputs(reports,scores=dict.fromkeys(MODES,1))
        changed = deepcopy(reports['partial'])
        changed['tasks'][0]['response_sha256'] = '0'*64
        with self.assertRaisesRegex(ValueError,'exact mode/condition/source'):
            score_neutral_revision_overlay(changed,POLICY,revision=revision,mode='partial')

    def test_tiny_first_loss_is_never_rounded_up_to_full(self):
        reports = fixture_reports(first=(.99999999999,.99999999999,False))
        revision = inputs(reports,scores=dict.fromkeys(MODES,1))
        result = score_neutral_revision_overlay(reports['capability'],POLICY,revision=revision,mode='capability')
        task = next(t for t in result['tasks'] if 'neutral_revision' in t)
        self.assertLess(task['completion']['exact'],1)
        self.assertLess(result['metrics']['earned']['confirmed'],100)
        self.assertLess(result['metrics']['overall']['exact'],100)
        changed = deepcopy(reports['partial']);changed['attempt_condition']='single_attempt'
        with self.assertRaises(ValueError):
            score_neutral_revision_overlay(changed,POLICY,revision=revision,mode='partial')


class NeutralRetainedSourcesTests(unittest.TestCase):
    def test_delta_uses_selected_full100_scores_and_keeps_decreases(self):
        transition = load_transition(ROOT)
        current = load_public(ROOT,ORIGINAL_ADOPTIONS['sol-6.1-max'])
        base = {mode:{condition:document(ROOT,ref) for condition,ref in refs.items()}
                for mode,refs in current['base_reports'].items()}
        delta = score_neutral_revision_delta(base,current['_scores'])
        self.assertAlmostEqual(delta['capability'],1.24722222222222)
        self.assertAlmostEqual(delta['partial'],1.267222222222216)
        self.assertAlmostEqual(delta['strict'],2.166666666666657)
        decreased = deepcopy(current['_scores'])
        decreased['partial']['metrics']['earned']['confirmed'] = base['partial'][CONDITION]['metrics']['earned']['confirmed']-.25
        self.assertEqual(score_neutral_revision_delta(base,decreased)['partial'],-.25)
        changed = deepcopy(current['_scores'])
        changed['strict']['neutral_revision']['base_report_sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'exact parent'):
            score_neutral_revision_delta(base,changed)
        changed = deepcopy(current['_scores'])
        changed['strict']['metrics']['earned']['exact']=None
        with self.assertRaisesRegex(ValueError,'Unresolved'):
            score_neutral_revision_delta(base,changed)

    def test_delta_accepts_retained_legacy_label_only_with_exact_parent(self):
        current = load_public(ROOT,ORIGINAL_ADOPTIONS['sol-6.1-max'])
        base = {mode:{condition:document(ROOT,ref) for condition,ref in refs.items()}
                for mode,refs in current['base_reports'].items()}
        expected = score_neutral_revision_delta(base,current['_scores'])
        legacy = deepcopy(base)
        for mode in MODES:
            legacy[mode][CONDITION]['benchmark_version'] = '0.6.0'
        self.assertEqual(score_neutral_revision_delta(legacy,current['_scores']),expected)
        legacy['strict'][CONDITION]['source_bindings']['private_report_sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'exact parent'):
            score_neutral_revision_delta(legacy,current['_scores'])
        legacy = deepcopy(base)
        legacy['strict'][CONDITION]['benchmark_version']='0.5.0'
        with self.assertRaisesRegex(ValueError,'exact parent'):
            score_neutral_revision_delta(legacy,current['_scores'])

    def test_current_public_adoptions_preserve_source_and_privacy(self):
        transition = load_transition(ROOT)
        for mid, ref in ORIGINAL_ADOPTIONS.items():
            self.assertEqual(transition['adoptions'][mid], ref)
        source = transition['_source_edition']
        expected = set(source['selected_result_models']) | set(source.get('current_assessment_admissions', {})) | {'dot-underlying-model-20261108'}
        self.assertFalse(set(transition['adoptions']) & set(transition['pending_models']))
        self.assertEqual(set(transition['adoptions']) | set(transition['pending_models'])
                         | set(transition['withdrawn_models']), expected)
        for mid, ref in transition['adoptions'].items():
            current = load_public(ROOT,ref)
            self.assertEqual(current['revision_counts']['pending'],0)
            for mode in MODES:
                old = document(ROOT,current['base_reports'][mode][CONDITION])
                score = current['_scores'][mode]
                self.assertEqual(score['whole_task_counts'],old['whole_task_counts'])
                self.assertEqual(score['metrics']['lean'],old['metrics']['lean'])
                self.assertNotIn('tasks',score)
                if mid in ORIGINAL_ADOPTIONS:
                    self.assertLess(score['metrics']['earned']['confirmed'],100)
            raw = json.dumps(current['_public_tasks'])
            self.assertNotIn('MG-TXP',raw)
            self.assertNotIn('MG-MCP005',raw)
            self.assertNotIn('/Users/',raw)

    def test_policy_rejects_tampered_candidate_standards(self):
        policy = json.loads((ROOT/'protocol/neutral-revision.json').read_bytes())
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for key in ('standards','invitation','protocol'):
                path = root/policy[key]['path'];path.parent.mkdir(parents=True,exist_ok=True)
                path.write_bytes((ROOT/policy[key]['path']).read_bytes())
            path = root/'protocol/neutral-revision.json'
            path.write_text(json.dumps(policy))
            load_policy(root)
            (root/policy['standards']['path']).write_bytes(b'changed')
            with self.assertRaises(ValueError):
                load_policy(root)


if __name__ == '__main__':
    unittest.main()
