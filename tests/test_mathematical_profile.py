"""Independent traits: fixed mathematical samples, exact sources and privacy."""
from contextlib import ExitStack
from copy import deepcopy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from math_gauge.evidence_retention import read_bytes
from math_gauge.mathematical_profile import (
    AXES, VERSION, PREVIOUS_VERSION, LEGACY_VERSION, WHOLE_COMPLETION, ProfileInputs, load_policy, project_public, source_bytes,
    validate_contracts, validate_public, validate_review, _validate_prior_profile,
    _validate_assessment_status, _validate_fidelity_core,
)
from math_gauge.scoring import score_mathematical_profile

ROOT = Path(__file__).resolve().parents[1]


def arithmetic_fixture(version=LEGACY_VERSION):
    """Public contracts plus synthetic private slots; no private checkout needed.

    Bypass evidence construction only for these pure arithmetic examples. The
    source boundary is independently exercised below with real temporary bytes.
    """
    policy, digest = load_policy(ROOT, version=version)
    tasks = deepcopy(policy['public_task_contracts'])
    for category, count in [('written-argument',4),('background-check',2),
                            ('theorem-extension',4),('manuscript-completion',4)]:
        for index in range(count):
            ident = category+'-synthetic-'+str(index)
            weights = dict(fidelity='1/35', completion='1/35')
            if category in {'written-argument','theorem-extension'}:
                weights['proof'] = '1/20'
            if category == 'background-check':
                weights['discernment'] = '1/11'
            if category == 'theorem-extension':
                weights.update(initiative='1/6', depth='1/12', closure='1/12')
            if category == 'manuscript-completion':
                weights.update(depth='1/10', closure='1/10')
            if version != LEGACY_VERSION:
                weights = dict.fromkeys(AXES, '1/35')
            tasks.append(dict(id=ident+':A1',case_id=ident,family_id=ident,
                subcategory=category,kind='initial',public=False,axis_weights=weights,
                goals=[dict(id='whole-goal',weight=100)]))
    inputs = object.__new__(ProfileInputs)
    inputs.policy = policy
    inputs.contracts = dict(schema='math-gauge.mathematical-profile-contracts/v1', version=version,
        benchmark_version='1.1.0',condition='nonlogical_retry_3',
        tasks=tasks,planned_families=policy['planned_families'],
        **({'completion_rule':WHOLE_COMPLETION} if version == VERSION else {}))
    inputs.review = dict(model_id='synthetic', version=version, tasks=[dict(id=c['id'],
        axes={a:dict(grade=4) for a in c['axis_weights']
              if a != 'completion' and (a != 'closure' or version != LEGACY_VERSION)},
        goals=[dict(id=g['id'],passed=True) for g in c['goals']],
        research=dict(complete=True)) for c in tasks])
    return inputs, policy, digest


class ProfileArithmeticTests(unittest.TestCase):
    def setUp(self):
        self.inputs,self.policy,self.digest = arithmetic_fixture()
        self.rows = {r['id']:r for r in self.inputs.review['tasks']}

    def score(self):
        return score_mathematical_profile(self.inputs)

    def test_each_family_keeps_its_fixed_mass(self):
        for axis in AXES:
            weights = {}
            for task in self.inputs.contracts['tasks']:
                if axis in task['axis_weights']:
                    family = task['family_id']
                    weights[family] = weights.get(family,Fraction())+Fraction(task['axis_weights'][axis])
            self.assertEqual(sum(weights.values()),1)
            if axis not in {'depth','closure'}:
                self.assertEqual(set(weights.values()),{Fraction(1,len(weights))})
        for metric in self.score()['metrics'].values():
            self.assertEqual((metric['exact'],metric['lower'],metric['upper']),(100,100,100))
            self.assertEqual(metric['reviewed_families'],metric['planned_families'])

    def test_c003_initial_and_whole_trajectory_each_occupy_half_a_family(self):
        for g in self.rows['MG-C003:A1']['goals']:
            g['passed'] = False
        initial = self.score()['metrics']['completion']
        self.assertAlmostEqual(initial['exact'],100-100/70)
        for g in self.rows['MG-C003:A1']['goals']:
            g['passed'] = True
        for suffix in ('R1','R2','R3'):
            for g in self.rows['MG-C003:'+suffix]['goals']:
                g['passed'] = False
        self.assertEqual(initial['exact'],self.score()['metrics']['completion']['exact'])

    def test_one_unknown_round_does_not_shrink_denominator(self):
        self.rows['MG-C003:R2']['axes']['fidelity']['grade'] = None
        for g in self.rows['MG-C003:R2']['goals']:
            g['passed'] = None
        for axis in ('fidelity','completion'):
            metric = self.score()['metrics'][axis]
            self.assertIsNone(metric['exact'])
            self.assertAlmostEqual(metric['lower'],100-100/210)
            self.assertEqual(metric['upper'],100)
            self.assertEqual(metric['reviewed_families'],34)

    def test_research_groups_each_have_half_not_their_task_count_ratio(self):
        for contract in self.inputs.contracts['tasks']:
            if contract['subcategory'] == 'manuscript-completion':
                row = self.rows[contract['id']]
                row['axes']['depth']['grade'] = 0
                for g in row['goals']:
                    g['passed'] = False
        for axis in ('depth','closure'):
            result = self.score()
            self.assertEqual(result['metrics'][axis]['exact'],50)
            self.assertEqual(result['groups'][axis]['theorem-extension']['exact'],100)
            self.assertEqual(result['groups'][axis]['manuscript-completion']['exact'],0)

    def test_unknown_behavior_and_known_zero_are_distinct(self):
        for row in self.rows.values():
            for value in row['axes'].values():
                value['grade'] = None
        for axis in ('proof','fidelity','discernment','initiative','depth'):
            m = self.score()['metrics'][axis]
            self.assertIsNone(m['exact'])
            self.assertEqual((m['lower'],m['upper'],m['reviewed_families']),(0,100,0))
        for row in self.rows.values():
            for value in row['axes'].values():
                value['grade'] = 0
            for g in row['goals']:
                g['passed'] = False
            row['research']['complete'] = False
        for m in self.score()['metrics'].values():
            self.assertEqual(m['exact'],0)
            self.assertEqual(m['reviewed_families'],m['planned_families'])

    def test_only_a_complete_goal_counts_and_partial_goals_stay_weighted(self):
        row = self.rows['MG-PS001:A1']
        row['goals'][0]['passed'] = False
        # Independent valid work does not backfill this failed complete goal.
        self.assertEqual(row['axes']['proof']['grade'],4)
        contract = next(t for t in self.inputs.contracts['tasks'] if t['id']==row['id'])
        lost = Fraction(str(contract['goals'][0]['weight']))/sum(Fraction(str(g['weight'])) for g in contract['goals'])
        self.assertAlmostEqual(self.score()['metrics']['completion']['exact'],100-float(lost)*100/35)


class ProfileV2ArithmeticTests(unittest.TestCase):
    def setUp(self):
        self.inputs,self.policy,self.digest = arithmetic_fixture(PREVIOUS_VERSION)
        self.rows = {row['id']:row for row in self.inputs.review['tasks']}

    def test_all_axes_use_the_same_fixed_35_family_contract(self):
        validate_contracts(self.inputs.contracts,self.policy)
        score = score_mathematical_profile(self.inputs)
        self.assertEqual(score['version'], PREVIOUS_VERSION)
        self.assertEqual(score['groups'], {})
        for axis in AXES:
            weights = {}
            for row in self.inputs.contracts['tasks']:
                self.assertEqual(set(row['axis_weights']),set(AXES))
                family = row['family_id']
                weights[family] = weights.get(family,Fraction())+Fraction(row['axis_weights'][axis])
            self.assertEqual(len(weights),35)
            self.assertEqual(set(weights.values()),{Fraction(1,35)})
            self.assertEqual(score['metrics'][axis]['exact'],100)

    def test_completion_and_result_closure_are_independent(self):
        for row in self.inputs.review['tasks']:
            for goal in row['goals']:
                goal['passed'] = False
            row['axes']['closure']['grade'] = 2
            row['research']['complete'] = True
        score = score_mathematical_profile(self.inputs)
        self.assertEqual(score['metrics']['completion']['exact'],0)
        self.assertEqual(score['metrics']['closure']['exact'],50)

    def test_every_kind_of_mathematics_contributes_on_every_axis(self):
        for row in self.inputs.review['tasks']:
            for judgment in row['axes'].values():
                judgment['grade'] = 0
            for goal in row['goals']:
                goal['passed'] = False
        for category in {row['subcategory'] for row in self.inputs.contracts['tasks']}:
            inputs = deepcopy(self.inputs)
            selected = next(row for row in inputs.contracts['tasks'] if row['subcategory'] == category)
            reviewed = next(row for row in inputs.review['tasks'] if row['id'] == selected['id'])
            for judgment in reviewed['axes'].values():
                judgment['grade'] = 4
            for goal in reviewed['goals']:
                goal['passed'] = True
            expected = float(Fraction(selected['axis_weights']['proof'])*100)
            for metric in score_mathematical_profile(inputs)['metrics'].values():
                self.assertAlmostEqual(metric['exact'],expected)

    def test_c003_unknown_stays_within_its_fixed_one_sixth_of_a_family(self):
        row = self.rows['MG-C003:R2']
        for judgment in row['axes'].values():
            judgment['grade'] = None
        for goal in row['goals']:
            goal['passed'] = None
        for metric in score_mathematical_profile(self.inputs)['metrics'].values():
            self.assertIsNone(metric['exact'])
            self.assertAlmostEqual(metric['unknown_weight'],100/210)
            self.assertAlmostEqual(metric['lower'],100-100/210)
            self.assertEqual(metric['upper'],100)
            self.assertEqual(metric['reviewed_families'],34)

    def test_contract_rejects_a_denominator_changed_for_one_axis(self):
        contract = next(row for row in self.inputs.contracts['tasks'] if row['kind'] == 'initial')
        contract['axis_weights']['initiative'] = '1/6'
        with self.assertRaises(ValueError):
            validate_contracts(self.inputs.contracts,self.policy)


class ProfileWholeTaskTests(unittest.TestCase):
    def setUp(self):
        self.inputs, self.policy, self.digest = arithmetic_fixture(VERSION)
        self.rows = {row['id']:row for row in self.inputs.review['tasks']}

    def score(self):
        return score_mathematical_profile(self.inputs)

    def test_one_failed_required_goal_rejects_the_whole_task_not_a_text_fraction(self):
        row = self.rows['MG-PS001:A1']
        self.assertGreater(len(row['goals']), 1)
        row['goals'][-1]['passed'] = False
        score = self.score()
        self.assertAlmostEqual(score['metrics']['completion']['exact'], 100-100/35)
        self.assertEqual(score['metrics']['proof']['exact'], 100)
        self.assertEqual(score['metrics']['closure']['exact'], 100)
        self.assertTrue(any(g['passed'] is True for g in row['goals']))

    def test_a_single_failed_diagnosis_rejects_the_whole_prescribed_trajectory(self):
        self.rows['MG-C003:R1']['goals'][-1]['passed'] = False
        score = self.score()
        self.assertAlmostEqual(score['metrics']['completion']['exact'], 100-100/70)
        for row in score['tasks']:
            if row['id'].startswith('MG-C003:R'):
                self.assertEqual(row['axes']['completion']['exact'], 0)
        self.assertEqual(score['metrics']['fidelity']['exact'], 100)
        self.assertTrue(all(g['passed'] is True for g in self.rows['MG-C003:R3']['goals']))

    def test_unknown_round_retains_the_entire_trajectory_interval(self):
        self.rows['MG-C003:R2']['goals'][0]['passed'] = None
        metric = self.score()['metrics']['completion']
        self.assertIsNone(metric['exact'])
        self.assertAlmostEqual(metric['unknown_weight'], 100/70)
        self.assertAlmostEqual(metric['lower'], 100-100/70)
        self.assertEqual(metric['upper'], 100)

    def test_known_failure_settles_a_conjunction_even_when_another_goal_is_unknown(self):
        self.rows['MG-C003:R1']['goals'][0]['passed'] = None
        self.rows['MG-C003:R3']['goals'][0]['passed'] = False
        metric = self.score()['metrics']['completion']
        self.assertAlmostEqual(metric['exact'], 100-100/70)
        self.assertEqual(metric['unknown_weight'], 0)

    def test_unknown_whole_task_has_no_confirmed_partial_completion(self):
        self.rows['MG-PS001:A1']['goals'][-1]['passed'] = None
        metric = self.score()['metrics']['completion']
        self.assertIsNone(metric['exact'])
        self.assertAlmostEqual(metric['lower'], 100-100/35)
        self.assertEqual(metric['upper'], 100)

    def test_tx_visible_baseline_does_not_inherit_an_unrequested_r3_gate(self):
        for contract in self.inputs.contracts['tasks']:
            if contract['subcategory'] == 'theorem-extension':
                self.rows[contract['id']]['research']['complete'] = False
                self.rows[contract['id']]['axes']['initiative']['grade'] = 0
        self.assertEqual(self.score()['metrics']['completion']['exact'], 100)

    def test_the_new_contract_must_freeze_its_acceptance_rule(self):
        validate_contracts(self.inputs.contracts, self.policy)
        del self.inputs.contracts['completion_rule']
        with self.assertRaises(ValueError):
            validate_contracts(self.inputs.contracts, self.policy)

    def test_core_scope_drift_cannot_keep_a_high_fidelity_grade(self):
        for grade in (3, 4):
            with self.assertRaises(ValueError):
                _validate_fidelity_core(dict(grade=grade, core_scope_failure=True))
        _validate_fidelity_core(dict(grade=2, core_scope_failure=True))
        _validate_fidelity_core(dict(grade=4, core_scope_failure=False))
        _validate_fidelity_core(dict(grade=None, core_scope_failure=None))

    def test_missing_core_scope_judgment_cannot_be_presented_as_reviewed(self):
        with self.assertRaises(ValueError):
            _validate_fidelity_core(dict(grade=4))


class PublicBoundaryTests(unittest.TestCase):
    def setUp(self):
        inputs,self.policy,self.digest = arithmetic_fixture()
        descriptor = dict(path='results/selected/record.json',sha256='0'*64)
        self.public = project_public(score_mathematical_profile(inputs),policy=self.policy,
            policy_sha256=self.digest,private_review_sha256='1'*64,private_materials_sha256='2'*64,
            source_record=descriptor,source_calibration=descriptor)

    def test_private_details_cannot_be_nested_in_public_group_scores(self):
        self.public['groups']['depth']['theorem-extension']['exact'] = {'private':'PRIVATE_SENTINEL'}
        with self.assertRaises(ValueError):
            validate_public(self.public,self.policy,policy_sha256=self.digest)

    def test_public_source_descriptors_are_also_allowlisted(self):
        self.public['source_record']['private_details'] = {'case':'PRIVATE_SENTINEL'}
        with self.assertRaises(ValueError):
            validate_public(self.public,self.policy,policy_sha256=self.digest)

    def test_projection_ignores_private_reviewer_objects(self):
        inputs,_,_ = arithmetic_fixture()
        score = score_mathematical_profile(inputs)
        score['tasks'][0]['private_details'] = 'PRIVATE_SENTINEL'
        descriptor = dict(path='results/selected/record.json',sha256='0'*64)
        public = project_public(score,policy=self.policy,policy_sha256=self.digest,
            private_review_sha256='1'*64,private_materials_sha256='2'*64,
            source_record=descriptor,source_calibration=descriptor)
        # Retained profile validation compares exact JSON bytes, including this
        # original field order; adding an initial route must not rewrite it.
        keys=list(public)
        self.assertEqual(keys[keys.index('source_record')+1], 'source_calibration')
        self.assertNotIn('PRIVATE_SENTINEL',json.dumps(public))
        self.assertNotIn('tasks',public)

    def test_v0_2_public_projection_has_no_private_or_separately_weighted_groups(self):
        inputs,policy,digest = arithmetic_fixture(PREVIOUS_VERSION)
        score = score_mathematical_profile(inputs)
        score['tasks'][0]['private_details'] = 'PRIVATE_SENTINEL'
        descriptor = dict(path='results/selected/record.json',sha256='0'*64)
        public = project_public(score,policy=policy,policy_sha256=digest,
            private_review_sha256='1'*64,private_materials_sha256='2'*64,
            source_record=descriptor,source_calibration=descriptor)
        self.assertEqual(public['groups'],{})
        self.assertNotIn('PRIVATE_SENTINEL',json.dumps(public))
        public['groups']['private'] = {'case_id':'PRIVATE_SENTINEL'}
        with self.assertRaises(ValueError):validate_public(public,policy,policy_sha256=digest)


class SourceBoundaryTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        base = Path(self.tmp.name)
        self.pub,self.prv = base/'public',base/'private'
        self.pub.mkdir();self.prv.mkdir()
        self.roots = dict(public=self.pub,private=self.prv)
        self.policy_sha,self.contract_sha = 'a'*64,'b'*64
        self.policy = dict(private_contract_sha256=self.contract_sha)

        def put(root,path,value):
            raw = (json.dumps(value,ensure_ascii=False)+'\n').encode() if not isinstance(value,bytes) else value
            target = root/path;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(raw)
            return dict(repository='public' if root==self.pub else 'private',path=path,bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest())
        self.put = put
        self.ids = ('case-A:A1','case-B:A1')
        answers = [put(self.prv,f'answers/{i}.md',f'original answer {i}'.encode()) for i in range(2)]
        states = [dict(case_id=slot.split(':')[0],slot_id=slot,response_sha256=answers[i]['sha256'],
                       submission_assessment=dict(classification='active_final')) for i,slot in enumerate(self.ids)]
        content = dict(tasks=[dict(id=slot,units=[dict(reason='actual evidence '+slot)]) for slot in self.ids])
        goals = dict(tasks=[dict(id=slot,goals=[dict(reason='complete goal '+slot)]) for slot in self.ids])
        cr,gr = put(self.prv,'reviews/content.json',content),put(self.prv,'reviews/goals.json',goals)
        report = put(self.prv,'reports/selected.json',dict(tasks=states,alignment_selfcheck=dict(rounds=[])))
        ci = put(self.prv,'calibration/inputs.json',dict(model_id='fixture',conditions={'nonlogical_retry_3':[]}))
        manifest = put(self.prv,'calibration/manifest.json',dict(inputs=ci,scores={'partial':{'nonlogical_retry_3':report}}))
        put(self.prv,'results/edition-reassessments/v1.1.0/transition.json',dict(calibrations={'fixture':manifest}))
        pub_cal = put(self.pub,'calibration/public.json',dict(private_manifest_sha256=manifest['sha256'],private_inputs_sha256=ci['sha256']))
        record = put(self.pub,'records/selected.json',dict(model_id='fixture'))
        sources = dict(public_source_record=record,calibration=pub_cal,calibration_inputs=ci,
                       selected_report=report,content_review=cr,goal_review=gr)
        sources.update({'answer:'+slot:answers[i] for i,slot in enumerate(self.ids)})
        self.materials = dict(model_id='fixture',condition='nonlogical_retry_3',policy_sha256=self.policy_sha,
            private_contract_sha256=self.contract_sha,sources=sources,tasks=[dict(id=slot,content_index=i,goal_index=i,
                response_sha256=answers[i]['sha256'],raw_answer=answers[i],selected_state=states[i]) for i,slot in enumerate(self.ids)])
        self.contracts = dict(tasks=[dict(id=slot,case_id=slot.split(':')[0],kind='initial',
            subcategory='written-argument',axis_weights={'fidelity':'1/2','completion':'1/2'},goals=[dict(id='whole',weight=100)]) for slot in self.ids])
        self.review = dict(schema='math-gauge.mathematical-profile-review/v1',version='0.1.0',benchmark_version='1.1.0',
            condition='nonlogical_retry_3',model_id='fixture',policy_sha256=self.policy_sha,private_contract_sha256=self.contract_sha,
            reviewer_id='synthetic-reviewer',reviewer_kind='ai',human_review='pending',new_candidate_calls=0,formal_comparison_eligible=False,tasks=[])
        for i,slot in enumerate(self.ids):
            ev = dict(source_id='content_review',pointer=f'/tasks/{i}/units/0/reason',quote='actual evidence '+slot)
            self.review['tasks'].append(dict(id=slot,axes={'fidelity':dict(grade=4,reason='Same original objects and assumptions.',evidence=[ev])},
                goals=[dict(id='whole',passed=True,reason='The complete goal is delivered.',evidence=[dict(source_id='goal_review',pointer=f'/tasks/{i}/goals/0/reason',quote='complete goal '+slot)])],research=None))
        stack = self.enterContext(ExitStack())
        stack.enter_context(patch('math_gauge.current_assessment_admissions.selections',return_value={}))
        stack.enter_context(patch('math_gauge.current_results.selected_current_record_paths',return_value={'fixture':record['path']}))
        stack.enter_context(patch('math_gauge.editions.load_assessment_transition',return_value={'calibrations':{'fixture':pub_cal}}))
        stack.enter_context(patch('math_gauge.current_results.load_source_assessment',return_value=(None,None,
            dict(private_review_sha256=cr['sha256'],private_goal_review_sha256=gr['sha256']),None,None)))

    def test_initial_assessment_uses_its_own_private_binding_not_old_calibration(self):
        sources=self.materials['sources']
        sources['initial_assessment']=sources.pop('calibration')
        sources['initial_assessment_inputs']=sources.pop('calibration_inputs')
        private_manifest=json.loads((self.prv/'calibration/manifest.json').read_bytes())
        ref=self.put(self.prv,'initial/manifest.json',private_manifest)
        sources['private_initial_assessment']=ref
        initial_inputs=json.loads((self.prv/sources['initial_assessment_inputs']['path']).read_bytes())
        public=json.loads((self.pub/sources['initial_assessment']['path']).read_bytes())
        public['private_manifest_sha256']=ref['sha256']
        sources['initial_assessment']=self.put(self.pub,'initial/public.json',public)
        with patch('math_gauge.current_assessment_admissions.selections',return_value={'fixture':sources['initial_assessment']}), \
             patch('math_gauge.current_assessment_admissions.validate_private',return_value=(private_manifest,initial_inputs)) as checked:
            self.validate()
        checked.assert_called_once()

    def validate(self):
        return validate_review(self.review,self.policy,self.contracts,self.materials,roots=self.roots,policy_sha256=self.policy_sha)

    def test_exact_original_source_chain_is_accepted(self):
        self.validate()

    def test_reject_report_of_another_model_even_under_valid_top_record(self):
        self.materials['sources']['selected_report'] = self.put(self.prv,'reports/other.json',dict(model_label='other'))
        with self.assertRaises(ValueError):self.validate()

    def test_reject_another_task_report_pointer(self):
        self.review['tasks'][0]['axes']['fidelity']['evidence'] = [dict(source_id='selected_report',pointer='/tasks/1/case_id',quote='case-B')]
        with self.assertRaises(ValueError):self.validate()

    def test_reject_mutated_convenience_index(self):
        self.materials['tasks'][0]['content_index'] = 1
        with self.assertRaises(ValueError):self.validate()

    def test_reject_other_answer_behind_same_slot_alias(self):
        self.materials['sources']['answer:'+self.ids[0]] = self.materials['sources']['answer:'+self.ids[1]]
        with self.assertRaises(ValueError):self.validate()

    def test_damaged_hot_source_never_becomes_valid_evidence(self):
        ref = self.materials['sources']['content_review']
        (self.prv/ref['path']).write_text('{}')
        with self.assertRaises(ValueError):self.validate()

    def test_wrong_exact_quote_is_rejected(self):
        self.review['tasks'][0]['axes']['fidelity']['evidence'][0]['quote'] = 'invented evidence'
        with self.assertRaises(ValueError):self.validate()

    def test_verified_nonfinal_work_cannot_complete_a_goal(self):
        self.materials['tasks'][0]['selected_state']['submission_assessment']['classification'] = 'forced_content'
        # Changing the convenience state alone is rejected before goal credit.
        with self.assertRaises(ValueError):self.validate()


class AssessmentStatusTests(unittest.TestCase):
    def check(self, classification, status, value, *, goal=False, **fields):
        material = dict(selected_state=dict(submission_assessment=dict(classification=classification)))
        _validate_assessment_status(dict(assessment_status=status,**fields),value,material,goal=goal)

    def test_settled_blank_is_known_zero_for_traits_and_goals(self):
        self.check('blank','operational_zero',0)
        self.check('blank','operational_zero',False,goal=True)
        for status,value in [('reviewed',0),('source_unresolved',None),('not_run',None)]:
            with self.assertRaises(ValueError):
                self.check('blank',status,value,missing_evidence='No mathematical delivery.')

    def test_unrun_is_unknown_and_cannot_be_zero_filled(self):
        self.check('not_run','not_run',None)
        with self.assertRaises(ValueError):self.check('not_run','reviewed',0)
        with self.assertRaises(ValueError):self.check('active_final','not_run',None)

    def test_forced_content_can_retain_independently_reviewed_original_work(self):
        self.check('forced_content','reviewed',3)
        self.check('forced_content','operational_zero',0)

    def test_missing_source_requires_a_typed_specific_unknown(self):
        self.check('active_final','source_unresolved',None,missing_evidence='Original sealed engineering unavailable.')
        with self.assertRaises(ValueError):self.check('active_final','source_unresolved',None)
        with self.assertRaises(ValueError):self.check('active_final','reviewed',None)
        with self.assertRaises(ValueError):
            self.check('active_final','source_unresolved',0,missing_evidence='Original sealed engineering unavailable.')


class InitialProfileSourceBoundaryTests(SourceBoundaryTests):
    """A first profile retains the ordinary selected-record evidence checks."""
    def setUp(self):
        super().setUp()
        self.policy['version'] = PREVIOUS_VERSION
        self.review.update(version=PREVIOUS_VERSION,review_origin='initial_profile')
        self.materials.update(schema='math-gauge.mathematical-profile-materials/v1',
                              version=PREVIOUS_VERSION,new_candidate_calls=0)
        for row in self.review['tasks']:
            for judgment in row['axes'].values():
                judgment['assessment_status'] = 'reviewed'
            for goal in row['goals']:
                goal['assessment_status'] = 'reviewed'
        # This two-slot fixture isolates source validation. The full42-slot,
        # fixed-family contract is independently exercised by arithmetic tests.
        old_contract = self.put(self.prv,'protocol/mathematical-profile/v0.1.0/contracts.json',self.contracts)
        legacy_policy = json.loads(read_bytes(ROOT/'protocol/mathematical-profile-v0.1.0.json'))
        legacy_policy['private_contract_sha256'] = old_contract['sha256']
        self.legacy_policy = self.put(self.pub,'protocol/mathematical-profile-v0.1.0.json',legacy_policy)
        self.put(self.pub,'protocol/mathematical-profile-v0.1.0.md',
                 read_bytes(ROOT/'protocol/mathematical-profile-v0.1.0.md'))

    def test_bound_manuscript_companion_is_exact_and_confined_to_its_task(self):
        alias = 'manuscript:' + self.ids[0] + ':manuscript'
        companion = self.put(self.prv, 'delivered/manuscript.md', b'original companion theorem')
        self.materials['sources'][alias] = companion
        evidence = dict(source_id=alias, pointer='', quote='original companion theorem')
        self.review['tasks'][0]['axes']['fidelity']['evidence'] = [evidence]
        with patch('math_gauge.mathematical_profile.manuscript_delivery_sources',
                   return_value={alias: companion}):
            self.validate()
            self.review['tasks'][1]['axes']['fidelity']['evidence'] = [evidence]
            with self.assertRaisesRegex(ValueError, 'selected task mathematical evidence'):
                self.validate()
            self.review['tasks'][1]['axes']['fidelity']['evidence'] = [dict(
                source_id='content_review', pointer='/tasks/1/units/0/reason',
                quote='actual evidence ' + self.ids[1])]
            forged = self.put(self.prv, 'unselected/work.md', b'original companion theorem')
            self.materials['sources'][alias] = forged
            with self.assertRaisesRegex(ValueError, 'exact selected delivery'):
                self.validate()
            self.materials['sources'][alias] = companion
            (self.prv / companion['path']).write_bytes(b'damaged original')
            with self.assertRaises(ValueError):
                self.validate()

    def test_unbound_manuscript_alias_cannot_become_profile_evidence(self):
        alias = 'manuscript:' + self.ids[0] + ':unselected'
        self.materials['sources'][alias] = self.put(self.prv, 'unselected.md', b'unselected work')
        self.review['tasks'][0]['axes']['fidelity']['evidence'] = [dict(
            source_id=alias, pointer='', quote='unselected work')]
        with patch('math_gauge.mathematical_profile.manuscript_delivery_sources', return_value={}):
            with self.assertRaisesRegex(ValueError, 'exact selected delivery'):
                self.validate()

    def test_first_profile_needs_explicit_origin(self):
        self.review.pop('review_origin')
        with self.assertRaises(ValueError):self.validate()

    def test_first_profile_cannot_invent_a_prior_review(self):
        self.materials['sources']['prior_profile_review'] = dict(path='invented.json',sha256='1'*64)
        with self.assertRaises(ValueError):self.validate()

    def test_incomplete_retained_review_cannot_be_bypassed_as_initial(self):
        self.put(self.prv,'results/mathematical-profiles/v0.1.0/fixture/review.json',dict(model_id='fixture'))
        with self.assertRaises(ValueError):self.validate()

    def test_private_index_entry_cannot_be_bypassed_when_payload_is_missing(self):
        self.put(self.prv,'results/mathematical-profiles/v0.1.0/index.json',
                 dict(version=LEGACY_VERSION,policy_sha256=self.legacy_policy['sha256'],models={'fixture':{}}))
        with self.assertRaises(ValueError):self.validate()

    def test_initial_profile_cannot_change_a_frozen_goal(self):
        self.contracts['tasks'][0]['goals'][0]['weight'] = 50
        with self.assertRaises(ValueError):self.validate()


class PriorProfileBindingTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        base = Path(self.tmp.name)
        self.pub,self.prv = base/'public',base/'private'
        self.pub.mkdir();self.prv.mkdir()
        self.roots = dict(public=self.pub,private=self.prv)

        def put(root,path,value):
            raw = value if isinstance(value,bytes) else (json.dumps(value,ensure_ascii=False)+'\n').encode()
            target = root/path;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(raw)
            return dict(repository='public' if root==self.pub else 'private',path=path,
                        bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest())
        self.put = put
        for suffix in ('json','md'):
            name = 'protocol/mathematical-profile-v0.1.0.'+suffix
            put(self.pub,name,read_bytes(ROOT/name))
        inputs,policy,digest = arithmetic_fixture()
        record = put(self.pub,'records/selected.json',dict(model_id='fixture'))
        contract_ref = put(self.prv,'old-contracts.json',inputs.contracts)
        self.contracts = deepcopy(inputs.contracts)
        self.contracts['version'] = PREVIOUS_VERSION
        old_sources = dict(public_source_record=record,contracts=contract_ref,
                           selected_report=dict(path='selected-report.json',sha256='4'*64))
        self.tasks = [dict(id='case:A1',selected_state=dict(status='original'))]
        header = dict(version=LEGACY_VERSION,model_id='fixture',condition='nonlogical_retry_3',policy_sha256=digest)
        prefix = 'results/mathematical-profiles/v0.1.0/fixture/'
        old_review = put(self.prv,prefix+'review.json',dict(header,tasks=[]))
        old_materials = put(self.prv,prefix+'source-bindings.json',dict(header,sources=old_sources,tasks=self.tasks))
        score = score_mathematical_profile(inputs);score['model_id']='fixture'
        public = project_public(score,policy=policy,policy_sha256=digest,
            private_review_sha256=old_review['sha256'],private_materials_sha256=old_materials['sha256'],
            source_record=record,source_calibration=record)
        ref = put(self.pub,prefix+'profile.json',public)
        put(self.pub,'results/mathematical-profiles/v0.1.0/index.json',
            dict(version=LEGACY_VERSION,policy_sha256=digest,models={'fixture':ref}))
        self.materials = dict(sources=dict(old_sources,contracts=dict(path='new-contracts.json',sha256='5'*64),
            prior_profile_review=old_review,prior_profile_materials=old_materials),tasks=deepcopy(self.tasks))

    def validate(self):
        _validate_prior_profile(dict(model_id='fixture'),self.materials,self.roots,contracts=self.contracts)

    def test_exact_retained_prior_review_and_selected_states_are_accepted(self):
        self.validate()

    def test_prior_review_cannot_be_substituted_even_with_a_valid_new_hash(self):
        self.materials['sources']['prior_profile_review'] = self.put(self.prv,
            'results/mathematical-profiles/v0.1.0/fixture/review.json',dict(model_id='other'))
        with self.assertRaises(ValueError):self.validate()

    def test_supplement_cannot_change_an_original_source_alias(self):
        self.materials['sources']['selected_report'] = dict(path='other.json',sha256='6'*64)
        with self.assertRaises(ValueError):self.validate()

    def test_supplement_cannot_change_the_selected_attempt_or_task_state(self):
        self.materials['tasks'][0]['selected_state']['status'] = 'another attempt'
        with self.assertRaises(ValueError):self.validate()

    def test_legacy_anchor_alias_does_not_fallback_after_damage(self):
        (self.pub/'protocol/mathematical-profile-v0.1.0.md').write_text('damaged frozen document')
        with self.assertRaises(ValueError):self.validate()

    def test_supplement_cannot_change_a_visible_goal_or_private_family(self):
        self.contracts['tasks'][-1]['family_id'] = 'different-private-family'
        with self.assertRaises(ValueError):self.validate()

    def test_retained_profile_cannot_claim_initial_origin(self):
        with self.assertRaises(ValueError):
            _validate_prior_profile(dict(model_id='fixture',review_origin='initial_profile'),
                                    self.materials,self.roots,contracts=self.contracts)


class RecentProfileBindingTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        base = Path(self.tmp.name)
        self.pub, self.prv = base/'public', base/'private'
        self.roots = dict(public=self.pub, private=self.prv)

        def put(root, path, value):
            raw = value if isinstance(value, bytes) else (json.dumps(value)+'\n').encode()
            target = root/path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(raw)
            return dict(path=path, bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())
        self.put = put
        for version in (LEGACY_VERSION, PREVIOUS_VERSION):
            for suffix in ('json', 'md'):
                rel = 'protocol/mathematical-profile-v'+version+'.'+suffix
                put(self.pub, rel, read_bytes(ROOT/rel))
        inputs, policy, digest = arithmetic_fixture(PREVIOUS_VERSION)
        record = dict(repository='public', **put(self.pub, 'records/selected.json', {'model_id':'fixture'}))
        old_contract = dict(repository='private', **put(self.prv, 'contracts-v2.json', inputs.contracts))
        sources = dict(public_source_record=record, contracts=old_contract,
                       selected_report=dict(path='retained-report.json', sha256='4'*64))
        self.tasks = [dict(id='case:A1', selected_state=dict(status='same-attempt'))]
        header = dict(version=PREVIOUS_VERSION, model_id='fixture', condition='nonlogical_retry_3', policy_sha256=digest)
        prefix = 'results/mathematical-profiles/v0.2.0/fixture/'
        old_review = put(self.prv, prefix+'review.json', dict(header, tasks=[]))
        old_materials = put(self.prv, prefix+'source-bindings.json', dict(header, sources=sources, tasks=self.tasks))
        score = score_mathematical_profile(inputs)
        score['model_id'] = 'fixture'
        public = project_public(score, policy=policy, policy_sha256=digest,
            private_review_sha256=old_review['sha256'], private_materials_sha256=old_materials['sha256'],
            source_record=record, source_calibration=record)
        ref = put(self.pub, prefix+'profile.json', public)
        put(self.pub, 'results/mathematical-profiles/v0.2.0/index.json',
            dict(version=PREVIOUS_VERSION, policy_sha256=digest, models={'fixture':ref}))
        put(self.prv, 'results/mathematical-profiles/v0.2.0/index.json',
            dict(version=PREVIOUS_VERSION, policy_sha256=digest,
                 models={'fixture':{'review':old_review, 'source-bindings':old_materials}}))
        self.materials = dict(version=VERSION, sources=dict(sources,
            contracts=dict(path='contracts-v3.json', sha256='5'*64),
            prior_component_review=dict(repository='private', **old_review),
            prior_component_materials=dict(repository='private', **old_materials)), tasks=deepcopy(self.tasks))
        self.contracts = deepcopy(inputs.contracts)
        self.contracts.update(version=VERSION, completion_rule=WHOLE_COMPLETION)

    def validate(self, **extra):
        _validate_prior_profile(dict(model_id='fixture', version=VERSION, **extra),
                                self.materials, self.roots, contracts=self.contracts)

    def test_new_component_binds_the_exact_selected_previous_review_and_materials(self):
        self.validate()

    def test_new_component_cannot_hide_an_existing_profile_as_initial(self):
        with self.assertRaises(ValueError):self.validate(review_origin='initial_profile')

    def test_a_different_valid_review_hash_is_not_the_selected_predecessor(self):
        ref = self.put(self.prv, 'substituted.json', {'model_id':'fixture'})
        self.materials['sources']['prior_component_review'] = dict(repository='private', **ref)
        with self.assertRaises(ValueError):self.validate()

    def test_new_component_cannot_replace_an_original_attempt_or_alias(self):
        self.materials['tasks'][0]['selected_state']['status'] = 'another-attempt'
        with self.assertRaises(ValueError):self.validate()

    def test_frozen_previous_policy_damage_is_not_hidden_by_current_policy(self):
        (self.pub/'protocol/mathematical-profile-v0.2.0.md').write_text('damaged')
        with self.assertRaises(ValueError):self.validate()

    def test_new_completion_method_does_not_change_the_visible_goal_definitions(self):
        self.contracts['tasks'][0]['goals'][0]['weight'] += 1
        with self.assertRaises(ValueError):self.validate()


if __name__ == '__main__':
    unittest.main()
