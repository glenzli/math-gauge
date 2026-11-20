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
    AXES, BEHAVIOR, VERSION, COMPLETION, CORE_GATE, ProfileInputs, load_policy, project_public,
    source_bytes, validate_contracts, validate_public, validate_review,
    _validate_assessment_status, _validate_fidelity_core, _validate_proof_core,
)
from math_gauge.scoring import score_mathematical_profile, profile_strict_completion_metric
ROOT = Path(__file__).resolve().parents[1]


def strict_report(value=32.833333333333336, *, unknown=False):
    return dict(score_mode='strict', attempt_condition='nonlogical_retry_3', metrics=dict(earned=dict(
        exact=None if unknown else round(value,10), confirmed=value,
        lower=value if unknown else round(value-1e-10,10), upper=value+10 if unknown else round(value+1e-10,10),
        complete=not unknown,coverage=dict(unit='fixed 100-point benchmark',planned=8,
                                         adjudicated=7 if unknown else 8,unknown=1 if unknown else 0))))


def arithmetic_fixture():
    policy,digest=load_policy(ROOT)
    tasks=deepcopy(policy['public_task_contracts'])
    for category,count in [('written-argument',4),('background-check',2),
                           ('theorem-extension',4),('manuscript-completion',4)]:
        for i in range(count):
            ident=category+'-synthetic-'+str(i)
            tasks.append(dict(id=ident+':A1',case_id=ident,family_id=ident,subcategory=category,
                kind='initial',public=False,axis_weights=dict.fromkeys(BEHAVIOR,'1/35'),
                goals=[dict(id='whole',weight=100)],proof_core=dict(required_goals=['whole'],
                    scope='Original task, including every required branch, dependency and representation bridge; valid alternative proofs or original-premise counterexamples are accepted.')))
    inputs=object.__new__(ProfileInputs)
    inputs.policy=policy
    inputs.contracts=dict(schema='math-gauge.mathematical-profile-contracts/v1',version=VERSION,
        benchmark_version='1.1.0',condition='nonlogical_retry_3',tasks=tasks,
        planned_families=policy['planned_families'],completion_rule=COMPLETION,proof_core_gate=CORE_GATE)
    inputs.review=dict(model_id='synthetic',version=VERSION,tasks=[dict(id=c['id'],
        axes={a:dict(grade=4) for a in BEHAVIOR},goals=[dict(id=g['id'],passed=True) for g in c['goals']])for c in tasks])
    inputs.strict_report=strict_report()
    return inputs,policy,digest


class ProfileArithmeticTests(unittest.TestCase):
    def setUp(self):
        self.inputs,self.policy,self.digest=arithmetic_fixture()
        self.rows={r['id']:r for r in self.inputs.review['tasks']}

    def test_six_axes_preserve_family_mass_and_selfcheck_nesting(self):
        validate_contracts(self.inputs.contracts,self.policy)
        for axis in BEHAVIOR:
            families={}
            for t in self.inputs.contracts['tasks']:
                family=t['family_id'];families[family]=families.get(family,Fraction())+Fraction(t['axis_weights'][axis])
                self.assertNotIn('completion',t['axis_weights'])
            self.assertEqual(set(families.values()),{Fraction(1,35)})
            self.assertEqual(len(families),35)
        score=score_mathematical_profile(self.inputs)
        self.assertTrue(all(score['metrics'][a]['exact']==100 for a in BEHAVIOR))
        self.assertAlmostEqual(score['metrics']['completion']['exact'],32.833333333333336)

    def test_completion_is_the_exact_official_value_not_family_goal_average(self):
        before=score_mathematical_profile(self.inputs)['metrics']['completion']
        for row in self.rows.values():
            for goal in row['goals']:goal['passed']=False
            for axis in BEHAVIOR:row['axes'][axis]['grade']=0
        after=score_mathematical_profile(self.inputs)
        self.assertEqual(after['metrics']['completion'],before)
        self.assertEqual(after['metrics']['proof']['exact'],0)
        self.inputs.strict_report=strict_report(64.5)
        self.assertEqual(score_mathematical_profile(self.inputs)['metrics']['completion']['exact'],64.5)

    def test_smc_unknown_retains_official_bounds_and_coverage(self):
        self.inputs.strict_report=strict_report(14,unknown=True)
        metric=score_mathematical_profile(self.inputs)['metrics']['completion']
        self.assertIsNone(metric['exact']);self.assertEqual((metric['confirmed'],metric['lower'],metric['upper']),(14,14,24))
        self.assertEqual(metric['coverage'],dict(unit='benchmark_subcategory',planned=8,reviewed=7))

    def test_unknown_proof_round_does_not_change_known_smc_or_shrink_family_denominator(self):
        self.rows['MG-C003:R2']['axes']['proof']['grade']=None
        score=score_mathematical_profile(self.inputs)
        m=score['metrics']['proof'];self.assertIsNone(m['exact'])
        self.assertAlmostEqual(m['unknown_weight'],100/210)
        self.assertEqual(m['coverage']['reviewed'],34)
        self.assertIsNotNone(score['metrics']['completion']['exact'])

    def test_delivery_zero_and_evidence_unknown_remain_distinct(self):
        for row in self.rows.values():row['axes']['proof']['grade']=None
        metric=score_mathematical_profile(self.inputs)['metrics']['proof']
        self.assertEqual((metric['lower'],metric['upper'],metric['coverage']['reviewed']),(0,100,0))
        for row in self.rows.values():row['axes']['proof']['grade']=0
        metric=score_mathematical_profile(self.inputs)['metrics']['proof']
        self.assertEqual((metric['exact'],metric['coverage']['reviewed']),(0,35))

    def test_contract_cannot_replace_original_required_goals_or_family_weight(self):
        self.inputs.contracts['tasks'][0]['proof_core']['required_goals']=[]
        with self.assertRaises(ValueError):validate_contracts(self.inputs.contracts,self.policy)
        inputs,policy,_=arithmetic_fixture();inputs.contracts['tasks'][0]['axis_weights']['proof']='1/6'
        with self.assertRaises(ValueError):validate_contracts(inputs.contracts,policy)

    def test_smc_rejects_a_different_mode_or_attempt_condition(self):
        for key,value in [('score_mode','capability'),('attempt_condition','single_attempt')]:
            report=strict_report();report[key]=value
            with self.assertRaises(ValueError):profile_strict_completion_metric(report)


class CoreGateTests(unittest.TestCase):
    def test_refuted_or_essential_unproved_core_cannot_keep_high_grade(self):
        for status in ('unresolved_core','refuted_core'):
            for grade in (3,4):
                with self.assertRaises(ValueError):_validate_proof_core(dict(grade=grade,core_status=status))
            _validate_proof_core(dict(grade=2,core_status=status))

    def test_local_gap_cannot_be_presented_as_complete(self):
        _validate_proof_core(dict(grade=3,core_status='local_gap'))
        with self.assertRaises(ValueError):_validate_proof_core(dict(grade=4,core_status='local_gap'))
        _validate_proof_core(dict(grade=4,core_status='established'))

    def test_no_progress_zero_and_missing_source_are_not_mathematical_refutations(self):
        _validate_proof_core(dict(grade=0,core_status='no_valid_progress'))
        _validate_proof_core(dict(grade=None,core_status='source_unresolved',assessment_status='source_unresolved'))
        for value in [dict(grade=4),dict(grade=0,core_status='refuted_core'),dict(grade=None,core_status='established')]:
            with self.assertRaises(ValueError):_validate_proof_core(value)

    def test_fidelity_gate_still_rejects_unbridged_scope_drift(self):
        for grade in (3,4):
            with self.assertRaises(ValueError):_validate_fidelity_core(dict(grade=grade,core_scope_failure=True))
        _validate_fidelity_core(dict(grade=2,core_scope_failure=True))


class PublicBoundaryTests(unittest.TestCase):
    def setUp(self):
        inputs,self.policy,self.digest=arithmetic_fixture();self.score=score_mathematical_profile(inputs)
        self.ref=dict(path='results/selected/record.json',sha256='0'*64)
        self.public=self.project()
    def project(self):
        return project_public(self.score,policy=self.policy,policy_sha256=self.digest,
            private_review_sha256='1'*64,private_materials_sha256='2'*64,source_record=self.ref,source_calibration=self.ref)
    def test_only_aggregates_and_allowlisted_sources_are_public(self):
        self.score['tasks'][0]['private_details']='PRIVATE_SENTINEL'
        self.assertNotIn('PRIVATE_SENTINEL',json.dumps(self.project()))
        self.public['source_record']['private_details']='PRIVATE_SENTINEL'
        with self.assertRaises(ValueError):validate_public(self.public,self.policy,policy_sha256=self.digest)
    def test_smc_coverage_cannot_be_mislabeled_as_35_families(self):
        self.public['metrics']['completion']['coverage']=dict(unit='mathematical_family',planned=35,reviewed=35)
        with self.assertRaises(ValueError):validate_public(self.public,self.policy,policy_sha256=self.digest)
    def test_public_group_or_metric_cannot_expose_private_rows(self):
        self.public['metrics']['proof']['private_rows']=['PRIVATE_SENTINEL']
        with self.assertRaises(ValueError):validate_public(self.public,self.policy,policy_sha256=self.digest)
        self.public=self.project();self.public['groups']={'private':'PRIVATE_SENTINEL'}
        with self.assertRaises(ValueError):validate_public(self.public,self.policy,policy_sha256=self.digest)


class SourceBoundaryTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        base = Path(self.tmp.name)
        self.pub,self.prv = base/'public',base/'private'
        self.pub.mkdir();self.prv.mkdir()
        self.roots = dict(public=self.pub,private=self.prv)
        self.policy_sha,self.contract_sha = 'a'*64,'b'*64
        self.policy = dict(version=VERSION,private_contract_sha256=self.contract_sha)

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
        smc=put(self.prv,'reports/strict.json',strict_report())
        psmc=put(self.pub,'reports/strict.json',strict_report())
        manifest=put(self.prv,'calibration/manifest.json',dict(inputs=ci,scores={
            'partial':{'nonlogical_retry_3':report},'strict':{'nonlogical_retry_3':smc}}))
        put(self.prv,'results/edition-reassessments/v1.1.0/transition.json',dict(calibrations={'fixture':manifest}))
        pub_cal=put(self.pub,'calibration/public.json',dict(private_manifest_sha256=manifest['sha256'],
            private_inputs_sha256=ci['sha256'],scores={'strict':{'nonlogical_retry_3':psmc}}))
        record = put(self.pub,'records/selected.json',dict(model_id='fixture'))
        sources = dict(public_source_record=record,calibration=pub_cal,calibration_inputs=ci,
                       selected_report=report,selected_smc_report=smc,public_smc_report=psmc,content_review=cr,goal_review=gr)
        sources.update({'answer:'+slot:answers[i] for i,slot in enumerate(self.ids)})
        self.materials = dict(version=VERSION,new_candidate_calls=0,model_id='fixture',condition='nonlogical_retry_3',policy_sha256=self.policy_sha,
            private_contract_sha256=self.contract_sha,sources=sources,tasks=[dict(id=slot,content_index=i,goal_index=i,
                response_sha256=answers[i]['sha256'],raw_answer=answers[i],selected_state=states[i]) for i,slot in enumerate(self.ids)])
        self.contracts = dict(tasks=[dict(id=slot,case_id=slot.split(':')[0],kind='initial',
            subcategory='written-argument',axis_weights={'fidelity':'1/2','proof':'1/2'},goals=[dict(id='whole',weight=100)]) for slot in self.ids])
        self.review = dict(schema='math-gauge.mathematical-profile-review/v1',version=VERSION,benchmark_version='1.1.0',
            condition='nonlogical_retry_3',model_id='fixture',policy_sha256=self.policy_sha,private_contract_sha256=self.contract_sha,
            reviewer_id='synthetic-reviewer',reviewer_kind='ai',human_review='pending',new_candidate_calls=0,formal_comparison_eligible=False,tasks=[])
        for i,slot in enumerate(self.ids):
            ev = dict(source_id='content_review',pointer=f'/tasks/{i}/units/0/reason',quote='actual evidence '+slot)
            self.review['tasks'].append(dict(id=slot,axes={'fidelity':dict(grade=4,core_scope_failure=False,assessment_status='reviewed',reason='Same original objects and assumptions.',evidence=[ev]),'proof':dict(grade=4,core_status='established',assessment_status='reviewed',reason='The original core is established.',evidence=[ev])},
                goals=[dict(id='whole',passed=True,assessment_status='reviewed',reason='The complete goal is delivered.',evidence=[dict(source_id='goal_review',pointer=f'/tasks/{i}/goals/0/reason',quote='complete goal '+slot)])],research=None))
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


    def test_reject_another_model_smc_even_under_a_valid_top_record(self):
        self.materials['sources']['selected_smc_report']=self.put(self.prv,'other/strict.json',strict_report(100))
        with self.assertRaisesRegex(ValueError,'exact selected assessment'):self.validate()
    def test_prior_profile_alias_cannot_become_an_evidence_dependency(self):
        self.materials['sources']['prior_profile_review']=dict(path='old.json',sha256='0'*64)
        with self.assertRaises(ValueError):self.validate()
    def test_refuted_core_cannot_be_hidden_in_an_otherwise_valid_source_review(self):
        self.review['tasks'][0]['axes']['proof']['core_status']='refuted_core'
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
