"""Synthetic software evidence for typed review dimensions and family scoring."""
import copy
import contextlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from math_gauge.benchmarks import BenchmarkProfile, build_plan
from math_gauge.catalog import Suite, candidate_message, read_json, validate_group_contract, write_json
from math_gauge.execution import run
from math_gauge.harness import export_harness_bundle, inspect_harness_bundle
from math_gauge.reliability import execute_reliability_run
from math_gauge.reliability_review import apply_reliability_reviews, reliability_review_templates
from math_gauge.review import _validate_answer_review
from math_gauge.scoring import score_inputs, score_runs, score_composed_runs
from test_composite_suites import RUNTIME, synthetic_suite


def fixture_suite(root, cid, family):
    synthetic_suite(root, cid)
    case = read_json(root / 'paper/case.json')
    case.update(track='determinate', task_kind='answer_review', parent_family_id=family)
    write_json(root / 'paper/case.json', case)
    write_json(root / 'paper/rubric.json', {'schema':'math-gauge.rubric/v1', 'expected':'mixed',
        'required_evidence':['Synthetic only'], 'critical_errors':['EVALUATOR_PRIVATE']})
    write_json(root / 'paper/contract.json', {'schema':'math-gauge.group-contract/v2',
        'kind':'answer_review', 'assessment_unit':'review_dimension', 'id':cid,
        'version':case['version'], 'parent_family_id':family, 'dimensions':[
            {'id':key,'points':points,'title':key,'required_evidence':['Synthetic evidence'],
             'critical_errors':['Synthetic invalid evidence']}
            for key, points in [('core_judgment',60),('evidence_scope',30),('completeness',10)]]})
    return Suite.load(root)


def fixture_profile(root, suite):
    slots=[{'slot_id':cid+':A1','case_id':cid,'kind':'independent','attempt_label':'A1',
            'context':'fresh','parent_slot':None,'message_id':None,'ordinal_per_model':i}
           for i,cid in enumerate(suite.cases,1)]
    for name,value in [('selection',{'protocol_version':'0.2.0','source_suite_sha256':suite.sha256,
                                    'case_count':0,'truth_counts':{},'cases':[]}),
                       ('prompts',{'protocol_version':'0.2.0','messages':[]}),
                       ('schedule',{'protocol_version':'0.2.0','slots':slots})]:
        write_json(root/(name+'.json'),value)
    path=root/'profile.json'
    write_json(path,{'schema':'math-gauge.benchmark-profile/v4','id':'synthetic-answer-review',
        'version':'fixture-1','operator_only':True,'path_base':'repository',
        'suite':{'id':suite.metadata['id'],'version':suite.metadata['version'],'sha256':suite.sha256},
        'components':[{'id':'answer-review','weight':100,'case_ids':list(suite.cases)}],
        'attempt_schedule':{cid:['A1'] for cid in suite.cases},
        'score_policy':{'core_attempt_labels':['A1'],'repeat_case_ids':[],
                        'repeat_attempt_labels':['A1','A2','A3']},
        'overall_weights':{'core':100,'repeat':0,'neutral':0,'stance':0},
        'reliability':{'protocol_version':'0.2.0','selection':'selection.json',
                       'prompts':'prompts.json','schedule':'schedule.json'}})
    return BenchmarkProfile.load(path,suite,repository_root=root)


class AnswerReviewTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory(prefix='math-gauge-answer-review-fixture-')
        self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name)
        self.first=fixture_suite(self.root/'first/cases','SYN-AR1','FAMILY-A')
        self.second=fixture_suite(self.root/'second/cases','SYN-AR2','FAMILY-A')
        self.third=fixture_suite(self.root/'third/cases','SYN-AR3','FAMILY-B')
        self.suite=Suite.combine([self.first,self.second,self.third])
        self.profile=fixture_profile(self.root/'profile',self.suite)
        self.plan=build_plan(self.profile,self.suite,runtime=RUNTIME)

    def test_plan_projection_keeps_dimensions_distinct_and_hidden(self):
        for row in self.plan['case_index']:
            self.assertNotIn('stages',row)
            self.assertEqual(row['assessment_unit'],'review_dimension')
            self.assertEqual([d['points'] for d in row['dimensions']],[60,30,10])
        for case in self.suite.cases.values():
            self.assertNotIn('EVALUATOR_PRIVATE',candidate_message(self.suite.request(case)))
        bundle=self.root/'bundle'
        export_harness_bundle(self.plan,self.suite,bundle,targets=['answer-review'])
        inspect_harness_bundle(bundle,plan=self.plan,suite=self.suite)
        checked=subprocess.run([sys.executable,'-I','-S',str(bundle/'controller.py'),
                                'check','--bundle',str(bundle)],capture_output=True,check=False)
        self.assertEqual(checked.returncode,0,checked.stderr.decode())
        self.assertEqual(json.loads(checked.stdout)['exported_slots'],3)

    def test_fractional_credit_and_major_error_are_independent(self):
        contract=read_json(self.first.root/'paper/contract.json')
        entry={'decision':'partial','dimensions':[{'dimension_id':d['id'],'score':score,
            'notes':'Synthetic bounded credit'} for d,score in zip(contract['dimensions'],[60,30,7.5])],
            'major_error':False,'major_error_notes':'Synthetic separate judgment'}
        score=_validate_answer_review(contract,entry,{'status':'ok'})
        self.assertEqual(score['completion']['exact'],.975)
        entry['major_error']=True
        self.assertEqual(_validate_answer_review(contract,entry,{'status':'ok'})['completion'],score['completion'])
        entry['major_error']=None
        self.assertIsNone(_validate_answer_review(contract,entry,{'status':'ok'})['major_error'])
        for invalid in [True,float('nan'),float('inf'),-1,11]:
            entry['dimensions'][-1]['score']=invalid
            with self.assertRaises(ValueError):_validate_answer_review(contract,entry,{'status':'ok'})
        invalid=copy.deepcopy(contract);invalid['dimensions'][0]['points']=50
        with self.assertRaises(ValueError):validate_group_contract(invalid)

    def test_family_means_missing_bounds_and_auxiliary_error_rate(self):
        path=self.root/'fixture-run'
        execute_reliability_run(self.plan,self.suite,path,
            replay={cid+':A1':'Synthetic original answer' for cid in self.suite.cases})
        reviews=reliability_review_templates(path)
        for entry,values,major in zip(reviews,[[60,30,10],[0,0,0],[60,30,10]],[False,True,False]):
            self.assertNotIn('stages',entry)
            entry.update(reviewer='synthetic',reviewer_kind='fixture',
                decision='pass' if sum(values)==100 else 'partial',assumption_fidelity='clean',
                proof_validity='valid',scope_accuracy='correct',notes='Synthetic only',findings=[],
                format_review={'decision':'valid','notes':'Complete synthetic bytes'},
                major_error=major,major_error_notes='Synthetic major-error axis')
            for dim,value in zip(entry['dimensions'],values):dim.update(score=value,notes='Synthetic credit')
        apply_reliability_reviews(path,reviews)
        report=score_runs([path])
        self.assertEqual(report['metrics']['answer-review']['exact'],75)
        self.assertEqual(report['metrics']['answer-review']['coverage']['planned'],2)
        self.assertEqual(report['metrics']['answer_review_major_error_rate']['exact'],25)
        from math_gauge.reliability_review import reliability_score_inputs
        inputs=reliability_score_inputs(path)
        inputs['slots']=[r for r in inputs['slots'] if r['case_id']!='SYN-AR2']
        partial=score_inputs(inputs)['metrics']['answer-review']
        self.assertEqual((partial['lower'],partial['upper'],partial['exact']),(75,100,None))

    def test_cli_rescoring_requires_explicit_composition(self):
        from math_gauge.cli import main, parser
        args=parser().parse_args(['benchmark-report','--run','fixture','--out',str(self.root/'out'),
                                  '--answer-review-sources','source.json','--suite',str(self.first.root)])
        self.assertEqual(args.answer_review_sources,'source.json')
        with contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(main(['benchmark-report','--run','fixture','--out',str(self.root/'out'),
                                  '--answer-review-sources','source.json']),2)
        self.assertFalse((self.root/'out').exists())

    def test_real_source_rescoring_checks_all_content_hashes_and_execution(self):
        ordinary=copy.copy(self.first);ordinary.cases=copy.deepcopy(self.first.cases)
        original=ordinary.cases['SYN-AR1'];original.pop('group_contract');original['version']='old-fixture'
        original['task_kind']='written'
        path=self.root/'ordinary'
        replay_path=self.root/'fixture-responses.json'
        write_json(replay_path,{'SYN-AR1':'Synthetic original response'})
        run(ordinary,path,replay=replay_path)
        from math_gauge.catalog import digest_bytes
        base=self.first.root/'paper'
        entry={'case_id':'SYN-AR1','response_sha256':digest_bytes((path/'SYN-AR1/response.md').read_bytes()),
            'contract_sha256':digest_bytes((base/'contract.json').read_bytes()),
            'rubric_sha256':digest_bytes((base/'rubric.json').read_bytes()),
            'reference_sha256':digest_bytes((base/'reference.md').read_bytes()),
            'reviewer':'synthetic','reviewer_kind':'fixture','decision':'partial',
            'assumption_fidelity':'clean','proof_validity':'valid','scope_accuracy':'correct',
            'unnecessary_restriction':False,'notes':'Post-observation synthetic rescore','findings':[],
            'major_error':False,'major_error_notes':'Synthetic only',
            'dimensions':[{'dimension_id':key,'score':value,'notes':'Synthetic credit'} for key,value in
                          [('core_judgment',60),('evidence_scope',30),('completeness',5)]]}
        review_path=self.root/'rescore.json';write_json(review_path,[entry])
        source={'run':path,'reviews':review_path,'post_observation_rescoring':True,'notes':'Synthetic version change'}
        result=score_composed_runs(self.plan,[],answer_review_sources=[source],suite=self.suite,
            model_aliases={'replay-fixture':RUNTIME['model_label']})
        self.assertEqual(result['composition']['new_candidate_calls'],0)
        self.assertTrue(result['evidence'][0]['answer_review_rescoring']['post_observation_rescoring'])
        from math_gauge.cli import main
        plan_path=self.root/'target-plan.json';write_json(plan_path,self.plan)
        sources_path=self.root/'sources.json'
        write_json(sources_path,[dict(source,run=str(path),reviews=str(review_path))])
        alias_path=self.root/'aliases.json'
        write_json(alias_path,{'replay-fixture':RUNTIME['model_label']})
        cli_out=self.root/'cli-report'
        args=['benchmark-report','--composition-plan',str(plan_path),'--out',str(cli_out),
              '--answer-review-sources',str(sources_path),'--model-aliases',str(alias_path)]
        for member in (self.first,self.second,self.third):args.extend(['--suite',str(member.root)])
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(main(args),0)
        self.assertEqual(read_json(cli_out/'report.json')['metrics']['answer-review'],
                         result['metrics']['answer-review'])
        changed=copy.deepcopy(entry);changed['rubric_sha256']='0'*64;write_json(review_path,[changed])
        with self.assertRaisesRegex(ValueError,'target contract'):
            score_composed_runs(self.plan,[],answer_review_sources=[source],suite=self.suite,
                model_aliases={'replay-fixture':RUNTIME['model_label']})
        write_json(review_path,[entry]);record=read_json(path/'SYN-AR1/record.json');record['status']='error'
        write_json(path/'SYN-AR1/record.json',record)
        with self.assertRaisesRegex(ValueError,'executed ok'):
            score_composed_runs(self.plan,[],answer_review_sources=[source],suite=self.suite,
                model_aliases={'replay-fixture':RUNTIME['model_label']})
