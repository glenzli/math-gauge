"""Submission gates keep work credit, fixed attempts and source bytes separate."""
import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from math_gauge import submission_evidence as evidence
from math_gauge.benchmarks import validate_assessment_policy
from math_gauge.scoring import (_submission_task, _submission_trajectory,
                                score_assessment_inputs, validate_capability_policy)

ROOT = Path(__file__).resolve().parents[1]


def descriptor(path, raw=b'original'):
    return dict(path=path, bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())


class SubmissionScoringTests(unittest.TestCase):
    def work(self):
        case = dict(case_id='MG-GR021', contract_sha256='a'*64,
            criteria=[dict(criterion_id='math', points=90),
                      dict(criterion_id='assertion_reliability', points=10)])
        review = dict(schema=evidence.WORK_SCHEMA, version='0.1.0',
            case_id='MG-GR021', phase='A1', attempt_condition='single_attempt',
            case_contract_sha256='a'*64, reviewer_kind='ai', source_repaired=False,
            new_candidate_calls=0, candidate_scripts_executed=False,
            selection='fixed_last_effective_attempt_within_condition',
            deadline_existence_verified=True, evidence=[descriptor('source.md')],
            credit_units=[dict(id='math', maximum=90, earned=90, reason='Verified mathematics'),
                          dict(id='assertion_reliability', maximum=10, earned=0, reason='No reliable final')])
        row = dict(classification='forced_content', mathematical_source='nonfinal_work',
            work_review=descriptor('review.json'), work=review)
        return case, row

    def test_nonfinal_valid_work_can_only_earn_mc_with_original_math_denominator(self):
        case, row = self.work()
        for claim in (None, {'status':'delivery_failed'},
                      {'embedded_reliability':{'criterion_id':'assertion_reliability'}}):
            for mode in ('capability', 'partial', 'strict'):
                value, passed, _ = _submission_task((0,0,0), False, 'old', row,
                    case=case, mode=mode, condition='single_attempt', claim=claim)
                self.assertEqual(value, (1,1,1) if mode=='capability' else (0,0,0))
                self.assertFalse(passed)
        row['work']['attempt_condition'] = 'nonlogical_retry_3'
        with self.assertRaises(ValueError):
            _submission_task((0,0,0),False,'old',row,case=case,mode='capability',condition='single_attempt')

    def test_forced_formal_body_is_referenced_once_and_unknown_is_not_failure(self):
        row = dict(classification='forced_content', mathematical_source='retained_formal_body')
        value, passed, _ = _submission_task((.7,.7,.7),False,'old',row,
            case={},mode='capability',condition='single_attempt')
        self.assertEqual(value,(.7,.7,.7));self.assertFalse(passed)
        row['classification']='not_run'
        value, passed, _ = _submission_task((1,1,1),True,'old',row,
            case={},mode='strict',condition='single_attempt')
        self.assertEqual(value,(0,1,None));self.assertIsNone(passed)
        value, passed, _ = _submission_task((-.5,1,None),None,'old',row,
            case={},mode='partial',condition='single_attempt')
        self.assertEqual(value,(-.5,1,None));self.assertIsNone(passed)

    def test_missing_normal_round_cannot_retain_strict_trajectory_or_reliable_points(self):
        alignment = dict(rounds=[dict(round=n,score=dict(lower=100,upper=100,exact=100),
            strict_pass=True,source_sha256=str(n)*64) for n in (1,2,3)])
        review = dict(rounds=[dict(round=n,classification='active_final' if n!=2 else 'forced_content',
            scored_math_is_delivered=True,reviewable_content_verified=True,
            mathematical_source_sha256=str(n)*64) for n in (1,2,3)])
        original = copy.deepcopy(alignment)
        for mode in ('capability','partial','strict'):
            scored, strict = _submission_trajectory(alignment,{'strict_pass':True},review,mode=mode)
            self.assertAlmostEqual(scored['metric']['exact'],100 if mode=='capability' else 200/3)
            self.assertFalse(strict['strict_pass'])
        self.assertEqual(alignment,original)
        review['rounds'][0]['scored_math_is_delivered']=False
        with self.assertRaisesRegex(ValueError,'Normal selfcheck'):
            _submission_trajectory(alignment,{'strict_pass':True},review,mode='partial')
        for row in review['rounds']:row['classification']='not_run'
        scored, strict = _submission_trajectory(alignment,{'strict_pass':False},review,mode='strict')
        self.assertIsNone(scored['metric']['exact']);self.assertIsNone(strict['strict_pass'])

    def test_new_method_requires_submission_pair_and_preserves_old_versions(self):
        policy=json.loads((ROOT/'protocol/scoring-policy.json').read_bytes())
        old=copy.deepcopy(policy);old.update(version='0.8.0',capability_policy_version='0.2.0')
        old.pop('submission_policy_version',None)
        new=copy.deepcopy(old);new.update(version='0.9.0',capability_policy_version='0.3.0',submission_policy_version='0.1.0')
        validate_assessment_policy(old);validate_assessment_policy(new)
        with self.assertRaises(ValueError):
            validate_assessment_policy(dict(new,capability_policy_version='0.2.0'))
        capability=json.loads((ROOT/'protocol/capability-scoring-policy.json').read_bytes())
        validate_capability_policy(dict(capability,version='0.3.0',nonfinal_work='verified_fixed_attempt_work_without_active_delivery'))
        from test_current_record_scoring import FreshRecordScoringTests
        fixture=FreshRecordScoringTests();fixture.setUp()
        with self.assertRaisesRegex(ValueError,'complete0.9.0 policy pair'):
            score_assessment_inputs(fixture.inputs,new,fixture.data['strict_policy'])

    def test_active_final_does_not_inherit_a_larger_unsubmitted_workspace(self):
        from test_current_record_scoring import FreshRecordScoringTests
        fixture=FreshRecordScoringTests();fixture.setUp()
        policy=copy.deepcopy(fixture.data['assessment_policy'])
        policy.update(version='0.9.0',capability_policy_version='0.3.0',submission_policy_version='0.1.0')
        component=json.loads((ROOT/'protocol/submission-scoring-policy.json').read_bytes())
        data=dict(schema=evidence.REVIEW_SCHEMA,version='0.1.0',model_label=fixture.inputs['model_label'],
            attempt_condition='single_attempt',initials=[dict(case_id=c['case_id'],classification='active_final',
                source_response_sha256='b'*64,reason='Synthetic normal final',evidence=[descriptor('final.md')],
                scored_math_is_delivered=c['case_id']!='MG-C003') for c in fixture.inputs['plan']['case_index']],
            rounds=[dict(round=n,classification='not_run',reason='No round in this condition',
                evidence=[descriptor('plan.json')]) for n in (1,2,3)])
        kwargs=dict(mathematical_substitutions={'MG-C003:A1':(24/92,)*3},
                    submission_review=data,submission_policy=component)
        with self.assertRaisesRegex(ValueError,'additional undelivered engineering'):
            score_assessment_inputs(fixture.inputs,policy,fixture.data['strict_policy'],**kwargs)
        row=next(r for r in data['initials'] if r['case_id']=='MG-C003')
        case=next(c for c in fixture.inputs['plan']['case_index'] if c['case_id']=='MG-C003')
        row['normal_review']=descriptor('normal-review.json')
        row['normal_math']=dict(schema=evidence.NORMAL_SCHEMA,version='0.1.0',case_id='MG-C003',phase='A1',
            attempt_condition='single_attempt',source_response_sha256='b'*64,complete=False,
            case_contract_sha256=case['group_contract_sha256'],reviewer_kind='ai',source_repaired=False,
            new_candidate_calls=0,candidate_scripts_executed=False,deadline_existence_verified=True,
            original_final_existence_verified=True,
            evidence=[descriptor('original-final.md')],credit_units=[dict(id=s['stage_id'],maximum=1,
                earned=int(i<18),reason='Original final unit review') for i,s in enumerate(case['stages'])])
        capability=json.loads((ROOT/'protocol/capability-scoring-policy.json').read_bytes())
        capability.update(version='0.3.0',nonfinal_work='verified_fixed_attempt_work_without_active_delivery')
        for mode in ('capability','partial'):
            report=score_assessment_inputs(fixture.inputs,policy,fixture.data['strict_policy'],
                mode=mode,capability_policy=capability if mode=='capability' else None,**kwargs)
            task=next(t for t in report['tasks'] if t['case_id']=='MG-C003')
            self.assertAlmostEqual(task['completion']['exact'],18/92)
            self.assertEqual(task['judgment_source'],'verified_normal_final')


class SubmissionSourceTests(unittest.TestCase):
    def test_original_policy_history_allows_method_change_without_rewriting_mathematics(self):
        with tempfile.TemporaryDirectory() as temporary:
            folder=Path(temporary)
            def keep(name,value):
                raw=json.dumps(value).encode();(folder/name).write_bytes(raw)
                return descriptor(name,raw)
            old=json.loads((ROOT/'protocol/scoring-policy.json').read_bytes())
            old.update(version='0.8.0',capability_policy_version='0.2.0')
            old.pop('submission_policy_version',None)
            policy=keep('original-policy.json',old)
            files=[policy]
            for mode in ('capability','partial','strict'):
                for condition in evidence.CONDITIONS:
                    files.append(keep(mode+'-'+condition+'.json',dict(
                        schema='math-gauge.assessment-score/v1',scoring_method_version='0.8.0',
                        capability_method_version='0.2.0',score_mode=mode,attempt_condition=condition)))
            history=keep('history.json',dict(schema='math-gauge.score-history/v1',
                assessment_method_version='0.8.0',capability_method_version='0.2.0',
                original_policy_sha256=policy['sha256'],files=files))
            record=dict(score_history=history)
            current=dict(old,version='0.9.0',capability_policy_version='0.3.0',submission_policy_version='0.1.0')
            self.assertEqual(evidence.original_assessment_policy(folder,record,current),old)
            changed=copy.deepcopy(current);changed['groups'][0]['weight']+=1
            with self.assertRaisesRegex(ValueError,'frozen mathematical policy'):
                evidence.original_assessment_policy(folder,record,changed)

    def test_source_mutation_and_symlinks_are_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            folder=Path(temporary);(folder/'source.md').write_bytes(b'original')
            item=descriptor('source.md')
            self.assertEqual(evidence._read(folder,item),b'original')
            (folder/'source.md').write_bytes(b'changed')
            with self.assertRaises(ValueError):evidence._read(folder,item)
            (folder/'alias').symlink_to(folder, target_is_directory=True)
            with self.assertRaises(ValueError):evidence._read(folder,descriptor('alias/source.md',b'changed'))

    def test_progress_without_positive_credit_is_not_active_and_counts_are_exclusive(self):
        data=dict(initials=[dict(classification='forced_content'),dict(classification='blank'),
                            dict(classification='active_final')])
        count=evidence.summary(data)
        self.assertEqual((count['active_final'],count['forced_content'],count['blank'],count['planned']),(1,1,1,3))

    def test_serialized_embedded_work_cannot_replace_bound_original_review(self):
        with tempfile.TemporaryDirectory() as temporary:
            folder=Path(temporary)
            data=dict(schema='math-gauge.submission-archive/v1',version='0.1.0',conditions={
                c:dict(attempt_condition=c,initials=[dict(work={'invented':True})]) for c in evidence.CONDITIONS})
            raw=json.dumps(data).encode();(folder/'archive.json').write_bytes(raw)
            with self.assertRaisesRegex(ValueError,'Serialized work'):
                evidence.load_condition(folder,dict(submission_evidence=descriptor('archive.json',raw)),'single_attempt')

    def test_condition_keys_cannot_be_swapped_when_responses_are_missing(self):
        with tempfile.TemporaryDirectory() as temporary:
            folder=Path(temporary)
            data=dict(schema='math-gauge.submission-archive/v1',version='0.1.0',conditions={
                c:dict(attempt_condition=other,initials=[]) for c,other in
                zip(evidence.CONDITIONS,reversed(evidence.CONDITIONS))})
            raw=json.dumps(data).encode();(folder/'archive.json').write_bytes(raw)
            with self.assertRaisesRegex(ValueError,'keys and attempt conditions'):
                evidence.load_condition(folder,dict(submission_evidence=descriptor('archive.json',raw)),'single_attempt')

    def test_public_validation_rejects_private_identifiers_paths_and_bodies(self):
        public_ids={f'PUBLIC-{n:02d}' for n in range(25)}
        row=dict(summary=dict(planned=39,active_final=25,forced_content=0,blank=14,pending=0,
                             pending_original_record_review=0),
            public_initials=[dict(case_id=c,classification='active_final',pending_original_record_review=False)
                             for c in sorted(public_ids)],private_pending_original_record_review=0,
            rounds=[dict(round=n,classification='active_final') for n in (1,2,3)])
        data=dict(schema='math-gauge.submission-projection/v1',version='0.1.0',source_sha256='a'*64,
                  conditions={c:copy.deepcopy(row) for c in evidence.CONDITIONS})
        with tempfile.TemporaryDirectory() as temporary:
            folder=Path(temporary);policy=(ROOT/'protocol/submission-scoring-policy.json').read_bytes()
            (folder/'policy.json').write_bytes(policy)
            def check(value):
                raw=json.dumps(value).encode();(folder/'projection.json').write_bytes(raw)
                record=dict(submission_policy=descriptor('policy.json',policy),
                    submission_evidence=descriptor('projection.json',raw),submission_evidence_source_sha256='a'*64)
                return evidence.validate_record_component(folder,record,public=True,public_ids=public_ids)
            check(data)
            for mutation in ('private_id','path','body'):
                bad=copy.deepcopy(data);selected=bad['conditions']['single_attempt']['public_initials'][0]
                if mutation=='private_id':selected['case_id']='PRIVATE-SECRET'
                elif mutation=='path':selected['private_path']='/private/research.md'
                else:bad['private_answer']='private source text'
                with self.subTest(mutation=mutation),self.assertRaises(ValueError):check(bad)
