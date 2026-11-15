"""Submission gates keep work credit, fixed attempts and source bytes separate."""
import copy
import hashlib
import json
from fractions import Fraction
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


class SourceRecoveryReceiptTests(unittest.TestCase):
    def fixture(self, root):
        folder = root / 'fixture-model/snapshot'
        folder.mkdir(parents=True)
        source = {'conditions': {'nonlogical_retry_3': {
            'summary': {'planned':39, 'pending':0, 'pending_original_record_review':3},
            'public_initials':[{'case_id':'MG-C003','pending_original_record_review':True}],
            'private_pending_original_record_review':2}}}
        raw = json.dumps(source).encode()
        (folder/'submission.json').write_bytes(raw)
        record = {'submission_evidence':descriptor('submission.json',raw),
                  'execution_summary':{'blocked_selfcheck_rounds':3,'delivered_selfcheck_rounds':0}}
        raw = json.dumps(record).encode()
        (folder/'record.json').write_bytes(raw)
        receipt = dict(schema='math-gauge.source-review-completion/v1',version='0.1.0',
            model_id='fixture-model',record_id='snapshot',record=descriptor('record.json',raw),
            submission_evidence=record['submission_evidence'],status='complete',
            scope='retained_initial_answers_and_source_recovery',reviewed_at='2026-11-11T00:00:00Z',
            initial_tasks_reviewed=39,resolved_public_cases=['MG-C003'],resolved_private_count=2,
            resolved_pending_count=3,unexecuted_selfcheck_rounds=[1,2,3],private_review_sha256='a'*64,
            reviewer_kind='ai',human_review='pending',scores_modified=False,new_candidate_calls=0)
        return folder, record, receipt

    def test_recovery_keeps_original_record_and_unrun_rounds(self):
        with tempfile.TemporaryDirectory() as temp:
            folder,record,receipt = self.fixture(Path(temp))
            original=(folder/'record.json').read_bytes()
            self.assertIsNone(evidence.load_review_completion(folder,record))
            (folder/'review-completion.json').write_text(json.dumps(receipt))
            self.assertEqual(evidence.load_review_completion(folder,record),receipt)
            self.assertEqual((folder/'record.json').read_bytes(),original)
            (folder/'record.json').write_bytes(original+b' ')
            with self.assertRaisesRegex(ValueError,'bytes changed'):
                evidence.load_review_completion(folder,record)

    def test_recovery_cannot_leak_private_ids_or_invent_round_delivery(self):
        with tempfile.TemporaryDirectory() as temp:
            folder,record,receipt=self.fixture(Path(temp))
            for key,value in [('private_case_ids',['secret']),('unexecuted_selfcheck_rounds',[]),
                              ('resolved_pending_count',2),('human_review','approved')]:
                bad=dict(receipt,**{key:value})
                (folder/'review-completion.json').write_text(json.dumps(bad))
                with self.subTest(key=key),self.assertRaises(ValueError):
                    evidence.load_review_completion(folder,record)


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

    def test_written_and_manuscript_stages_keep_verified_partial_credit(self):
        for component in ('proofs', 'manuscript-completion'):
            with self.subTest(component=component):
                case, row = self.work()
                case.pop('criteria')
                case['case_id'] = row['work']['case_id'] = 'staged-written-fixture'
                case['component'] = component
                case['stages'] = [dict(stage_id='math', points=90, lean_required=False),
                    dict(stage_id='assertion_reliability', points=10, lean_required=False)]
                row['work']['credit_units'][0]['earned'] = 45
                original = copy.deepcopy(row['work'])
                for mode in ('capability', 'partial', 'strict'):
                    value, passed, _ = _submission_task((0,0,0), False, 'old', row,
                        case=case, mode=mode, condition='single_attempt')
                    self.assertEqual(value, (Fraction(45,100),)*3 if mode=='capability' else (0,)*3)
                    self.assertFalse(passed)
                self.assertEqual(row['work'], original)

    def test_formalization_partial_obligation_remains_invalid(self):
        case, row = self.work()
        case.pop('criteria')
        case['stages'] = [dict(stage_id='math', points=90),
                          dict(stage_id='assertion_reliability', points=10)]
        row['work']['credit_units'][0]['earned'] = 45
        for explicit_component in (False, True):
            with self.subTest(explicit_component=explicit_component):
                if explicit_component:
                    case['component'] = 'lean-formalization'
                    case['stages'][0].pop('lean_required', None)
                else:
                    case['component'] = 'proofs'
                    case['stages'][0]['lean_required'] = True
                with self.assertRaisesRegex(ValueError, 'binary unit'):
                    evidence.validate_work(row['work'], case, 'single_attempt')

    def test_mixed_stages_only_require_binary_credit_for_the_lean_obligation(self):
        case, row = self.work()
        case.pop('criteria')
        case['component'] = 'proofs'
        case['stages'] = [dict(stage_id='math', points=90, lean_required=True),
            dict(stage_id='assertion_reliability', points=10, lean_required=False)]
        row['work']['credit_units'][1]['earned'] = 4.5
        evidence.validate_work(row['work'], case, 'single_attempt')
        row['work']['credit_units'][0]['earned'] = 45
        with self.assertRaisesRegex(ValueError, 'binary unit'):
            evidence.validate_work(row['work'], case, 'single_attempt')

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


class UserNonfinalSourceSelectionTests(unittest.TestCase):
    def fixture(self, folder, *, auth_updates=None, seal_updates=None, declared=True,
                changed_selection_payload=False):
        def keep(name, value):
            raw = (json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode()
            (folder/name).write_bytes(raw)
            return descriptor(name, raw)
        artifact = descriptor('source.lean', b'unchanged original source')
        (folder/'source.lean').write_bytes(b'unchanged original source')
        seal = dict(normal_complete_delivery=False, answer_sha256=None,
                    utc='2026-11-15T00:00:00Z', work=[artifact])
        seal.update(seal_updates or {})
        seal_d = keep('seal.json', seal)
        auth = dict(schema='math-gauge.explicit-user-nonfinal-source-selection/v1',
            version='0.1.0', model_id='fixture-model', case_id='fixture-case', phase='A1',
            attempt_condition='nonlogical_retry_3', explicit_user_selection=True,
            post_observation=True, execution_time_authorization=False,
            human_mathematical_approval=False, new_candidate_calls=0, RMC=0, SMC=0,
            selected_attempt_root='/original/physical-3', selected_cumulative_physical_request=3,
            selected_effective_attempt=2, selected_mathematical_source=artifact,
            selected_native_seal=seal_d, source_message_id='original-message',
            source_thread_id='original-chat', exact_user_quote='Select the second effective original.',
            user_message_utc='2026-11-15T01:00:00Z')
        auth.update(auth_updates or {})
        selection = dict(schema=evidence.USER_SELECTION_SCHEMA, version='0.1.0',
            model_id='fixture-model', case_id='fixture-case', phase='A1',
            attempt_condition='nonlogical_retry_3', case_contract_sha256='a'*64,
            selected_original_attempt='/original/physical-3', selected_physical_request=3,
            selected_effective_attempt=2, selected_native_seal=seal_d,
            selected_mathematical_sources=[artifact], authorization=keep('authorization.json', auth),
            post_observation=True, no_normal_final=True, applies_to_MC_only=True,
            rmc=0, smc=0, source_repaired=False, cross_attempt_union=False, new_candidate_calls=0)
        payload = copy.deepcopy(selection)
        if changed_selection_payload:
            payload['selected_effective_attempt'] = 1
        selection['source'] = keep('exception.json', payload)
        work = dict(schema=evidence.WORK_SCHEMA, version='0.1.0', model_id='fixture-model',
            case_id='fixture-case', phase='A1', attempt_condition='nonlogical_retry_3',
            case_contract_sha256='a'*64, reviewer_kind='ai', source_repaired=False,
            new_candidate_calls=0, candidate_scripts_executed=False,
            selection=evidence.USER_SELECTION, user_source_selection=selection,
            deadline_existence_verified=True, normal_final_exists=False,
            actual_original_attempt='/original/physical-3', actual_physical_request=3,
            actual_effective_attempt=2, original_work_sources=[artifact],
            evidence=[selection['source'], seal_d, artifact],
            credit_units=[dict(id='math', maximum=100, earned=100, reason='Complete original proof')])
        case = dict(case_id='fixture-case', contract_sha256='a'*64,
                    criteria=[dict(criterion_id='math', points=100)])
        row = dict(case_id='fixture-case', classification='forced_content',
            reason='User selected one original nonfinal source after observation.',
            source_response_sha256=None, mathematical_source='nonfinal_work',
            reviewable_content_verified=True, evidence=[artifact], work_review=keep('work.json', work))
        conditions = {}
        for condition in evidence.CONDITIONS:
            r = row if condition == 'nonlogical_retry_3' else dict(
                case_id='fixture-case', classification='blank', reason='Original first failure.',
                source_response_sha256=None, evidence=[artifact])
            conditions[condition] = dict(schema=evidence.REVIEW_SCHEMA, version='0.1.0',
                model_label='Fixture model', attempt_condition=condition, initials=[r],
                rounds=[dict(round=n, classification='not_run', reason='No round.',
                             evidence=[artifact]) for n in (1, 2, 3)])
        archive = dict(schema='math-gauge.submission-archive/v1', version='0.1.0', conditions=conditions)
        policy = json.loads((ROOT/'protocol/submission-scoring-policy.json').read_bytes())
        if declared:
            policy.update(nonfinal_source_selection_exception_version='0.1.0',
                          nonfinal_source_selection_exceptions=[selection['source']])
        record = dict(submission_evidence=keep('archive.json', archive),
                      submission_policy=keep('policy.json', policy))
        return case, work, record

    def test_bound_user_selection_preserves_failed_delivery_and_mc_only(self):
        with tempfile.TemporaryDirectory() as temp:
            folder = Path(temp); case, work, record = self.fixture(folder)
            original = (folder/'source.lean').read_bytes()
            loaded = evidence.load_condition(folder, record, 'nonlogical_retry_3')
            row = loaded['initials'][0]
            self.assertEqual(row['work'], work)
            for mode in ('capability', 'partial', 'strict'):
                value, passed, _ = _submission_task((0, 0, 0), False, 'old', row,
                    case=case, mode=mode, condition='nonlogical_retry_3')
                self.assertEqual(value, (1, 1, 1) if mode == 'capability' else (0, 0, 0))
                self.assertFalse(passed)
            self.assertEqual((folder/'source.lean').read_bytes(), original)

    def test_user_selection_cannot_change_scope_attempt_or_combine_originals(self):
        with tempfile.TemporaryDirectory() as temp:
            case, work, _ = self.fixture(Path(temp))
            for key, value in [('case_id', 'other-case'), ('attempt_condition', 'single_attempt'),
                               ('selected_effective_attempt', 3), ('no_normal_final', False),
                               ('applies_to_MC_only', False), ('rmc', 1),
                               ('selected_mathematical_sources', [descriptor('other.lean')]),
                               ('cross_attempt_union', True)]:
                bad = copy.deepcopy(work); bad['user_source_selection'][key] = value
                with self.subTest(key=key), self.assertRaises(ValueError):
                    evidence.validate_work(bad, case, 'nonlogical_retry_3')

    def test_loader_requires_declared_exact_authority_and_original_cutoff(self):
        examples = [dict(declared=False), dict(changed_selection_payload=True),
            dict(auth_updates={'selected_effective_attempt': 1}),
            dict(auth_updates={'exact_user_quote': ''}),
            dict(auth_updates={'execution_time_authorization': True}),
            dict(auth_updates={'human_mathematical_approval': True}),
            dict(auth_updates={'user_message_utc': '2026-11-14T23:59:59Z'}),
            dict(auth_updates={'selected_mathematical_source': descriptor('other.lean')}),
            dict(seal_updates={'normal_complete_delivery': True}),
            dict(seal_updates={'work': []})]
        for params in examples:
            with self.subTest(params=params), tempfile.TemporaryDirectory() as temp:
                folder = Path(temp); _, _, record = self.fixture(folder, **params)
                with self.assertRaises(ValueError):
                    evidence.load_condition(folder, record, 'nonlogical_retry_3')

    def test_source_bytes_cannot_change_after_user_selection(self):
        with tempfile.TemporaryDirectory() as temp:
            folder = Path(temp); _, _, record = self.fixture(folder)
            (folder/'source.lean').write_bytes(b'repaired source')
            with self.assertRaisesRegex(ValueError, 'bytes changed'):
                evidence.load_condition(folder, record, 'nonlogical_retry_3')


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
