"""Synthetic closed native records only; no private case or actual model grades."""
from contextlib import closing
from copy import deepcopy
import json
from pathlib import Path
import sqlite3
import tempfile
import unittest
from unittest.mock import patch

from math_gauge import independent_research_admitted_delivery as admitted
from math_gauge import independent_research_native as original_native
from math_gauge import independent_research_value as value
from math_gauge import independent_research_adoption as adoption
from math_gauge import taste_v130 as flow
import test_taste_v130 as fixture_support
from test_independent_research_review import write_policy


def ref(path, raw):
    return dict(path=str(path), bytes=len(raw), sha256=admitted.digest(raw))


class AdmittedDeliveryTests(unittest.TestCase):
    def setUp(self):
        self.fixture = fixture_support.ProtocolFixture('runTest')
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        self.root = self.fixture.root
        self.archive_root = self.root/'retained'
        self.archive_root.mkdir()
        self.inventory = []
        self.binding = admitted.digest(self.fixture.registration.read_bytes())
        self.prompts = self.fixture.reg['rounds']
        self.session, self.context = 'synthetic-native-session', 'synthetic-candidate-context'
        self.rows = []
        self.policy = write_policy(self.fixture)
        self.origin = '/synthetic/original'
        self.prior = None
        self.seal_prior = None
        self.extra = [self.source('user-extra600.json', dict(actual_explicit_user_extension=600)),
                      self.source('user-extra300.json', dict(actual_explicit_user_extension=300))]
        self.r1_manuscript = self.source('R1/cutoff/manuscript.md', b'R1 synthetic original mathematical manuscript.\n')
        self.prior_r1 = self.source('prior-R1-admission.json', dict(native_session_id=self.session,
            chain_context_id=self.context, registration=dict(sha256=self.binding),
            forced_parent_manuscript=self.r1_manuscript, R1_original_normal_final=False,
            R1_original_delivery_state_preserved='delivery-failed'))
        auth = dict(schema='math-gauge.carbon-open-research-forced-submission-authorization/v1',
            model_configuration=admitted.MODEL, native_session_id=self.session,
            registration=dict(sha256=self.binding), selected_rounds=list(flow.ROUNDS),
            adopted_after_observation=True, benchmark_adoption_authorized=True,
            R2_seconds=2700, R3_seconds=2700, prior_R1_forced_admission=self.prior_r1,
            source_receipts=[self.prior_r1])
        auth.update(dict.fromkeys(('fourth_round_allowed', 'fresh_math_attempt_allowed', 'math_feedback_allowed',
            'native_status_rewrite_allowed', 'normal_final_synthesized', 'force_content_direct_math_zero',
            'normal_only_validator_rewrite_allowed', 'human_mathematical_approval', 'commit_authorized',
            'push_authorized', 'deployment_authorized'), False))
        self.auth = self.source('user-authorization.json', auth)
        self.addCleanup(patch.stopall)
        patch.object(admitted, 'AUTHORIZATION_SHA256', self.auth['sha256']).start()
        for rid in flow.ROUNDS:
            self.round(rid, normal=rid != 'R1')
        db = self.root/'closed.sqlite'
        with closing(sqlite3.connect(db)) as conn:
            conn.execute('CREATE TABLE synthetic_history(id integer)')
            conn.execute('INSERT INTO synthetic_history VALUES (1)')
            conn.commit()
        self.db = self.source('native/closed.sqlite', db.read_bytes())
        exit_ref = self.source('process-exit.json', dict(pid=12345, returncode=-15))
        continuity = self.source('continuity.json', dict(schema='math-gauge.carbon-native-history-continuity/v1',
            native_session_id=self.session, passed=True, complete_own_history=True, new_independent_context=False,
            history_before_sha256=self.db['sha256'], history_after_sha256=self.db['sha256'], source_receipts=[self.db]))
        history = self.source('closed-history.json', dict(schema=admitted.HISTORY, native_session_id=self.session,
            complete_own_history=True, all_processes_exited=True, hidden_history_used_as_mathematical_submission=False,
            authentication_state_excluded=True, snapshots=[dict(id='whole-closed', source_files=[self.db], complete=True)],
            process_exits=[exit_ref], continuity_proofs=[continuity]))
        self.document = dict(schema=admitted.ADMISSION, edition=flow.EDITION, model_id=admitted.MODEL,
            native_session_id=self.session, candidate_context_id=self.context, registration_sha256=self.binding,
            authorization=self.auth, prior_R1_admission=self.prior_r1, archive=None, history=history,
            rounds=self.rows, human_review='pending', conditions=dict(original_round_limit_seconds=2700,
                R1_extension_seconds=900, R1_extension_timing='post-cutoff-user-authorized', network_tools_used=False,
                external_retrieval_used=False, source_materials_unchanged=True,
                account_condition_change_preserved=True, system_retry_exclusion_inferred=False))
        self.path = self.root/'admission.json'
        self.save()
        self.evidence = self.load()
        self.review = self.make_review()

    def source(self, name, data):
        raw = data if isinstance(data, bytes) else admitted.encoded(data)
        target = self.archive_root/name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(raw)
        original = self.origin+'/'+name
        self.inventory.append(dict(original_path=original, path=name, bytes=len(raw), sha256=admitted.digest(raw)))
        return ref(original, raw)

    def overwrite_source(self, source, data):
        row = next(r for r in self.inventory if r['original_path'] == source['path'])
        raw = admitted.encoded(data)
        (self.archive_root/row['path']).write_bytes(raw)
        row.update(bytes=len(raw), sha256=admitted.digest(raw))
        source.update(bytes=len(raw), sha256=admitted.digest(raw))

    def save(self):
        archive = dict(schema=admitted.ARCHIVE, closed=True, all_processes_exited=True,
            authentication_state_excluded=True, original_source_bytes_unchanged=True, files=self.inventory)
        archive_path = self.archive_root/'archive.json'
        raw = admitted.encoded(archive)
        archive_path.write_bytes(raw)
        self.document['archive'] = ref('retained/archive.json', raw)
        self.path.write_bytes(admitted.encoded(self.document))

    def load(self):
        return admitted.load_admission(self.path, self.binding, round_prompts=self.prompts)

    def round(self, rid, *, normal):
        main = self.source(rid+'/chain/'+rid+'.md', (rid+' synthetic visible normal final.\n').encode()) if normal else self.r1_manuscript
        extra = [self.source(rid+'/chain/'+rid+'.files/companion.md', (rid+' explicit original companion.\n').encode())] if normal else []
        sealed_raw = dict(main, path=rid+'.md') if normal else None
        sealed_files = [dict(r, path=rid+'.files/companion.md') for r in extra]
        observation = dict(schema='math-gauge.research-round-observation/v1',round=rid, context_id=self.context, kind='operator-attestation',
            delivery='normal-final' if normal else 'delivery-failed', first_normal_final=True if normal else None,
            boundary=dict(kind='first-normal-final' if normal else 'deadline', at='2026-11-25T00:01:00Z'),
            raw=sealed_raw, delivered_files=[dict(r,path='companion.md') for r in extra])
        obs = self.source(rid+'/chain/'+rid+'.observation.json', observation)
        seal = self.source(rid+'/chain/'+rid+'.seal.json', dict(round=rid, previous=self.seal_prior,
            registration_sha256=self.binding, prompt_sha256=self.prompts[rid]['sha256'],
            delivery=observation['delivery'], raw=sealed_raw, files=sealed_files,
            observation=dict(obs,path=rid+'.observation.json')))
        elapsed, prefix = (30, 0) if normal else (300, 3299)
        request = self.source(rid+'/request.json', dict(event='user', message=dict(content=
            (self.fixture.case/f'candidate/{rid}.md').read_text() if rid != 'R1' else admitted.R1_CONTINUATION)))
        terminal = dict(event='result', result=dict(conversation_id=self.session,status='SUCCESS', response=(rid+' synthetic visible normal final.\n'))) if normal else None
        wire = self.source(rid+'/wire.ndjson', (json.dumps(terminal).encode()+b'\n') if normal else b'{"event":"input-proof"}\n')
        boundary = self.source(rid+'/boundary.json', dict(schema='math-gauge.carbon-open-research-native-boundary/v1',round=rid, native_session_id=self.session,
            began='2026-11-25T00:00:00Z', elapsed_seconds=elapsed, agent_thought_used_as_submission=False))
        result = self.source(rid+'/result.json', dict(schema='math-gauge.carbon-account-r1-round/v1', round=rid,
            native_session_id=self.session, model='gemini-4-carbon', effort='medium', native_transport='print-stream-json',
            no_synthetic_acp_receipts=True, new_independent_opportunity=False,
            old_results_classifications_seals_native_db_rewritten=False, agent_thought_used_for_submission=False,
            elapsed_seconds=elapsed, original_prefix_seconds=prefix, total_round_math_elapsed_seconds=elapsed+prefix,
            budget_seconds_this_dispatch=2700 if normal else 300, began='2026-11-25T00:00:00Z',
            first_normal_final=normal, delivery=observation['delivery'], status='normal_final' if normal else 'cutoff_without_final',
            seal=seal, native_prompt_request=request, raw_events=wire,
            visible_agent_message=main, native_terminal='SUCCESS' if normal else None,
            native_result=terminal, failure=None if normal else dict(type='TimeoutError'),
            explicit_delivered_files=[dict(r,path='companion.md') for r in extra]))
        cutoff = self.source(rid+'/cutoff.json', dict(schema=admitted.CUTOFF, round=rid, native_session_id=self.session,
            boundary_source=boundary, candidate_writes_stopped=True, operator_repaired=False, hidden_thought_used=False,
            files=[main])) if not normal else None
        row = dict(round=rid, selected_delivery='normal-final' if normal else 'forced-content',
            original_result=result, original_boundary=boundary, original_seal=seal, original_observation=obs,
            cutoff_inventory=cutoff, documents=[dict(source=main,role='manuscript')]+
                [dict(source=r,role='explicit-attachment') for r in extra], parent_sha256=self.prior,
            budget_segments=[dict(seconds=2700,kind='original-limit',authorization=None)]+
                ([] if normal else [dict(seconds=n,kind='user-extension',authorization=a) for n,a in zip((600,300),self.extra)]))
        self.rows.append(row)
        self.prior, self.seal_prior = admitted.digest(admitted.encoded(row)), seal['sha256']

    def citation(self, rid):
        source = self.evidence.records[rid]['raw']
        raw = flow._read(self.evidence.archive.root, source)
        return dict(round=rid, file=source['path'], start=0, end=len(raw), quote=raw.decode())

    def judgment(self, fields, rounds):
        return dict(fields, reason='Synthetic independent judgment.', evidence=[self.citation(r) for r in rounds] if any(v is not None for v in fields.values()) else [])

    def make_review(self):
        def axis(keys, points, deduction, flags):
            return dict(mc_score=sum(points), rmc_score=sum(points)-10,
                smc=dict(lower=80,upper=80,exact=80) if keys[0]=='value' else dict(lower=50,upper=70,exact=None),
                all_required_checkpoints=True if keys[0]=='value' else False,
                reason='Synthetic full trajectory judgment.', evidence=[self.citation(r) for r in flow.ROUNDS],
                directions={k:dict(mc_points=p,net_rmc_points=p-(10 if i==0 else 0),verdict=flags[i],
                    reason='Synthetic allocated credit.',evidence=[self.citation('R1')]) for i,(k,p) in enumerate(zip(keys,points))},
                error_deductions=[dict(id=deduction, criterion=keys[0], points=10,
                    reason='Synthetic retained error.', evidence=[self.citation('R1')])])
        gates = {a:{s['id']:self.judgment(dict(verdict=(None if s['id']=='C1' else False if s['id']=='C2' else True)),
            flow.ROUNDS if a in ('taste','capacity') else s['rounds']) for s in self.fixture.contract['gates'][a]} for a in flow.AXES}
        return dict(schema=admitted.REVIEW, edition=flow.EDITION, case_id='CASE-FIXTURE',
            registration_sha256=self.binding, admission_sha256=self.evidence.admission_sha256,
            review_policy_sha256=admitted.trajectory.policy_sha256(self.fixture.registration,self.policy),
            delivery_records=self.evidence.row_hashes, reviewer=dict(adoption.REVIEWER,reviewer_id='synthetic-reviewer',
                reviewer_context_id='synthetic-independent-context'),
            axes=dict(autonomy=self.judgment(dict(score=100,strict=True),('R1','R2')),
                taste=axis(['value','structure','selection'],[50,20,20],'taste-error',[True,True,True]),
                capacity=axis(['C0','C1','C2','C3','C4'],[20]*5,'capacity-error',[True,None,False,True,True])),
            gates=gates, round_reviews={a:{rid:self.judgment(dict(score=80,strict=False),(rid,))
                for rid in self.fixture.contract['round_coverage'][a]} for a in flow.AXES},
            selection_audit=dict(sufficient_choices=True,reason='Synthetic actual selectable material.',
                kept=[self.citation('R3')],removed=[self.citation('R1')]),
            error_roots=[dict(id=root,effects={a:'Synthetic genuine effect.'},reason='Synthetic root.',
                evidence=[self.citation('R1')]) for root,a in [('taste-error','taste'),('capacity-error','capacity')]],
            extension=dict(level='E0',assessed_rounds=list(flow.ROUNDS),independent_question='No extra question.',
                outside_core='Synthetic boundary.',result_and_scope='No unsolicited unit.',value='No extra assessed value.',
                reason='Synthetic separate assessment.',evidence=[self.citation('R3')]))

    def check(self, review=None):
        return admitted.validate_review(review or self.review,self.evidence,self.fixture.contract,
            case_id='CASE-FIXTURE',review_policy_sha256=admitted.trajectory.policy_sha256(self.fixture.registration,self.policy))

    def test_forced_source_keeps_original_failure_and_requires_closed_all_three(self):
        self.assertEqual([self.evidence.records[r]['delivery'] for r in flow.ROUNDS],['forced-content','normal-final','normal-final'])
        original=self.evidence.archive.json(self.rows[0]['original_seal'])
        self.assertEqual(original['delivery'],'delivery-failed');self.assertIsNone(original['raw'])
        incomplete=deepcopy(self.document);incomplete['rounds'].pop()
        self.path.write_bytes(admitted.encoded(incomplete))
        with self.assertRaisesRegex(ValueError,'complete selected'): self.load()

    def test_damaged_archived_source_never_reads_intact_original_or_falls_back(self):
        target=self.evidence.archive.root/self.evidence.records['R1']['raw']['path']
        target.write_bytes(b'DAMAGED')
        with self.assertRaisesRegex(ValueError,'hash mismatch'): self.load()

    def test_source_chain_and_normal_status_cannot_be_forged(self):
        self.document['rounds'][0]['selected_delivery']='normal-final'
        self.save()
        with self.assertRaises(ValueError): self.load()

    def test_exact_authorization_and_actual_extension_conditions_are_required(self):
        self.document['conditions']['R1_extension_seconds']=0;self.save()
        with self.assertRaisesRegex(ValueError,'conditions'): self.load()

    def test_cutoff_cannot_add_later_workspace_or_operator_repaired_proof(self):
        source=self.rows[0]['cutoff_inventory'];cutoff=self.evidence.archive.json(source)
        cutoff['operator_repaired']=True;self.overwrite_source(source,cutoff);self.save()
        with self.assertRaises(ValueError): self.load()

    def test_same_raw_credit_uses_frozen_weights_and_unknown_denominator(self):
        grade=self.check()
        self.assertEqual(grade['axes']['taste'],dict(mc=90,rmc=80,strict=True))
        self.assertEqual(grade['criteria']['capacity'],dict(planned=5,passed=3,unknown=1))
        self.assertEqual(grade['strict_credit']['capacity'],dict(lower=50,upper=70,exact=None))
        row=dict(status='reviewed',**grade,source_sha256='e'*64)
        policy,_=value.load_policy();policy=dict(policy,item_weights=dict(taste=2,capacity=1))
        reports={mode:dict(metrics={g:dict(exact=60) for g in ('overall','written','lean','research')}) for mode in ('MC','RMC','SMC')}
        result=admitted.project_model(reports,policy,row)
        self.assertAlmostEqual(result['score_modes']['MC']['item']['exact'],280/3)
        self.assertIsNone(result['score_modes']['SMC']['item']['exact'])
        self.assertEqual(result['composite_by_base']['SMC']['lower'],61)
        self.assertAlmostEqual(result['composite_by_base']['SMC']['upper'],54+23/3)
        self.assertEqual(result['admitted_source_sha256'],'e'*64)

    def test_omitted_error_root_wrong_quote_or_self_review_is_rejected(self):
        for mutation in ('root','quote','self'):
            review=deepcopy(self.review)
            if mutation=='root':review['axes']['taste']['error_deductions']=[]
            elif mutation=='quote':review['axes']['taste']['directions']['value']['evidence'][0]['quote']='FAKE'
            else:review['reviewer']['reviewer_context_id']=self.context
            with self.subTest(mutation=mutation),self.assertRaises(ValueError): self.check(review)

    def test_explicit_frozen_runner_reads_original_case_when_current_runner_has_drifted(self):
        from math_gauge.evidence_retention import _git
        public=flow.POLICY_FILE.parents[3]
        frozen=self.root/'reader-package';frozen.mkdir()
        registered=deepcopy(self.fixture.reg)
        registered['runner']['files']=[]
        for source in self.fixture.reg['runner']['files']:
            raw=_git(public,'show','7f7fd7cd5241155d14d3e5c7846c5efe17d45291:'+source['path'])
            target=frozen/'frozen-runner'/source['path'];target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(raw)
            registered['runner']['files'].append(ref(source['path'],raw))
        registration=self.fixture.registration.with_name('retained-reader-registration.json')
        registration.write_bytes(admitted.encoded(registered))
        manifest=dict(schema=admitted.FROZEN_RUNNER,source_commit='7f7fd7cd5241155d14d3e5c7846c5efe17d45291',
            registration_sha256=admitted.digest(registration.read_bytes()),root='frozen-runner',files=registered['runner']['files'],
            reader_use='original-load-case-only',final_scoring_owner='current-shared-scoring',network_fetch=False)
        path=frozen/'manifest.json';path.write_bytes(admitted.encoded(manifest))
        drift=self.root/'different-current';drift.mkdir()
        for source in self.fixture.reg['runner']['files']:
            target=drift/source['path'];target.parent.mkdir(parents=True,exist_ok=True)
            target.write_bytes(_git(public,'show','7f7fd7cd5241155d14d3e5c7846c5efe17d45291:'+source['path'])+b'\n# unrelated later source change\n')
        with patch.object(flow,'POLICY_FILE',drift/'protocol/mathematical-taste/v1.3.0/policy.json'):
            with self.assertRaisesRegex(ValueError,'hash mismatch'):flow.load_case(registration)
            actual=admitted.retained_case_reader(registration,path,public)
            self.assertEqual(actual[2],registered)
        source=frozen/'frozen-runner/math_gauge/scoring.py';source.write_bytes(source.read_bytes()+b'\n')
        with self.assertRaisesRegex(ValueError,'hash mismatch'):admitted.retained_case_reader(registration,path,public)

    def test_qualitative_round_diagnostics_are_reviewed_without_invented_numbers(self):
        review=deepcopy(self.review);review.pop('round_reviews')
        review['round_diagnostics']={rid:dict(assessment='reviewed',diagnostic_score=None,
            reason='Synthetic actually reviewed full manuscript.',evidence=[self.citation(rid)]) for rid in flow.ROUNDS}
        grade=self.check(review)
        self.assertEqual(grade['axes']['taste']['rmc'],80)
        bad=deepcopy(review);bad['round_diagnostics']['R1']['diagnostic_score']=0
        with self.assertRaises(ValueError):self.check(bad)

    def test_one_semantic_error_may_have_one_independent_allocation_on_each_axis(self):
        review=deepcopy(self.review)
        root=review['error_roots'][0]
        root['id']='shared-root';root['effects']['capacity']='A distinct capacity effect of the same error.'
        review['error_roots']=[root]
        for axis in ('taste','capacity'):review['axes'][axis]['error_deductions'][0]['id']='shared-root'
        grade=self.check(review)
        self.assertEqual(grade['axes']['taste']['rmc'],80)
        self.assertEqual(grade['axes']['capacity']['rmc'],90)

    def test_exact_historical_phase_never_substitutes_the_current_bytes(self):
        current=self.r1_manuscript
        raw=b'An earlier immutable phase of the same original path.\n'
        target=self.archive_root/'phases/earlier.md';target.parent.mkdir();target.write_bytes(raw)
        earlier=ref(current['path'],raw)
        self.inventory.append(dict(original_path=earlier['path'],path='phases/earlier.md',bytes=len(raw),sha256=earlier['sha256']))
        self.save();evidence=self.load()
        self.assertEqual(evidence.archive.read(earlier),raw)
        self.assertNotEqual(evidence.archive.read(current),raw)
        wrong=dict(earlier,sha256='0'*64)
        with self.assertRaises(ValueError):evidence.archive.read(wrong)

    def test_unassessed_taste_keeps_its_fixed_unknown_share(self):
        review=deepcopy(self.review)
        for gate in review['gates']['taste'].values():gate.update(verdict=None,evidence=[])
        review['axes']['taste'].update(mc_score=None,rmc_score=None,directions=None,error_deductions=[],
            evidence=[],smc=dict(lower=0,upper=100,exact=None),all_required_checkpoints=None)
        review['error_roots']=[r for r in review['error_roots'] if 'taste' not in r['effects']]
        review['selection_audit'].update(sufficient_choices=None,kept=[])
        grade=self.check(review)
        self.assertEqual(grade['criteria']['taste'],dict(planned=3,passed=0,unknown=3))
        row=dict(status='reviewed',**grade,source_sha256='e'*64)
        policy,_=value.load_policy();policy=dict(policy,item_weights=dict(taste=2,capacity=1))
        reports={mode:dict(metrics={g:dict(exact=60) for g in ('overall','written','lean','research')}) for mode in ('MC','RMC','SMC')}
        result=admitted.project_model(reports,policy,row)
        self.assertIsNone(result['composite_by_base']['RMC']['exact'])
        self.assertEqual(result['composite_by_base']['RMC']['lower'],57)
        self.assertAlmostEqual(result['composite_by_base']['RMC']['upper'],54+29/3)

    def test_old_normal_only_owner_stays_closed_to_new_admission(self):
        public=dict(schema=admitted.SCHEMA)
        with self.assertRaises(ValueError): original_native.validate_public(public)

    def test_synthetic_end_to_end_prepare_emits_only_aggregate_and_exact_binding(self):
        public=self.root/'public';public.mkdir()
        base=admitted.encoded(dict(benchmark_version='1.2.0',models=[dict(id=admitted.MODEL)]))
        parent_name=f'results/independent-research-baselines/v0.1.0/{admitted.digest(base)}/data.json'
        target=public/parent_name;target.parent.mkdir(parents=True);target.write_bytes(base)
        for name in admitted.external.POLICY_PATHS.values():
            p=public/name;p.parent.mkdir(parents=True,exist_ok=True)
            p.write_bytes((flow.POLICY_FILE.parents[3]/name).read_bytes())
        review_path=self.root/'review.json';review_path.write_bytes(admitted.encoded(self.review))
        selection=self.root/'selection.json'
        selection.write_bytes(admitted.encoded(dict(schema=admitted.SELECTION,
            baseline=ref(parent_name,base), registration=ref(self.fixture.registration,self.fixture.registration.read_bytes()),
            review_policy=ref(self.policy,self.policy.read_bytes()),admission=ref(self.path,self.path.read_bytes()),
            review=ref(review_path,review_path.read_bytes()))))
        result=admitted.prepare(selection,public)
        row=result['models'][admitted.MODEL]
        self.assertEqual((row['normal_rounds'],row['forced_rounds'],row['round_dispatches']),(2,1,3))
        self.assertGreater(row['axes']['taste']['rmc'],0)
        raw=admitted.encoded(result).decode()
        for private in ('CASE-FIXTURE','/synthetic/','synthetic-independent-context','Synthetic original','quote'):
            self.assertNotIn(private,raw)
        for key in ('private_case','raw_manuscript'):
            bad=deepcopy(result);bad[key]='FORBIDDEN'
            with self.assertRaises(ValueError):admitted.validate_public(bad)
