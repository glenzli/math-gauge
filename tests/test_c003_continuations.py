"""Focused synthetic source and scoring tests; no candidate calls or grading."""
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import sqlite3
import unittest

from math_gauge import c003_continuations as continuation
from math_gauge import scoring
from math_gauge.records import descriptor, evidence_bytes, project_assessment_score
from math_gauge.benchmarks import identity
import test_current_record_scoring as current_record_fixtures
import test_agy_native_evidence as native_fixtures

REPO = Path(__file__).resolve().parents[1]


def put(root, name, value):
    path = root / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(value if isinstance(value, bytes) else json.dumps(value).encode())
    return descriptor(root, path)


class ContinuationSourceTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)

    def source(self, count=0):
        contract = json.loads((REPO/'cases/lean-formalization/MG-C003/contract.json').read_bytes())
        ids = [r['id'] for r in contract['stages']]
        mapping = dict(case_id='MG-C003', version='0.1.1', items=[dict(id=oid, status='incomplete',
            declarations=[], representation='Synthetic test mapping', dependencies=[]) for oid in ids])
        files = [dict(name=name, retained_kind='regular', evidence=put(self.root, 'work/'+name, raw))
                 for name, raw in [('Main.lean', b'-- synthetic incomplete original source\n'),
                                   ('alignment.json', json.dumps(mapping).encode())]]
        seal = dict(native_status='ERROR', normal_complete_delivery=False, symlinks_not_followed=[],
            work=[dict(path=f['name'], **{k:f['evidence'][k] for k in ('bytes','sha256')}) for f in files])
        node = dict(phase='A1', files=files, seal=put(self.root, 'seal.json', seal))
        kernel = dict(schema='math-gauge.c003-source-kernel-review/v1', source_seal_sha256=node['seal']['sha256'],
            status='passed' if count else 'failed', source_repaired=False, axioms_allowed=True,
            files_sha256={'Main.lean':files[0]['evidence']['sha256']},
            evidence=[put(self.root, 'compile.log', b'SYNTHETIC compiler evidence')],
            audited_declarations=[dict(file='Main.lean', name='synthetic')])
        rows = [dict(id=oid, complete=i<count, declarations=[dict(file='Main.lean', name='synthetic')] if i<count else [])
                for i,oid in enumerate(ids)]
        review = dict(schema='math-gauge.c003-sealed-source-review/v1', version='0.1.0',
            case_id='MG-C003', case_version='0.1.1', phase='A1', source_seal_sha256=node['seal']['sha256'],
            reviewer_kind='ai', human_review='pending', source_repaired=False, obligations=rows,
            kernel_review=put(self.root, 'kernel-review.json', kernel))
        node['math_review']=put(self.root, 'math-review.json', review)
        node['project_review']=put(self.root, 'project-review.json', dict(
            schema='math-gauge.c003-project-delivery-review/v1', reviewer_kind='ai',
            source_seal_sha256=node['seal']['sha256'], entry='Main.lean',
            all_target_modules_in_main_import_closure=True, local_lean_files=['Main.lean']))
        return node, seal, contract, ids

    def test_failed_compile_incomplete_baseline_is_reviewable_without_becoming_complete(self):
        node, seal, _, ids = self.source()
        files = continuation._inventory(self.root, node, seal)
        review = continuation._review(self.root, node, files, set(ids))
        self.assertTrue(all(r['complete'] is False for r in review['obligations']))
        self.assertEqual(seal['native_status'], 'ERROR')
        review['obligations'][0].update(complete=True, declarations=[dict(file='Main.lean', name='synthetic')])
        node['math_review']=put(self.root,'math-review.json',review)
        with self.assertRaisesRegex(ValueError, 'bound kernel'):
            continuation._review(self.root,node,files,set(ids))

    def test_byte_damage_escape_and_link_cannot_be_repaired_by_admission(self):
        node, seal, _, _ = self.source()
        (self.root/'work/Main.lean').write_bytes(b'late source edit')
        with self.assertRaisesRegex(ValueError, 'bytes changed'):
            continuation._inventory(self.root,node,seal)
        for name in ['../outside.lean','/absolute.lean','x//y.lean']:
            with self.subTest(name=name), self.assertRaises(ValueError):
                continuation._safe_name(name)
        with tempfile.TemporaryDirectory() as outside:
            path=Path(outside)/'data';path.write_bytes(b'original')
            (self.root/'alias').symlink_to(path)
            item=dict(path='alias',bytes=8,sha256=hashlib.sha256(b'original').hexdigest())
            with self.assertRaisesRegex(ValueError,'symlink'):
                evidence_bytes(self.root,item)

    def test_full_needs_real_main_and_mapping_keep_compares_source_bytes(self):
        node,seal,contract,_=self.source()
        files=continuation._inventory(self.root,node,seal)
        continuation._project_delivery(self.root,node,files,contract)
        altered=copy.deepcopy(files)
        entry,raw=altered['Main.lean']
        entry['sha256']='f'*64
        self.assertNotEqual(continuation._semantic_inventory(files),continuation._semantic_inventory(altered))
        del altered['Main.lean']
        with self.assertRaisesRegex(ValueError,'actual complete project'):
            continuation._project_delivery(self.root,node,altered,contract)

    def test_native_error_cannot_be_relabelled_as_normal_full(self):
        fixture=native_fixtures.AgyEvidenceTests();fixture.setUp();self.addCleanup(fixture.doCleanups)
        fixture.row.update(id='MG-C003:R1',case_id='MG-C003')
        fixture.data.update(case_id='MG-C003',phase='R1')
        fixture.data['dispatch']=fixture.put('dispatch.json',dict(case_id='MG-C003',outer_budget_seconds=10800))
        fixture.save()
        node=dict(phase='R1',native=fixture.row,seal=fixture.data['native_terminal_seal'],
            authentication_evidence=fixture.put('auth.log',b'authMethod=consumer, quotaProject=synthetic'))
        continuation._native(fixture.root,node,failed=False,plan=dict(model='argon',effort='high'))
        # Native SUCCESS with failed CLI cleanup remains valid. ERROR does not.
        fixture.terminal['result']['status']='ERROR'
        fixture.data['native_terminal_event']=fixture.put('terminal.json',fixture.terminal)
        fixture.data['native_events']=fixture.put('events.ndjson',(json.dumps(fixture.terminal)+'\n').encode())
        fixture.execution['artifact_hashes']['output/events.ndjson']=fixture.data['native_events']['sha256']
        fixture.data['native_execution']=fixture.put('execution.json',fixture.execution)
        fixture.save()
        with self.assertRaisesRegex(ValueError,'exact first native SUCCESS'):
            continuation._native(fixture.root,node,failed=False,plan=dict(model='argon',effort='high'))

    def test_component_absence_and_single_attempt_do_not_change_old_sources(self):
        self.assertIsNone(continuation.load(self.root,None,record={},inputs={},source_policy={},
            condition='single_attempt',effective_scores={}))
        with self.assertRaisesRegex(ValueError,'does not backfill'):
            continuation.load(self.root,{},record={},inputs={},source_policy={},
                condition='single_attempt',effective_scores={})

    def test_legacy_sources_cannot_drop_proofs_or_borrow_another_original_record(self):
        node,_,_,_=self.source()
        manifest=dict(files={row['name']:row['evidence'] for row in node['files']})
        manifest['files']['Main.olean']=dict(bytes=1,sha256='a'*64)
        node['omitted_non_source_cache']=['Main.olean']
        files=continuation._legacy_file_inventory(self.root,node,manifest)
        self.assertEqual(set(files),{'Main.lean','alignment.json'})
        missing=copy.deepcopy(node);missing['files']=missing['files'][1:]
        with self.assertRaisesRegex(ValueError,'dropped original source'):
            continuation._legacy_file_inventory(self.root,missing,manifest)
        missing['omitted_non_source_cache'].append('Main.lean')
        with self.assertRaisesRegex(ValueError,'compiler caches'):
            continuation._legacy_file_inventory(self.root,missing,manifest)

        review=put(self.root,'original-formalization.json',b'original review bytes')
        original=dict(schema='math-gauge.result-record/v1',benchmark_version='0.6.0',record_id='fixture-record',
            model=dict(requested_label='fixture label'),formalization_review=dict(review,path='reviews/formalization.json'))
        public=copy.deepcopy(original);public['model']['display']='fixture-model'
        data=dict(public_base_record=put(self.root,'public-record.json',public),
            baseline=dict(original_formalization_review=review))
        args=dict(record=original,inputs=dict(model_label='fixture label'),
            selection=dict(model_id='fixture-model',record_id='fixture-record'))
        continuation._legacy_record_binding(self.root,data,**args)
        for field,value in [('model',dict(requested_label='other label',display='fixture-model')),
                            ('record_id','other-record'),('formalization_review',dict(original['formalization_review'],sha256='f'*64))]:
            changed=copy.deepcopy(public);changed[field]=value
            data['public_base_record']=put(self.root,'public-record.json',changed)
            with self.subTest(field=field),self.assertRaisesRegex(ValueError,'another model or original record'):
                continuation._legacy_record_binding(self.root,data,**args)

    def test_legacy_supplied_inputs_are_complete_unique_and_cannot_repair_proofs(self):
        node,seal,_,_=self.source()
        files=continuation._inventory(self.root,node,seal)
        request=dict(files=[dict(name='Frozen.lean',content='-- original public dependency\n'),
                            dict(name='source/chapter.md',content='Original chapter')])
        origin=put(self.root,'original-request.json',request)
        supplied=[dict(name=row['name'],evidence=put(self.root,'supplied/'+row['name'],row['content'].encode()),
                       origin_evidence=origin)for row in request['files']]
        node['runtime_supplied_inputs']=supplied
        kernel=dict(input_files_sha256={'Frozen.lean':supplied[0]['evidence']['sha256']})
        combined=continuation._legacy_supplied_inputs(self.root,node,copy.deepcopy(files),kernel,request)
        self.assertEqual(combined['Main.lean'][1],files['Main.lean'][1])
        for entries,error in [(supplied[:1],'every original frozen request'),(supplied+supplied[:1],'unique')]:
            node['runtime_supplied_inputs']=entries
            with self.subTest(error=error),self.assertRaisesRegex(ValueError,error):
                continuation._legacy_supplied_inputs(self.root,node,copy.deepcopy(files),kernel,request)
        malicious=dict(files=[dict(name='Main.lean',content='-- operator proof repair\n')])
        node['runtime_supplied_inputs']=[dict(name='Main.lean',
            evidence=put(self.root,'repair.lean',malicious['files'][0]['content'].encode()),origin_evidence=origin)]
        with self.assertRaisesRegex(ValueError,'overwrote an original legacy file'):
            continuation._legacy_supplied_inputs(self.root,node,copy.deepcopy(files),kernel,malicious)

    def test_empty_success_system_exclusion_is_neither_final_nor_parent(self):
        fixture=native_fixtures.AgyEvidenceTests();fixture.setUp();self.addCleanup(fixture.doCleanups)
        fixture.terminal['result'].update(response='',denied_actions=[dict(action='command',display_name='Bash')])
        terminal=fixture.put('terminal.json',fixture.terminal)
        seal=fixture.put('seal.json',dict(native_status='SUCCESS',normal_complete_delivery=False))
        retained=dict(original_terminal=terminal,original_seal=seal,
            original_result=fixture.put('physical-result.json',dict(normal_complete_delivery=False)),
            original_response=fixture.put('answer.md',b''),
            native_events=fixture.put('events.ndjson',(json.dumps(fixture.terminal)+'\n').encode()),
            visible_command_evidence=fixture.put('denial.json',dict(command='read frozen cache',denied=True)),
            supplied_lean_environment=fixture.put('lean-environment.json',dict(cache='/unreadable/public-cache')))
        receipt=dict(schema='math-gauge.c003-operational-exclusion/v1',version='0.1.0',phase='R1',physical_request=1,
            category='proven_system_configuration_failure',effective_attempt_consumed=False,workspace_used_as_parent=False,
            native_status_rewritten=False,normal_final_reconstructed=False,mathematical_quality_used_for_exclusion=False,
            **retained)
        entry=dict(receipt=fixture.put('exclusion.json',receipt),retained=retained)
        self.assertEqual(continuation._operational_exclusions(fixture.root,[entry],[]),{('R1',1)})
        self.assertEqual(json.loads(evidence_bytes(fixture.root,terminal))['result']['status'],'SUCCESS')
        for node,error in [(dict(phase='R1',physical_request_global=1),'selected final'),
                           (dict(phase='R2',parent_source_anchor_sha256=seal['sha256']),'selected selfcheck parent')]:
            with self.subTest(error=error),self.assertRaisesRegex(ValueError,error):
                continuation._operational_exclusions(fixture.root,[entry],[node])
        fixture.data.update(native_terminal_event=terminal,native_terminal_seal=seal,response=retained['original_response'])
        fixture.row['response']=retained['original_response'];fixture.save()
        with self.assertRaises(ValueError):
            native_fixtures.validate_delivery(fixture.root,fixture.row,evidence_bytes)

    def test_aggregate_progress_uses_highest_completed_native_body_without_editing_history(self):
        body=b'FULL\nOriginal final text\n'
        # Protobuf field20 -> field1, using the same decoder as retained recovery.
        nested=b'\x0a'+bytes([len(body)])+body
        payload=b'\xa2\x01'+bytes([len(nested)])+nested
        aggregate=b'Compiling file 1\nCompiling file 2\n{}\n'+body
        node=dict(phase='R1',native={'response':put(self.root,'aggregate.md',aggregate)},
            final_body=put(self.root,'native-final.md',body))
        step=put(self.root,'step.bin',payload)
        db_path=self.root/'original-native.db'
        db=sqlite3.connect(db_path)
        db.execute('CREATE TABLE trajectory_meta (trajectory_id TEXT,cascade_id TEXT)')
        db.execute('INSERT INTO trajectory_meta VALUES (?,?)',('synthetic-trajectory','synthetic-own-context'))
        db.execute('CREATE TABLE steps (idx INTEGER,step_type INTEGER,status INTEGER,step_payload BLOB)')
        db.executemany('INSERT INTO steps VALUES (?,?,?,?)',[(3,15,3,b'progress'),(7,15,3,payload)])
        db.commit();db.close()
        database=descriptor(self.root,db_path)
        inventory=dict(conversation_id='synthetic-own-context',complete_conversation_export=True,
            source_database=database,
            rows=[dict(idx=3,step_type=15,native_status_code=3,payload_sha256=hashlib.sha256(b'progress').hexdigest()),
                  dict(idx=7,step_type=15,native_status_code=3,payload_sha256=step['sha256'])],
            source_evidence=[database])
        extraction=dict(schema='math-gauge.normal-native-final-body-extraction/v1',version='0.1.0',phase='R1',
            conversation_id='synthetic-own-context',source_raw_bytes_rewritten=False,native_terminal_status='SUCCESS',
            selection='highest_completed_agent_response_index',aggregate_response=node['native']['response'],
            final_body=node['final_body'],selected_step_index=7,selected_step_payload=step,
            native_step_inventory=put(self.root,'step-inventory.json',inventory))
        node['final_body_extraction']=put(self.root,'extraction.json',extraction)
        self.assertEqual(continuation._final_body(self.root,node),body)
        self.assertEqual(evidence_bytes(self.root,node['native']['response']),aggregate)
        extraction['selected_step_index']=3
        node['final_body_extraction']=put(self.root,'extraction.json',extraction)
        with self.assertRaisesRegex(ValueError,'selected by content'):
            continuation._final_body(self.root,node)


class ContinuationScoringTests(unittest.TestCase):
    def setUp(self):
        self.fixture=current_record_fixtures.FreshRecordScoringTests();self.fixture.setUp()
        f=self.fixture
        self.review=copy.deepcopy(f.alignment)
        f.unavailable('MG-C003','delivery_failed')
        f.alignment['baseline'].update(source_kind='not_available',delivery_status='delivery_failed',
            source_sha256=None,delivery_verified=False)
        for item in f.alignment['baseline']['obligations']:item['complete']=None
        f.alignment['rounds']=[dict(round=n,snapshot=None,diagnosis=None) for n in (1,2,3)]
        self.policy=json.loads((REPO/'protocol/scoring-policy.json').read_bytes())
        self.bases={}
        # These base reports are synthetic. HCH02's reviewed task is deliberately
        # retained as a recognizable effective correction and must stay identical.
        for mode in ('capability','partial','strict'):
            base=f.score(mode)
            base.update(scoring_method_version='0.9.0',attempt_condition='nonlogical_retry_3',
                source_bindings={'selected_hch02_correction_sha256':'e'*64})
            chapter=next(t for t in base['tasks'] if t['case_id']=='MG-C003')
            chapter['submission_assessment']={'classification':'forced_content','active_final':False}
            base['tasks'][0]['private_review_details']={'case_id':'PRIVATE_CANARY_7CB1',
                'original_answer':'UNPUBLISHED_ANSWER_7CB1','path':'/private/source/CANARY_7CB1'}
            base['lean_formalization_breakdown']['fixture_correction_marker']='effective HCH02 source'
            self.bases[mode]=base
        self.review['baseline']['delivery_verified']=False
        # A failed A1 can begin with 24 correct obligations and be repaired in R1.
        for row in self.review['rounds']:
            for item in row['snapshot']['obligations']:item['complete']=True
            row['diagnosis'].update(claims_complete=True,accurate=True)
        self.normal=[dict(round=n,classification='active_final',scored_math_is_delivered=True,
            mathematical_source_sha256=r['snapshot']['source_sha256'])for n,r in enumerate(self.review['rounds'],1)]

    def selected(self, rounds=None):
        f=self.fixture
        payload=dict(model_label=f.inputs['model_label'],condition='nonlogical_retry_3',
            target_inputs_identity=identity(f.inputs),source_policy=f.policy,alignment_review=self.review,
            round_submissions=rounds or self.normal,
            effective_base_identities={m:identity(b)for m,b in self.bases.items()},
            effective_base_sha256={m:('a' if m=='capability'else'b'if m=='partial'else'c')*64 for m in self.bases},
            public_identity=dict(component=continuation.COMPONENT,source_component_sha256='d'*64,
                initial_answers_replaced=False,adopted_conditions=['nonlogical_retry_3']))
        return continuation.ContinuationInputs(json.dumps(payload).encode())

    def score(self,mode,rounds=None):
        return scoring.score_c003_continuation_overlay(self.bases[mode],self.policy,
            continuation=self.selected(rounds),inputs=self.fixture.inputs,mode=mode)

    def test_repaired_selfcheck_can_pass_without_replacing_failed_a1_or_hch02(self):
        before=copy.deepcopy(self.bases)
        for mode in self.bases:
            result=self.score(mode)
            self.assertTrue(result['strict_alignment_selfcheck']['strict_pass'])
            self.assertEqual(result['metrics']['lean-selfcheck']['exact'],100)
            self.assertEqual(result['tasks'],before[mode]['tasks'])
            chapter=next(t for t in result['tasks'] if t['case_id']=='MG-C003')
            self.assertEqual(chapter['completion']['exact'],0)
            self.assertFalse(chapter['strict_pass'])
            self.assertEqual(result['lean_formalization_breakdown'],before[mode]['lean_formalization_breakdown'])
            self.assertEqual(result['metrics']['lean-formalization'],before[mode]['metrics']['lean-formalization'])
            self.assertEqual(result['capacity'],before[mode]['capacity'])
            self.assertEqual(result['coverage'],before[mode]['coverage'])
            self.assertEqual(result['whole_task_counts'],before[mode]['whole_task_counts'])
            self.assertEqual(result['source_bindings']['selected_hch02_correction_sha256'],'e'*64)
            self.assertEqual(result['alignment_selfcheck']['metric']['coverage']['planned'],3)
            self.assertFalse(result['initial_answers_replaced'])
            projection=project_assessment_score(result)
            self.assertNotIn('tasks',projection)
            for canary in ('PRIVATE_CANARY_7CB1','UNPUBLISHED_ANSWER_7CB1','/private/source/CANARY_7CB1'):
                self.assertNotIn(canary,json.dumps(projection))
        self.assertEqual(before,self.bases)

    def test_new_round_failure_zeroes_that_rmc_round_and_fails_strict(self):
        rounds=copy.deepcopy(self.normal)
        rounds[1].update(classification='forced_content',reviewable_content_verified=True,scored_math_is_delivered=False)
        self.review['rounds'][1]['snapshot']['delivery_verified']=False
        rounds[2]={'round':3,'classification':'not_run'}
        self.review['rounds'][2].update(snapshot=None,diagnosis=None)
        rmc=self.score('partial',rounds)
        mc=self.score('capability',rounds)
        self.assertEqual(rmc['alignment_selfcheck']['rounds'][1]['score']['exact'],0)
        self.assertEqual(mc['alignment_selfcheck']['rounds'][1]['score']['exact'],100)
        self.assertIsNone(rmc['metrics']['lean-selfcheck']['exact'])
        self.assertAlmostEqual(rmc['metrics']['lean-selfcheck']['lower'],100/3)
        self.assertAlmostEqual(rmc['metrics']['lean-selfcheck']['upper'],200/3)
        self.assertFalse(self.score('strict',rounds)['strict_alignment_selfcheck']['strict_pass'])

    def test_record_condition_and_effective_correction_cannot_be_swapped(self):
        selected=self.selected()
        changed=copy.deepcopy(self.fixture.inputs);changed['model_label']='other'
        with self.assertRaises(ValueError):selected.for_score(changed,condition='nonlogical_retry_3')
        with self.assertRaises(ValueError):selected.for_score(self.fixture.inputs,condition='single_attempt')
        base=copy.deepcopy(self.bases['partial'])
        base['source_bindings'].pop('selected_hch02_correction_sha256')
        with self.assertRaisesRegex(ValueError,'effective score source'):
            scoring.score_c003_continuation_overlay(base,self.policy,continuation=selected,
                inputs=self.fixture.inputs,mode='partial')

    def test_no_component_legacy_outputs_remain_exact_and_parent_check_stays_strict(self):
        spec=importlib.util.spec_from_file_location('math_gauge._unchanged_scoring',REPO/'math_gauge/scoring.py')
        legacy=importlib.util.module_from_spec(spec);spec.loader.exec_module(legacy)
        f=self.fixture
        for mode in self.bases:
            kwargs=dict(formalization_review=f.formal,assessment_policy=f.data['assessment_policy'],
                strict_policy=f.data['strict_policy'],mode=mode,capability_policy=f.capability if mode=='capability'else None)
            old=legacy.score_assessment_record_inputs(f.inputs,f.alignment,f.policy,**kwargs)
            new=scoring.score_assessment_record_inputs(f.inputs,f.alignment,f.policy,**kwargs)
            self.assertEqual(json.dumps(old,sort_keys=True),json.dumps(new,sort_keys=True))
        # Restore an ordinary available source only for this negative old gate.
        other=current_record_fixtures.FreshRecordScoringTests();other.setUp()
        broken=copy.deepcopy(other.alignment);broken['baseline']['source_sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'alignment-study parent'):
            scoring.score_assessment_record_inputs(other.inputs,broken,other.policy,
                formalization_review=other.formal,assessment_policy=other.data['assessment_policy'],
                strict_policy=other.data['strict_policy'])
