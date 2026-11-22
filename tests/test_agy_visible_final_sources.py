"""Focused source-bound admission fixtures; no native/model/network/collector."""
import copy
import hashlib
import json
from pathlib import Path
import sqlite3
import tempfile
import unittest
import math_gauge
from unittest.mock import patch

from math_gauge.agy_evidence import validate_delivery, validate_failure
from math_gauge.agy_native_sources import SCHEMA, INPUT_SCHEMA, validate_projection
from math_gauge.catalog import candidate_message
from math_gauge.records import descriptor, evidence_bytes, load_manuscript_completion_inputs
import test_agy_native_evidence as legacy


def sha(raw): return hashlib.sha256(raw).hexdigest()
def varint(value):
    out=bytearray()
    while value>127: out.append((value&127)|128);value>>=7
    out.append(value);return bytes(out)
def field(key, value):return varint((key<<3)|2)+varint(len(value))+value


class VisibleFinalSourcesTests(unittest.TestCase):
    def put(self, name, obj):
        raw=obj if isinstance(obj,bytes) else (json.dumps(obj,ensure_ascii=False)+'\n').encode()
        p=self.root/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)
        return descriptor(self.root,p)
    def document(self, ref):return json.loads(evidence_bytes(self.root,ref))
    def setUp(self):
        b=legacy.AgyEvidenceTests('test_exact_native_success_survives_failed_cli_cleanup');b.setUp()
        self.addCleanup(b.doCleanups);self.root=b.root;self.b=b
        self.data=b.data;self.row=b.row;self.execution=b.execution
        self.attempt='/original/batch/attempts/S/physical-1'
        self.conversation='own-conversation'
        task=b'Original proof \xce\xb1'
        request=dict(schema='math-gauge.request/v1',case_id='S',task=task.decode(),instruction='Read the original task',files=[])
        payload=candidate_message(request).encode()
        self.logical_request=request
        self.data['schema']=SCHEMA
        self.data.update(physical_request=1,original_attempt=self.attempt)
        self.row['response']=self.data['response']=self.put('true-final.md','Final proof β.'.encode())
        self.final=evidence_bytes(self.root,self.row['response'])
        self.data['input_projection']=self.projection([dict(role='user',content=payload.decode())])
        p=self.data['input_projection']
        p.update(original_task=self.put('original-task.md',task),logical_request=self.put('logical-request.json',request),
                 candidate_message=self.put('candidate-message.md',payload),native_header=self.data['candidate_input'],provided_files=[])
        manifest=dict(cases={'S':dict(original_payload=p['candidate_message'],native_header=p['native_header'],original_candidate_message_sha256=sha(payload))})
        p['exact_input_manifest']=self.put('exact-manifest.json',manifest)
        p['projection_preflight']=self.put('projection-preflight.json',dict(schema='math-gauge.exact-original-A1-input-preflight/v1',
            case_id='S',original_payload=p['candidate_message'],native_header=p['native_header'],index=p['attachment_index'],
            manifest=p['exact_input_manifest'],mathematical_input_bytes_unchanged=True,reviewer_feedback_included=False,candidate_calls=0))
        p['operator_record']=self.put('operator-record.json',dict(case_id='S',candidate_message_sha256=sha(payload),
            request_sha256=sha(json.dumps(request,ensure_ascii=False,sort_keys=True).encode())))
        self.execution.update(requested_model='neon',requested_effort='xhigh',process_identity_protocol='pid+lstart-UTC/v1')
        self.execution['parent_identity'].update(executable_sha256='1'*64,birth_identity='2026-11-21T00:00:00Z',
            process_identity_verified_before_and_after_policy=True,policy_evidence=self.attempt+'/session/runtime/parent-probe.json')
        self.data['local_tools']['process_checks'][0]['original_path']=self.execution['parent_identity']['policy_evidence']
        probe=self.document(self.data['local_tools']['process_checks'][0]['evidence']);probe['kind']='live-pid-policy-query'
        self.data['local_tools']['process_checks'][0]['evidence']=self.put('parent-probe-v2.json',probe)
        self.data['local_tools']['prelaunch_birth_snapshot']=self.put('birth-snapshot.json',dict(schema='math-gauge.process-birth-snapshot/v1',rows=[]))
        self.execution['prelaunch_process_snapshot']=self.data['local_tools']['prelaunch_birth_snapshot']
        self.data['local_tools']['network_probe']=self.put('network-v2.json',dict(kind='actual-network-connect',passed=True,result=dict(passed=True,errno=1)))
        self.data['local_tools']['native_control']=self.control()
        plan=self.document(self.data['native_plan']);plan.update(model='neon',effort='xhigh',run_dir=self.attempt+'/session',cwd=self.attempt+'/session/work',stdin_file=self.attempt+'/session/runtime/request.ndjson')
        self.execution['cwd']=plan['cwd'];self.data['native_plan']=self.put('plan-v2.json',plan)
        self.data['acquisition_freeze']=self.put('acquisition-freeze.json',dict(benchmark_version='1.0.0',utc='2026-11-21T00:00:00Z',
            native_binary_sha256='1'*64,requested_model='neon',requested_effort='xhigh',source_bindings=[p['exact_input_manifest'],
            self.document(self.data['local_tools']['native_control'])['original_validation']]))
        self.data['dispatch']=self.put('dispatch-v2.json',dict(case_id='S',physical_request_number=1,outer_budget_seconds=10,
            freeze_sha256=self.data['acquisition_freeze']['sha256'],utc='2026-11-21T00:01:00Z'))
        self.seal=dict(native_status='SUCCESS',normal_complete_delivery=True,trigger='first-native-terminal',elapsed_seconds=3,deadline_seconds=10,work=[])
        self.result=dict(schema='math-gauge.synthetic-new-model-result/v1',case_id='S',physical_request_number=1,
            normal_complete_delivery=True,artifact_checks_passed=True,tool_mismatch=None,requested_model='neon',requested_effort='xhigh',freeze_sha256=self.data['acquisition_freeze']['sha256'])
        header=evidence_bytes(self.root,self.data['candidate_input'])
        self.payload=field(20,field(1,self.final))+field(21,b'OPAQUE: not decoded')
        self.dbrows=[(0,14,3,0,field(19,field(2,header)),0),(1,15,3,0,field(20,field(1,b'earlier draft')),0),(2,15,3,0,self.payload,0)]
        self.database()
        self.aggregate(b'Aggregate prefix\n'+self.final+b'\n')
    def projection(self, messages, phase='A1'):
        rows=[];sources=[]
        for i,m in enumerate(messages):
            raw=m['content'].encode();cut=max(1,len(raw)//2)
            while cut<len(raw) and raw[cut]&0xc0==0x80:cut+=1
            parts=[]
            for j,x in enumerate([raw[:cut],raw[cut:]]):
                name=f'{i:02d}-{j:02d}.txt';ref=self.put('fragments/'+name,x)
                parts.append(dict(file=name,bytes=len(x),sha256=sha(x)));sources.append(dict(name=name,evidence=ref))
            rows.append(dict(message_index=i,role=m['role'],utf8_bytes=len(raw),sha256=sha(raw),parts=parts))
        serialized=json.dumps(dict(messages=messages),ensure_ascii=False,indent=2)
        if phase!='A1':serialized='请按以下完整消息的角色与顺序继续对话，回答最后一条用户消息。\n\n'+serialized
        full=self.put('fragments/full.json',serialized.encode())
        sources.append(dict(name='full.json',evidence=full))
        index=dict(schema='math-gauge.exact-own-visible-history-attachments/v1',messages=rows,
                   full_serialized_history=dict(file='full.json',bytes=full['bytes'],sha256=full['sha256']))
        return dict(schema=INPUT_SCHEMA,reviewer_feedback_included=False,attachment_index=self.put('fragments/index.json',index),attachment_sources=sources)
    def control(self):
        positive=dict(passed=True,real_model_service_calls=0,no_candidate_mathematics_submitted=True,
            execution=dict(kind='non_math_canary',requested_model='old-argon',requested_effort='high',result_status='SUCCESS',tool_mismatch=None,
                           parent_identity=dict(executable_sha256='1'*64)),
            report=dict(all_denials_and_allows_passed=True,work_roundtrip=True,tool_network_denied=True,source_bytes_read=0))
        self.positive=positive
        negative=dict(passed=False,real_model_service_calls=0,execution=dict(requested_model='old-argon'))
        denial=dict(schema='math-gauge.offline-native-bypass-denial/v1',passed=True,real_model_service_calls=0,
            native_unsandboxed_execution_refused=True,native_terminal_response_was_empty=True,marker_present=False,
            normal_final_not_claimed_for_negative_control=True)
        values={'positive':positive,'negative':negative,'denial':denial,'previous':dict(passed=True,real_model_service_calls=0)}
        refs={k:self.put('control/'+k+'.json',v) for k,v in values.items()}
        validation=dict(schema='math-gauge.native-offline-capability-controls/v1',passed=True,real_model_service_calls=0,
            positive_control=refs['positive'],original_paired_control=refs['negative'],negative_control=refs['denial'],original_validation=refs['previous'],
            original_negative_empty_native_final_preserved=True,new_per_session_open_network_probes_required=True,
            reused_for_same_binary_different_model=True,bypass_negative_control=dict(passed=True,original_control_result_preserved=True))
        q=dict(schema='math-gauge.agy-offline-control-qualification/v1',version='0.1.0',post_observation=True,source_raw_bytes_rewritten=False,
            scope='native_local_file_and_network_boundary_only',backend_model_attested=False,old_model_labels_preserved=True,
            real_model_service_calls=0,native_binary_sha256='1'*64,original_validation=self.put('control/validation.json',validation),
            sources=[dict(original_path=x['path'],evidence=x) for x in refs.values()])
        return self.put('control/qualification.json',q)
    def database(self):
        path=self.root/'db.sqlite'
        if path.exists():path.unlink()
        c=sqlite3.connect(path)
        c.execute('create table trajectory_meta(trajectory_id text,cascade_id text)')
        c.execute('insert into trajectory_meta values(?,?)',('original-trajectory',self.conversation))
        c.execute('create table steps(idx integer,step_type integer,status integer,has_subtrajectory integer,step_payload blob,step_format integer)')
        c.executemany('insert into steps values(?,?,?,?,?,?)',self.dbrows);c.commit();c.close()
        db=descriptor(self.root,path)
        original=dict(db,path=self.attempt+'/session/state/antigravity-cli/conversations/'+self.conversation+'.db')
        copied=dict(db,path=self.attempt+'/sealed/native-state/conversations/'+self.conversation+'.db')
        snapshot=dict(schema='math-gauge.stopped-native-database-snapshot/v1',stable_before_after_copy=True,source_files_unchanged=True,
                      files=[dict(source=original,sealed_copy=copied)])
        snapshot=self.put('database-snapshot.json',snapshot)
        self.seal['native_database_snapshot_sha256']=snapshot['sha256']
        inventory=dict(schema='math-gauge.native-sqlite-step-inventory/v1',conversation_id=self.conversation,complete_conversation_export=True,
            source_database=db,source_evidence=[db],source_database_requires_WAL=False,
            rows=[dict(idx=i,step_type=t,native_status_code=s,native_status='completed' if s==3 else 'other',has_subtrajectory=bool(h),step_format=f,payload_sha256=sha(p)) for i,t,s,h,p,f in self.dbrows])
        inv=self.put('inventory.json',inventory);selected=self.put('selected.pb',self.payload)
        self.data['normal_final_source']=dict(step_inventory=inv,selected_payload=selected,database_snapshot=snapshot,
            database_files=[dict(name=self.conversation+'.db',evidence=db)])
        self.witness=dict(schema='math-gauge.normal-native-final-body-extraction/v1',source_raw_bytes_rewritten=False,
            original_attempt=self.attempt,phase='A1',conversation_id=self.conversation,native_terminal_status='SUCCESS',
            selection='highest_completed_agent_response_index',protobuf_field='20.1',hidden_reasoning_decoded=False,
            legacy_v0_1_0_admission_compatible=True,WAL_dependent_formal_admission_requires_explicit_adapter=False,
            source_origin='same_physical_attempt_stable_sealed_DB_WAL_SHM',live_native_database_read=False,other_conversations_read=False,
            native_step_inventory=inv,selected_step_payload=selected,native_database_snapshot=snapshot,final_body=self.data['response'],
            native_final_sha256=self.data['response']['sha256'],native_final_bytes=self.data['response']['bytes'],selected_step_index=2)
    def aggregate(self,raw):
        terminal=dict(event='result',result=dict(status='SUCCESS',conversation_id=self.conversation,response=raw.decode()))
        self.terminal=terminal;self.data['native_terminal_event']=self.put('terminal-v2.json',terminal)
        self.data['native_events']=self.put('events-v2.ndjson',(json.dumps(terminal)+'\n').encode())
        self.execution['artifact_hashes']['output/events.ndjson']=self.data['native_events']['sha256']
        self.data['native_execution']=self.put('execution-v2.json',self.execution)
        self.data['aggregate_response']=self.put('aggregate.md',raw)
        self.seal.update(raw_terminal_sha256=self.data['native_terminal_event']['sha256'],answer_sha256=sha(raw),native_return_sha256=sha(raw))
        self.data['native_terminal_seal']=self.put('seal-v2.json',self.seal)
        self.result['native_terminal']=self.seal
        self.data['execution_result']=self.put('result-v2.json',self.result)
        self.witness.update(raw_result_response_sha256=sha(raw),raw_result_response_bytes=len(raw),
            exact_native_final_is_substring_at=raw.find(self.final),aggregate_response_equal_final_body=raw==self.final)
        self.data['normal_final_source']['extraction']=self.put('extraction.json',self.witness)
        self.save()
    def save(self):self.row['agy_native_evidence']=self.put('v2-admission.json',self.data)
    def validate(self):return validate_delivery(self.root,self.row,evidence_bytes)
    def test_highest_final_not_aggregate_and_cleanup_preserved(self):
        before=evidence_bytes(self.root,self.data['local_tools']['native_control'])
        result=self.validate();self.assertEqual(result['text'],self.final.decode())
        self.assertEqual(result['cli_exit_code'],-9)
        self.assertNotEqual(result['aggregate_response_sha256'],result['selected_visible_final_sha256'])
        self.assertEqual(before,evidence_bytes(self.root,self.data['local_tools']['native_control']))
    def test_plus_LF_aggregate_is_normal_without_trimming_final(self):
        self.aggregate(self.final+b'\n');self.assertEqual(self.validate()['text'].encode(),self.final)
    def test_native_error_cannot_be_promoted_by_readable_DB(self):
        terminal=copy.deepcopy(self.terminal);terminal['result']['status']='ERROR'
        self.data['native_terminal_event']=self.put('error-terminal.json',terminal)
        self.data['native_events']=self.put('error-events.ndjson',(json.dumps(terminal)+'\n').encode())
        self.execution['artifact_hashes']['output/events.ndjson']=self.data['native_events']['sha256']
        self.data['native_execution']=self.put('error-execution.json',self.execution);self.save()
        with self.assertRaises(ValueError):self.validate()
    def test_exact_deadline_is_not_a_timely_final(self):
        self.seal['elapsed_seconds']=10;self.aggregate(self.final+b'\n')
        with self.assertRaisesRegex(ValueError,'timely'):self.validate()
    def test_cross_physical_or_wrong_DB_user_is_rejected(self):
        self.data['physical_request']=2;self.save()
        with self.assertRaises(ValueError):self.validate()
        self.data['physical_request']=1
        self.dbrows[0]=(0,14,3,0,field(19,field(2,b'foreign request')),0)
        self.database();self.aggregate(self.final+b'\n')
        with self.assertRaisesRegex(ValueError,'user19.2'):self.validate()
    def test_earlier_completed_step_is_not_a_final_fallback(self):
        self.witness['selected_step_index']=1
        self.data['normal_final_source']['extraction']=self.put('earlier-extraction.json',self.witness);self.save()
        with self.assertRaisesRegex(ValueError,'highest completed'):self.validate()
    def test_WAL_dependent_witness_needs_distinct_adapter(self):
        self.witness['legacy_v0_1_0_admission_compatible']=False
        self.data['normal_final_source']['extraction']=self.put('wal-extraction.json',self.witness);self.save()
        with self.assertRaisesRegex(ValueError,'immutable-main'):self.validate()
    def test_one_byte_projection_change_and_false_logical_task_fail(self):
        p=self.data['input_projection'];p['original_task']=self.put('different-task.md',b'Changed task');self.save()
        with self.assertRaisesRegex(ValueError,'original mathematical task'):self.validate()
        p['original_task']=self.put('original-task.md',b'Original proof \xce\xb1')
        p['attachment_sources'][0]['evidence']=self.put('changed-fragment.txt',b'Changed fragment');self.save()
        with self.assertRaises(ValueError):self.validate()
    def test_self_consistent_fullcopy_cannot_disagree_with_fragment_history(self):
        p=self.data['input_projection']
        index=self.document(p['attachment_index'])
        wrong=json.dumps(dict(messages=[dict(role='user',content='A different full history')]),ensure_ascii=False,indent=2).encode()
        changed=self.put('different-full.json',wrong)
        name=index['full_serialized_history']['file']
        index['full_serialized_history']=dict(file=name,bytes=changed['bytes'],sha256=changed['sha256'])
        p['attachment_sources'][-1]=dict(name=name,evidence=changed)
        p['attachment_index']=self.put('different-full-index.json',index)
        self.save()
        with self.assertRaisesRegex(ValueError,'Complete serialized visible history'):
            self.validate()
    def test_binary_reuse_and_birth_probe_are_required(self):
        self.execution['parent_identity']['executable_sha256']='2'*64
        self.data['native_execution']=self.put('other-execution.json',self.execution);self.save()
        with self.assertRaisesRegex(ValueError,'binary'):self.validate()
        self.execution['parent_identity']['executable_sha256']='1'*64
        self.execution['parent_identity'].pop('birth_identity')
        self.data['native_execution']=self.put('nobirth-execution.json',self.execution);self.save()
        with self.assertRaisesRegex(ValueError,'birth/probe'):self.validate()
    def test_missing_session_network_probe_is_not_replaced_by_control(self):
        self.data['local_tools']['network_probe']=self.put('not-probed.json',dict(passed=False));self.save()
        with self.assertRaisesRegex(ValueError,'per-session|Actual AGY'):self.validate()
    def test_negative_original_passed_false_must_not_be_rewritten(self):
        q=self.document(self.data['local_tools']['native_control']);v=self.document(q['original_validation'])
        bad=self.put('control/changed-negative.json',dict(passed=True,real_model_service_calls=0))
        v['original_paired_control']=bad;q['original_validation']=self.put('control/changed-validation.json',v)
        q['sources'].append(dict(original_path=bad['path'],evidence=bad))
        self.data['local_tools']['native_control']=self.put('control/changed-qualification.json',q);self.save()
        from math_gauge.agy_control_evidence import validate_control
        with self.assertRaisesRegex(ValueError,'negative outcome'):
            validate_control(self.root,self.data['local_tools']['native_control'],self.execution,evidence_bytes)
    def test_normal_v2_does_not_enter_legacy_failure_admission(self):
        with self.assertRaises(ValueError):validate_failure(self.root,self.row,evidence_bytes)
    def test_prescribed_history_uses_truefinal_not_aggregate(self):
        parent_ref=self.row['agy_native_evidence'];parent=copy.deepcopy(self.data)
        parent['native_terminal_seal']=self.put('parent-seal.json',dict(work=[]))
        parent_ref=self.put('parent-admission.json',parent)
        neutral='Check the same task without feedback.'
        expected=[dict(role='user',content='Original visible input'),dict(role='assistant',content=self.final.decode()),dict(role='user',content=neutral)]
        p=copy.deepcopy(self.data['input_projection']);p.update(self.projection(expected,phase='R1'))
        header=self.put('round-header.md',b'OWN VISIBLE HISTORY')
        p.update(native_header=header,immediate_parent_native_evidence=parent_ref,neutral_invitation=self.put('neutral.md',neutral.encode()),
            projected_request=self.put('round-projection.json',dict(case_id='S',round=1,messages=expected,candidate_user_message='OWN VISIBLE HISTORY')),
            projection_preflight=self.put('round-preflight.json',dict(round=1,parent_attempt=self.attempt,parent_seal=parent['native_terminal_seal'],
                reviewer_feedback_included=False,artifact_checks_passed=True,frozen_inputs_unchanged=True,all_original_messages_reconstruct_exactly=True,carried_files=[])))
        projected=self.document(p['projected_request'])
        frozen=dict(parent_attempt=self.attempt,parent_seal=parent['native_terminal_seal'],reviewer_feedback_included=False,
            projected_request_sha256=sha(json.dumps(projected,ensure_ascii=False,sort_keys=True).encode()),
            candidate_message_sha256=header['sha256'],full_serialized_history_sha256=self.document(p['attachment_index'])['full_serialized_history']['sha256'])
        round_freeze=self.put('round-freeze.json',frozen)
        plan=self.put('selfcheck-plan.json',dict(neutral_prompt_sha256=p['neutral_invitation']['sha256']))
        pre=self.document(p['projection_preflight']);pre.update(round_freeze_sha256=round_freeze['sha256'],plan_sha256=plan['sha256'])
        p['projection_preflight']=self.put('round-preflight.json',pre)
        data=dict(self.data,phase='R1',candidate_input=header,input_projection=p,round_freeze=round_freeze,selfcheck_plan=plan)
        with patch('math_gauge.agy_evidence.validate_delivery',return_value=dict(input_messages=expected[:1],text=self.final.decode())):
            self.assertEqual(validate_projection(self.root,data,evidence_bytes),expected)
            wrong=copy.deepcopy(expected);wrong[1]['content']='Aggregate prefix\n'+self.final.decode()
            p.update(self.projection(wrong,phase='R1'))
            with self.assertRaisesRegex(ValueError,'truefinal parent chain'):validate_projection(self.root,data,evidence_bytes)
    def test_manuscript_uses_common_visible_final_gate_without_old_model_schema(self):
        policy=copy.deepcopy(json.loads((Path(math_gauge.__file__).resolve().parents[1]/'protocol/scoring-policy.json').read_bytes())['manuscript_completion'])
        policy.update(version='0.1.0',public_cases=0,public_case_ids=[],private_cases=1,families=1)
        task=self.data['input_projection']['original_task']
        contract=self.put('manuscript-contract.json',dict(id='S',kind='research_exploration',dimensions=[dict(id='model',points=100)]))
        rubric=self.put('manuscript-rubric.json',dict(task_sha256=task['sha256'],post_observation=True,criteria=[dict(id='model',points=100)]))
        case=dict(case_id='S',family_id='synthetic',component='manuscript-completion',source_visibility='private',contract_kind='research_exploration',
            task_kind='written',criteria=[dict(criterion_id='model',points=100)],total_weight=100,original_task=task,task_sha256=task['sha256'],
            contract=contract,contract_sha256=contract['sha256'],reference=self.put('reference.md',b'synthetic reference'),source_rubric=rubric)
        review=self.put('review.json',dict(schema='math-gauge.manuscript-completion-review/v1',case_id='S',stage='A1',reviewer_kind='ai',human_review='pending',
            formal_comparison_eligible=False,answer_sha256=self.row['response']['sha256'],rubric_sha256=rubric['sha256'],score=100,strict_pass=True,
            criteria=[dict(id='model',max_points=100,points=100,decision='full',evidence=[])]))
        row=dict(self.row,slot_id='S:A1',attempt_label='A1',status='response_received_execution_unverified',points=100,complete=True,
            execution=self.data['native_execution'],execution_result=self.data['execution_result'],execution_plan=self.data['native_plan'],
            original_input=task,candidate_input=self.data['candidate_input'],native_request=self.data['native_request'],native_events=self.data['native_events'],
            native_capability_control=self.data['local_tools']['native_control'],review=review,selected_physical_request=1,effective_model_attempt=1)
        attempt=dict(physical_request=1,execution=row['execution'],native_events=row['native_events'],response=row['response'],
            first_complete_answer=True,excluded_pure_system_failure=False,effective_model_attempt=1)
        row['physical_request_ledger']=self.put('history.json',dict(selected_physical_request=1,effective_model_attempt=1,first_complete_answer_selected=True,attempts=[attempt]))
        inputs=dict(schema='math-gauge.manuscript-completion-inputs/v1',benchmark_version='0.6.0',model_label='Synthetic native',attempt_labels=['A1'],
            policy=policy,human_review='pending',formal_comparison_eligible=False,case_index=[case],slots=[row])
        record=dict(manuscript_completion_inputs=self.put('manuscript-inputs.json',inputs))
        self.assertEqual(load_manuscript_completion_inputs(self.root,record)['slots'][0]['points'],100)
        changed=self.put('other-original.md',b'Different original task')
        case.update(original_task=changed,task_sha256=changed['sha256'],source_rubric=self.put('other-rubric.json',dict(task_sha256=changed['sha256'],post_observation=True,criteria=[dict(id='model',points=100)])))
        record['manuscript_completion_inputs']=self.put('other-inputs.json',inputs)
        with self.assertRaisesRegex(ValueError,'original source'):load_manuscript_completion_inputs(self.root,record)

if __name__=='__main__':unittest.main()
