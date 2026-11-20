"""Opted-in companions must belong to the exact selected native terminal."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from math_gauge.manuscript_surplus import delivery_context, descriptor


class RecordDeliveryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.archive = self.root / 'archive'
        self.cid = 'manuscript-case'
        self.session = Path('sessions/manuscript-case/physical-1')
        self.body = b'An explicitly delivered complete mathematical argument.'
        self.answer = b'Read [the argument](argument.md).'
        self.artifact = self.put(self.session/'terminal-output-sealed/artifacts/argument.md', self.body)
        self.response = self.put(self.session/'output/response.md', self.answer)
        events = [dict(type='item.completed',item=dict(type='agent_message',text=self.answer.decode())),
                  dict(type='turn.completed',usage={})]
        events_raw = b''.join((json.dumps(e)+'\n').encode() for e in events)
        native = self.put(self.session/'output/events.ndjson',events_raw)
        execution = self.put(self.session/'runtime/execution.json',{})
        collection = self.put(self.session/'runtime/collection.json',dict(case_id=self.cid,
            normal_final_locked=True,qualified_delivery=True,native_terminal_completed=True,
            physical_attempt=1,response_sha256=self.response['sha256']))
        observation = self.put(self.session/'runtime/terminal-output-observation.json',dict(
            schema='math-gauge.first-terminal-output-observation/v1',session=self.session.as_posix(),
            native_event=events[-1],native_events_prefix_bytes=len(events_raw),
            native_events_prefix_sha256=hashlib.sha256(events_raw).hexdigest(),
            files=[dict(filename='argument.md',bytes=len(self.body),sha256=self.artifact['sha256'],
                original_relative_path='output/artifacts/argument.md',
                snapshot_relative_path='terminal-output-sealed/artifacts/argument.md')]))
        result = self.put('result.json',dict(schema='math-gauge.independent-idea-native-result/v1',
            original_collection=collection,original_output_observation=observation))
        self.selected = dict(case_id=self.cid,response=self.response,native_events=native,
            execution=execution,execution_result=result,selected_physical_request=1)
        self.component = dict(slots=[self.selected])
        self.inputs = self.put('inputs.json',self.component)
        self.record = dict(manuscript_completion_inputs=self.inputs,records=[dict(
            id=self.cid+':A1',case_id=self.cid,kind='independent',parent_id=None,response=self.response,
            artifacts=[self.artifact],source=dict(native_events=native,native_execution=execution,
            collection=collection,selected_physical_request=1))])
        self.context = dict(record=self.root_ref(self.put('record.json',self.record)),
            inputs=self.root_ref(self.inputs),cases={self.cid:dict(source_status='reviewed',
                response_sha256=self.response['sha256'],documents=[dict(role='response',**self.root_ref(self.response))])})
        self.loader = patch('math_gauge.records.load_manuscript_completion_inputs',return_value=self.component)
        self.loader.start();self.addCleanup(self.loader.stop)

    def put(self,path,value):
        path=self.archive/path;path.parent.mkdir(parents=True,exist_ok=True)
        path.write_bytes(value if isinstance(value,bytes) else (json.dumps(value)+'\n').encode())
        return descriptor(path,self.archive)

    def root_ref(self,item):
        return dict(item,path='archive/'+item['path'])

    def refresh_record(self):
        self.context['record']=self.root_ref(self.put('record.json',self.record))

    def extended(self):
        return delivery_context(self.root,self.context,'all_bound_additional_deliveries')

    def test_named_terminal_artifact_is_added_without_mutating_default_inventory(self):
        before=deepcopy(self.context)
        self.assertIs(delivery_context(self.root,self.context),self.context)
        result=self.extended()
        self.assertEqual(self.context,before)
        self.assertEqual(len(result['cases'][self.cid]['documents']),2)
        self.assertEqual(result['cases'][self.cid]['documents'][-1]['sha256'],self.artifact['sha256'])

    def test_unnamed_artifact_is_rejected(self):
        item=self.put(self.session/'terminal-output-sealed/artifacts/unmentioned.md',self.body)
        result=json.loads((self.archive/self.selected['execution_result']['path']).read_bytes())
        obs_ref=result['original_output_observation']
        obs=json.loads((self.archive/obs_ref['path']).read_bytes())
        obs['files'][0].update(filename='unmentioned.md',
            original_relative_path='output/artifacts/unmentioned.md',
            snapshot_relative_path='terminal-output-sealed/artifacts/unmentioned.md')
        result['original_output_observation']=self.put(self.session/'runtime/terminal-output-observation.json',obs)
        self.selected['execution_result']=self.put('result.json',result)
        self.record['records'][0]['artifacts']=[item];self.refresh_record()
        with self.assertRaisesRegex(ValueError,'not named'):self.extended()

    def test_older_collector_without_explicit_normal_lock_keeps_old_inventory(self):
        source=self.record['records'][0]['source']
        old=json.loads((self.archive/source['collection']['path']).read_bytes())
        old.pop('normal_final_locked')
        source['collection']=self.put(self.session/'runtime/collection.json',old)
        result=json.loads((self.archive/self.selected['execution_result']['path']).read_bytes())
        result['original_collection']=source['collection']
        self.selected['execution_result']=self.put('result.json',result)
        self.refresh_record()
        self.assertEqual(self.extended(),self.context)

    def test_artifact_from_another_case_or_attempt_is_rejected(self):
        for other in ['sessions/other/physical-1','sessions/manuscript-case/physical-2']:
            with self.subTest(other=other):
                item=self.put(Path(other)/'terminal-output-sealed/artifacts/argument.md',self.body)
                self.record['records'][0]['artifacts']=[item];self.refresh_record()
                with self.assertRaisesRegex(ValueError,'terminal output seal'):self.extended()

    def test_changed_artifact_bytes_or_descriptor_hash_are_rejected(self):
        self.record['records'][0]['artifacts'][0]=dict(self.artifact,sha256='0'*64)
        self.refresh_record()
        with self.assertRaises(ValueError):self.extended()
        self.record['records'][0]['artifacts']=[self.artifact];self.refresh_record()
        (self.archive/self.artifact['path']).write_bytes(b'changed after terminal')
        with self.assertRaises(ValueError):self.extended()

    def test_another_cases_collection_is_rejected(self):
        source=self.record['records'][0]['source']
        value=json.loads((self.archive/source['collection']['path']).read_bytes());value['case_id']='another-case'
        collection=self.put(self.session/'runtime/collection.json',value);source['collection']=collection
        result=json.loads((self.archive/self.selected['execution_result']['path']).read_bytes())
        result['original_collection']=collection;self.selected['execution_result']=self.put('result.json',result)
        self.refresh_record()
        with self.assertRaisesRegex(ValueError,'normal-final collection'):self.extended()


if __name__=='__main__':unittest.main()
