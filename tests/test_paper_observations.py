"""Returned-paper evidence stays separate from runtime and native records."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

import test_native_observations as native_fixture
from math_gauge import paper_observations as paper
from math_gauge.records import descriptor, selected_cli_records, selected_paper_records
from math_gauge.scoring import score_paper_observation

ROOT = Path(__file__).resolve().parents[1]


class PaperObservationTests(unittest.TestCase):
    def fixture(self):
        data, policy = native_fixture.NativeHarnessTests().fixture()
        catalog = json.loads((ROOT / 'cases/catalog.json').read_bytes())['entries']
        categories = {'proofs': 'written-argument', 'answer-review': 'argument-review'}
        public = {}
        for entry in catalog:
            public.setdefault(categories.get(entry['category'], entry['category']), []).append(entry['case_id'])
        claims = {r['case_id']: r for r in data['claim_review']['cases']}
        for category in public:
            rows = [r for r in data['tasks'] if r['subcategory'] == category]
            for index, task in enumerate(rows):
                original = task['case_id']
                cid = public[category][index] if index < len(public[category]) else 'PRIVATE-' + original
                task.update(case_id=cid, slot_id=cid + ':A1', visibility='public' if cid in public[category] else 'private',
                            status='reviewed', attempts=[dict(attempt=1, status='delivered', reason=None)])
                claims[original]['case_id'] = cid
                if task.get('strict_completion_case'):
                    case = task['strict_completion_case']
                    case['case_id'] = case['strict_completion_policy']['case_id'] = cid
                    task['strict_completion_review']['case_id'] = cid
        data.update(schema=paper.MATH_SCHEMA, version=paper.VERSION, runtime_evidence_verified=False, sources=[])
        for key in ('source_supplements_sha256', 'alignment', 'alignment_source_policy', 'alignment_review'):
            data.pop(key, None)
        policies = [policy] + [json.loads((ROOT / 'protocol' / name).read_bytes()) for name in
                     ('strict-scoring-policy.json', 'capability-scoring-policy.json', 'claim-penalty-policy.json')]
        return data, policies

    def score(self, data, policies, mode='partial', condition='nonlogical_retry_3'):
        return score_paper_observation(data, *policies, mode=mode, condition=condition)

    def missing(self, data, cid, status):
        task = next(t for t in data['tasks'] if t['case_id'] == cid)
        row = next(r for r in data['claim_review']['cases'] if r['case_id'] == cid)
        task.update(status=status, points=0 if status == 'delivery_failed' else None,
            complete=False if status == 'delivery_failed' else None, response=None, review=None,
            attempts=[dict(attempt=n, status='delivery_failed', reason='operator_reported_failure') for n in (1,2,3)]
                if status == 'delivery_failed' else [], attempt_evidence={'path':'operator.json','bytes':2,'sha256':'a'*64})
        row.update(status=status, findings=[], sources=[])
        row.pop('source_response_sha256', None); row.pop('source_review_sha256', None)

    def test_first_failed_attempt_cannot_inherit_retry_mathematics(self):
        data, policies = self.fixture()
        task = next(t for t in data['tasks'] if t['case_id'] == 'MG-GP001')
        task['attempts'] = [dict(attempt=1,status='delivery_failed',reason='max_output_tokens'),
                            dict(attempt=2,status='delivered',reason=None)]
        task['attempt_evidence'] = {'path':'operator.json','bytes':2,'sha256':'a'*64}
        first = self.score(data, policies, condition='single_attempt')
        retry = self.score(data, policies)
        a = next(t for t in first['tasks'] if t['case_id']=='MG-GP001')
        b = next(t for t in retry['tasks'] if t['case_id']=='MG-GP001')
        self.assertEqual(a['completion']['exact'], 0)
        self.assertFalse(a['strict_pass']); self.assertIsNone(a['response_sha256'])
        self.assertEqual(a['claim_assessment']['applied_deduction'], 0)
        self.assertEqual(b['completion']['exact'], 1)
        changed = copy.deepcopy(data)
        changed['tasks'][0]['attempts'].append(dict(attempt=3,status='delivered',reason=None))
        with self.assertRaisesRegex(ValueError, 'first delivery'):
            self.score(changed, policies)
        changed = copy.deepcopy(data); changed['tasks'][0]['attempts'][0]['reason']='mathematical_error'
        with self.assertRaisesRegex(ValueError, 'mathematical error'):
            self.score(changed, policies)

    def test_three_failed_deliveries_are_zero_and_c003_and_rounds_stay_unknown(self):
        data, policies = self.fixture()
        for cid in ('MG-GR023','MG-AR004'):
            self.missing(data, cid, 'delivery_failed')
        private = next(t['case_id'] for t in data['tasks'] if t['visibility']=='private'
                       and t['subcategory']=='written-argument')
        self.missing(data, private, 'delivery_failed')
        self.missing(data, 'MG-C003', 'unresolved')
        for mode in paper.MODES:
            result = self.score(data, policies, mode)
            for cid in ('MG-GR023','MG-AR004',private):
                task = next(t for t in result['tasks'] if t['case_id']==cid)
                self.assertEqual(task['completion']['exact'],0)
                self.assertEqual(task['claim_assessment']['applied_deduction'],0)
            self.assertIsNone(next(t for t in result['tasks'] if t['case_id']=='MG-C003')['completion']['exact'])
            self.assertIsNone(result['metrics']['overall']['exact'])
            self.assertEqual(result['whole_task_counts']['unknown'],1)
            self.assertEqual(result['coverage']['source_reviewed_tasks'],35)
            self.assertEqual(result['coverage']['observed_delivery_failures'],3)
            self.assertIsNone(result['strict_alignment_selfcheck']['strict_pass'])
            self.assertTrue(all(r['complete'] is None for r in result['alignment_selfcheck']['rounds']))
            self.assertEqual(result['capacity']['total'],100)

    def test_paper_cannot_claim_runtime_backend_or_inherit_rates(self):
        data, policies = self.fixture()
        changed = copy.deepcopy(data); changed['runtime_evidence_verified']=True
        with self.assertRaisesRegex(ValueError,'runtime evidence'):
            self.score(changed, policies)
        result = self.score(data, policies)
        self.assertFalse(result['transport_import_validated'])
        self.assertFalse(result['runtime_evidence_verified'])
        self.assertEqual(result['record_kind'],'paper_observation')
        aggregate = paper.project_score(result)
        self.assertNotIn('tasks',aggregate)
        self.assertIsNone(aggregate['backend_sku'])
        with self.assertRaisesRegex(ValueError,'private'):
            paper._public_only({'extra':{'path':'private/MG-MCP005/answer.md'}},['MG-GP001'])
        item={'path':'artifact.json','bytes':1,'sha256':'a'*64}
        public=[t for t in data['tasks'] if t['visibility']=='public']
        record=dict(schema=paper.SCHEMA,version=paper.VERSION,record_kind='paper_observation',
            benchmark_version='0.6.0',model_id='synthetic-model',model_label=data['model_label'],
            source_alias='operator-supplied-alias',source_effort='max',backend_sku=None,reviewer_kind='ai',
            human_review='pending',formal_comparison_eligible=False,transport_import_validated=False,
            runtime_evidence_verified=False,retention={'user_requested':True},comparison_note='Runtime unknown.',
            harness=dict(name='Returned paper observation',version=None,detail='Returned text only.',
                tool_usage='Unknown.',local_tools_allowed=True,search_allowed=False,tool_network_access=False,
                runtime_verified=False),mathematical_input_sha256='b'*64,
            assessment_policy=item,strict_scoring_policy=item,capability_scoring_policy=item,claim_penalty_policy=item,
            public_task_scores=item,public_claim_review=item,public_case_ids=sorted(t['case_id'] for t in public),
            public_deliveries=[{k:t[k] for k in ('case_id','status','response','review')} for t in public],
            selfcheck_rounds=[dict(round=n,status='not_run',response=None,review=None) for n in (1,2,3)],
            trajectory={'state':'unresolved'},content_rates_status='not_reviewed',
            **{field:{condition:item for condition in paper.CONDITIONS} for field in paper.RESULT_FIELDS.values()})
        paper.validate_record(record,policies[0])
        attributed=copy.deepcopy(record);attributed['harness']['name']='Codex CLI'
        paper.validate_record(attributed,policies[0])
        attributed['harness']['runtime_verified']=True
        with self.assertRaisesRegex(ValueError,'runtime validation'):
            paper.validate_record(attributed,policies[0])
        for key,value in (('backend_sku','assumed-backend'),('runtime_evidence_verified',True),
                          ('content_rates_status','inherited')):
            changed=copy.deepcopy(record);changed[key]=value
            with self.assertRaises(ValueError):paper.validate_record(changed,policies[0])
        changed=copy.deepcopy(record);changed['public_deliveries'][0]['private_answer']='secret'
        with self.assertRaisesRegex(ValueError,'unsupported or private'):
            paper.validate_record(changed,policies[0])

    def test_selected_record_schema_dispatch_never_picks_an_unselected_paper(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary)
            (root/'benchmark.json').write_text(json.dumps(dict(version='0.6.0',selected_result_models=['model'],
                selected_result_record_ids={'model':'chosen'})))
            for name,schema in (('chosen','math-gauge.result-record/v1'),('other',paper.SCHEMA)):
                folder=root/'results/v0.6.0/model'/name;folder.mkdir(parents=True)
                (folder/'record.json').write_text(json.dumps(dict(schema=schema,record_kind='paper_observation')))
            self.assertEqual(len(selected_cli_records(root)),1)
            self.assertEqual(selected_paper_records(root),[])
            (root/'results/v0.6.0/model/chosen/record.json').write_text(json.dumps(
                dict(schema=paper.SCHEMA,record_kind='paper_observation')))
            self.assertEqual(selected_cli_records(root),[])
            self.assertEqual(len(selected_paper_records(root)),1)

    def test_private_raw_review_and_claim_quotes_are_byte_bound(self):
        data, policies = self.fixture()
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary)
            def artifact(name,value):
                path=root/name;path.parent.mkdir(parents=True,exist_ok=True)
                path.write_text(value)
                return descriptor(root,path)
            claims={r['case_id']:r for r in data['claim_review']['cases']}
            for task in data['tasks']:
                task['response']=artifact('answers/'+task['case_id']+'.md','Original answer '+task['case_id'])
                task['review']=artifact('reviews/'+task['case_id']+'.json',json.dumps(dict(
                    case_id=task['case_id'],raw_points=task['points'],raw_max=task['maximum'],strict_pass=task['complete'])))
                claim=claims[task['case_id']]
                claim.update(source_response_sha256=task['response']['sha256'],source_review_sha256=task['review']['sha256'],
                    sources=[task['response'],task['review']])
                if task.get('strict_completion_case'):
                    case=task['strict_completion_case']
                    case['strict_completion_policy_source']=artifact('core-policy.json',json.dumps(case['strict_completion_policy']))
                    task['strict_completion_review'].update(answer_sha256=task['response']['sha256'],
                        policy_sha256=case['strict_completion_policy_source']['sha256'])
                    task['strict_completion_review_source']=artifact('core-review.json',json.dumps(task['strict_completion_review']))
            first=data['tasks'][0]
            quote='Original answer'
            claims[first['case_id']]['findings']=[dict(id='local-quote',root_cause='one-local-error',
                kind='false_assertion',severity='local',strict_blocking=True,core_endorsement=False,
                covered_by='none',reason='A specifically reviewed local assertion.',evidence=[dict(
                    path=first['response']['path'],sha256=first['response']['sha256'],
                    byte_start=0,byte_end=len(quote.encode()),quote=quote)])]
            inputs=artifact('math-inputs.json',json.dumps(data))
            record={'mathematical_inputs':inputs,'mathematical_input_sha256':inputs['sha256']}
            paper.load_private_inputs(root,record,policies[0])
            target=root/data['tasks'][0]['response']['path']
            original=target.read_bytes();target.write_bytes(original+b' changed')
            with self.assertRaisesRegex(ValueError,'evidence bytes changed'):
                paper.load_private_inputs(root,record,policies[0])
            target.write_bytes(original)
            claims[first['case_id']]['findings'][0]['evidence'][0]['quote']='Different words'
            inputs=artifact('math-inputs.json',json.dumps(data));record.update(
                mathematical_inputs=inputs,mathematical_input_sha256=inputs['sha256'])
            with self.assertRaisesRegex(ValueError,'UTF-8 bytes'):
                paper.load_private_inputs(root,record,policies[0])
            claims[first['case_id']]['findings'][0]['evidence'][0]['quote']=quote
            data['tasks'][0]['points']=99
            inputs=artifact('math-inputs.json',json.dumps(data));record.update(
                mathematical_inputs=inputs,mathematical_input_sha256=inputs['sha256'])
            with self.assertRaisesRegex(ValueError,'completeness|criterion review'):
                paper.load_private_inputs(root,record,policies[0])


if __name__=='__main__':
    unittest.main()
