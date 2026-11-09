"""Returned-paper evidence stays separate from runtime and native records."""
import copy
import hashlib
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

    def adoption_fixture(self, folder):
        data, policies = self.fixture()
        native, _ = native_fixture.NativeHarnessTests().fixture()
        review = copy.deepcopy(native['alignment_review'])
        source_policy = native['alignment_source_policy']
        artifacts = []

        def artifact(name, value):
            path = folder / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(value if isinstance(value, str) else json.dumps(value))
            item = descriptor(folder, path)
            artifacts.append(item)
            return item

        policy_source = artifact('legacy/policy.json', source_policy)
        review['policy_sha256'] = policy_source['sha256']
        rows, phases, phase_reviews = [], [], []
        snapshots = [review['baseline']] + [r['snapshot'] for r in review['rounds']]
        previous = None
        for index, snapshot in enumerate(snapshots):
            phase = 'A1' if index == 0 else 'R' + str(index)
            rid = 'MG-C003:A1' if index == 0 else 'MG-C003:alignment:' + str(index)
            response = artifact('legacy/' + phase + '/answer.md', 'Original final ' + phase)
            source = artifact('legacy/' + phase + '/Main.lean', 'Original engineering ' + phase)
            source_hash = hashlib.sha256(json.dumps({'Main.lean': source['sha256']},
                sort_keys=True, separators=(',', ':')).encode()).hexdigest()
            snapshot.update(source_sha256=source_hash, delivery_verified=False)
            if index:
                review['rounds'][index - 1]['diagnosis']['source_sha256'] = source_hash
            alignment = artifact('legacy/' + phase + '/alignment.json', snapshot['obligations'])
            inventory = artifact('legacy/' + phase + '/inventory.json', {'files': {'Main.lean': source}})
            row = dict(id=rid, case_id='MG-C003', parent_id=previous, response=response,
                original_alignment=alignment, observed_snapshot=inventory,
                evaluation={} if index == 0 else {'diagnosis': review['rounds'][index - 1]['diagnosis']})
            rows.append(row)
            phases.append(dict(phase=phase, source_record_id=rid, parent_source_record_id=previous,
                response=response, original_alignment=alignment, observed_snapshot=inventory,
                engineering_sources={'Main.lean': source}, source_sha256=source_hash))
            phase_reviews.append(dict(case_id='MG-C003', slot_id='MG-C003:' + phase,
                source_sha256=source_hash, original_response_sha256=response['sha256'],
                compiled_sources={'Main.lean': source['sha256']}, obligations=snapshot['obligations']))
            previous = rid
        trajectory = {'state': 'incomplete_stable', 'planned_rounds': 3, 'recorded_rounds': 3}
        record_source = artifact('legacy/record.json', dict(schema='math-gauge.result-record/v1',
            model={'requested_label': 'synthetic-model / observed'}, human_review='pending',
            formal_comparison_eligible=False, trajectory=trajectory, records=rows))
        review_source = artifact('legacy/alignment-review.json', review)
        formal_source = artifact('legacy/formalization-review.json', {'cases': [phase_reviews[0]]})
        phase_source = artifact('legacy/phase-reviews.json', {'cases': phase_reviews})
        authorization = artifact('private/user-selection.txt', 'Use this original whole trajectory.')
        adoption = dict(schema=paper.ADOPTION_SCHEMA, version=paper.VERSION, case_id='MG-C003',
            selection='explicit_user_selected_whole_legacy_trajectory', post_observation=True,
            user_selected=True, authorization_sha256=authorization['sha256'], source_record=record_source,
            source_policy=policy_source, source_alignment_review=review_source,
            source_formalization_review=formal_source, source_phase_reviews=phase_source,
            phase_sources=phases, trajectory=trajectory)
        adoption_source = artifact('alignment-adoption.json', adoption)
        task = next(t for t in data['tasks'] if t['case_id'] == 'MG-C003')
        task.update(response=phases[0]['response'], points=92, maximum=92)
        claim = next(c for c in data['claim_review']['cases'] if c['case_id'] == 'MG-C003')
        claim['source_response_sha256'] = task['response']['sha256']
        data.update(version=paper.ADOPTED_VERSION, alignment_adoption=adoption,
            alignment_adoption_source=adoption_source, alignment_review=review,
            alignment_source_policy=source_policy, sources=artifacts)
        record = dict(version=paper.ADOPTED_VERSION, model_id='synthetic-model',
            public_case_ids=sorted(t['case_id'] for t in data['tasks'] if t['visibility'] == 'public'),
            public_deliveries=[dict(case_id='MG-C003', status='reviewed', response=task['response'])],
            alignment_adoption=adoption_source, trajectory=trajectory,
            selfcheck_rounds=[dict(round=n, status='reviewed', response=phases[n]['response'],
                                   review=review_source) for n in (1, 2, 3)])
        return data, policies, record

    def test_adopted_whole_trajectory_uses_shared_arithmetic_and_resolves_unknowns(self):
        from math_gauge.scoring import _alignment_trajectory, strict_alignment_trajectory
        with tempfile.TemporaryDirectory() as temporary:
            data, policies, record = self.adoption_fixture(Path(temporary))
            paper._load_alignment_adoption(Path(temporary), record, data)
            for mode in paper.MODES:
                result = self.score(data, policies, mode)
                expected = _alignment_trajectory(data['alignment_review'], data['alignment_source_policy'],
                                                 positive_only=mode == 'capability')[0]
                self.assertEqual(result['alignment_selfcheck'], expected)
                self.assertEqual(result['strict_alignment_selfcheck'], strict_alignment_trajectory(
                    data['alignment_review'], data['alignment_source_policy']))
                self.assertEqual(result['coverage']['source_alignment_rounds'], 3)
                self.assertIsNotNone(result['metrics']['overall']['exact'])
                self.assertFalse(result['runtime_evidence_verified'])
                self.assertFalse(result['strict_alignment_selfcheck']['strict_pass'])
            data['version'] = paper.VERSION
            with self.assertRaisesRegex(ValueError, 'Legacy paper'):
                self.score(data, policies)

    def test_adoption_rejects_mixed_phase_bytes_parents_and_changed_diagnosis(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            data, policies, record = self.adoption_fixture(root)
            for mutate in (
                lambda d: d['alignment_adoption']['phase_sources'].pop(),
                lambda d: d['alignment_adoption']['phase_sources'][2].update(parent_source_record_id='other'),
                lambda d: d['alignment_adoption']['phase_sources'][1]['engineering_sources']['Main.lean'].update(sha256='f'*64),
                lambda d: next(t for t in d['tasks'] if t['case_id'] == 'MG-C003').update(points=91),
            ):
                changed = copy.deepcopy(data)
                mutate(changed)
                with self.assertRaises(ValueError):
                    self.score(changed, policies)
            changed = copy.deepcopy(data)
            changed['alignment_review']['rounds'][0]['diagnosis']['accurate'] = False
            with self.assertRaisesRegex(ValueError, 'original bytes'):
                paper._load_alignment_adoption(root, record, changed)
            target = root / data['alignment_adoption']['phase_sources'][2]['engineering_sources']['Main.lean']['path']
            target.write_bytes(target.read_bytes() + b' modified')
            with self.assertRaisesRegex(ValueError, 'evidence bytes changed'):
                paper._load_alignment_adoption(root, record, data)

    def test_source_confirmed_api_exclusions_preserve_physical_and_effective_attempts(self):
        with tempfile.TemporaryDirectory() as temporary:
            data, policies, _ = self.adoption_fixture(Path(temporary))
            task = next(t for t in data['tasks'] if t['case_id'] == 'MG-GR023')
            source = data['sources'][0]
            task['physical_attempts'] = [dict(physical_request=n, effective_attempt=None,
                status='delivery_failed', reason='service_error', excluded_system_failure=True,
                source=source, exclusion=dict(basis='user_confirmed_api_failure', declaration=source,
                    note='User confirmed the original API failures.')) for n in (1, 2, 3)]
            task['physical_attempts'] += [dict(physical_request=4, effective_attempt=1,
                status='delivery_failed', reason='deadline_exceeded', excluded_system_failure=False,
                source=source, exclusion=None), dict(physical_request=5, effective_attempt=2,
                status='delivered', reason=None, excluded_system_failure=False, source=source, exclusion=None)]
            task['attempts'] = [dict(attempt=1, status='delivery_failed', reason='deadline_exceeded'),
                                dict(attempt=2, status='delivered', reason=None)]
            task['attempt_evidence'] = source
            first, retry = (self.score(data, policies, condition=c) for c in paper.CONDITIONS)
            first_task = next(t for t in first['tasks'] if t['case_id'] == task['case_id'])
            retry_task = next(t for t in retry['tasks'] if t['case_id'] == task['case_id'])
            self.assertEqual(first_task['completion']['exact'], 0)
            self.assertEqual(retry_task['completion']['exact'], 1)
            for reason in ('max_output_tokens', 'deadline_exceeded'):
                changed = copy.deepcopy(data)
                selected = next(t for t in changed['tasks'] if t['case_id'] == task['case_id'])
                selected['physical_attempts'][0]['reason'] = reason
                with self.assertRaisesRegex(ValueError, 'exclusion'):
                    self.score(changed, policies)
            changed = copy.deepcopy(data)
            selected = next(t for t in changed['tasks'] if t['case_id'] == task['case_id'])
            selected['physical_attempts'][3]['effective_attempt'] = 2
            with self.assertRaisesRegex(ValueError, 'numbering'):
                self.score(changed, policies)
            for field, index in (('physical_request', 0), ('effective_attempt', 3)):
                changed = copy.deepcopy(data)
                selected = next(t for t in changed['tasks'] if t['case_id'] == task['case_id'])
                selected['physical_attempts'][index][field] = True
                with self.assertRaises(ValueError):
                    self.score(changed, policies)

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
