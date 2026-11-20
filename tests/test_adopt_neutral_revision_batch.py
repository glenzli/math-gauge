"""Whole-model adoption, explicit files and additive resource source contracts."""
from copy import deepcopy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from math_gauge.records import project_assessment_score
from math_gauge.neutral_revision import descriptor, select_revision_tasks
from scripts import adopt_neutral_revision_batch as batch
from scripts import results_revision_resources as resources
from test_neutral_revision import fixture_reports, POLICY, MODES, CONDITION

ROOT = Path(__file__).resolve().parents[1]


class BatchAdoptionTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.public, self.private, self.run = (self.root / name for name in ('public','private','run'))
        for path in (self.public, self.private, self.run):
            path.mkdir()
        self.mid, self.cid = 'synthetic-batch-model', 'MG-TX001'

    def put(self, root, name, value):
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(value if isinstance(value, bytes) else batch.encoded(value))
        return descriptor(root, path)

    def external(self, name, value):
        item = self.put(self.run, name, value)
        return dict(item, path=str(self.run / item['path']))

    def companion(self, model, calls=1):
        return dict(schema=resources.SCHEMA, version='0.1.0', benchmark_version='1.2.0',
            score_weight_applied_to_resources=False, grade_feedback_arm_included=False,
            review_calls_included=False, new_calls=calls, reused_calls=0, selected_calls=calls,
            models=[dict(id=model, revision=dict(planned_calls=calls))])

    def fixture(self):
        for name in ('neutral-revision.json','neutral-revision.md','neutral-revision-candidate-standards.md',
                     'neutral-revision-candidate-invitation.md','scoring-policy.json'):
            self.put(self.public, 'protocol/' + name, (ROOT / 'protocol' / name).read_bytes())
        catalog = json.loads((ROOT / 'cases/catalog.json').read_bytes())
        self.put(self.public, 'cases/catalog.json', catalog)
        self.put(self.public, 'benchmark.json', dict(version='1.2.0', neutral_revision_transition={}))
        record = self.put(self.public, 'results/fixture/record.json', {'fixture': True})
        self.put(self.private, record['path'], {'fixture': True})
        first_answer = self.put(self.private, 'original/answer.md', b'Entire synthetic original self-assessment.\r\n')
        first_review = self.put(self.private, 'original/review.json', {'fixture_review': True})
        task = self.put(self.public, 'original/task.md', b'Complete synthetic original task.\n')
        tasks = [dict(case_id=row['case_id'], family_id=row['family_id'], subcategory=row['assessment_category'],
            response_sha256='a'*64, review_sha256='b'*64, strict_pass=True,
            completion=dict(lower=1,upper=1,exact=1), submission_assessment=dict(classification='active_final'))
            for row in catalog['entries']]
        for child in POLICY['subcategories']:
            if child['aggregation'] == 'trajectory':
                continue
            public_families = {row['family_id'] for row in tasks if row['subcategory']==child['id']}
            for ordinal in range(child['families'] - len(public_families)):
                cid = 'SYNTHETIC-PRIVATE-' + child['id'] + '-' + str(ordinal)
                tasks.append(dict(case_id=cid, family_id=cid, subcategory=child['id'],
                    response_sha256='a'*64, review_sha256='b'*64, strict_pass=True,
                    completion=dict(lower=1,upper=1,exact=1), submission_assessment=dict(classification='active_final')))
        reports = fixture_reports()
        for mode in MODES:
            reports[mode]['tasks'] = deepcopy(tasks)
            target = next(row for row in reports[mode]['tasks'] if row['case_id']==self.cid)
            target.update(response_sha256=first_answer['sha256'], review_sha256=first_review['sha256'],
                strict_pass=False, completion=dict(lower=0,upper=0,exact=0))
        private_reports, public_reports = {}, {}
        for mode in MODES:
            private_reports[mode] = self.put(self.private, 'base/' + mode + '.json', reports[mode])
            public_reports[mode] = {}
            for condition in ('single_attempt', CONDITION):
                projected = project_assessment_score(reports[mode])
                projected['attempt_condition'] = condition
                projected['source_bindings']['private_report_sha256'] = private_reports[mode]['sha256']
                public_reports[mode][condition] = self.put(self.public, 'base/' + mode + '-' + condition + '.json', projected)
        chosen = select_revision_tasks(reports, model_id=self.mid)
        self.assertEqual(len(chosen), 1)
        chosen[0].update(source_case=dict(scope='public', **task), original_answer=dict(scope='private', **first_answer),
            original_review=dict(scope='private', **first_review))
        source = dict(model_id=self.mid, record_id='fixture', selection=chosen, reports=reports,
            base_reports=private_reports, public_base_reports=public_reports, source_record=record)
        source['record_id'] = 'fixture'
        self.cost_fixture(source)
        runtime = dict(cells=[dict(model_id=self.mid, case_id=self.cid, id=self.mid+'--'+self.cid)])
        runtime_ref = self.external('runtime-freeze.json', runtime)
        for name in ('pre-run-freeze.json','packet-index-evaluator-only.json','model-source-identities.json'):
            self.external(name, {'fixture': True})
        usage = dict(input_tokens=100, cached_input_tokens=20, cache_write_input_tokens=0, output_tokens=10)
        prefix = 'engineering/sessions/' + self.mid + '--' + self.cid + '/'
        answer = self.external(prefix + 'output/response.md', b'Complete final. Explicitly delivered proof.md\nSelf-assessment: complete.\r\n')
        attachment = self.external(prefix + 'terminal-output-sealed/proof.md', b'Complete synthetic proof.\r\n')
        execution = self.external(prefix + 'runtime/execution.json', dict(status='completed', request_count=1,
            started_utc='2026-11-20T00:00:00+00:00', usage=usage, observed_model=None,
            requested_model='synthetic-native', requested_effort='max'))
        events = self.external(prefix + 'output/events.ndjson', (json.dumps(dict(type='turn.completed', usage=usage))+'\n').encode())
        seal = self.external(prefix + 'runtime/seal.json', dict(trigger='first-native-terminal',
            trigger_observed_utc='2026-11-20T00:00:10+00:00', work_files=[]))
        observed = self.external(prefix + 'runtime/terminal-output-observation.json', dict(files=[dict(
            filename='proof.md', sha256=attachment['sha256'])]))
        collection = self.external(prefix + 'runtime/collection.json', dict(normal_final_delivered=True,
            response_sha256=answer['sha256']))
        original_input = self.external(prefix + 'input/task.md', b'Complete synthetic candidate input.\n')
        request = dict(messages=[dict(role='user', content='Complete synthetic candidate input.\n')],
            source_response_sha256=first_answer['sha256'])
        request['request_sha256'] = batch.identity(request)
        request_ref = self.external('requests/' + self.mid + '--' + self.cid + '.json', request)
        runtime['cells'][0].update(input_sha256=original_input['sha256'], requested_model='synthetic-native', effort='max',
            portable_request=request_ref, portable_request_sha256=request['request_sha256'])
        runtime_ref = self.external('runtime-freeze.json', runtime)
        initial = self.external(prefix + 'runtime/initial-work-materials.json', dict(files=[]))
        for name in ('plan.json','attempt-ledger.json','cli-identity.json'):
            self.external(prefix + 'runtime/' + name, {'fixture': True})
        delivery = dict(id=self.mid+'--'+self.cid, model_id=self.mid, case_id=self.cid,
            normal_final_delivered=True, response=answer, native_execution=execution,
            native_events=events, seal=seal, collection=collection, original_input=original_input,
            initial_work=initial, terminal_output_observation=observed,
            named_sealed_files=[dict(source=attachment, same_bytes_as_initial_material=False)])
        self.external('sealed-deliveries.json', dict(runtime_freeze=runtime_ref,
            normal_finals=[delivery], operational_failures=[]))
        review = self.external('root-review.json', dict(MC=100, RMC=100, SMC=True,
            response_sha256=answer['sha256'], reviewer_kind='ai', human_review='pending',
            mathematical_verdict_finalized=True))
        prior_reviews = [self.external('review-evidence/' + name + '/review.json', dict(
            reviewer=name, original_bytes=True)) for name in ('original-terra','primary-sol','root-audit')]
        lock = dict(schema=batch.LOCK_SCHEMA, runtime_freeze=runtime_ref,
            rows={delivery['id']:dict(review=review, attachments=[attachment], review_sources=prior_reviews)})
        lock_ref = self.external('selected-final-reviews.json', lock)
        transition = dict(adoptions={}, pending_models=[self.mid], source_edition={}, policy={})
        return source, delivery, lock, Path(lock_ref['path']), transition

    def cost_fixture(self, source):
        slots = [dict(id='slot-'+str(i), answer_sha256='a'*64, units=[dict(price_id='retained-fixture')]) for i in range(42)]
        inventory = dict(prices=[dict(id='retained-fixture', rates_per_million=dict(input=1,cached_input=.1,cache_write=1,output=2))],
            models=[dict(model_id=self.mid, record_id=source['record_id'], slots=slots)])
        item = self.put(self.private, 'results/costs/v0.1.0/fixture.json', inventory)
        self.put(self.private, 'results/costs/v0.1.0/current.json', dict(selected='fixture.json', sha256=item['sha256']))
        self.put(self.public, 'results/costs/v0.1.0/current.json', dict(models=[dict(model_id=self.mid,
            record_id=source['record_id'], status='observed', total_usd=10, known_usd=10,
            estimate_range_usd=None, coverage={}, pricing_basis='retained-fixture')]))
        self.put(self.public, resources.DATA_PATH, self.companion('existing-model'))

    def test_shared_consumer_accepts_complete_source_bound_staged_proposal(self):
        source, delivery, lock, lock_path, transition = self.fixture()
        original_resources = (self.public / resources.DATA_PATH).read_bytes()
        before = (self.public / 'benchmark.json').read_bytes()
        with patch.object(batch, 'load_model_selection', return_value=source), patch.object(batch, 'load_transition', return_value=transition):
            result = batch.prepare(self.public, self.private, self.run, self.root/'proposal', reviews=lock_path)
        self.assertEqual(result['new_models'], [self.mid])
        self.assertEqual(result['models'][0]['status'], 'ready')
        self.assertEqual((self.public/'benchmark.json').read_bytes(), before)
        self.assertEqual((self.public/resources.DATA_PATH).read_bytes(), original_resources)
        resource = resources.load_public(self.root/'proposal/public')
        new = next(row for row in resource['models'] if row['id']==self.mid)
        self.assertIsNone(new['base']['candidate_execution_seconds'])
        self.assertIsNone(new['combined']['candidate_execution_seconds'])
        self.assertEqual(new['revision']['candidate_execution_seconds'], 10)
        self.assertEqual(new['combined']['planned_calls'], 43)
        self.assertIsNone(resource['batch_span_seconds'])
        public_raw = b''.join((self.root/'proposal/public'/item['path']).read_bytes()
            for item in result['artifacts']['public'])
        self.assertNotIn(b'SYNTHETIC-PRIVATE-', public_raw)
        private_inputs = json.loads((self.root/'proposal/private'/DIRECTORY/self.mid/'fixture/inputs.json').read_bytes())
        self.assertEqual(private_inputs['rows'][0]['continuation']['attachments'][0]['sha256'], lock['rows'][delivery['id']]['attachments'][0]['sha256'])
        source_rows = [row for row in private_inputs['rows'][0]['continuation']['sources']
            if '/review-sources/' in row['path'] and not row['path'].endswith('/source-map.json')]
        self.assertEqual({row['sha256'] for row in source_rows},
            {row['sha256'] for row in lock['rows'][delivery['id']]['review_sources']})

    def test_missing_review_never_rescales_or_prepares_partial_model_scores(self):
        source, _, _, _, transition = self.fixture()
        with patch.object(batch, 'load_model_selection', return_value=source), patch.object(batch, 'load_transition', return_value=transition):
            result = batch.prepare(self.public, self.private, self.run, self.root/'pending')
        self.assertEqual(result['new_models'], [])
        self.assertEqual(result['models'][0]['status'], 'pending')
        self.assertNotIn('scores', result['models'][0])
        self.assertEqual(result['artifacts'], {'public': [], 'private': []})

    def test_explicit_attachment_selection_and_finality_are_required(self):
        source, delivery, lock, lock_path, _ = self.fixture()
        chosen = lock['rows'][delivery['id']]
        malformed = deepcopy(lock)
        del malformed['rows'][delivery['id']]['attachments']
        lock_path.write_bytes(batch.encoded(malformed))
        with self.assertRaisesRegex(ValueError, 'explicit attachment'):
            batch.load_review_selection(lock_path, self.run/'runtime-freeze.json')
        review_path = Path(chosen['review']['path'])
        review = json.loads(review_path.read_bytes()); review['mathematical_verdict_finalized'] = False
        review_path.write_bytes(batch.encoded(review))
        chosen['review'] = dict(path=str(review_path), **{k:v for k,v in descriptor(self.run, review_path).items() if k!='path'})
        with self.assertRaisesRegex(ValueError, 'Preliminary'):
            batch.validate_locked_delivery(source['selection'][0], delivery, chosen, lock_root=self.run)

    def test_unnamed_unsealed_file_cannot_be_promoted_as_attachment(self):
        source, delivery, lock, _, _ = self.fixture()
        selected = lock['rows'][delivery['id']]
        delivery['named_sealed_files'] = []
        with self.assertRaisesRegex(ValueError, 'terminal-bound'):
            batch.validate_locked_delivery(source['selection'][0], delivery, selected, lock_root=self.run)

    def test_public_continuation_cannot_expose_another_private_task_identifier(self):
        source, delivery, lock, lock_path, transition = self.fixture()
        selected = lock['rows'][delivery['id']]
        review_path = Path(selected['review']['path'])
        review = json.loads(review_path.read_bytes())
        review['private_cross_reference'] = next(row['case_id'] for row in source['reports']['partial']['tasks']
            if row['case_id'].startswith('SYNTHETIC-PRIVATE-'))
        review_path.write_bytes(batch.encoded(review))
        selected['review'] = dict(path=str(review_path), bytes=len(review_path.read_bytes()), sha256=batch.sha(review_path.read_bytes()))
        lock_path.write_bytes(batch.encoded(lock))
        with patch.object(batch, 'load_model_selection', return_value=source), patch.object(batch, 'load_transition', return_value=transition):
            with self.assertRaisesRegex(ValueError, 'Private task identifiers'):
                batch.prepare(self.public, self.private, self.run, self.root/'rejected', reviews=lock_path)

    def test_resource_index_preserves_original_and_rejects_overlapping_or_tampered_sources(self):
        first = self.put(self.public, resources.DATA_PATH, self.companion('one'))
        second = self.put(self.public, 'results/continuation-resources/v0.1.0/batches/two.json', self.companion('two'))
        self.put(self.public, resources.INDEX_PATH, dict(schema='math-gauge.neutral-revision-resources-index/v1',
            version='0.1.0', benchmark_version='1.2.0', sources=[first,second]))
        before = (self.public/resources.DATA_PATH).read_bytes()
        self.assertEqual({row['id'] for row in resources.load_public(self.public)['models']}, {'one','two'})
        self.assertEqual((self.public/resources.DATA_PATH).read_bytes(), before)
        (self.public/second['path']).write_bytes(b'changed')
        with self.assertRaises(ValueError):
            resources.load_public(self.public)

    def test_cutoff_keeps_known_time_unknown_cost_and_original_empty_response(self):
        source, delivery, lock, lock_path, transition = self.fixture()
        response_path = Path(delivery['response']['path'])
        response_path.write_bytes(b'')
        delivery['response'] = dict(path=str(response_path), bytes=0, sha256=batch.sha(b''))
        delivery['normal_final_delivered'] = False
        collection_path = Path(delivery['collection']['path'])
        collection_path.write_bytes(batch.encoded(dict(normal_final_delivered=False, response_sha256=batch.sha(b''))))
        delivery['collection'] = dict(path=str(collection_path), bytes=len(collection_path.read_bytes()), sha256=batch.sha(collection_path.read_bytes()))
        execution_path = Path(delivery['native_execution']['path'])
        execution = json.loads(execution_path.read_bytes());execution.update(status='failed', usage=None)
        execution_path.write_bytes(batch.encoded(execution))
        delivery['native_execution'] = dict(path=str(execution_path), bytes=len(execution_path.read_bytes()), sha256=batch.sha(execution_path.read_bytes()))
        seal_path = Path(delivery['seal']['path'])
        seal_path.write_bytes(batch.encoded(dict(trigger='fixed-controller-deadline',
            trigger_observed_utc='2026-11-20T00:45:00+00:00', work_files=[])))
        delivery['seal'] = dict(path=str(seal_path), bytes=len(seal_path.read_bytes()), sha256=batch.sha(seal_path.read_bytes()))
        cutoff = dict(schema='math-gauge.neutral-revision-cutoff-review/v1', case_id=self.cid,
            failure_evidence_sha256=delivery['collection']['sha256'], reviewer_kind='ai', human_review='pending',
            mathematical_verdict_finalized=True, original_work_unmodified=True, no_normal_final=True,
            no_cross_attempt_union=True, content_sha256=None, no_content=True,
            capability_completion=dict(lower=0,upper=0,exact=0))
        review = self.external('cutoff-root-review.json', cutoff)
        lock['rows'][delivery['id']].update(review=review, attachments=[])
        lock_path.write_bytes(batch.encoded(lock))
        self.external('sealed-deliveries.json', dict(runtime_freeze=lock['runtime_freeze'], normal_finals=[], operational_failures=[delivery]))
        self.external('operational-attribution/'+delivery['id']+'.json', dict(capacity_observed=True,
            exclusive_cause_not_proven=True, pure_system_exclusion=False, mathematical_error_adjudicated=False))
        with patch.object(batch, 'load_model_selection', return_value=source), patch.object(batch, 'load_transition', return_value=transition):
            result = batch.prepare(self.public, self.private, self.run, self.root/'cutoff-proposal', reviews=lock_path)
        self.assertEqual(result['new_models'], [self.mid])
        current = resources.load_public(self.root/'cutoff-proposal/public')
        item = next(row for row in current['models'] if row['id']==self.mid)
        self.assertEqual(item['revision']['candidate_execution_seconds'], 2700)
        self.assertEqual(item['revision']['physical_requests'], 1)
        self.assertEqual(item['revision']['effective_attempts'], 1)
        self.assertIsNone(item['revision']['total_usd'])
        self.assertIsNone(item['combined']['total_usd'])
        self.assertIsNone(item['revision']['tokens'])
        self.assertEqual(item['revision']['known_usd'], 0)
        inputs = json.loads((self.root/'cutoff-proposal/private'/DIRECTORY/self.mid/'fixture/inputs.json').read_bytes())
        self.assertTrue(any('operational-attribution' in row['path'] for row in inputs['study_sources']))
        continuation = inputs['rows'][0]['continuation']
        self.assertNotIn('answer', continuation)
        self.assertTrue(any(row['path'].endswith('original-cutoff-response.md') and row['bytes']==0 for row in continuation['sources']))

    def test_recovery_resources_distinguish_unconfirmed_and_confirmed_system_failures(self):
        source, delivery, _, _, _ = self.fixture()
        execution = self.external('prior/runtime/execution.json', dict(status='failed', request_count=1,
            started_utc='2026-11-19T23:00:00+00:00', usage=None, observed_model=None))
        seal = self.external('prior/runtime/seal.json', dict(trigger='fixed-controller-deadline',
            trigger_observed_utc='2026-11-19T23:45:00+00:00'))
        events = self.external('prior/output/events.ndjson', b'{"type":"error","message":"Selected model is at capacity"}\n')
        prior = dict(model_id=self.mid, case_id=self.cid, native_execution=execution, native_events=events, seal=seal)
        delivery['prior_attempts'] = [prior]
        delivery['recovery_supplement'] = self.external('single-recovery.json', dict(post_observation=True))
        companion, _ = resources.build_batch_public(self.public, self.private, self.run, self.mid, source, [delivery])
        item = companion['models'][0]
        self.assertEqual(companion['selected_tasks'], 1)
        self.assertEqual(companion['selected_calls'], 2)
        self.assertEqual(item['revision']['physical_requests'], 2)
        self.assertEqual(item['revision']['effective_attempts'], 2)
        self.assertEqual(item['revision']['candidate_execution_seconds'], 2710)
        self.assertIsNone(item['revision']['total_usd'])
        self.assertGreater(item['revision']['known_usd'], 0)
        self.assertIsNone(item['revision']['tokens'])
        self.assertGreater(item['revision']['known_tokens']['total_tokens'], 0)
        self.assertEqual(item['public_cases'], [dict(case_id=self.cid, seconds=2710, reused=False)])

        evidence = {key: self.put(self.private, 'retained/' + key, Path(prior[key]['path']).read_bytes())
                    for key in ('native_execution', 'seal', 'native_events')}
        exclusion = dict(schema='math-gauge.neutral-revision-system-exclusions/v1', benchmark_version='1.2.0',
            model_id=self.mid, record_id=source['record_id'], authority='user_confirmed_after_observation',
            attempts=[dict(case_id=self.cid, reason='capacity', **evidence)])
        self.put(self.private, f"{DIRECTORY}/{self.mid}/{source['record_id']}/resource-system-exclusions.json", exclusion)
        corrected, _ = resources.build_batch_public(self.public, self.private, self.run, self.mid, source, [delivery])
        item = corrected['models'][0]
        revision = item['revision']
        self.assertEqual((revision['physical_requests'], revision['effective_attempts'], revision['system_exclusions']),
                         (2, 1, 1))
        self.assertEqual(revision['system_failure_reasons'], {'capacity': 1})
        self.assertEqual(revision['candidate_execution_seconds'], 10)
        self.assertEqual(revision['total_usd'], revision['known_usd'])
        self.assertEqual(item['public_cases'], [dict(case_id=self.cid, seconds=10, reused=False)])


DIRECTORY = batch.DIRECTORY

if __name__ == '__main__':
    unittest.main()
