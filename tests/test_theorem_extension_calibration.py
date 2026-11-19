"""Synthetic source-bound TX recalibration; no candidate calls or mathematics grading."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

from math_gauge import theorem_extension_calibration as calibration
from math_gauge import scoring, submission_evidence
from math_gauge.benchmarks import identity
from math_gauge.records import descriptor, project_assessment_score, project_public_task_view
import test_theorem_extension as extension_fixtures


ROOT = Path(__file__).resolve().parents[1]


def put(root, name, value):
    path = root / name
    path.parent.mkdir(parents=True, exist_ok=True)
    raw = value if isinstance(value, bytes) else (json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode()
    path.write_bytes(raw)
    return descriptor(root, path)


class CalibrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        extension_fixtures.TheoremExtensionScoringTests.setUpClass()

    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name) / 'private'
        self.public = Path(temp.name) / 'public'
        self.root.mkdir()
        self.public.mkdir()
        self.fixture = extension_fixtures.TheoremExtensionScoringTests()
        put(self.public, 'cases/catalog.json', dict(schema='math-gauge.case-catalog/v1',
            entries=[dict(case_id=row['case_id']) for row in self.fixture.plan['case_index']]))
        self.policy = json.loads((ROOT / 'protocol/scoring-policy.json').read_bytes())
        self.folder = Path('results/v0.6.0/fixture-model/snapshot')
        self.grade = copy.deepcopy(self.fixture.research((1,) * 6))
        self.ids = [r['case_id'] for r in self.grade['slots']]
        self.model = self.fixture.plan['model_label']
        self.calibration_policy = json.loads((ROOT / 'protocol/theorem-extension-calibration.json').read_bytes())
        self.calibration_policy['standards'] = put(self.public, 'protocol/calibration.md', b'Synthetic public standard')
        private_standard = put(self.root, 'protocol/calibration.md', b'Synthetic private standard')
        self.calibration_policy['private_standards'] = {k: private_standard[k] for k in ('bytes', 'sha256')}
        for case in self.calibration_policy['public_case_contracts']:
            for key in ('task', 'contract'):
                item = case[key]
                put(self.public, item['path'], (ROOT / item['path']).read_bytes())
        self.policy_ref = put(self.public, 'protocol/calibration.json', self.calibration_policy)
        for row in self.grade['slots']:
            cid = row['case_id']
            response = put(self.root / self.folder, cid + '/answer.md',
                           ('SYNTHETIC original answer for ' + cid + '.\n').encode())
            review = put(self.root / self.folder, cid + '/review.json',
                         dict(B=2, R=1, answer_sha256=response['sha256']))
            row['response'], row['review'] = response, review
        cases = [dict(case_id=r['case_id'], status='reviewed', scope_note='Synthetic source audit.',
            sources=[], findings=[], source_response_sha256=r['response']['sha256'],
            source_review_sha256=r['review']['sha256'], baseline_disposition='correct')
            for r in self.grade['slots']]
        full_ids = [r['case_id'] for r in self.fixture.plan['case_index']]
        for cid in full_ids:
            if cid not in self.ids:
                cases.append(dict(case_id=cid, status='not_run', scope_note='Synthetic unrun source.',
                    sources=[], findings=[], source_response_sha256=None, source_review_sha256=None,
                    baseline_disposition=None))
        self.claims = dict(schema='math-gauge.claim-review-condition/v1', policy_version='0.1.0',
            model_label=self.model, reviewer_kind='ai', human_review='pending', formal_comparison_eligible=False,
            cases=cases)
        evidence = put(self.root / self.folder, 'source-evidence.txt', b'Synthetic source declaration')
        self.submissions = {}
        for condition in calibration.CONDITIONS:
            self.submissions[condition] = dict(schema=submission_evidence.REVIEW_SCHEMA, version='0.1.0',
                attempt_condition=condition, model_label=self.model,
                initials=[dict(case_id=r['case_id'],
                    classification='active_final' if r['case_id'] in self.ids else 'not_run',
                    source_response_sha256=r['source_response_sha256'], reason='Synthetic observation.',
                    evidence=[evidence]) for r in cases],
                rounds=[dict(round=n, classification='not_run', reason='Synthetic unrun round.', evidence=[evidence])
                        for n in (1, 2, 3)])
        self.submission_ref = put(self.root / self.folder, 'submissions.json', dict(
            schema='math-gauge.submission-archive/v1', version='0.1.0', conditions=self.submissions))
        self.record = dict(schema='math-gauge.paper-observation-record/v1', benchmark_version='0.6.0',
            model_id='fixture-model', record_id='snapshot', submission_evidence=self.submission_ref)
        self.record_ref = put(self.root, (self.folder / 'record.json').as_posix(), self.record)
        self.math = dict(schema='math-gauge.paper-observation-math/v1', benchmark_version='0.6.0', model_label=self.model,
            tasks=[dict(case_id=r['case_id'], status='reviewed', baseline_B=r['baseline_B'],
                research_R=r['research_R'], response=r['response'], review=r['review'],
                attempts=[dict(status='completed')]) for r in self.grade['slots']], claim_review=self.claims)
        self.math_ref = put(self.root, (self.folder / 'math-inputs.json').as_posix(), self.math)
        self.effective = self.build_bases()
        self.input_data = dict(schema=calibration.INPUT_SCHEMA, version='0.1.0', benchmark_version='1.1.0',
            model_id='fixture-model', model_label=self.model, record_id='snapshot', source_record=self.record_ref,
            policy=self.policy_ref, private_standards=private_standard, base_reports={}, conditions={},
            reviewer_kind='ai', human_review='pending', post_observation=True, formal_comparison_eligible=False,
            new_candidate_calls=0, source_raw_bytes_rewritten=False)
        for mode in calibration.MODES:
            self.input_data['base_reports'][mode] = {c: put(self.root, 'reassessment/base-' + mode + '-' + c + '.json', s)
                for c, s in self.effective[mode].items()}
        for condition in calibration.CONDITIONS:
            self.input_data['conditions'][condition] = []
            for source in self.grade['slots']:
                cid = source['case_id']
                row = dict(case_id=cid, source_inputs=self.math_ref,
                    response=dict(source['response'], path=(self.folder / source['response']['path']).as_posix()),
                    source_review=dict(source['review'], path=(self.folder / source['review']['path']).as_posix()),
                    baseline_B=2, old_R=1, new_R=3)
                review = dict(schema=calibration.REVIEW_SCHEMA, version='0.1.0', case_id=cid,
                    answer_sha256=row['response']['sha256'], source_review_sha256=row['source_review']['sha256'],
                    baseline_B=2, old_R=1, new_R=3, policy_sha256=self.policy_ref['sha256'],
                    standard_sha256=(self.calibration_policy['standards']['sha256'] if cid in calibration.PUBLIC_CASES
                                     else private_standard['sha256']), reviewer_kind='ai', reviewer=['Synthetic reviewer'],
                    human_review='pending', post_observation=True, status='reviewed', reason='Synthetic tier change.',
                    attained='Synthetic complete contribution.', not_attained='Maximum tier; none required.',
                    citations=[dict(quote='SYNTHETIC original answer')])
                row['new_review'] = put(self.root, 'reassessment/' + condition + '/' + cid + '-review.json', review)
                self.input_data['conditions'][condition].append(row)

    def build_bases(self):
        out = {}
        for mode in calibration.MODES:
            out[mode] = {}
            for condition in calibration.CONDITIONS:
                report = scoring.score_assessment_inputs(dict(plan=self.fixture.plan,
                    model_label=self.model, slots=[]), self.policy, self.fixture.strict, mode=mode,
                    theorem_extension_inputs=self.grade, claim_review=self.claims,
                    claim_policy=json.loads((ROOT / 'protocol/claim-penalty-policy.json').read_bytes()),
                    capability_policy=json.loads((ROOT / 'protocol/capability-scoring-policy.json').read_bytes())
                        if mode == 'capability' else None,
                    submission_review=self.submissions[condition],
                    submission_policy=json.loads((ROOT / 'protocol/submission-scoring-policy.json').read_bytes()))
                report['attempt_condition'] = condition
                if self.math['schema'] == 'math-gauge.paper-observation-math/v1':
                    report.update(record_kind='paper_observation', transport_import_validated=False,
                                  runtime_evidence_verified=False)
                elif self.math['schema'] == 'math-gauge.native-harness-math/v1':
                    report.update(record_kind='native_harness', transport_import_validated=False)
                report['source_bindings'] = dict(mathematical_input_sha256=self.math_ref['sha256'],
                    submission_evidence_sha256=self.submission_ref['sha256'])
                out[mode][condition] = report
        return out

    def load(self):
        ref = put(self.root, 'reassessment/inputs.json', self.input_data)
        return calibration.load_inputs(self.root, ref, public_root=self.public,
            policy=self.calibration_policy, effective_scores=self.effective)

    def refresh_sources(self):
        self.submission_ref = put(self.root / self.folder, 'submissions.json', dict(
            schema='math-gauge.submission-archive/v1', version='0.1.0', conditions=self.submissions))
        self.record['submission_evidence'] = self.submission_ref
        self.record_ref = put(self.root, (self.folder / 'record.json').as_posix(), self.record)
        self.math_ref = put(self.root, (self.folder / 'math-inputs.json').as_posix(), self.math)
        self.effective = self.build_bases()
        self.input_data['source_record'] = self.record_ref
        for mode in calibration.MODES:
            self.input_data['base_reports'][mode] = {c: put(self.root, 'reassessment/base-' + mode + '-' + c + '.json', s)
                for c, s in self.effective[mode].items()}
        for rows in self.input_data['conditions'].values():
            for row in rows:
                row['source_inputs'] = self.math_ref

    def score(self, mode='partial', condition='nonlogical_retry_3', inputs=None):
        return scoring.score_theorem_extension_calibration_overlay(self.effective[mode][condition],
            self.policy, calibration=self.load() if inputs is None else inputs, mode=mode, condition=condition)

    def test_all_modes_use_same_new_r_and_keep_non_tx_objects_and_original_bytes(self):
        inputs = self.load()
        original = copy.deepcopy(self.effective)
        source_bytes = (self.root / self.record_ref['path']).read_bytes()
        for mode in calibration.MODES:
            result = self.score(mode, inputs=inputs)
            self.assertEqual(result['benchmark_version'], '1.1.0')
            self.assertEqual(result['source_benchmark_version'], '0.6.0')
            self.assertEqual(result['metrics']['theorem-extension']['exact'], 100)
            self.assertEqual(result['contributions']['theorem-extension']['exact'], 10)
            self.assertEqual(result['metrics']['theorem-extension']['coverage']['planned'], 6)
            for before, after in zip(self.effective[mode]['nonlogical_retry_3']['tasks'], result['tasks']):
                if before['subcategory'] != 'theorem-extension':
                    self.assertEqual(before, after)
            for key, metric in self.effective[mode]['nonlogical_retry_3']['metrics'].items():
                if key not in {'theorem-extension', 'research', 'earned', 'overall'}:
                    self.assertEqual(result['metrics'][key], metric)
            self.assertEqual(result['alignment_selfcheck'], self.effective[mode]['nonlogical_retry_3']['alignment_selfcheck'])
        self.assertEqual(self.effective, original)
        self.assertEqual((self.root / self.record_ref['path']).read_bytes(), source_bytes)

    def test_review_byte_damage_wrong_answer_or_baseline_is_rejected(self):
        row = self.input_data['conditions']['single_attempt'][0]
        for field, value in [('baseline_B', 1), ('response', self.input_data['conditions']['single_attempt'][1]['response'])]:
            original = copy.deepcopy(row)
            row[field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                self.load()
            row.clear(); row.update(original)
        path = self.root / row['new_review']['path']
        path.write_bytes(path.read_bytes() + b' ')
        with self.assertRaisesRegex(ValueError, 'bytes changed'):
            self.load()

    def test_bad_citation_missing_family_and_wrong_condition_cannot_pass(self):
        row = self.input_data['conditions']['single_attempt'][0]
        review = json.loads((self.root / row['new_review']['path']).read_bytes())
        review['citations'] = [dict(quote='Not present in the original answer')]
        row['new_review'] = put(self.root, row['new_review']['path'], review)
        with self.assertRaisesRegex(ValueError, 'different answer bytes'):
            self.load()
        review['citations'] = [dict(quote='SYNTHETIC original answer')]
        row['new_review'] = put(self.root, row['new_review']['path'], review)
        inputs = self.load()
        wrong = copy.deepcopy(self.effective['partial']['nonlogical_retry_3'])
        wrong['attempt_condition'] = 'single_attempt'
        with self.assertRaisesRegex(ValueError, 'condition or effective source'):
            scoring.score_theorem_extension_calibration_overlay(wrong, self.policy, calibration=inputs,
                mode='partial', condition='nonlogical_retry_3')
        self.input_data['conditions']['single_attempt'].pop()
        with self.assertRaisesRegex(ValueError, 'all six'):
            self.load()

    def test_original_penalty_and_strict_blocking_survive_higher_r(self):
        inputs = self.load()
        payload = json.loads(inputs._payload)
        for condition in calibration.CONDITIONS:
            row = payload['conditions'][condition][0]
            claim = row['claim']
            claim['findings'] = [dict(id='local', root_cause='local', kind='false_assertion', severity='local',
                strict_blocking=True, core_endorsement=False, covered_by='none', reason='Synthetic false assertion.',
                evidence=[dict(source=0, quote='SYNTHETIC')])]
            for mode in calibration.MODES:
                base = self.effective[mode][condition]
                task = next(t for t in base['tasks'] if t['case_id'] == row['case_id'])
                from fractions import Fraction
                v, passed, detail = scoring.claim_penalties.assess((Fraction(1, 3),) * 3, False, claim, mode=mode)
                task['completion'] = {k:float(x) for k,x in zip(('lower','upper','exact'),v)}
                task['strict_pass'], task['claim_assessment'] = passed, detail
                task['submission_assessment']['prior_completion'] = copy.deepcopy(task['completion'])
                task['submission_assessment']['prior_strict_pass'] = passed
                payload['base_identities'][mode][condition] = identity(base)
        revised = calibration.CalibrationInputs(json.dumps(payload).encode())
        partial = self.score(inputs=revised)
        task = next(t for t in partial['tasks'] if t['case_id'] == self.ids[0])
        self.assertAlmostEqual(task['completion']['exact'], .95)
        self.assertFalse(task['strict_pass'])
        self.assertEqual(task['claim_assessment']['finding_ids'], ['local'])
        strict = self.score('strict', inputs=revised)
        self.assertAlmostEqual(strict['metrics']['theorem-extension']['exact'], 500 / 6)
        self.assertEqual(self.score('capability', inputs=revised)['metrics']['theorem-extension']['exact'], 100)

    def test_only_validated_input_type_and_matching_source_identity_is_accepted(self):
        with self.assertRaisesRegex(ValueError, 'validated source'):
            self.score(inputs={'new_R':3})
        inputs = self.load()
        self.effective['partial']['nonlogical_retry_3']['model_label'] = 'another model'
        with self.assertRaisesRegex(ValueError, 'model, condition or effective source'):
            self.score(inputs=inputs)

    def test_baseline_and_ordinary_charge_compose_by_max_and_core_cap_is_retained(self):
        from fractions import Fraction
        for kind in ('baseline', 'core'):
            with self.subTest(kind=kind):
                payload = json.loads(self.load()._payload)
                working = copy.deepcopy(self.effective)
                for condition in calibration.CONDITIONS:
                    row = payload['conditions'][condition][0]
                    row['baseline_B'] = 1 if kind == 'baseline' else 2
                    claim = row['claim']
                    claim['baseline_disposition'] = 'incorrect' if kind == 'baseline' else 'correct'
                    claim['findings'] = [dict(id='error', root_cause='one-root',
                        kind='false_assertion' if kind == 'baseline' else 'false_endorsement',
                        severity='local' if kind == 'baseline' else 'critical', strict_blocking=True,
                        core_endorsement=kind == 'core', covered_by='none', reason='Synthetic finding.',
                        evidence=[dict(source=0, quote='SYNTHETIC')])]
                    for mode in calibration.MODES:
                        base = working[mode][condition]
                        task = next(t for t in base['tasks'] if t['case_id'] == row['case_id'])
                        deduction = Fraction(1, 3) if kind == 'baseline' else Fraction(0)
                        value, passed, detail = scoring.claim_penalties.assess((Fraction(1, 3),) * 3,
                            False, claim, mode=mode, baseline_deduction=deduction)
                        task['completion'] = {k:float(x) for k,x in zip(('lower','upper','exact'),value)}
                        task['strict_pass'], task['claim_assessment'] = passed, detail
                        task['research']['baseline_B'] = row['baseline_B']
                        task['research']['baseline_penalty_points'] = int(deduction * 3)
                        task['submission_assessment']['prior_completion'] = copy.deepcopy(task['completion'])
                        task['submission_assessment']['prior_strict_pass'] = passed
                        payload['base_identities'][mode][condition] = identity(base)
                inputs = calibration.CalibrationInputs(json.dumps(payload).encode())
                result = scoring.score_theorem_extension_calibration_overlay(working['partial']['single_attempt'],
                    self.policy, calibration=inputs, mode='partial', condition='single_attempt')
                task = next(t for t in result['tasks'] if t['case_id'] == self.ids[0])
                self.assertAlmostEqual(task['completion']['exact'], 2 / 3 if kind == 'baseline' else 0)
                self.assertFalse(task['strict_pass'])
                self.assertEqual(task['claim_assessment']['generic_deduction'], .05 if kind == 'baseline' else .2)
                self.assertAlmostEqual(task['claim_assessment']['applied_deduction'], 1 / 3 if kind == 'baseline' else .2)
                self.assertEqual(task['claim_assessment']['core_endorsement_cap_applied'], kind == 'core')

    def test_unchanged_r_keeps_exact_old_rollups_while_binding_new_review(self):
        for condition, rows in self.input_data['conditions'].items():
            for row in rows:
                row['new_R'] = row['old_R']
                review = json.loads((self.root / row['new_review']['path']).read_bytes())
                review['new_R'] = row['new_R']
                row['new_review'] = put(self.root, row['new_review']['path'], review)
        inputs = self.load()
        for mode in calibration.MODES:
            result = self.score(mode, inputs=inputs)
            self.assertEqual(result['metrics'], self.effective[mode]['nonlogical_retry_3']['metrics'])
            self.assertEqual(result['contributions'], self.effective[mode]['nonlogical_retry_3']['contributions'])
            self.assertNotEqual(next(t for t in result['tasks'] if t['case_id'] == self.ids[0])['review_sha256'],
                self.grade['slots'][0]['review']['sha256'])

    def test_native_source_omitted_status_retains_its_original_reviewed_meaning(self):
        self.math['schema'] = 'math-gauge.native-harness-math/v1'
        self.record['schema'] = 'math-gauge.native-harness-private/v1'
        self.record.pop('benchmark_version')
        for row in self.math['tasks']:
            row.pop('status')
            row.pop('attempts')
        self.refresh_sources()
        inputs = self.load()
        self.assertEqual(self.score(inputs=inputs)['metrics']['theorem-extension']['exact'], 100)
        self.assertTrue(all('status' not in r for r in self.math['tasks']))

    def test_missing_final_remains_zero_and_unrun_retains_unknown_deduction_bounds(self):
        for number, status in ((0, 'delivery_failed'), (1, 'not_run')):
            cid = self.ids[number]
            level = 0 if status == 'delivery_failed' else None
            source = self.grade['slots'][number]
            source.update(status=status, baseline_B=None, research_R=level, response=None, review=None)
            if status == 'delivery_failed':
                source.update(failure_reason='service_error', execution={'sha256':'c'*64})
            self.math['tasks'][number].update(status=status, baseline_B=None, research_R=level,
                response=None, review=None, attempts=[dict(status=status)])
            claim = next(r for r in self.claims['cases'] if r['case_id'] == cid)
            claim.update(status=status, source_response_sha256=None, source_review_sha256=None,
                         baseline_disposition=None)
            for condition in calibration.CONDITIONS:
                sub = next(r for r in self.submissions[condition]['initials'] if r['case_id'] == cid)
                sub.update(classification='blank' if status == 'delivery_failed' else 'not_run',
                           source_response_sha256=None)
                row = self.input_data['conditions'][condition][number]
                row.update(response=None, source_review=None, baseline_B=None, old_R=level, new_R=level)
                review = json.loads((self.root / row['new_review']['path']).read_bytes())
                review.update(answer_sha256=None, source_review_sha256=None, baseline_B=None,
                              old_R=level, new_R=level, status=status, citations=[])
                row['new_review'] = put(self.root, row['new_review']['path'], review)
        self.refresh_sources()
        inputs = self.load()
        reliable = self.score(inputs=inputs)
        metric = reliable['metrics']['theorem-extension']
        self.assertIsNone(metric['exact'])
        self.assertAlmostEqual(metric['lower'], (4 - 2 / 3) / 6 * 100)
        self.assertAlmostEqual(metric['upper'], 5 / 6 * 100)
        self.assertEqual(metric['coverage']['planned'], 6)
        blank = next(t for t in reliable['tasks'] if t['case_id'] == self.ids[0])
        unknown = next(t for t in reliable['tasks'] if t['case_id'] == self.ids[1])
        self.assertEqual(blank['completion']['exact'], 0)
        self.assertIsNone(blank['research']['baseline_B'])
        self.assertIsNone(unknown['completion']['exact'])
        self.assertIsNone(unknown['strict_pass'])

    def test_public_projection_remains_aggregate_only_and_rejects_private_extra_fields(self):
        inputs = self.load()
        report = self.score(inputs=inputs)
        projected = project_assessment_score(report)
        self.assertNotIn('tasks', projected)
        self.assertNotIn('Fixture-Private-', json.dumps(projected))
        self.assertEqual(projected['tx_calibration']['inputs_sha256'], json.loads(inputs._payload)['inputs_sha256'])
        manifest = dict(schema=calibration.PUBLIC_SCHEMA, private_case_ids=['private'])
        item = put(self.public, 'reassessment/public.json', manifest)
        with self.assertRaisesRegex(ValueError, 'privacy boundary'):
            calibration.load_public(self.public, item, policy=self.calibration_policy,
                effective_scores={}, source_record={})

    def public_fixture(self):
        inputs = self.load()
        inputs_ref = descriptor(self.root, self.root / 'reassessment/inputs.json')
        ids = sorted(r['case_id'] for r in self.fixture.plan['case_index'])
        public_record = copy.deepcopy(self.record)
        public_record['public_deliveries'] = []
        originals = {row['case_id']: row for row in self.grade['slots']}
        for cid in ids:
            response = originals.get(cid, {}).get('response')
            if response is not None:
                put(self.public / self.folder, response['path'],
                    (self.root / self.folder / response['path']).read_bytes())
            public_record['public_deliveries'].append(dict(case_id=cid, response=response))
        private_manifest = dict(schema=calibration.PRIVATE_SCHEMA, version='0.1.0',
            benchmark_version='1.1.0', model_id='fixture-model', record_id='snapshot',
            inputs=inputs_ref, scores={})
        manifest = dict(schema=calibration.PUBLIC_SCHEMA, version='0.1.0', benchmark_version='1.1.0',
            model_id='fixture-model', record_id='snapshot',
            source_record=put(self.public, self.record_ref['path'], public_record), policy=self.policy_ref,
            private_inputs_sha256=inputs_ref['sha256'], private_manifest_sha256='a'*64,
            base_reports={}, scores={}, public_reviews={}, human_review='pending',
            formal_comparison_eligible=False, new_candidate_calls=0, post_observation=True)
        old_tasks = dict(schema='math-gauge.public-task-scores/v1', benchmark_version='1.0.0',
            model_label=self.model, public_case_ids=ids, human_review='pending',
            formal_comparison_eligible=False, views={})
        new_tasks = copy.deepcopy(old_tasks)
        new_tasks['benchmark_version'] = '1.1.0'
        public_bases, public_scores = {}, {}
        for mode in calibration.MODES:
            manifest['base_reports'][mode], manifest['scores'][mode] = {}, {}
            private_manifest['scores'][mode] = {}
            public_bases[mode], public_scores[mode], old_tasks['views'][mode], new_tasks['views'][mode] = {}, {}, {}, {}
            for condition in calibration.CONDITIONS:
                base = self.effective[mode][condition]
                old_sha = self.input_data['base_reports'][mode][condition]['sha256']
                public_base = calibration.project_score(base)
                public_base['source_bindings']['private_report_sha256'] = old_sha
                public_bases[mode][condition] = public_base
                manifest['base_reports'][mode][condition] = put(self.public,
                    'reassessment/base-' + mode + '-' + condition + '.json', public_base)
                old_tasks['views'][mode][condition] = project_public_task_view(base, ids, old_sha)
                report = self.score(mode, condition, inputs=inputs)
                private_ref = put(self.root, 'reassessment/' + mode + '-' + condition + '.json', report)
                private_manifest['scores'][mode][condition] = private_ref
                public_score = calibration.project_score(report)
                public_score['source_bindings']['private_report_sha256'] = private_ref['sha256']
                public_scores[mode][condition] = public_score
                manifest['scores'][mode][condition] = put(self.public,
                    'reassessment/' + mode + '-' + condition + '.json', public_score)
                new_tasks['views'][mode][condition] = project_public_task_view(report, ids, private_ref['sha256'])
        manifest['base_public_tasks'] = put(self.public, 'reassessment/base-public-tasks.json', old_tasks)
        manifest['public_tasks'] = put(self.public, 'reassessment/public-tasks.json', new_tasks)
        private_ref = put(self.root, 'reassessment/private.json', private_manifest)
        manifest['private_manifest_sha256'] = private_ref['sha256']
        for condition in calibration.CONDITIONS:
            refs = []
            for row in self.input_data['conditions'][condition]:
                if row['case_id'] in calibration.PUBLIC_CASES:
                    ref = row['new_review']
                    copied = put(self.public, ref['path'], (self.root / ref['path']).read_bytes())
                    refs.append(dict(case_id=row['case_id'], review=copied))
            manifest['public_reviews'][condition] = refs
        public_ref = put(self.public, 'reassessment/public.json', manifest)
        return (inputs, private_ref, manifest, public_ref, public_record,
                public_bases, public_scores, old_tasks, new_tasks, ids)

    def test_private_replay_and_public_round_trip_share_one_canonical_result(self):
        (inputs, private_ref, manifest, public_ref, public_record,
         public_bases, public_scores, old_tasks, new_tasks, ids) = self.public_fixture()
        checked = calibration.load_private(self.root, private_ref, public_root=self.public,
            policy=self.calibration_policy, effective_scores=self.effective, assessment_policy=self.policy)
        self.assertEqual(checked['_scores']['partial']['single_attempt'],
                         self.score('partial', 'single_attempt', inputs=inputs))
        public = calibration.load_public(self.public, public_ref, policy=self.calibration_policy,
            effective_scores=public_bases, source_record=public_record, public_case_ids=ids)
        self.assertEqual(public['_scores'], public_scores)
        self.assertEqual(public['_public_tasks'], new_tasks)
        paired = calibration.verify_pair(self.public, self.root, public_ref, private_ref,
            policy=self.calibration_policy, assessment_policy=self.policy,
            public_effective_scores=public_bases, private_effective_scores=self.effective,
            source_record=public_record, public_case_ids=ids)
        self.assertEqual(paired['public']['_scores'], public_scores)
        # Opaque source hashes alone cannot authorize a hand-edited aggregate.
        score = copy.deepcopy(public_scores['partial']['single_attempt'])
        score['metrics']['earned']['confirmed'] += 1
        original_ref = manifest['scores']['partial']['single_attempt']
        manifest['scores']['partial']['single_attempt'] = put(self.public, 'reassessment/tampered-score.json', score)
        public_ref = put(self.public, 'reassessment/public.json', manifest)
        with self.assertRaisesRegex(ValueError, 'private shared-scorer report'):
            calibration.verify_pair(self.public, self.root, public_ref, private_ref,
                policy=self.calibration_policy, assessment_policy=self.policy,
                public_effective_scores=public_bases, private_effective_scores=self.effective,
                source_record=public_record, public_case_ids=ids)
        manifest['scores']['partial']['single_attempt'] = original_ref
        # An unrelated public task cannot acquire a different judgment through
        # a TX projection, even with freshly recomputed container hashes.
        non_tx = next(r for r in new_tasks['views']['partial']['single_attempt']['tasks']
                      if r['case_id'] not in calibration.PUBLIC_CASES)
        non_tx['strict_pass'] = True
        manifest['public_tasks'] = put(self.public, 'reassessment/public-tasks.json', new_tasks)
        public_ref = put(self.public, 'reassessment/public.json', manifest)
        with self.assertRaisesRegex(ValueError, 'another task judgment'):
            calibration.load_public(self.public, public_ref, policy=self.calibration_policy,
                effective_scores=public_bases, source_record=public_record, public_case_ids=ids)

    def test_rehashed_private_member_substitution_cannot_replace_canonical_public_membership(self):
        (_, private_ref, manifest, _, public_record,
         public_bases, _, old_tasks, new_tasks, ids) = self.public_fixture()
        removed = next(cid for cid in ids if cid not in calibration.PUBLIC_CASES)
        private_id = self.ids[2]
        altered_ids = sorted(set(ids) - {removed} | {private_id})
        for projection in (old_tasks, new_tasks):
            projection['public_case_ids'] = altered_ids
            for mode in calibration.MODES:
                for condition in calibration.CONDITIONS:
                    rows = projection['views'][mode][condition]['tasks']
                    rows[:] = [r for r in rows if r['case_id'] != removed]
                    full = self.effective[mode][condition]
                    if projection is new_tasks:
                        full = self.score(mode, condition)
                    task = next(r for r in full['tasks'] if r['case_id'] == private_id)
                    rows.append({key:copy.deepcopy(task[key]) for key in
                        ('case_id', 'completion', 'strict_pass', 'response_sha256', 'review_sha256')})
                    rows.sort(key=lambda row:row['case_id'])
        manifest['base_public_tasks'] = put(self.public, 'reassessment/base-public-tasks.json', old_tasks)
        manifest['public_tasks'] = put(self.public, 'reassessment/public-tasks.json', new_tasks)
        public_ref = put(self.public, 'reassessment/public.json', manifest)
        for requested in (None, altered_ids, ids):
            with self.subTest(requested=requested), self.assertRaisesRegex(ValueError, 'canonical|task projection'):
                calibration.load_public(self.public, public_ref, policy=self.calibration_policy,
                    effective_scores=public_bases, source_record=public_record, public_case_ids=requested)
        with self.assertRaisesRegex(ValueError, 'canonical|task projection'):
            calibration.verify_pair(self.public, self.root, public_ref, private_ref,
                policy=self.calibration_policy, assessment_policy=self.policy,
                public_effective_scores=public_bases, private_effective_scores=self.effective,
                source_record=public_record)

    def test_base_task_projection_rejects_private_fields_and_wrong_source_assessment(self):
        (_, _, manifest, _, public_record, public_bases, _, old_tasks, _, _) = self.public_fixture()
        valid = copy.deepcopy(old_tasks)
        for change in ('top-level', 'task', 'source-version'):
            old_tasks = copy.deepcopy(valid)
            if change == 'top-level':
                old_tasks['private_note'] = 'A private annotation must not enter this container.'
            elif change == 'task':
                old_tasks['views']['partial']['single_attempt']['tasks'][0]['private_note'] = 'Not public.'
            else:
                old_tasks['benchmark_version'] = '0.6.0'
            manifest['base_public_tasks'] = put(self.public, 'reassessment/base-public-tasks.json', old_tasks)
            public_ref = put(self.public, 'reassessment/public.json', manifest)
            with self.subTest(change=change), self.assertRaises(ValueError):
                calibration.load_public(self.public, public_ref, policy=self.calibration_policy,
                    effective_scores=public_bases, source_record=public_record)

    def test_public_review_quotes_actual_selected_answer_and_tx_metadata_rejects_private_fields(self):
        (_, _, manifest, _, public_record, public_bases, public_scores, _, new_tasks, _) = self.public_fixture()
        ref = manifest['public_reviews']['single_attempt'][0]
        review = json.loads((self.public / ref['review']['path']).read_bytes())
        review['citations'] = [dict(quote='This sentence does not occur in the original answer.')]
        original_ref = copy.deepcopy(ref['review'])
        ref['review'] = put(self.public, 'reassessment/bad-review.json', review)
        for mode in calibration.MODES:
            task = next(r for r in new_tasks['views'][mode]['single_attempt']['tasks'] if r['case_id'] == ref['case_id'])
            task['review_sha256'] = ref['review']['sha256']
        manifest['public_tasks'] = put(self.public, 'reassessment/public-tasks.json', new_tasks)
        public_ref = put(self.public, 'reassessment/public.json', manifest)
        with self.assertRaisesRegex(ValueError, 'different answer bytes'):
            calibration.load_public(self.public, public_ref, policy=self.calibration_policy,
                effective_scores=public_bases, source_record=public_record)
        ref['review'] = original_ref
        score = copy.deepcopy(public_scores['partial']['single_attempt'])
        score['tx_calibration']['private_note'] = 'Do not project private diagnostic fields.'
        manifest['scores']['partial']['single_attempt'] = put(self.public, 'reassessment/bad-score.json', score)
        public_ref = put(self.public, 'reassessment/public.json', manifest)
        with self.assertRaisesRegex(ValueError, 'aggregate-only boundary'):
            calibration.load_public(self.public, public_ref, policy=self.calibration_policy,
                effective_scores=public_bases, source_record=public_record)

    def test_public_answer_reads_exact_condition_selected_original_index(self):
        folder = self.public / self.folder
        first = put(folder, 'first-answer.md', b'SYNTHETIC first condition answer')
        retry = put(folder, 'retry-answer.md', b'SYNTHETIC selected retry answer')
        refs = {}
        for condition, answer in zip(calibration.CONDITIONS, (first, retry)):
            refs[condition] = dict(source_records=put(folder, condition + '-records.json',
                dict(records=[dict(case_id='MG-TX001', id='MG-TX001:A1', response=answer)])))
        record = dict(attempt_condition_sources=put(folder, 'condition-sources.json', dict(conditions=refs)))
        self.assertEqual(calibration._public_answer(self.public, self.folder, record, cid='MG-TX001',
            condition='nonlogical_retry_3', response_sha256=retry['sha256']), b'SYNTHETIC selected retry answer')
        with self.assertRaisesRegex(ValueError, 'selected original answer bytes'):
            calibration._public_answer(self.public, self.folder, record, cid='MG-TX001',
                condition='single_attempt', response_sha256=retry['sha256'])


if __name__ == '__main__':
    unittest.main()
