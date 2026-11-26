"""Synthetic contract fixtures; these are not candidate outputs or judgments."""
from copy import deepcopy
import json
import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from math_gauge import exploration_orientation as owner

class ExplorationOrientationTests(unittest.TestCase):

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.public, self.private = (self.root / 'public', self.root / 'private')
        self.public.mkdir()
        self.private.mkdir()
        self.roots = dict(public=self.public, private=self.private)
        self.policy = dict(cohort=dict(selected_configurations=['fixture']))
        self.pb = dict(bytes=30589, sha256=owner.POLICY_SHA256)
        self.registry = []

        def add(sid, rid, text, kind):
            name = 'prompts/' + rid + '.md' if sid.startswith('prompt:') else 'raw/' + sid.replace(':', '-') + '.md'
            path = self.private / name
            path.parent.mkdir(exist_ok=True)
            path.write_text(text)
            ref = owner.reference('private', name, path.read_bytes())
            self.registry.append(dict(source_id=sid, round=rid, descriptor=ref, selection_binding={}, kind=kind))
            return ref
        self.refs = {}
        for rid in owner.ROUND_IDS:
            self.refs['prompt:' + rid] = add('prompt:' + rid, rid, 'Choose and investigate an actual question.', 'task-boundary')
            self.refs[rid] = add(rid, rid, 'Concrete optional construction; operation; observed obstruction.', 'anchor-delivery')
        self.support = []
        facts_raw = owner.encoded(dict(facts=[dict(read_scope='full', mathematical_check='Synthetic required proof checked.') for _ in range(27)]))
        (self.private / 'facts.json').write_bytes(facts_raw)
        fact_ref = owner.reference('private', 'facts.json', facts_raw)
        for index in range(27):
            cid = 'fixture-' + str(index)
            task = add('task:' + cid, 'A1', 'Solve exactly the required goal.', 'support-task-boundary')
            source = add('a1:' + cid + ':answer', 'A1', 'Required proof with no optional fragment.', 'support-delivery')
            self.support.append(dict(case_id=cid, family_id=cid, source_state='selected-source-available', aliases={'answer': 'a1:' + cid + ':answer'}, task_source_id='task:' + cid, original_task=task, selected_a1_binding=dict(source={}, pointer='/slots/' + str(index)), factual_review_pointers=[dict(source=fact_ref, pointer='/facts/' + str(index))]))
        self.material = dict(schema=owner.MATERIAL_SCHEMA, model_id='fixture', policy_binding=self.pb, cohort_binding={}, selected_trajectory_manifest={}, source_registry=self.registry, support_opportunities=self.support, existing_anchor_factual_reviews=[])
        self.review = dict(schema=owner.REVIEW_SCHEMA, edition=owner.EDITION, model_id='fixture', record_id='synthetic-fixture', policy_binding=self.pb, cohort_binding={}, selected_trajectory_manifest={}, new_candidate_calls=0, main_scores_modified=False, existing_axes_modified=False, reviewer=dict(kind='ai', human_review='pending', post_observation=True, identity='synthetic-test', context_id='fixture'), source_registry=[{k: deepcopy(v) for k, v in row.items() if k != 'kind'} | dict(read_scope='full') for row in self.registry], sources_complete=True, profile_identifiability='identifiable', actions=[self.action()], episodes=[dict(episode_id='episode', action_refs=['action'], question_or_route_family='A concrete optional route', deduplication_reason='One question, one episode.', independence_cluster='cluster', first_seen_round='R1', last_observed_round='R1', final_disposition='Located an actual obstacle.')], stage_trace=[dict(action_id='action', episode_id='episode', round='R1', prompt_relation='self_chosen_within_open_invitation', stage_role='new', relation_to_previous_action=None, evidence=[self.quote('R1')])], axes={}, corroboration=dict(feeds_main_radar=False, planned_families=27, status='complete', family_observations=[]))
        for aid in owner.AXIS_IDS:
            positive = aid == 'vertical_deepening'
            self.review['axes'][aid] = dict(grade=4 if positive else 0, state='reviewed' if positive else 'reviewed_absence', coding_confidence='high', exposure_constraints=[], action_refs=['action'] if positive else [], prompt_and_freedom_reason='The original invitation permits this choice.', source_coverage=dict(R1='full', R2='full', R3='full', attachments='not_applicable'), organizing_role_reason='The concrete question organizes the inquiry.' if positive else 'Full read found no such action.', verification_summary='The serious attempted route remains unclosed.', unknown_reason=None, reviewed_absence_reason=None if positive else 'All selected rounds read; only another eligible organizing action is present.', mainline_rationale='Actual operations pursue the same question.', centrality_rationale='Removing this route changes the agenda.', whole_trajectory_evidence=[self.quote('R1')] if positive else [])
        for slot in self.support:
            self.review['corroboration']['family_observations'].append(dict(family_id=slot['family_id'], screening_complete=True, read_scope='full', selected_a1_binding=slot['selected_a1_binding'], task_and_required_boundary_binding=slot['original_task'], eligible_extra_action_refs=[], by_axis={aid: dict(fragment_present=False, relation='insufficient', reason='Only the required goal is delivered.', substantive_and_autonomous_reason=None, evidence=[]) for aid in owner.AXIS_IDS}))
        self.review = owner.with_derived_counts(self.review, self.material)
        self.real_source_gate = owner.validate_material_sources
        self.source_gate = patch.object(owner, 'validate_material_sources', return_value=None)
        self.source_gate.start()

    def tearDown(self):
        self.source_gate.stop()
        self.temp.cleanup()

    def quote(self, sid):
        ref = next((row['descriptor'] for row in self.registry if row['source_id'] == sid))
        raw = (self.private / ref['path']).read_bytes()
        return dict(source_id=sid, sha256=ref['sha256'], start=0, end=len(raw), quote=raw.decode())

    def action(self):
        return dict(action_id='action', episode_id='episode', question_or_choice='Probe a meaningful optional mechanism.', concrete_operation='Carry out a nonroutine construction.', actual_observation_or_failure_location='A concrete bottleneck is located.', requiredness_reason='The route was chosen within the open invitation.', independence_cluster='cluster', round='R1', source_id='R1', prompt_relation='self_chosen_within_open_invitation', stage_role='new', requiredness='discretionary_within_main_open_task', question_inferred_from_math=False, parent_action_id=None, evidence=[self.quote('R1')], task_boundary_evidence=[self.quote('prompt:R1')], verification=dict(state='substantive_attempt_unclosed', execution_support='execution_not_established', mathematical_reason='The bottleneck remains unproved.', claim_limits='No completed theorem is asserted.', source_evidence=[self.quote('R1')], reused_review_refs=[]), axis_assignments=[dict(axis_id='vertical_deepening', organizing_role='central', trigger_reason='The chosen mechanism is pursued.', role_reason='It organizes the subsequent questions.', evidence=[self.quote('R1')])])

    def check(self, review=None):
        value = self.review if review is None else review
        return owner.validate_review(value, self.material, self.policy, public_root=self.public, private_root=self.private)

    def test_serious_unclosed_attempt_can_organize_grade_four(self):
        self.check()

    def test_truth_failure_is_separate_from_organizing_role(self):
        for status in ('refuted_claim', 'invalid_operation'):
            review = deepcopy(self.review)
            review['actions'][0]['verification']['state'] = status
            self.check(review)

    def test_high_grade_needs_mainline_and_centrality_not_length(self):
        for field in ('mainline_rationale', 'centrality_rationale'):
            review = deepcopy(self.review)
            review['axes']['vertical_deepening'][field] = None
            with self.assertRaises(ValueError):
                self.check(review)

    def test_zero_requires_identifiable_context_and_full_absence(self):
        review = deepcopy(self.review)
        review['actions'][0]['requiredness'] = 'required_or_routine'
        with self.assertRaisesRegex(ValueError, 'identifiable exploration'):
            self.check(review)
        review = deepcopy(self.review)
        review['axes']['horizontal_expansion']['reviewed_absence_reason'] = None
        with self.assertRaisesRegex(ValueError, 'Zero requires'):
            self.check(review)

    def test_source_gap_is_not_zero(self):
        review = deepcopy(self.review)
        review['sources_complete'] = False
        with self.assertRaisesRegex(ValueError, 'complete read coverage'):
            self.check(review)

    def test_wrong_quote_hash_and_unselected_alias_fail(self):
        for update in ({'sha256': '0' * 64}, {'source_id': 'hidden-thought'}):
            review = deepcopy(self.review)
            review['actions'][0]['evidence'][0].update(update)
            with self.assertRaises(ValueError):
                self.check(review)

    def test_no_numeric_old_scores_enter_public_projection(self):
        report = owner.project_public(self.review, self.material, private_review_sha256='a' * 64)
        owner.validate_public(report, self.pb)
        self.assertFalse(report['is_score'])
        self.assertIsNone(report['higher_is_better'])
        serialized = json.dumps(report)
        self.assertNotIn('fixture-0', serialized)
        self.assertNotIn('source_id', serialized)
        self.assertNotIn('quote', serialized)
        report['raw_answer'] = 'private bytes'
        with self.assertRaisesRegex(ValueError, 'aggregate fields'):
            owner.validate_public(report, self.pb)

    def test_support_counts_do_not_fill_null_main(self):
        review = deepcopy(self.review)
        row = review['axes']['horizontal_expansion']
        row.update(grade=None, state='classification_unresolved', unknown_reason='classification_unresolved', coding_confidence='unresolved')
        review = owner.with_derived_counts(review, self.material)
        self.check(review)
        report = owner.project_public(review, self.material, private_review_sha256='a' * 64)
        self.assertIsNone(report['axes']['horizontal_expansion']['grade'])
        self.assertIsNone(report['corroboration']['horizontal_expansion']['support'])
        owner.validate_public(report, self.pb)

    def test_family_partition_cannot_shrink_or_double_count(self):
        review = deepcopy(self.review)
        review['corroboration']['family_observations'].pop()
        with self.assertRaisesRegex(ValueError, 'all27'):
            self.check(review)
        review = deepcopy(self.review)
        review['corroboration']['family_observations'][-1] = deepcopy(review['corroboration']['family_observations'][0])
        with self.assertRaisesRegex(ValueError, 'once per axis'):
            self.check(review)

    def test_counts_must_match_actual_unique_family_labels(self):
        review = deepcopy(self.review)
        review['corroboration']['by_axis']['vertical_deepening']['support'] = 1
        with self.assertRaisesRegex(ValueError, 'counts must match'):
            self.check(review)

    def test_public_projection_rejects_hidden_reason_field(self):
        report = owner.project_public(self.review, self.material, private_review_sha256='a' * 64)
        report['axes']['vertical_deepening']['reason'] = 'Private mathematical reason.'
        with self.assertRaises(ValueError):
            owner.validate_public(report, self.pb)

    def test_a1_action_cannot_be_main_radar_evidence(self):
        review = deepcopy(self.review)
        review['axes']['horizontal_expansion'].update(grade=2, state='reviewed', action_refs=['a1-extra'])
        with self.assertRaisesRegex(ValueError, 'main radar'):
            self.check(review)

    def test_registry_membership_rejects_an_unselected_file_with_correct_hash(self):
        area = self.root / 'intake'
        (area / 'models').mkdir(parents=True)
        original = dict(model_id='fixture', anchor=dict(original_task_materials=dict(supplied_materials=[self.refs['prompt:' + rid] for rid in owner.ROUND_IDS]), rounds=[dict(round=rid, selected_documents=[dict(source_id=rid, source=self.refs[rid])]) for rid in owner.ROUND_IDS], existing_mathematical_facts=[], existing_autonomous_mathematical_review=dict(source_status='stale-unavailable-before-explicit-admission'), selected_source_adoption=[]), a1_support_opportunities=[])
        for slot in self.support:
            source = next((r['descriptor'] for r in self.registry if r['source_id'] == slot['aliases']['answer']))
            original['a1_support_opportunities'].append(dict(case_id=slot['case_id'], family_id=slot['family_id'], source_state=slot['source_state'], common_task_ref=slot['original_task'], selected_documents={'answer': source}, existing_autonomous_mathematical_review=slot['factual_review_pointers'][0], other_existing_mathematical_facts=[]))
        raw = owner.encoded(original)
        (area / 'models/fixture.json').write_bytes(raw)
        inventory = dict(cohort=['fixture'], models=[dict(model_id='fixture', path='models/fixture.json', **owner.binding(raw))])
        inv = owner.encoded(inventory)
        (area / 'source-manifest.json').write_bytes(inv)
        material = deepcopy(self.material)
        modelref = owner.reference('private', owner.INTAKE_PREFIX + '/models/fixture.json', raw)
        material.update(selected_trajectory_manifest=modelref, cohort_binding=dict(configuration_ids_sha256=owner.digest(owner.encoded(['fixture'])), source_inventory=owner.binding(inv)), support_contract=dict(bytes=102239, sha256=owner.SUPPORT_SHA256), anchor_rounds=original['anchor']['rounds'], source_selection_receipts=[])
        for row in material['source_registry']:
            row['selection_binding'] = modelref
        with patch.object(owner, 'INTAKE_SHA256', owner.digest(inv)), patch.object(owner, '_verify_indexed_selection'):
            self.real_source_gate(material, public_root=self.public, private_root=self.private, intake_root=area)
            material['source_registry'][1]['descriptor'] = dict(material['source_registry'][1]['descriptor'], path='raw/unselected.md')
            (self.private / 'raw/unselected.md').write_bytes((self.private / self.refs['R1']['path']).read_bytes())
            with self.assertRaisesRegex(ValueError, 'opened an unselected source'):
                self.real_source_gate(material, public_root=self.public, private_root=self.private, intake_root=area)

    def test_stage_public_loader_and_final_attach_preserve_existing_fields(self):
        policy = dict(version=owner.VERSION, edition=owner.EDITION, status='frozen-before-new-orientation-coding', publication=dict(axis_order=list(owner.AXIS_IDS)), construct=dict(scale=dict(total=None)), main_scores_modified=False, existing_ten_axes_modified=False, cohort=dict(selected_configurations=['fixture', 'fixture2']))
        pb = owner.binding(owner.encoded(policy))
        material = deepcopy(self.material)
        material['policy_binding'] = pb
        review = deepcopy(self.review)
        review['policy_binding'] = pb
        material2 = deepcopy(material)
        material2['model_id'] = 'fixture2'
        review2 = deepcopy(review)
        review2['model_id'] = 'fixture2'
        with patch.object(owner, 'POLICY_SHA256', pb['sha256']):
            public, private = owner.stage({'fixture': review, 'fixture2': review2}, {'fixture': material, 'fixture2': material2}, policy, public_root=self.public, private_root=self.private)
            public[owner.POLICY_PATH] = owner.encoded(policy)
            for name, raw in public.items():
                p = self.public / name
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_bytes(raw)
            component = owner.load_public(self.public, cohort=['fixture2', 'fixture'])
            self.assertEqual(component['models'][0]['axes']['vertical_deepening']['grade'], 4)
            old = {'benchmark_version': '1.2.0', 'models': [{'id': 'fixture2'}, {'id': 'fixture'}], 'preserved': {'raw': 'same'}}
            self.assertEqual(owner.attach_public(deepcopy(old), self.public), old)
            data = deepcopy(old)
            data['benchmark_version'] = '1.3.0'
            owner.attach_public(data, self.public)
            self.assertEqual(data['preserved'], old['preserved'])
            self.assertIn('exploration_orientation', data)
            for cohort in (['other'], ['fixture', 'fixture'], ['fixture', 'other']):
                with self.assertRaisesRegex(ValueError, 'displayed settled cohort'):
                    owner.load_public(self.public, cohort=cohort)
            path = self.public / (owner.PRIVATE_PREFIX + '/fixture/profile.json')
            path.write_bytes(path.read_bytes() + b' ')
            with self.assertRaisesRegex(ValueError, 'source bytes changed'):
                owner.load_public(self.public, cohort=['fixture', 'fixture2'])

    def test_reused_full_review_scope_is_honest_and_family_bound(self):
        review = deepcopy(self.review)
        for index, row in enumerate(review['corroboration']['family_observations']):
            row['read_scope'] = 'reused_full_review_and_exact_fragments'
            row['reused_factual_review_refs'] = self.support[index]['factual_review_pointers']
        self.check(review)
        review['corroboration']['family_observations'][0]['reused_factual_review_refs'] = self.support[1]['factual_review_pointers']
        with self.assertRaisesRegex(ValueError, 'Unselected mathematical review'):
            self.check(review)

    def test_later_abandonment_tag_comes_from_actual_trace(self):
        review = deepcopy(self.review)
        review['stage_trace'].append(dict(action_id='action', episode_id='episode', round='R3', prompt_relation='required_or_routine', stage_role='abandoned', relation_to_previous_action='action', evidence=[self.quote('R3')]))
        self.check(review)
        report = owner.project_public(review, self.material, private_review_sha256='a' * 64)
        self.assertIn('abandoned_route', report['tags'])
        self.assertNotIn('invited_followup', report['tags'])

    def test_child_supplement_download_link_and_privacy_contract(self):
        path = Path(owner.__file__).resolve().parents[1] / 'scripts/results_exploration_orientation.py'
        spec = importlib.util.spec_from_file_location('exploration_adapter_fixture', path)
        adapter = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(adapter)
        component = dict(edition='1.3.0', private_only_marker='never-render-this')
        shell = adapter.render_panel(component)
        self.assertIn('id="exploration-orientation"', shell)
        self.assertNotIn('never-render-this', shell)
        report = owner.project_public(self.review, self.material, private_review_sha256='a' * 64)
        envelope = dict(schema='math-gauge.exploration-orientation/v1', version=owner.VERSION, edition='1.3.0', policy_sha256=owner.POLICY_SHA256, source_index=dict(path=owner.PUBLIC_INDEX, bytes=1, sha256='b' * 64), axis_order=list(owner.AXIS_IDS), scale=[0, 4], models=[report], human_review='pending', post_observation=True)
        files = adapter.download_files(envelope)
        self.assertIn('versions/1.3.0/downloads/exploration-orientation.json', files)
        self.assertIn('href="versions/1.3.0/downloads/exploration-orientation.json"', shell)
        self.assertEqual(adapter.render_panel(None), '')
        with self.assertRaisesRegex(ValueError, 'public aggregate envelope'):
            adapter.download_files(dict(envelope, private_only_marker='must-not-export'))
if __name__ == '__main__':
    unittest.main()
