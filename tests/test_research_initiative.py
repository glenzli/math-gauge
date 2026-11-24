from copy import deepcopy
from pathlib import Path
import json
import tempfile
import unittest

from math_gauge import research_initiative as owner


class InitiativeCase(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.roots = {'private': self.root, 'public': self.root}
        self.policy_hash = 'a' * 64
        self.policy = {'planned_opportunities': 28, 'private_contract_sha256': 'b' * 64}

    def fixture(self, *, grades=None, mid='model-a', unavailable=(), blank=()):
        ids = ['case-' + str(i) for i in range(27)] + ['independent-extension']
        grades = grades or dict.fromkeys(ids, 0)
        materials, proposed = [], []
        for cid in ids:
            status = 'unavailable' if cid in unavailable else 'settled_blank' if cid in blank else 'available'
            sources, evidence = {}, []
            if status == 'available':
                path = self.root / mid / (cid + '.md')
                path.parent.mkdir(exist_ok=True)
                quote = f'{mid}/{cid}: a separately posed question and checked mathematical work.'
                path.write_text(quote + '\nOriginal requested work remains separate.\n')
                ref = owner.reference(self.root, path, 'private')
                sources['answer'] = ref
                evidence = [dict(source_id='answer', sha256=ref['sha256'], start=0,
                                 end=len(quote.encode()), quote=quote)]
            materials.append(dict(opportunity_id=cid, source_status=status,
                                  classification='blank' if status == 'settled_blank' else 'active_final',
                                  sources=sources))
            proposed.append(dict(model_id=mid, opportunity_id=cid,
                grade=None if status == 'unavailable' else grades[cid],
                assessment_status='reviewed' if status == 'available' else status,
                full_delivery_read=True, original_requirement_boundary='Required original goal, unchanged.',
                independent_question='A separately posed mathematical question.',
                mathematical_check='Verified within the explicit additional scope.',
                grade_reason='Judged from the exact original answer, not its other scores.', evidence=evidence))
        parent = dict(schema='math-gauge.research-initiative-review-proposal/v1', reviewer_kind='ai',
            human_review='pending', reviewer=dict(requested_model='gpt-6.1-sol', effort='max', context='fresh-review-context'),
            rows=proposed)
        path = self.root / (mid + '-primary.json')
        path.write_bytes(owner.encoded(parent))
        ref = owner.reference(self.root, path, 'private')
        rows = [dict(deepcopy(r), primary_review=dict(ref=ref, row=i)) for i, r in enumerate(proposed)]
        review = dict(schema='math-gauge.research-initiative-review/v1', version=owner.VERSION,
            edition=owner.EDITION, condition=owner.CONDITION, model_id=mid, policy_sha256=self.policy_hash,
            private_contract_sha256=self.policy['private_contract_sha256'], reviewer_kind='ai',
            human_review='pending', new_candidate_calls=0, reviewer_context_id='coordinator-context', rows=rows)
        material = dict(model_id=mid, rows=materials)
        return review, material

    def validate(self, review, material):
        return owner.validate_review(review, material, self.policy, self.policy_hash, self.roots)

    def test_new_three_round_opportunity_has_exactly_one_equal_weight(self):
        grades = dict.fromkeys(['case-' + str(i) for i in range(27)] + ['independent-extension'], 0)
        grades['independent-extension'] = 4
        review, material = self.fixture(grades=grades)
        self.validate(review, material)
        score = owner.score_review(review)
        self.assertAlmostEqual(score['metric']['exact'], 100 / 28)
        self.assertEqual(score['extension_metric']['exact'], 100)
        self.assertEqual(score['legacy_metric']['exact'], 0)
        self.assertEqual(score['metric']['coverage']['planned'], 28)

    def test_sealed_companions_are_read_with_the_final_but_loose_workspace_is_excluded(self):
        state = self.root / 'state'
        state.mkdir()
        for rid in ('R1', 'R2', 'R3'):
            final = state / (rid + '.md')
            final.write_text('The mathematical manuscript is explicitly delivered as a companion.')
            manuscript = state / (rid + '.files') / 'manuscript.md'
            manuscript.parent.mkdir()
            manuscript.write_text(rid + ': original mathematical manuscript')
            final_ref = owner.reference(state, final, 'private')
            file_ref = owner.reference(state, manuscript, 'private')
            seal = dict(delivery='normal-final', raw={k: final_ref[k] for k in ('path', 'bytes', 'sha256')},
                        files=[{k: file_ref[k] for k in ('path', 'bytes', 'sha256')}])
            (state / (rid + '.seal.json')).write_bytes(owner.encoded(seal))
        (state / 'unsubmitted-work.md').write_text('Not a delivered answer.')
        files = owner._sealed_sources(state)
        self.assertEqual(len(files), 6)
        self.assertIn('R1.files/manuscript.md', files)
        self.assertNotIn('unsubmitted-work.md', files)
        (state / 'R2.files/manuscript.md').write_text('A later repair must fail the original seal.')
        with self.assertRaises(ValueError):
            owner._sealed_sources(state)

    def test_legacy_named_attachment_preserves_its_actual_capture_limit(self):
        session = self.root / 'original/sessions/case-0/physical-1'
        (session / 'output/artifacts').mkdir(parents=True)
        (session / 'runtime').mkdir()
        named = '/private/tmp/old-run/sessions/case-0/physical-1/output/artifacts/manuscript.md'

        def save(path, value):
            path.write_bytes(value if isinstance(value, bytes) else owner.encoded(value))
            return owner.reference(self.root, path, 'private')

        answer = save(session / 'output/response.md', ('Full delivered manuscript: ' + named).encode())
        artifact = save(session / 'output/artifacts/manuscript.md', b'Original delivered mathematical body.')
        events = save(session / 'output/events.ndjson', b'\n'.join(json.dumps(event).encode() for event in [
            dict(type='item.completed', item=dict(type='file_change', status='completed',
                 changes=[dict(path=named, kind='add')])), dict(type='turn.completed')]))
        collection = save(session / 'runtime/collection.json', dict(qualified_delivery=True,
            native_terminal_completed=True, response_sha256=answer['sha256']))
        local = lambda ref: {**ref, 'path': str(Path(ref['path']).relative_to('original')), 'repository': None}
        record_sources = {}
        for key, ref in (('native_events', events), ('collection', collection)):
            record_sources[key] = {k: v for k, v in local(ref).items() if k != 'repository'}
        record = save(self.root / 'original/record.json', dict(records=[dict(id='case-0:A1', source=record_sources)]))
        base = dict(sources={'private_source_record': record, 'answer:case-0:A1': answer})
        row = dict(model_id='model-a', opportunity_id='case-0', source_id='delivered:case-0:manuscript',
            record=record, answer=answer, events=events, collection=collection, artifact=artifact,
            native_named_path=named, completed_file_change_events=[0], first_terminal_event=1,
            terminal_content_digest_observed=False, archive_bytes_match_current=True,
            archive_git_revision='a' * 40, archive_blob='b' * 40,
            provenance='The old collector omitted the terminal hash; original archived explicit delivery retained.')
        path = self.root / owner.DELIVERY_SUPPLEMENTS
        path.parent.mkdir(parents=True)
        data = dict(schema='math-gauge.research-initiative-delivery-supplements/v1', version=owner.VERSION,
            reviewer_kind='ai', human_review='pending', post_observation=True, new_candidate_calls=0, rows=[row])
        path.write_bytes(owner.encoded(data))
        _, found = owner._delivery_supplements(self.roots, 'model-a', base)
        self.assertEqual(found['case-0'][row['source_id']], artifact)
        self.assertNotIn('other-workspace.md', str(found))
        row['completed_file_change_events'] = [1]
        path.write_bytes(owner.encoded(data))
        with self.assertRaisesRegex(ValueError, 'preterminal'):
            owner._delivery_supplements(self.roots, 'model-a', base)
        row['completed_file_change_events'] = [0]
        row['terminal_content_digest_observed'] = True
        path.write_bytes(owner.encoded(data))
        with self.assertRaisesRegex(ValueError, 'evidence limits'):
            owner._delivery_supplements(self.roots, 'model-a', base)

    def test_one_full_legacy_unit_and_one_full_extra_unit_have_identical_mass(self):
        ids = ['case-' + str(i) for i in range(27)] + ['independent-extension']
        a, _ = self.fixture(grades={key: 4 if key == 'case-5' else 0 for key in ids})
        b, _ = self.fixture(grades={key: 4 if key == 'independent-extension' else 0 for key in ids}, mid='model-b')
        self.assertEqual(owner.score_review(a)['metric'], owner.score_review(b)['metric'])

    def test_known_zero_is_not_unknown_and_complete_coverage_is_not_full_credit(self):
        review, material = self.fixture()
        self.validate(review, material)
        score = owner.score_review(review)['metric']
        self.assertEqual(score['exact'], 0)
        self.assertEqual(score['coverage']['reviewed'], 28)

    def test_unrun_independent_work_keeps_fixed_interval_instead_of_rescaling(self):
        review, material = self.fixture(unavailable={'independent-extension'})
        self.validate(review, material)
        metric = owner.score_review(review)['metric']
        self.assertIsNone(metric['exact'])
        self.assertEqual(metric['lower'], 0)
        self.assertAlmostEqual(metric['upper'], 100 / 28)
        self.assertEqual(metric['coverage'], dict(unit='research_opportunity', planned=28, reviewed=27))
        review['rows'][-1]['grade'] = 0
        review['rows'][-1]['coordinator_adjustment'] = dict(reviewer_kind='ai', human_review='pending',
                                                         reason='Even a named adjustment cannot invent missing work.')
        with self.assertRaisesRegex(ValueError, 'unknown'):
            self.validate(review, material)

    def test_settled_empty_original_has_zero_without_inventing_a_quote(self):
        review, material = self.fixture(blank={'case-0'})
        self.validate(review, material)
        self.assertEqual(owner.score_review(review)['metric']['coverage']['reviewed'], 28)
        review['rows'][0]['grade'] = None
        review['rows'][0]['coordinator_adjustment'] = dict(reviewer_kind='ai', human_review='pending',
                                                        reason='Even a named adjustment cannot turn a settled blank into unrun.')
        with self.assertRaisesRegex(ValueError, 'settled blank'):
            self.validate(review, material)

    def test_full_common_scale_and_partial_grades_use_the_same_fixed_denominator(self):
        ids = ['case-' + str(i) for i in range(27)] + ['independent-extension']
        all_full, material = self.fixture(grades=dict.fromkeys(ids, 4))
        self.validate(all_full, material)
        self.assertEqual(owner.score_review(all_full)['metric']['exact'], 100)
        mixed, _ = self.fixture(grades={key: {'case-0': 3, 'case-1': 1, 'independent-extension': 2}.get(key, 0)
                                        for key in ids}, mid='model-b')
        self.assertAlmostEqual(owner.score_review(mixed)['metric']['exact'], 150 / 28)

    def test_missing_or_duplicate_opportunities_cannot_disappear_from_the_denominator(self):
        review, material = self.fixture()
        for rows in (review['rows'][:-1], [*review['rows'][:-1], review['rows'][0]]):
            broken = dict(review, rows=rows)
            with self.assertRaisesRegex(ValueError, 'exactly once'):
                self.validate(broken, material)

    def test_quote_must_bind_this_model_this_task_and_exact_utf8_original_bytes(self):
        review, material = self.fixture()
        row = review['rows'][0]
        row['evidence'] = deepcopy(review['rows'][1]['evidence'])
        with self.assertRaisesRegex(ValueError, 'original bytes'):
            self.validate(review, material)
        review, material = self.fixture()
        material['rows'][0]['sources']['answer']['sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'source bytes changed'):
            self.validate(review, material)

    def test_source_mutation_is_detected_even_if_the_old_quote_remains_present(self):
        review, material = self.fixture()
        path = self.root / material['rows'][0]['sources']['answer']['path']
        path.write_bytes(path.read_bytes() + b'Late unsubmitted addition')
        with self.assertRaisesRegex(ValueError, 'source bytes changed'):
            self.validate(review, material)

    def test_primary_review_cannot_be_borrowed_or_silently_regraded(self):
        review, material = self.fixture()
        review['rows'][0]['primary_review']['row'] = 1
        with self.assertRaisesRegex(ValueError, 'another primary'):
            self.validate(review, material)
        review, material = self.fixture()
        review['rows'][0]['grade'] = 2
        with self.assertRaisesRegex(ValueError, 'named reason'):
            self.validate(review, material)
        review['rows'][0]['coordinator_adjustment'] = dict(reviewer_kind='ai', human_review='pending',
                                                         reason='Named source-bound cross-model mathematical calibration.')
        self.validate(review, material)

    def test_reading_and_mathematical_judgment_are_explicit_not_inferred_from_a_score(self):
        review, material = self.fixture()
        review['rows'][0]['full_delivery_read'] = False
        with self.assertRaisesRegex(ValueError, 'complete-source'):
            self.validate(review, material)
        review, material = self.fixture()
        review['human_review'] = 'approved'
        with self.assertRaisesRegex(ValueError, 'human approval'):
            self.validate(review, material)

    def test_public_output_contains_only_aggregate_scores_and_opaque_source_hashes(self):
        review, material = self.fixture()
        self.validate(review, material)
        report = owner.public_projection(review, material, self.policy_hash)
        owner.validate_public(report, self.policy, self.policy_hash)
        public = owner.encoded(report).decode()
        self.assertNotIn('case-0', public)
        self.assertNotIn('separately posed', public)
        self.assertNotIn(str(self.root), public)
        self.assertNotIn('fresh-review-context', public)
        leaked = deepcopy(report)
        leaked['metric']['coverage']['private_case'] = 'case-0'
        with self.assertRaisesRegex(ValueError, 'aggregate only'):
            owner.validate_public(leaked, self.policy, self.policy_hash)

    def test_public_components_must_retain_equal_weight_and_coverage(self):
        review, material = self.fixture(unavailable={'independent-extension'})
        report = owner.public_projection(review, material, self.policy_hash)
        owner.validate_public(report, self.policy, self.policy_hash)
        broken = deepcopy(report)
        broken['metric']['coverage']['reviewed'] = 26
        with self.assertRaisesRegex(ValueError, 'coverage must count'):
            owner.validate_public(broken, self.policy, self.policy_hash)
        broken = deepcopy(report)
        broken['metric']['upper'] = 20
        broken['metric']['unknown_weight'] = 20
        with self.assertRaisesRegex(ValueError, 'share one mean'):
            owner.validate_public(broken, self.policy, self.policy_hash)


if __name__ == '__main__':
    unittest.main()
