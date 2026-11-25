"""Independent profile opportunity arithmetic, source boundaries and review gates."""
from copy import deepcopy
from fractions import Fraction
import tempfile
from pathlib import Path
import unittest

from math_gauge import profile_structure as owner
from math_gauge.scoring import score_profile_structure


def arithmetic_inputs():
    """Validated-input fixture for pure arithmetic, separate from source validation."""
    cases = ['closed-' + str(i) for i in range(30)]
    groups = [cases[:2], cases[2:4], *[[cid] for cid in cases[4:]]]
    weights = [3] * 20 + [2] + [1] * 7
    families = [dict(family_id='family-' + str(i), case_ids=members, weight=w)
                for i, (members, w) in enumerate(zip(groups, weights))]
    opened = ['open-' + str(i) for i in range(5)] + ['study']
    factors = [1, 2, 1, 2, 2, 3]
    opportunities = [dict(case_id=cid, opportunity_factor=w,
                         stage_rule='R3_actual_delivery' if cid == 'study' else 'adopted-revision')
                     for cid, w in zip(opened, factors)]
    inputs = object.__new__(owner.ProfileStructureInputs)
    inputs.contracts = dict(depth=dict(families=families, task_bindings=[dict(case_id=c) for c in cases]),
                            open_research=dict(opportunities=opportunities))
    rows = [dict(axis='depth', case_id=cid, stage='first', grade=4) for cid in cases]
    rows += [dict(axis='open_research', case_id=cid, stage='independent' if cid == 'study' else 'first', grade=4)
             for cid in opened]
    inputs.review = dict(model_id='model', rows=rows)
    inputs.materials = dict(revision_available=True, rows=[dict(stage='independent', source_status='available',
        classification='three-normal-finals', evidence_source_ids=['R3'])])
    inputs.policy = dict(weights=dict(owner.WEIGHTS), revision=dict(original_weight='4/5', revision_weight='1/5'))
    inputs.revision_eligible = set(cases + opened)
    return inputs


class ProfileStructureArithmeticTests(unittest.TestCase):
    def test_validated_inputs_required_and_all_goals_full_are_exact(self):
        with self.assertRaisesRegex(ValueError, 'authenticated'):
            score_profile_structure({})
        score = score_profile_structure(arithmetic_inputs())
        self.assertEqual(score['first']['depth']['exact'], 100)
        self.assertEqual(score['revision']['open_research']['exact'], 100)
        self.assertEqual(score['first']['depth']['coverage']['weight_reviewed'], 69)

    def test_audit_variants_share_one_opportunity_before_its_weight(self):
        inputs = arithmetic_inputs()
        inputs.review['rows'][0]['grade'] = 0
        score = score_profile_structure(inputs)['first']['depth']
        self.assertAlmostEqual(score['exact'], float(100 - Fraction(50 * 3, 69)))
        self.assertEqual(score['coverage']['reviewed'], 28)

    def test_selected_revision_decline_is_twenty_percent_of_its_own_opportunity(self):
        inputs = arithmetic_inputs()
        inputs.review['rows'].append(dict(axis='depth', case_id='closed-4', stage='revision', grade=0))
        result = score_profile_structure(inputs)
        self.assertEqual(result['first']['depth']['exact'], 100)
        self.assertAlmostEqual(result['revision']['depth']['exact'], float(100 - Fraction(20 * 3, 69)))
        self.assertEqual(result['revision_coverage'], dict(status='adopted', selected=1, reviewed=1, unknown=0))

    def test_unknown_continuation_retains_only_its_fixed_twenty_percent_interval(self):
        inputs = arithmetic_inputs()
        inputs.review['rows'].append(dict(axis='open_research', case_id='open-1', stage='revision', grade=None))
        result = score_profile_structure(inputs)['revision']['open_research']
        self.assertIsNone(result['exact'])
        self.assertAlmostEqual(result['lower'], float(100 - Fraction(20 * 2, 11)))
        self.assertEqual(result['upper'], 100)
        self.assertEqual(result['coverage']['reviewed'], 5)
        self.assertEqual(result['coverage']['weight_reviewed'], 9)

    def test_last_research_opportunity_is_counted_once_and_unknown_is_not_zero(self):
        inputs = arithmetic_inputs()
        inputs.review['rows'][-1]['grade'] = None
        score = score_profile_structure(inputs)
        for stage in ('first', 'revision'):
            metric = score[stage]['open_research']
            self.assertIsNone(metric['exact'])
            self.assertAlmostEqual(metric['lower'], float(Fraction(800, 11)))
            self.assertEqual(metric['upper'], 100)
            self.assertEqual(metric['coverage']['reviewed'], 5)
        inputs.review['rows'][-1]['grade'] = 0
        metric = score_profile_structure(inputs)['first']['open_research']
        self.assertAlmostEqual(metric['exact'], float(Fraction(800, 11)))
        self.assertEqual(metric['coverage']['reviewed'], 6)
        self.assertEqual(metric['unknown_weight'], 0)

    def test_pending_revision_does_not_inherit_unselected_legacy_scores(self):
        inputs = arithmetic_inputs()
        inputs.materials['revision_available'] = False
        inputs.revision_eligible.remove('closed-0')
        inputs.revision_eligible.remove('closed-1')
        score = score_profile_structure(inputs)
        self.assertEqual(score['first']['depth']['exact'], 100)
        metric = score['revision']['depth']
        self.assertIsNone(metric['exact'])
        self.assertAlmostEqual(metric['lower'], float(Fraction(300, 69)))
        self.assertEqual(metric['coverage']['reviewed'], 1)
        self.assertAlmostEqual(score['revision']['open_research']['lower'], float(Fraction(300, 11)))

    def test_public_projection_has_no_task_inventory_and_rejects_private_fields(self):
        score = score_profile_structure(arithmetic_inputs())
        report = owner.project_public(score, policy_hash='a' * 64, private_review_sha256='b' * 64,
                                      private_materials_sha256='c' * 64)
        owner.validate_public(report, {}, 'a' * 64)
        self.assertNotIn('tasks', report)
        for location in ('root', 'coverage'):
            changed = deepcopy(report)
            target = changed if location == 'root' else changed['first']['depth']['coverage']
            target['private_case'] = 'private-fixture-marker'
            with self.assertRaises(ValueError):
                owner.validate_public(changed, {}, 'a' * 64)


class ProfileStructurePublicLoaderTests(unittest.TestCase):
    def test_public_aggregates_load_without_private_material_and_reject_source_or_privacy_tampering(self):
        import json
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            policy_raw = (Path(__file__).resolve().parents[1] / owner.POLICY_PATH).read_bytes()
            (root / owner.POLICY_PATH).parent.mkdir(parents=True)
            (root / owner.POLICY_PATH).write_bytes(policy_raw)
            policy_hash = owner.digest(policy_raw)
            self.assertIsNone(owner.load_public(root, benchmark_version=owner.EDITION),
                              'A frozen standard without an adopted index must not activate new results')
            cohort, models = ['model-' + str(i) for i in range(20)], {}
            for mid in cohort:
                inputs = arithmetic_inputs()
                inputs.review['model_id'] = mid
                report = owner.project_public(score_profile_structure(inputs), policy_hash=policy_hash,
                    private_review_sha256='b' * 64, private_materials_sha256='c' * 64)
                raw = owner.encoded(report)
                name = owner.DIRECTORY + '/' + mid + '/profile.json'
                (root / name).parent.mkdir(parents=True)
                (root / name).write_bytes(raw)
                models[mid] = dict(path=name, bytes=len(raw), sha256=owner.digest(raw))
            index = dict(schema='math-gauge.profile-structure-index/v1', version=owner.VERSION, edition=owner.EDITION,
                condition=owner.CONDITION, policy_sha256=policy_hash, cohort=cohort, models=models, **owner.BOUNDARIES)
            (root / owner.INDEX_PATH).write_bytes(owner.encoded(index))
            source = owner.load_public(root, benchmark_version=owner.EDITION)
            self.assertEqual(len(source['models']), 20)
            self.assertIsNone(owner.load_public(root, benchmark_version='1.2.0'))
            (root / owner.POLICY_PATH).unlink()
            with self.assertRaisesRegex(ValueError, 'missing its selected policy'):
                owner.load_public(root, benchmark_version=owner.EDITION)
            (root / owner.POLICY_PATH).write_bytes(policy_raw)
            filename = root / models[cohort[0]]['path']
            original = filename.read_bytes()
            filename.write_bytes(original + b' ')
            with self.assertRaisesRegex(ValueError, 'bytes changed'):
                owner.load_public(root, benchmark_version=owner.EDITION)
            report = json.loads(original)
            report['private_task_inventory'] = ['private-fixture-marker']
            raw = owner.encoded(report)
            filename.write_bytes(raw)
            models[cohort[0]].update(bytes=len(raw), sha256=owner.digest(raw))
            (root / owner.INDEX_PATH).write_bytes(owner.encoded(index))
            with self.assertRaisesRegex(ValueError, 'aggregate-only'):
                owner.load_public(root, benchmark_version=owner.EDITION)


class ProfileStructureJudgmentTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.raw = b'An established mechanism crosses the bridge under exactly these conditions.'
        (self.root / 'answer.md').write_bytes(self.raw)
        self.source = dict(repository='public', path='answer.md', bytes=len(self.raw), sha256=owner.digest(self.raw))
        self.roots = dict(public=self.root, private=self.root)
        self.contracts = dict(open_research=dict(opportunities=[dict(case_id='study', stage_rule='R3_actual_delivery')]))
        self.material = dict(axis='depth', case_id='closed', stage='first', source_status='available',
                             sources=dict(answer=self.source), evidence_source_ids=['answer'], verified_math_facts=[])
        self.row = dict(model_id='model', axis='depth', case_id='closed', stage='first', grade=4,
            status='reviewed', full_delivery_read=True, review_scope='full-delivery', reused_verification=[],
            facets={name: dict(state='established', reason='Exact mechanism and dependency checked.') for name in owner.FACETS['depth']},
            reason='The original task structure is unified.', next_tier_reason='Highest supported tier.',
            evidence=[dict(source_id='answer', quote=self.raw.decode())], core_scope_failure=False,
            optional_error_deletion=[], g3_gap_witness='', g4_closure_chain='Mechanism to bridge to exact original scope.',
            independent_local_structure='')

    def validate(self, row=None, material=None):
        owner.validate_judgment(row or self.row, material or self.material, self.contracts, self.roots)

    def test_focused_review_preserves_false_full_read_and_bound_verification(self):
        verification = owner.encoded(dict(proof=dict(checked=True)))
        (self.root / 'verification.json').write_bytes(verification)
        source = dict(repository='public', path='verification.json', bytes=len(verification), sha256=owner.digest(verification))
        self.material['verified_math_facts'] = [dict(source=source, pointer='/proof')]
        self.row.update(full_delivery_read=False, review_scope='trait-and-dependency-with-retained-math-verification',
                        reused_verification=[dict(source=source, pointer='/proof')])
        self.validate()
        self.row['reused_verification'][0]['pointer'] = '/missing'
        with self.assertRaisesRegex(ValueError, 'verification differs'):
            self.validate()

    def test_original_source_review_does_not_invent_reused_mathematics_or_full_auxiliary_reads(self):
        self.row.update(full_delivery_read=False, review_scope='trait-and-dependency-from-original-source',
                        reused_verification=[], review_scope_note='All mathematical core read; auxiliary code was not used.')
        self.validate()
        self.row['review_scope'] = 'full-delivery'
        with self.assertRaisesRegex(ValueError, 'full-delivery audit'):
            self.validate()

    def test_retained_verification_allows_existing_descendants_but_not_siblings_or_missing_nodes(self):
        raw = owner.encoded(dict(tasks=[dict(), dict(), dict(findings=[dict(checked=True)]), dict(other=True)]))
        (self.root / 'subtree.json').write_bytes(raw)
        ref = dict(repository='public', path='subtree.json', bytes=len(raw), sha256=owner.digest(raw))
        self.material['verified_math_facts'] = [dict(source=ref, pointer='/tasks/2')]
        self.row.update(full_delivery_read=False, review_scope='trait-and-dependency-with-retained-math-verification',
                        reused_verification=[dict(source=ref, pointer='/tasks/2/findings/0')])
        self.validate()
        for pointer in ('/tasks/3', '/tasks/28'):
            self.row['reused_verification'][0]['pointer'] = pointer
            with self.assertRaisesRegex(ValueError, 'verification differs'):
                self.validate()
        self.row['reused_verification'][0]['pointer'] = '/tasks/2/missing'
        with self.assertRaisesRegex(ValueError, 'pointer is missing'):
            self.validate()
        self.material['verified_math_facts'][0]['pointer'] = '/'
        self.row['reused_verification'][0]['pointer'] = '/tasks/2/findings/0'
        self.validate()

    def test_wrong_model_source_quote_and_earlier_manuscript_are_rejected(self):
        self.row['evidence'][0]['quote'] = 'Reviewer-added repaired proof'
        with self.assertRaisesRegex(ValueError, 'absent'):
            self.validate()
        self.row['evidence'] = [dict(source_id='R1', quote=self.raw.decode())]
        with self.assertRaisesRegex(ValueError, 'unselected'):
            self.validate()

    def test_failed_depth_core_allows_only_an_independent_established_local_three(self):
        self.row.update(grade=3, core_scope_failure=True)
        self.row['facets']['unification']['state'] = 'refuted'
        with self.assertRaisesRegex(ValueError, 'separate established local'):
            self.validate()
        self.row['independent_local_structure'] = 'Complete local structure has no dependency on the failed global core.'
        self.validate()
        self.row['grade'] = 4
        with self.assertRaises(ValueError):
            self.validate()

    def test_open_three_requires_local_gap_witness_and_no_essential_gap(self):
        self.material['axis'] = self.row['axis'] = 'open_research'
        self.row.update(grade=3, facets={name: dict(state='established', reason='Original scope checked.')
                                       for name in owner.FACETS['open_research']})
        self.row['facets']['closure']['state'] = 'local_gap'
        with self.assertRaisesRegex(ValueError, 'local-gap witness'):
            self.validate()
        self.row['g3_gap_witness'] = 'One displayed equality remains; direct substitution fills it without a new mechanism, hypothesis or scope change.'
        self.validate()
        self.row['facets']['scope']['state'] = 'essential_gap'
        with self.assertRaisesRegex(ValueError, 'essential scope gap'):
            self.validate()

    def test_optional_error_deletion_cannot_repair_or_shrink_the_required_scope(self):
        self.row['optional_error_deletion'] = [dict(source_id='answer', error_quote='these conditions', reason='An independent optional aside.',
            core_unchanged=True, dependencies_unchanged=True, scope_unchanged=False, no_source_repair=True)]
        with self.assertRaisesRegex(ValueError, 'cannot be deleted'):
            self.validate()

    def test_primary_request_identity_and_named_coordinator_changes_are_source_bound(self):
        proposal = dict(schema='math-gauge.profile-structure-review-proposal/v1', reviewer_kind='ai',
            human_review='pending', reviewer=dict(requested_model='gpt-6.1-sol', effort='max', context='actual-caller-context'),
            rows=[deepcopy(self.row)])
        raw = owner.encoded(proposal)
        (self.root / 'primary.json').write_bytes(raw)
        ref = dict(repository='public', path='primary.json', bytes=len(raw), sha256=owner.digest(raw))
        self.row['primary_review'] = dict(source=ref, row=0)
        materials = dict(model_id='model', rows=[self.material])
        review = dict(schema='math-gauge.profile-structure-review/v1', version=owner.VERSION, edition=owner.EDITION,
            condition=owner.CONDITION, model_id='model', policy_sha256='a' * 64,
            materials_sha256=owner.digest(owner.encoded(materials)), rows=[self.row], **owner.BOUNDARIES)
        owner.validate_review(review, materials, {}, 'a' * 64, self.contracts, self.roots)
        self.row['grade'] = 3
        with self.assertRaisesRegex(ValueError, 'coordinator adjustment'):
            owner.validate_review(review, materials, {}, 'a' * 64, self.contracts, self.roots)
        self.row['coordinator_adjustment'] = dict(reviewer_kind='ai', human_review='pending', reason='Named independent dependency correction.')
        owner.validate_review(review, materials, {}, 'a' * 64, self.contracts, self.roots)
        self.row['primary_review']['row'] = 2
        with self.assertRaisesRegex(ValueError, 'primary reviewer'):
            owner.validate_review(review, materials, {}, 'a' * 64, self.contracts, self.roots)

    def test_all_nested_candidate_assets_are_hashed_and_damaged_bytes_cannot_be_ignored(self):
        tree = dict(depth=dict(tasks=[self.source]), open_research=dict(candidate_materials=dict(files=[self.source])))
        self.assertEqual(len(owner.validate_source_tree(tree, self.roots)), 1)
        (self.root / 'answer.md').write_bytes(b'damaged candidate asset')
        with self.assertRaisesRegex(ValueError, 'source bytes changed'):
            owner.validate_source_tree(tree, self.roots)

    def test_same_model_fake_supplement_and_arbitrary_r3_owner_are_rejected(self):
        owners = {name: dict(self.source, path=name + '.json') for name in ('first', 'revision', 'initiative', 'open_research')}
        bindings = dict(material_source=owners['first'], initiative_material_source=owners['initiative'],
                        open_material_source=owners['open_research'])
        owner._validate_owner_bindings('first', bindings, owners)
        for field in ('initiative_material_source', 'open_material_source'):
            changed = deepcopy(bindings)
            changed[field] = dict(self.source, path='same-model-forged-owner.json')
            with self.assertRaisesRegex(ValueError, 'same-model'):
                owner._validate_owner_bindings('first', changed, owners)
        with self.assertRaisesRegex(ValueError, 'indexed selected initiative'):
            owner._validate_owner_bindings('independent', dict(material_source=self.source), owners)
        owner._validate_owner_bindings('independent', dict(material_source=owners['initiative']), owners)

    def test_preparation_can_select_indexed_neutral_owner_only_with_identical_preserved_first_sources(self):
        def save(name, value):
            raw = owner.encoded(value)
            filename = self.root / name
            filename.parent.mkdir(parents=True, exist_ok=True)
            filename.write_bytes(raw)
            return dict(repository='private', path=name, bytes=len(raw), sha256=owner.digest(raw))
        old = dict(model_id='model', condition=owner.CONDITION, first=[dict(original='unchanged')],
                   sources=dict(base_materials=self.source))
        legacy = save('results/open-research/v0.1.0/model/source-bindings.json', old)
        current = save('indexed-owner.json', dict(old, revision=[dict(adopted='new-stage')]))
        packet = dict(model_id='model', stage='first', open_material_source=legacy)
        selected = dict(open_research=current)
        result = owner._select_current_open_owner(packet, selected, self.roots)
        self.assertEqual(result['open_material_source'], current)
        self.assertEqual(packet['open_material_source'], legacy, 'The original preparation snapshot stays unchanged')
        packet['open_material_source'] = dict(legacy, path='same-model-forged-owner.json')
        with self.assertRaisesRegex(ValueError, 'lookalike'):
            owner._select_current_open_owner(packet, selected, self.roots)
        packet['open_material_source'] = legacy
        selected['open_research'] = save('changed-first-owner.json', dict(old, first=[dict(original='changed')]))
        with self.assertRaisesRegex(ValueError, 'changed original'):
            owner._select_current_open_owner(packet, selected, self.roots)

    def test_prepared_packet_cannot_rename_task_or_replace_selected_source(self):
        base = dict(model_id='model', condition=owner.CONDITION, sources={},
                    tasks=[dict(id='closed:A1', raw_answer=self.source)])
        raw = owner.encoded(base)
        (self.root / 'materials.json').write_bytes(raw)
        ref = dict(repository='public', path='materials.json', bytes=len(raw), sha256=owner.digest(raw))
        packet = dict(model_id='model', case_id='closed', stage='first', material_source=ref,
                      source_status='available', sources=dict(answer=dict(source=self.source, text=self.raw.decode())))
        owner._authenticated_sources(packet, self.roots, self.contracts)
        (self.root / 'other.md').write_bytes(self.raw)
        packet['sources']['answer']['source'] = dict(self.source, path='other.md')
        with self.assertRaisesRegex(ValueError, 'unselected answer'):
            owner._authenticated_sources(packet, self.roots, self.contracts)
        packet['sources'] = dict(task=dict(source=self.source, text=self.raw.decode()))
        with self.assertRaisesRegex(ValueError, 'renamed'):
            owner._authenticated_sources(packet, self.roots, self.contracts)

    def test_available_but_pending_trait_stays_unknown_without_a_false_zero(self):
        self.row.update(grade=None, status='review_pending', evidence=[])
        self.validate()
        self.row['status'] = 'reviewed'
        with self.assertRaisesRegex(ValueError, 'unadjudicated'):
            self.validate()

    def test_thin_wrapper_supplement_requires_both_explicit_role_hash_and_actual_continuation_source(self):
        def save(name, value):
            raw = owner.encoded(value)
            (self.root / name).write_bytes(raw)
            return dict(repository='public', path=name, bytes=len(raw), sha256=owner.digest(raw))
        verification = save('verified.json', dict(necessary_mechanism='already mathematically checked'))
        wrapper = save('wrapper.json', dict(original_mathematical_review={k:v for k,v in verification.items() if k!='repository'}))
        material = save('original-material.json', dict(model_id='model'))
        packet = dict(model_id='model', axis='depth', case_id='closed', stage='revision', material_source=material)
        selected = dict(sources=dict(review=wrapper), revision_ref=dict(continuation=dict(sources=dict(original=verification))))
        row = dict(model_id='model', axis='depth', case_id='closed', stage='revision', source_material=material,
                   wrapper=wrapper, verification=[dict(role='original_mathematical_review', source=verification, pointer='/')])
        manifest = dict(schema='math-gauge.profile-structure-verification-supplements/v1', version=owner.VERSION,
                        edition=owner.EDITION, condition=owner.CONDITION, rows=[row], **owner.BOUNDARIES)
        ref = save('supplement.json', manifest)
        self.assertEqual(owner._validate_verification_supplement(ref, packet, selected, self.roots, self.contracts),
                         [dict(source=verification, pointer='/')])
        selected['revision_ref']['continuation']['sources'] = {}
        with self.assertRaisesRegex(ValueError, 'original continuation'):
            owner._validate_verification_supplement(ref, packet, selected, self.roots, self.contracts)
        selected['revision_ref']['continuation']['sources'] = dict(original=verification)
        row['verification'][0]['role'] = 'original_five_axis_review'
        ref = save('trait-supplement.json', manifest)
        with self.assertRaisesRegex(ValueError, 'Old trait grades'):
            owner._validate_verification_supplement(ref, packet, selected, self.roots, self.contracts)

    def test_base_verification_cannot_borrow_another_task_in_the_same_source_file(self):
        raw = owner.encoded(dict(tasks=[dict(checked='this task'), dict(checked='another task')]))
        (self.root / 'facts.json').write_bytes(raw)
        facts = dict(repository='public', path='facts.json', bytes=len(raw), sha256=owner.digest(raw))
        base = dict(model_id='model', condition=owner.CONDITION, sources=dict(content_review=facts),
                    tasks=[dict(id='closed:A1', raw_answer=self.source, content_index=0)])
        raw = owner.encoded(base)
        (self.root / 'source-material.json').write_bytes(raw)
        material = dict(repository='public', path='source-material.json', bytes=len(raw), sha256=owner.digest(raw))
        packet = dict(model_id='model', case_id='closed', stage='first', material_source=material, source_status='available',
                      sources=dict(answer=dict(source=self.source, text=self.raw.decode())),
                      verified_math_facts=[dict(source=facts, pointer='/tasks/1')])
        with self.assertRaisesRegex(ValueError, 'this task'):
            owner._authenticated_sources(packet, self.roots, self.contracts)
        packet['verified_math_facts'][0]['pointer'] = '/tasks/0'
        owner._authenticated_sources(packet, self.roots, self.contracts)

    def test_named_empty_source_intake_uses_original_no_content_receipts(self):
        def save(name, value):
            raw = owner.encoded(value)
            (self.root / name).write_bytes(raw)
            return dict(repository='public', path=name, bytes=len(raw), sha256=owner.digest(raw))
        source_material = save('source-material.json', dict(model_id='model'))
        failure = save('failure.json', dict(model_id='model', case_id='closed', status='cutoff_without_final',
            normal_final_delivered=False, response_sha256=owner.digest(b''), delivered_attachments=[]))
        cutoff = save('cutoff.json', dict(model_id='model', case_id='closed', failure_evidence_sha256=failure['sha256'],
            no_content=True, content_sha256=None, original_work_unmodified=True, no_normal_final=True, no_cross_attempt_union=True))
        intake = dict(schema='math-gauge.profile-structure-source-intake/v1', version=owner.VERSION, edition=owner.EDITION,
            condition=owner.CONDITION, model_id='model', axis='depth', case_id='closed', stage='revision',
            kind='retained-continuation-no-content', previous_source_status='unavailable', source_status='settled_blank',
            source_material=source_material, failure_evidence=failure, cutoff_review=cutoff,
            reason='The original source owner retained a verified empty cutoff.', **owner.BOUNDARIES)
        ref = save('intake.json', intake)
        packet = dict(model_id='model', axis='depth', case_id='closed', stage='revision', material_source=source_material)
        selected = dict(sources=dict(failure_evidence=failure, cutoff_review=cutoff), revision_ref=dict(continuation=dict(
            status='delivery_failed', failure_evidence=failure, cutoff_review=cutoff)))
        owner._validate_intake(ref, packet, selected, self.roots)
        selected['revision_ref']['continuation']['status'] = 'normal_final'
        with self.assertRaisesRegex(ValueError, 'delivered mathematical answer'):
            owner._validate_intake(ref, packet, selected, self.roots)
        selected['revision_ref']['continuation']['status'] = 'delivery_failed'
        intake['case_id'] = 'different-case'
        wrong = save('wrong-intake.json', intake)
        with self.assertRaisesRegex(ValueError, 'foreign'):
            owner._validate_intake(wrong, packet, selected, self.roots)

    def test_genuine_unknown_and_settled_blank_do_not_require_invented_quotes(self):
        self.material['source_status'] = 'unavailable'
        self.row.update(grade=None, status='unrun', evidence=[])
        self.validate()
        self.material['source_status'] = 'settled_blank'
        self.row.update(grade=0, status='settled_blank')
        self.validate()
        self.row['grade'] = None
        with self.assertRaisesRegex(ValueError, 'known zero'):
            self.validate()


class IndependentProfileSourceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.roots = dict(public=self.root, private=self.root)
        self.contracts = dict(open_research=dict(opportunities=[dict(case_id='study', stage_rule='R3_actual_delivery')]))

    def save(self, name, value):
        raw = value if isinstance(value, bytes) else owner.encoded(value)
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)
        return dict(repository='private', path=name, bytes=len(raw), sha256=owner.digest(raw))

    def test_selected_independent_math_review_cannot_borrow_taste_or_another_review(self):
        review = self.save('review.json', dict(axes=dict(capacity=dict(reason='A proved mechanism.'),
                                                       taste=dict(reason='Different judgment.')), error_roots=[]))
        absolute = dict(review, path=str(self.root / review['path']))
        absolute.pop('repository')
        selection = self.save('selection.json', dict(schema='math-gauge.independent-research-native-selection/v1',
            models=[dict(id='model', review=absolute)]))
        material = self.save('materials.json', dict(model_id='model'))
        packet = dict(model_id='model', axis='open_research', case_id='study', stage='independent',
                      material_source=material, selection=selection)
        row = dict(model_id='model', axis='open_research', case_id='study', stage='independent',
            source_material=material, selection=selection, role='review',
            verification=[dict(source=review, pointer='/axes/capacity')])

        def check(chosen):
            ref = self.save('verification.json', dict(schema='math-gauge.profile-structure-independent-verifications/v1',
                version=owner.VERSION, edition=owner.EDITION, condition=owner.CONDITION, rows=[chosen], **owner.BOUNDARIES))
            return owner._independent_verifications(ref, packet, self.roots, self.contracts)

        self.assertEqual(check(row), row['verification'])
        for change in ('role', 'subtree', 'source', 'model'):
            wrong = deepcopy(row)
            if change == 'role':
                wrong['role'] = 'old_capacity_grade'
            elif change == 'subtree':
                wrong['verification'][0]['pointer'] = '/axes/taste'
            elif change == 'source':
                wrong['verification'][0]['source'] = self.save('lookalike-review.json', dict(error_roots=[]))
            else:
                wrong['model_id'] = 'other-model'
            with self.subTest(change=change), self.assertRaises(ValueError):
                check(wrong)

    def test_normal_trajectory_source_does_not_relabel_delivery_or_replace_final_with_prior_text(self):
        first = self.save('R1.md', b'Earlier partial manuscript.')
        final = self.save('R3.md', b'Actual final manuscript.')
        selection = self.save('selection.json', dict(selected=True))
        selected = dict(opportunity_id='independent-extension', source_status='available',
            classification='three-normal-finals', sources=dict(R1=first, R3=final), selection=selection,
            adopted_source_sha256='d'*64)
        material = self.save('materials.json', dict(model_id='model', condition=owner.CONDITION, rows=[selected]))
        packet = dict(model_id='model', axis='open_research', case_id='study', stage='independent',
            material_source=material, classification=selected['classification'], source_status='available',
            selection=selection, adopted_source_sha256='d'*64,
            sources=dict(R1=dict(source=first, text='Earlier partial manuscript.'),
                         R3=dict(source=final, text='Actual final manuscript.')))
        owner._authenticated_sources(packet, self.roots, self.contracts)
        wrong = deepcopy(packet)
        wrong['classification'] = 'unearned-normal-final'
        with self.assertRaisesRegex(ValueError, 'selected retained trajectory'):
            owner._authenticated_sources(wrong, self.roots, self.contracts)
        wrong = deepcopy(packet)
        wrong['sources']['R3'] = dict(source=first, text='Earlier partial manuscript.')
        with self.assertRaisesRegex(ValueError, 'unselected answer'):
            owner._authenticated_sources(wrong, self.roots, self.contracts)

    def test_admitted_source_aliases_preserve_the_actual_round_not_an_earlier_selected_hash(self):
        from types import SimpleNamespace
        from unittest.mock import patch
        from math_gauge import independent_research_admitted_delivery as admitted
        first = self.save('retained/R1.md', b'First selected manuscript.')
        final = self.save('retained/R3.md', b'Final selected manuscript.')
        projected = dict(source_binding=dict(adoption_sha256=''), models={admitted.MODEL:dict(source_sha256='e'*64)})
        selection = self.save('admitted-selection.json', dict(schema=admitted.FROZEN_SELECTION,
            registration=dict(path=str(self.root/'registration.json'), sha256='a'*64),
            frozen_runner=dict(path=str(self.root/'frozen-runner.json')), admission=dict(path=str(self.root/'admission.json'))))
        projected['source_binding']['adoption_sha256'] = selection['sha256']
        public = self.save(admitted.PUBLIC_PATH.as_posix(), projected)
        public['repository'] = 'public'
        intake = dict(schema='math-gauge.profile-structure-independent-addition/v1', version=owner.VERSION,
            edition=owner.EDITION, condition=owner.CONDITION, model_id=admitted.MODEL,
            axis='open_research', case_id='independent-research', stage='independent',
            kind=admitted.SOURCE_KIND, source_status='available', classification=admitted.SOURCE_KIND,
            reason='Explicit separately selected final source.', selection=selection, public_adoption=public,
            adopted_source_sha256='e'*64, sources=dict(R1=first, R3=final), **owner.BOUNDARIES)
        documents = [dict(round=rid, documents=[dict(source=dict(path='/original/'+rid+'.md'))]) for rid in ('R1','R3')]
        archive = SimpleNamespace(root=self.root,
            descriptor=lambda source: dict(path='retained/'+Path(source['path']).name))
        evidence = SimpleNamespace(original=dict(rounds=documents), archive=archive)
        packet = dict(model_id=admitted.MODEL, axis='open_research', stage='independent')
        with patch.object(admitted, 'prepare', return_value=projected), \
             patch.object(admitted, 'retained_case_reader', return_value=({},None,dict(rounds={}))), \
             patch.object(admitted, 'load_admission', return_value=evidence):
            ref = self.save('intake.json', intake)
            _, sources = owner._admitted_independent(ref, packet, self.roots)
            self.assertEqual(sources, intake['sources'])
            intake['sources']['R3'] = first
            ref = self.save('wrong-intake.json', intake)
            with self.assertRaisesRegex(ValueError, 'omitted or substituted'):
                owner._admitted_independent(ref, packet, self.roots)


if __name__ == '__main__':
    unittest.main()
