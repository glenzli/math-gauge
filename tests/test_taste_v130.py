"""Synthetic offline protocol tests. No private case content or candidate calls."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from math_gauge import taste_v130 as flow
from math_gauge.scoring import score_research_preview


def write_json(path, data):
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n')


def descriptor(path, root):
    raw = path.read_bytes()
    return dict(path=path.relative_to(root).as_posix(), bytes=len(raw),
                sha256=hashlib.sha256(raw).hexdigest())


class ProtocolFixture(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.sources = self.root / 'sources'
        self.case = self.sources / 'CASE-FIXTURE'
        for name in ('candidate', 'packet/figures', 'evaluator'):
            (self.case / name).mkdir(parents=True)
        for rid in flow.ROUNDS:
            (self.case / f'candidate/{rid}.md').write_text(f'{rid}: Synthetic invitation.\n')
        (self.case / 'candidate/rules.md').write_text('Synthetic local-only rules.\n')
        (self.case / 'packet/body.md').write_text('Synthetic source. ![figure](./figures/fixture.png)\n')
        (self.case / 'packet/figures/fixture.png').write_bytes(b'fixture-image')
        (self.case / 'evaluator/rubric.md').write_text('EVALUATOR-ONLY-SENTINEL\n')
        write_json(self.case / 'evaluator/provenance.json', {'synthetic': True})
        def gate(name, rounds, required=True):
            return dict(id=name, rounds=rounds, required=required)
        self.contract = dict(schema='math-gauge.taste-preview-private-contract/v1',
            case_id='CASE-FIXTURE', packet_forbidden_literals=['EVALUATOR-ONLY-SENTINEL'],
            supporting_references=[], gates={
                'autonomy': [gate('A1', ['R1']), gate('A2', ['R2'])],
                'taste': [gate('T1', list(flow.ROUNDS))],
                'capacity': [gate(f'C{i}', ['R3']) for i in range(5)] + [gate('optional', ['R3'], False)]},
            round_coverage={'autonomy': ['R1', 'R2'], 'taste': list(flow.ROUNDS), 'capacity': list(flow.ROUNDS)})
        write_json(self.case / 'evaluator/review-contract.json', self.contract)
        public = flow.POLICY_FILE.parents[3]
        self.reg = dict(schema=flow.SCHEMA, edition=flow.EDITION, status='local_pending',
            category='open-research', case_id='CASE-FIXTURE', case_root='CASE-FIXTURE', visibility='private',
            rounds={r: descriptor(self.case / f'candidate/{r}.md', self.case) for r in flow.ROUNDS},
            rules=descriptor(self.case / 'candidate/rules.md', self.case),
            packet=[descriptor(p, self.case) for p in sorted((self.case / 'packet').rglob('*')) if p.is_file()],
            review_contract=descriptor(self.case / 'evaluator/review-contract.json', self.case),
            rubric=descriptor(self.case / 'evaluator/rubric.md', self.case),
            provenance=descriptor(self.case / 'evaluator/provenance.json', self.case),
            runner={'binding': 'local-file-sha256', 'files': [descriptor(public / f, public) for f in
                ('math_gauge/taste_v130.py', 'math_gauge/scoring.py',
                 'protocol/mathematical-taste/v1.3.0/policy.json')]})
        self.registration = self.sources / 'registration.json'
        write_json(self.registration, self.reg)
        self.state = self.root / 'archive'
        self.work = self.root / 'participant'
        self.context = 'fresh-synthetic-session'
        self.observation = self.root / 'operator-observation.json'

    def reveal(self, rid, context=None):
        return flow.reveal(self.registration, self.state, self.work, rid, context or self.context)

    def seal(self, rid, *, delivery='normal-final', artifact=False, **changes):
        answer = self.work / f'answer-{rid}.md'
        if delivery == 'normal-final':
            answer.write_text(f'Fixture {rid}: 命题。 Proof and boundaries.\n')
        refs = []
        if artifact:
            path = self.work / 'artifact.md'
            path.write_text('Explicitly delivered mathematical file.\n')
            refs.append(descriptor(path, self.work))
        obs = dict(schema='math-gauge.research-round-observation/v1', round=rid,
            context_id=self.context, request_id=f'fixture-{rid}', kind='fixture', delivery=delivery,
            first_normal_final=True if delivery == 'normal-final' else None,
            boundary={'kind': 'first-normal-final' if delivery == 'normal-final' else 'deadline', 'at': None},
            native_terminal=None, raw=descriptor(answer, self.work) if delivery == 'normal-final' else None,
            delivered_files=refs)
        obs.update(changes)
        write_json(self.observation, obs)
        return flow.seal_final(self.registration, self.state, self.work, rid, self.context,
            answer if delivery == 'normal-final' else None, self.observation)

    def finish(self):
        for rid in flow.ROUNDS:
            self.reveal(rid)
            self.seal(rid)

    def citation(self, rid):
        path = self.state / f'{rid}.md'
        raw = path.read_bytes()
        return dict(round=rid, file=path.name, start=0, end=len(raw), quote=raw.decode())

    def review(self):
        self.finish()
        review = flow.review_template(self.registration, self.state, 'fixture-reviewer', 'independent-fixture')
        for axis in flow.AXES:
            review['axes'][axis] = dict(score=80, strict=True, reason='Synthetic assessment.',
                evidence=[self.citation(r) for r in self.contract['round_coverage'][axis]])
            for rid in review['round_reviews'][axis]:
                review['round_reviews'][axis][rid] = dict(score=80, strict=True, reason='Synthetic manuscript check.',
                    evidence=[self.citation(rid)])
            for spec in self.contract['gates'][axis]:
                review['gates'][axis][spec['id']] = dict(verdict=True, reason='Synthetic gate check.',
                    evidence=[self.citation(r) for r in spec['rounds']])
        review['selection_audit'] = dict(sufficient_choices=True, reason='Synthetic available choices audited.',
            kept=[self.citation('R3')], removed=[self.citation('R1')])
        return review

    def validate(self, review):
        path = self.root / 'review.json'
        write_json(path, review)
        return flow.validate_review(self.registration, self.state, path)

    def test_candidate_projection_is_exact_and_does_not_copy_evaluator_or_future_rounds(self):
        self.reveal('R1')
        actual = {p.relative_to(self.work).as_posix() for p in self.work.rglob('*') if p.is_file()}
        self.assertEqual(actual, {'rules.md', 'packet/body.md', 'packet/figures/fixture.png', 'rounds/R1.md'})
        self.assertFalse(any(b'EVALUATOR-ONLY-SENTINEL' in p.read_bytes() for p in self.work.rglob('*') if p.is_file()))
        self.assertEqual(json.loads((self.state / 'session.json').read_text())['isolation'],
                         'not-provided-by-this-offline-tool')

    def test_round_order_requires_frozen_final_and_same_context(self):
        with self.assertRaises(ValueError): self.reveal('R2')
        self.reveal('R1')
        with self.assertRaises(ValueError): self.reveal('R2')
        self.seal('R1')
        with self.assertRaises(ValueError): self.reveal('R2', 'different-context')
        with self.assertRaises(ValueError): self.reveal('R3')
        self.reveal('R2')
        self.seal('R2')
        self.reveal('R3')
        self.seal('R3')
        for rid in ('R1', 'R3', 'R4'):
            with self.assertRaises(ValueError): self.reveal(rid)

    def test_first_final_is_exclusive_and_snapshots_original_explicit_files(self):
        self.reveal('R1')
        self.seal('R1', artifact=True)
        before = (self.state / 'R1.md').read_bytes()
        (self.work / 'answer-R1.md').write_text('Later replacement')
        (self.work / 'artifact.md').write_text('Later undelivered artifact')
        self.assertEqual((self.state / 'R1.md').read_bytes(), before)
        self.assertEqual((self.state / 'R1.files/artifact.md').read_text(), 'Explicitly delivered mathematical file.\n')
        with self.assertRaises(ValueError): self.seal('R1')

    def test_unsealed_partial_files_are_not_silently_overwritten_after_interruption(self):
        self.reveal('R1')
        (self.state / 'R1.md').write_text('Original partial collection')
        with self.assertRaises(FileExistsError): self.seal('R1')
        self.assertEqual((self.state / 'R1.md').read_text(), 'Original partial collection')
        self.assertFalse((self.state / 'R1.seal.json').exists())

    def test_hash_damage_and_round_holes_are_detected(self):
        self.reveal('R1'); self.seal('R1')
        (self.state / 'R1.md').write_text('damaged')
        with self.assertRaises(ValueError): self.reveal('R2')

    def test_supplied_inputs_may_not_be_modified(self):
        self.reveal('R1'); self.seal('R1')
        (self.work / 'packet/body.md').write_text('changed input')
        with self.assertRaises(ValueError): self.reveal('R2')

    def test_final_seal_rechecks_the_actual_packet_even_without_a_later_round(self):
        self.reveal('R1')
        (self.work/'packet/body.md').write_text('Changed before final')
        with self.assertRaises(ValueError): self.seal('R1')

    def test_failed_and_unresolved_deliveries_block_continuation_without_inventing_a_final(self):
        self.reveal('R1'); self.seal('R1', delivery='delivery-failed')
        self.assertFalse((self.state / 'R1.md').exists())
        with self.assertRaises(ValueError): self.reveal('R2')
        with self.assertRaises(ValueError): flow.review_template(self.registration, self.state, 'r', 'x')

    def test_operator_attestation_cannot_promote_error_or_a_later_final(self):
        self.reveal('R1')
        with self.assertRaises(ValueError): self.seal('R1', native_terminal='ERROR')
        with self.assertRaises(ValueError): self.seal('R1', native_terminal='error')
        with self.assertRaises(ValueError): self.seal('R1', first_normal_final=False)

    def test_path_escape_symlink_and_overlapping_source_trees_are_rejected(self):
        self.reveal('R1')
        link = self.work / 'link'
        link.symlink_to(self.case, target_is_directory=True)
        with self.assertRaises(ValueError): flow._contained(self.work, 'link/candidate/R1.md')
        with self.assertRaises(ValueError): flow._contained(self.work, '../evaluator')
        with self.assertRaises(ValueError):
            flow.reveal(self.registration, self.root/'archive2', self.sources/'participant', 'R1', 'x')

    def test_original_archives_cannot_be_written_inside_the_public_repository(self):
        with self.assertRaises(ValueError):
            flow.reveal(self.registration, flow.POLICY_FILE.parents[3]/'runs/v130-forbidden-archive',
                        self.work, 'R1', self.context)

    def test_registration_binds_rubric_runner_and_fixed_packet_bytes(self):
        flow.load_case(self.registration)
        (self.case / 'evaluator/rubric.md').write_text('changed review key')
        with self.assertRaises(ValueError): flow.load_case(self.registration)

    def test_pending_template_keeps_scores_and_gates_unknown(self):
        self.finish()
        review = flow.review_template(self.registration, self.state, 'fixture', 'other-context')
        result = self.validate(review)
        self.assertTrue(all(v['score'] is None and v['strict'] is None for v in result.values()))

    def test_private_review_is_bound_to_finals_exact_quotes_and_independent_context(self):
        review = self.review()
        self.validate(review)
        bad = deepcopy(review); bad['axes']['autonomy']['evidence'][0]['quote'] = 'invented quote'
        with self.assertRaises(ValueError): self.validate(bad)
        bad = deepcopy(review); bad['reviewer_context_id'] = self.context
        with self.assertRaises(ValueError): self.validate(bad)
        bad = deepcopy(review); bad['sealed_finals']['R3'] = '0'*64
        with self.assertRaises(ValueError): self.validate(bad)

    def test_five_hard_gates_do_not_allow_compensation_and_optional_gate_is_optional(self):
        review = self.review()
        review['gates']['capacity']['optional']['verdict'] = False
        self.validate(review)
        review['gates']['capacity']['C0']['verdict'] = False
        with self.assertRaises(ValueError): self.validate(review)
        review['axes']['capacity']['strict'] = False
        self.validate(review)
        review['gates']['capacity']['C0']['verdict'] = None
        review['gates']['capacity']['C0']['evidence'] = []
        review['axes']['capacity']['strict'] = None
        self.validate(review)

    def test_capacity_gate_must_cite_actual_final_not_deleted_earlier_work(self):
        review = self.review()
        review['gates']['capacity']['C0']['evidence'] = [self.citation('R1')]
        with self.assertRaises(ValueError): self.validate(review)

    def test_no_high_taste_for_absent_choices_or_missing_manuscript_review(self):
        review = self.review()
        bad = deepcopy(review); bad['selection_audit']['sufficient_choices'] = False
        with self.assertRaises(ValueError): self.validate(bad)
        bad = deepcopy(review); bad['round_reviews']['taste']['R2']['score'] = None
        with self.assertRaises(ValueError): self.validate(bad)

    def test_fixtures_cannot_be_relabelled_as_model_or_human_reviews(self):
        review = self.review()
        review['reviewer_kind'] = 'ai'
        with self.assertRaises(ValueError): self.validate(review)
        review['reviewer_kind'] = 'fixture'; review['human_review'] = 'approved'
        with self.assertRaises(ValueError): self.validate(review)


class CompositeScoringTests(unittest.TestCase):
    def setUp(self):
        self.policy = json.loads(flow.POLICY_FILE.read_bytes())
        self.base = dict(MC=90, RMC=80, SMC=60)
        self.axes = dict(initiative=37, discernment=70, open_research=50, depth=64, completion=60)
        self.review = {k: dict(score=v, strict=True) for k, v in zip(flow.AXES, (40, 60, 80))}

    def score(self, **kwargs):
        base = kwargs.pop('base', self.base)
        groups = kwargs.pop('base_groups', {m:dict.fromkeys(('written','lean','research'),v) for m,v in base.items()})
        return score_research_preview(base, kwargs.pop('base_axes', self.axes), base_groups=groups,
            status=kwargs.pop('status', 'reviewed'), review=kwargs.pop('review', self.review),
            policy=kwargs.pop('policy', self.policy), **kwargs)

    def test_two_layers_are_explicit_and_do_not_redefine_legacy_modes_or_initiative(self):
        result = self.score()
        self.assertEqual(result['item_composite']['exact'], 65)
        self.assertEqual(result['composite_by_base']['RMC']['exact'], 78.5)
        self.assertEqual(result['legacy_scores'], self.base)
        self.assertEqual(result['legacy_abilities'], self.axes)
        self.assertNotIn('initiative', result['abilities'])
        self.assertEqual(result['abilities']['open_research_autonomy']['exact'], 40)
        self.assertEqual(result['abilities']['mathematical_taste']['denominator']['planned'], 3)
        self.assertEqual(result['abilities']['completion_v130']['exact'], result['strict_overall']['exact'])
        self.assertFalse(result['rank_eligible'])

    def test_full_score_failure_and_partial_review_keep_fixed_denominators(self):
        full = {k: dict(score=100, strict=True) for k in flow.AXES}
        all_full = self.score(base=dict.fromkeys(self.base, 100), review=full)
        self.assertEqual(all_full['strict_overall']['exact'], 100)
        partial = deepcopy(full); partial['taste'] = dict(score=None, strict=None)
        result = self.score(review=partial)
        self.assertIsNone(result['item_composite']['exact'])
        self.assertEqual((result['item_composite']['lower'], result['item_composite']['upper']), (75, 100))
        self.assertIsNone(result['item_strict'])
        partial['autonomy']['strict'] = False
        self.assertEqual(self.score(review=partial)['item_strict'], 0)
        self.assertEqual(result['coverage']['components_planned'], 3)
        self.assertEqual(result['coverage']['components_reviewed'], 2)

    def test_unrun_pending_invalid_are_unknown_and_not_reweighted_or_zeroed(self):
        for status in ('not-run', 'review-pending', 'invalid'):
            with self.subTest(status=status):
                result = self.score(status=status, review=None)
                metric = result['composite_by_base']['RMC']
                self.assertIsNone(metric['exact'])
                self.assertEqual((metric['lower'], metric['upper']), (72, 82))
                self.assertFalse(result['comparable_preview'])
                self.assertIsNone(result['abilities']['mathematical_taste']['exact'])

    def test_delivery_failure_is_operational_zero_not_a_mathematical_axis_judgment(self):
        result = self.score(status='delivery-failed', review=None)
        self.assertEqual(result['item_composite']['exact'], 0)
        self.assertEqual(result['item_strict'], 0)
        self.assertTrue(all(v is None for v in result['subscores'].values()))
        self.assertEqual(result['legacy_scores']['MC'], 90)
        self.assertFalse(result['comparable_preview'])

    def test_known_zero_and_unknown_base_intervals_stay_distinct(self):
        result = self.score(base=dict(MC=0, RMC=None, SMC=dict(lower=10, upper=20, exact=None)))
        self.assertEqual(result['composite_by_base']['MC']['exact'], 6.5)
        self.assertIsNone(result['composite_by_base']['RMC']['exact'])
        self.assertEqual(result['strict_overall']['lower'], 19)
        self.assertEqual(result['strict_overall']['upper'], 28)

    def test_ten_point_marginal_and_signed_decrease(self):
        for base in (0, 23, 100):
            low = self.score(base=dict.fromkeys(self.base, base),
                review={k: dict(score=0, strict=False) for k in flow.AXES})
            high = self.score(base=dict.fromkeys(self.base, base),
                review={k: dict(score=100, strict=True) for k in flow.AXES})
            for mode in self.base:
                self.assertAlmostEqual(high['composite_by_base'][mode]['exact'] -
                                       low['composite_by_base'][mode]['exact'], 10)
                self.assertLessEqual(abs(low['composite_by_base'][mode]['exact']-base), 10)
        self.assertLess(self.score()['composite_by_base']['MC']['exact'], self.base['MC'])

    def test_legacy_groups_are_reweighted_individually_and_missing_groups_remain_unknown(self):
        groups = {m: dict(written=100, lean=0, research=0) for m in self.base}
        result = self.score(base=dict.fromkeys(self.base, 35), base_groups=groups)
        self.assertEqual(result['composite_by_base']['RMC']['exact'], 36.5)
        self.assertEqual(result['legacy_scores']['RMC'], 35)
        result = score_research_preview(self.base, self.axes, status='reviewed', review=self.review, policy=self.policy)
        self.assertIsNone(result['composite_by_base']['RMC']['exact'])

    def test_signed_unknown_group_deductions_are_retained_and_only_whole_total_is_floored(self):
        groups={m:dict(written=0,lean=0,research=0) for m in self.base}
        groups['RMC']['written']=dict(lower=-20,upper=100,exact=None,confirmed=10)
        result=self.score(base_groups=groups)
        self.assertAlmostEqual(result['composite_by_base']['RMC']['lower'],.5)
        self.assertEqual(result['confirmed_by_base']['RMC'],9.5)
        self.assertIsNone(result['composite_by_base']['RMC']['exact'])

    def test_adjustable_parameters_are_validated_without_observation_based_normalization(self):
        policy = deepcopy(self.policy)
        policy['overall_item_weight'] = .2
        policy['legacy_group_weights']['written'] = .2
        result = self.score(policy=policy)
        self.assertEqual(result['composite_by_base']['RMC']['exact'], 77)
        for field in ('autonomy', 'taste'):
            bad = deepcopy(policy); bad['continuous_item_weights'][field] = .5
            with self.assertRaises(ValueError): self.score(policy=bad)
        bad = deepcopy(self.review); bad['capacity']['score'] = float('nan')
        with self.assertRaises(ValueError): self.score(review=bad)
        with self.assertRaises(ValueError): self.score(status='not-run')


class DisplayProjectionTests(unittest.TestCase):
    def test_only_allowlisted_aggregate_fields_reach_the_preview(self):
        from scripts.preview_open_research_v130 import fixture_data, public_row
        report = flow.preview(dict(MC=50, RMC=50, SMC=50), {}, status='not-run')
        report.update(case_id='PRIVATE-SENTINEL', evidence='PRIVATE-SENTINEL',
                      manuscript='PRIVATE-SENTINEL', gates='PRIVATE-SENTINEL')
        row = public_row('fixture-only', 'Synthetic', report)
        self.assertNotIn('PRIVATE-SENTINEL', json.dumps(row))
        self.assertEqual(row['components']['autonomy']['state'], 'not-tested')
        self.assertTrue(all(r['kind'] == 'synthetic-fixture' for r in fixture_data()['rows']))

    def test_published_baselines_cannot_inherit_a_research_grade(self):
        from scripts.preview_open_research_v130 import baseline_data
        data = baseline_data()
        source = json.loads((flow.POLICY_FILE.parents[3]/'site/data.json').read_bytes())
        self.assertEqual({r['id'] for r in data['rows']}, {r['id'] for r in source['models']})
        self.assertTrue(all(r['kind'] == 'existing-model-unmeasured' for r in data['rows']))
        for row in data['rows']:
            self.assertTrue(all(v == dict(state='not-tested', value=None, strict=None) for v in row['components'].values()))
            self.assertIsNone(row['task_strict'])
            self.assertIsNone(row['strict_overall']['exact'])
            self.assertIsNone(row['composite']['exact'])

class SharedHomepageEditionTests(unittest.TestCase):
    def test_original_homepage_adds_reverse_ordered_version_and_reweighted_bars(self):
        import subprocess
        from scripts.results_research_preview import prepare_research_preview, CONFIG
        root=flow.POLICY_FILE.parents[3]
        names=('index.html','editions.json','data.json','data/editions/1.2.0/index.json')
        original={name:subprocess.check_output(['git','show','HEAD:site/'+name],cwd=root).decode() for name in names}
        before=deepcopy(original)
        result=prepare_research_preview(original,root)
        self.assertEqual(original,before)
        for key in ('data.json','data/editions/1.2.0/index.json'):
            self.assertEqual(result[key],original[key])
        old=json.loads(CONFIG.search(original['index.html'])[2]);new=json.loads(CONFIG.search(result['index.html'])[2])
        self.assertEqual(list(new['versions']),['1.3.0','1.2.0','1.1.0','1.0.0'])
        self.assertEqual(new['latest'],'1.3.0')
        self.assertEqual(new['versions']['1.3.0']['label']['zh'],'1.3.0')
        for version,entry in old['versions'].items():
            if tuple(map(int, version.split('.'))) < (1, 3, 0):
                self.assertEqual(new['versions'][version],entry)
        view=json.loads(result['data/editions/1.3.0/index.json'])['data']
        self.assertEqual(view['research_preview']['weight_frame'],dict(written=30,lean=30,research=30,independent_open_research=10))
        rows={r['id']:r for r in view['research_preview']['rows']}
        for model in view['models']:
            source=model['strict']['nonlogical_retry_3']['metrics']['earned']
            self.assertIsNone(source['exact'])
            self.assertEqual(source['coverage'],dict(unit='fixed_weighted_category',planned=4,adjudicated=3,unknown=1))
            self.assertEqual(source['confirmed'],rows[model['id']]['strict_confirmed'])
            bar=view['chart_scenes']['chart-groups']['bars'][model['id']]['strict']
            self.assertEqual(bar['value'],source['confirmed'])
            self.assertAlmostEqual(source['upper']-source['lower'],10)
        self.assertEqual({p for p in result if p.endswith('.html')},{'index.html'})

    def test_roots_without_the_new_policy_keep_the_existing_publication(self):
        from scripts.results_research_preview import prepare_research_preview
        with tempfile.TemporaryDirectory() as directory:
            original={'index.html':'existing'}
            self.assertIs(prepare_research_preview(original,Path(directory)),original)

class PrivateMarkerProjectionTests(unittest.TestCase):
    def test_private_fixture_marker_never_reaches_public_html_client_or_download(self):
        import subprocess,uuid
        from scripts.preview_open_research_v130 import fixture_data,public_row
        marker=uuid.uuid4().hex
        root=flow.POLICY_FILE.parents[3]
        grades={k:dict(score=v,strict=False) for k,v in zip(flow.AXES,(80,0,60))}
        report=flow.preview(dict.fromkeys(('MC','RMC','SMC'),50),{},status='reviewed',review=grades,
            base_groups={m:dict.fromkeys(('written','lean','research'),50) for m in ('MC','RMC','SMC')})
        report['private_evaluator_notes']=marker
        with tempfile.TemporaryDirectory() as directory:
            work=Path(directory);private=work/'private';public=work/'public';private.mkdir();public.mkdir()
            write_json(private/'fixture.json',report)
            row=public_row('fixture-alpha','Pure synthetic',json.loads((private/'fixture.json').read_bytes()))
            data=fixture_data();data['rows'][0]=row
            serialized=json.dumps(data,ensure_ascii=False)
            code="const ui=require('./scripts/templates/research-preview.js');let s='';process.stdin.on('data',b=>s+=b);process.stdin.on('end',()=>process.stdout.write(ui.render(JSON.parse(s))));"
            html=subprocess.check_output(['node','-e',code],input=serialized.encode(),cwd=root)
            (public/'index.html').write_bytes(html)
            (public/'client.js').write_text('globalThis.fixture='+serialized+';')
            write_json(public/'download.json',dict(kind='synthetic-fixture',aggregate=row))
            for artifact in public.iterdir():self.assertNotIn(marker.encode(),artifact.read_bytes())
            self.assertEqual(row['components']['autonomy']['value'],80)
            self.assertEqual(row['components']['taste']['value'],0)
            self.assertTrue((private/'fixture.json').read_text().find(marker)>=0)
