"""Synthetic source contracts only; no real Carbon score, native process or private task."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from math_gauge import independent_research_admitted_delivery as native
from math_gauge import independent_research_value as value
from scripts.results_research_baseline import (ADDITIONS_PATH, ADDITIONS_SCHEMA, POLICY_PATH,
    BaselineSelection, select_additions, display_baseline)
from scripts import adopt_independent_research_admitted_delivery as cli
from test_independent_research_native import public_fixture
from test_research_ability_projection import baseline
from test_research_ability_projection import selection, overlay, MEASURED
from math_gauge import independent_research_adoption as adoption
from math_gauge import legacy_taste_addition as taste_addition
from math_gauge import independent_research_score_modes as modes
from math_gauge import independent_research_strict_credit as credit
from math_gauge import independent_research_item_weights as item_weights
from math_gauge.research_profile import POLICY_PATH as PROFILE_PATH, VALUE_POLICY_PATH
from math_gauge.taste_v130 import POLICY_FILE
from scripts.results_research_preview import prepare_research_preview
from scripts.cost_reference import independent_research_reference
from scripts import results_independent_research_resources as resources


def encoded(data):
    return native.encoded(data)


def descriptor(path, root=None):
    raw = path.read_bytes()
    return dict(path=path.relative_to(root).as_posix() if root else str(path),
                bytes=len(raw), sha256=native.digest(raw))


def synthetic_addition(parent):
    index = public_fixture()
    model = index['models'].pop(index['cohort'][0])
    model.update(normal_rounds=2,forced_rounds=1,delivery_kinds=['forced-content','normal-final','normal-final'])
    index.update(schema=native.SCHEMA, version='0.1.0', cohort=[native.MODEL], source_kind=native.SOURCE_KIND,
        models={native.MODEL: model}, source_binding=dict(base_edition='1.2.0',baseline=parent,adoption_sha256='b'*64,
            admission_sha256='c'*64,review_sha256='d'*64,authorization_sha256=native.AUTHORIZATION_SHA256),
        method=dict(selection='post-observation-user-selected-cutoff',native_status_preserved=True,
            forced_content_is_mathematically_reviewed=True,original_round_limit_seconds=2700,
            R1_user_extension_seconds=900,account_condition_changed=True,historical_results_unchanged=True,
            resource_usage_scope='unknown-until-independently-reconciled'))
    return index


class NativeParentAdditionTests(unittest.TestCase):
    def setUp(self):
        self.temp = TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.old = baseline()
        self.old.update(schema='math-gauge.results/v1',manuscript_observations=dict(models=[]))
        self.old['gap_diagnostics']['tables']=[]
        for model in self.old['models']:
            model['harness']=dict(name='Synthetic')
            model['logo']['sha256']='d'*64
            model['combined']=deepcopy(model['retry']['combined'])
            for report in (model['combined'],model['retry']['combined'],*model['capability'].values(),*model['strict'].values()):
                report['contributions']={}
        self.new = deepcopy(self.old)
        carbon = deepcopy(self.old['models'][0])
        carbon.update(id=native.MODEL, label='Synthetic Carbon fixture')
        self.new['models'].append(carbon)
        self.old_raw, self.new_raw = encoded(self.old), encoded(self.new)
        self.selected = BaselineSelection(self.old_raw.decode(), self.old, self.new_raw.decode(), True)
        self.write('site/data.json', self.old_raw)
        self.write('site/versions/1.2.0/data.json', self.new_raw)
        policy = self.write(POLICY_PATH, encoded(dict(synthetic_original_selection=True)))
        parent_path = f'results/independent-research-baselines/v0.1.0/{native.digest(self.new_raw)}/data.json'
        self.parent = descriptor(self.write(parent_path, self.new_raw), self.root)
        for name in native.external.POLICY_PATHS.values():
            self.write(name, (value.POLICY_FILE.parents[3]/name).read_bytes())
        self.index = synthetic_addition(self.parent)
        self.index['policy_bindings'] = native.external.policy_bindings(self.root)
        native_path = self.write(native.PUBLIC_PATH, encoded(self.index))
        self.manifest = dict(schema=ADDITIONS_SCHEMA, version='0.1.0', edition='1.3.0',
            original_selection=descriptor(policy, self.root), new_candidate_calls=0, new_mathematical_judgments=0,
            additions=[dict(id=native.MODEL, baseline=self.parent,
                            native_index=descriptor(native_path, self.root), resources=None)])
        self.write(ADDITIONS_PATH, encoded(self.manifest))

    def write(self, name, raw):
        path = self.root/name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)
        return path

    def configure_projection(self):
        original_policy=POLICY_FILE.read_bytes()
        adopted=selection(self.old_raw,original_policy)
        adopted_raw=encoded(adopted)
        overlay_raw=overlay(adopted_raw)
        policy,_=value.load_policy()
        policy['base_results_sha256']=native.digest(overlay_raw)
        policy_raw=encoded(policy)
        revised_raw=encoded(dict(schema=value.PUBLIC,version=value.VERSION,edition='1.3.0',
            policy_sha256=native.digest(policy_raw),base_results_sha256=native.digest(overlay_raw),
            candidate_calls_by_adoption=0,cohort=[MEASURED],models={MEASURED:dict(taste=dict(mc=10,rmc=0,strict=False),
                criteria=dict(planned=3,passed=1,unknown=0),extension_level='E1',source_sha256='a'*64)}))
        strict_policy,_=credit.load_policy()
        strict_policy.update(value_policy_sha256=native.digest(policy_raw),value_results_sha256=native.digest(revised_raw),
                             score_modes_results_sha256=native.digest(overlay_raw))
        strict_raw_policy=encoded(strict_policy)
        strict_raw=encoded(dict(schema=credit.PUBLIC,version=credit.VERSION,edition='1.3.0',
            policy_sha256=native.digest(strict_raw_policy),value_results_sha256=native.digest(revised_raw),
            candidate_calls_by_adoption=0,cohort=[MEASURED],models={MEASURED:dict(
                taste=dict(lower=0,upper=0,exact=0),capacity=dict(lower=70,upper=70,exact=70),source_sha256='b'*64)}))
        weights=dict(schema=item_weights.SCHEMA,version=item_weights.VERSION,edition='1.3.0',
            status='local-user-selected-item-weights',item_weights=dict(taste=2,capacity=1),
            value_policy_sha256=native.digest(policy_raw),value_results_sha256=native.digest(revised_raw),
            strict_credit_policy_sha256=native.digest(strict_raw_policy),strict_credit_results_sha256=native.digest(strict_raw))
        for name,raw in [(adoption.PUBLIC_PATH,adopted_raw),(modes.POLICY_PATH,modes.POLICY_FILE.read_bytes()),
            (modes.PUBLIC_PATH,overlay_raw),(value.POLICY_PATH,policy_raw),(value.PUBLIC_PATH,revised_raw),
            (credit.PATH,strict_raw_policy),(credit.PUBLIC_PATH,strict_raw),(item_weights.POLICY_PATH,encoded(weights)),
            (POLICY_FILE.relative_to(POLICY_FILE.parents[3]),original_policy),
            (PROFILE_PATH,(POLICY_FILE.parents[3]/PROFILE_PATH).read_bytes()),
            (VALUE_POLICY_PATH,(POLICY_FILE.parents[3]/VALUE_POLICY_PATH).read_bytes())]:
            self.write(name,raw)
        selected_policy=dict(schema='math-gauge.independent-research-baseline-selection/v1',version='0.1.0',
            edition='1.3.0',selection='retained-original-adoption-baseline',
            baseline=dict(edition='1.2.0',**descriptor(self.root/'site/data.json',self.root)),
            settled_index=descriptor(self.root/adoption.PUBLIC_PATH,self.root),
            current_base_publication=dict(edition='1.2.0',data_path='versions/1.2.0/data.json'),
            original_grade_bindings_modified=False,new_candidate_calls=0,new_mathematical_judgments=0)
        self.write(POLICY_PATH,encoded(selected_policy))
        self.index['policy_bindings']=native.external.policy_bindings(self.root)
        self.write(native.PUBLIC_PATH,encoded(self.index))
        self.manifest['original_selection']=descriptor(self.root/POLICY_PATH,self.root)
        self.manifest['additions'][0]['native_index']=descriptor(self.root/native.PUBLIC_PATH,self.root)
        self.write(ADDITIONS_PATH,encoded(self.manifest))
        for name in ('research-preview.js','research-preview.css','edition-notes.js','board-controls.js',
                     'results-core.js','home-results.js','mathematical-profile.js','mathematical-profile.css'):
            self.write('scripts/templates/'+name,(POLICY_FILE.parents[3]/'scripts/templates'/name).read_bytes())

    def test_publication_join_preserves_old_math_and_downloads_use_per_model_parent(self):
        self.configure_projection()
        files={'data.json':self.new_raw.decode(),'data/editions/1.2.0/index.json':encoded(dict(
            edition='1.2.0',page='index.html',data=self.new)).decode(),
            'index.html':'<head><script type="application/json" id="edition-config">{"versions":{"1.2.0":{}},"scripts":[]}</script></head><main></main>',
            'editions.json':'{"editions":[{"version":"1.2.0","data":"data.json"}]}'}
        manifest=(self.root/ADDITIONS_PATH).read_bytes()
        (self.root/ADDITIONS_PATH).unlink()
        before=prepare_research_preview(files,self.root)
        self.write(ADDITIONS_PATH,manifest)
        after=prepare_research_preview(files,self.root)
        old,new=(json.loads(package['versions/1.3.0/data.json']) for package in (before,after))
        old_rows={r['id']:r for r in old['research_preview']['rows']}
        rows={r['id']:r for r in new['research_preview']['rows']}
        for mid,row in old_rows.items():
            self.assertEqual(rows[mid],row)
            self.assertEqual(new['independent_research_abilities']['by_model'][mid],old['independent_research_abilities']['by_model'][mid])
        self.assertEqual(new['research_preview']['source_binding'],old['research_preview']['source_binding'])
        self.assertEqual(new['research_preview']['schema'],'math-gauge.research-board-preview/v7')
        self.assertEqual(after['data.json'].encode(),self.old_raw)
        self.assertEqual(after['versions/1.2.0/data.json'].encode(),self.new_raw)
        for suffix in ('','-strict','-capability'):
            download=json.loads(after[f'versions/1.3.0/downloads/{native.MODEL}-combined{suffix}-retry.json'])
            self.assertEqual(download['source_binding']['sha256'],self.parent['sha256'])
            self.assertEqual(download['baseline_parent'],self.parent)
            self.assertNotIn('adoption_binding',download)
        result=native.project_model(dict(MC=self.new['models'][-1]['capability']['nonlogical_retry_3'],
            RMC=self.new['models'][-1]['retry']['combined'],SMC=self.new['models'][-1]['strict']['nonlogical_retry_3']),
            dict(value.load_policy(self.root/value.POLICY_PATH)[0],item_weights=dict(taste=2,capacity=1)),
            self.index['models'][native.MODEL])
        self.assertEqual(rows[native.MODEL]['composites'],result['composite_by_base'])
        self.assertEqual(new['independent_research_abilities']['schema'],'math-gauge.independent-research-abilities/v9')
        carbon_model=next(m for m in new['models'] if m['id']==native.MODEL)
        self.assertEqual(carbon_model['independent_research_delivery']['normal_rounds'],2)
        self.assertEqual(carbon_model['independent_research_delivery']['forced_rounds'],1)
        for stage in ('first','revision'):
            for axis in ('depth_v130','open_research_v130'):
                metric=new['independent_research_abilities']['by_model'][native.MODEL]['stages'][stage][axis]
                self.assertIsNone(metric['exact'])
                self.assertEqual((metric['lower'],metric['upper']),(0,100))
        self.assertIsNone(new['independent_research_abilities']['by_model'][native.MODEL]['stages']['revision']['mathematical_taste']['exact'])

    def test_taste_sidecar_changes_only_added_profile_and_binds_its_own_source(self):
        self.configure_projection()
        self.write(taste_addition.strict.POLICY_PATH,taste_addition.strict.POLICY_FILE.read_bytes())
        metric=lambda n:dict(lower=n,upper=n,exact=n,confirmed=n,
            coverage=dict(unit='theorem_extension_family',planned=6,observed=6,reviewed=6))
        sidecar=dict(schema=taste_addition.SCHEMA,version='0.1.0',edition='1.3.0',condition='nonlogical_retry_3',
            source_binding=dict(base_edition='1.2.0',baseline=self.parent,reuse_audit_sha256=taste_addition.REUSE_AUDIT_SHA256,
                source_catalog_sha256='1'*64,original_index_sha256='2'*64,accepted_proposals_sha256=[c*64 for c in '3456']),
            policy_sha256=taste_addition.strict.load_policy()[1],base_scope_policy_sha256='7'*64,
            cohort=[native.MODEL],models={native.MODEL:dict(first=metric(95),revision=metric(96))},
            reused_revision_families=4,reviewer_kind='ai',human_review='pending',post_observation=True,
            new_candidate_calls=0,new_mathematical_judgments=0)
        path=self.write(taste_addition.PUBLIC_PATH,encoded(sidecar))
        self.manifest['version']='0.2.0';self.manifest['additions'][0]['legacy_taste']=descriptor(path,self.root)
        self.write(ADDITIONS_PATH,encoded(self.manifest))
        [addition]=select_additions(self.root,self.selected)
        self.assertEqual(addition.legacy_taste_ref['sha256'],native.digest(encoded(sidecar)))
        self.assertEqual(self.index['models'][native.MODEL]['axes']['taste']['rmc'],72)
        files={'data.json':self.new_raw.decode(),'data/editions/1.2.0/index.json':encoded(dict(edition='1.2.0',page='index.html',data=self.new)).decode(),
            'index.html':'<head><script type="application/json" id="edition-config">{"versions":{"1.2.0":{}},"scripts":[]}</script></head><main></main>',
            'editions.json':'{"editions":[{"version":"1.2.0","data":"data.json"}]}'}
        projected=json.loads(prepare_research_preview(files,self.root)['versions/1.3.0/data.json'])
        metrics=projected['independent_research_abilities']['by_model'][native.MODEL]['stages']
        self.assertEqual(metrics['first']['mathematical_taste']['exact'],63)
        self.assertEqual(metrics['revision']['mathematical_taste']['exact'],63.2)
        bad=deepcopy(sidecar);bad['source_binding']['baseline']['private_source']='forbidden'
        with self.assertRaises(ValueError):taste_addition.validate_public(bad)
        bad=deepcopy(sidecar);bad['models'][native.MODEL]['revision']['coverage']['planned']=4
        with self.assertRaises(ValueError):taste_addition.validate_public(bad)

    def test_addition_preserves_old_parent_and_binds_its_own_exact_source(self):
        old_index = public_fixture()
        with self.assertRaises(ValueError):
            native.validate_public(old_index, baseline_hash=self.parent['sha256'])
        before = (self.root/'site/data.json').read_bytes()
        [added] = select_additions(self.root, self.selected)
        self.assertEqual(added.parent, self.parent)
        self.assertEqual(added.index, self.index)
        display = display_baseline(self.selected, [added])
        self.assertEqual(display['models'][:-1], self.old['models'])
        self.assertEqual(display['models'][-1]['id'], native.MODEL)
        self.assertEqual((self.root/'site/data.json').read_bytes(), before)
        self.assertEqual(self.selected.data, self.old)
        self.assertEqual(added.index['models'][native.MODEL]['forced_rounds'], 1)

    def test_no_manifest_does_not_search_or_admit_new_current_model(self):
        (self.root/ADDITIONS_PATH).unlink()
        self.assertEqual(select_additions(self.root, self.selected), ())
        self.assertEqual(display_baseline(self.selected, ()), self.old)

    def test_wrong_parent_changed_model_overlap_and_private_fields_fail(self):
        for mutation in ('parent', 'retained-model', 'new-model', 'overlap', 'private'):
            with self.subTest(mutation=mutation):
                manifest = deepcopy(self.manifest)
                selected = self.selected
                if mutation == 'parent':
                    manifest['additions'][0]['baseline']['sha256'] = 'f'*64
                elif mutation in ('retained-model', 'new-model'):
                    data = deepcopy(self.new)
                    data['models'][0 if mutation == 'retained-model' else -1]['display_order'] = False
                    selected = BaselineSelection(self.old_raw.decode(), self.old, encoded(data).decode(), True)
                    if mutation == 'retained-model':
                        # A different frozen parent must also fail the old-model invariant.
                        raw = encoded(data)
                        ref = descriptor(self.write(f'results/independent-research-baselines/v0.1.0/{native.digest(raw)}/data.json', raw), self.root)
                        manifest['additions'][0]['baseline'] = ref
                elif mutation == 'overlap':
                    manifest['additions'][0]['id'] = self.old['models'][0]['id']
                else:
                    manifest['additions'][0]['private_quote'] = 'SYNTHETIC-PRIVATE-MARKER'
                self.write(ADDITIONS_PATH, encoded(manifest))
                with self.assertRaises(ValueError):
                    select_additions(self.root, selected)

    def test_public_original_stays_closed_and_new_source_cannot_hide_forced_delivery(self):
        from math_gauge import independent_research_native as original
        with self.assertRaises(ValueError): original.validate_public(self.index)
        for change in ('delivery', 'private', 'parent'):
            bad=deepcopy(self.index)
            if change=='delivery': bad['models'][native.MODEL]['normal_rounds']=3
            elif change=='parent': bad['source_binding']['baseline']['path']='site/data.json'
            else: bad['models'][native.MODEL]['raw_manuscript']='SYNTHETIC-PRIVATE-MARKER'
            with self.assertRaises(ValueError): native.validate_public(bad)

    def test_separate_install_keeps_old_native_index_and_rejects_stale_writer(self):
        old_path = self.write('protocol/mathematical-taste/v1.3.0/native-results.json', encoded(public_fixture()))
        old = old_path.read_bytes()
        target = self.root/native.PUBLIC_PATH
        target.unlink()
        cli.apply_index(self.root, self.index, None)
        self.assertEqual(old_path.read_bytes(), old)
        self.assertEqual(target.read_bytes(), encoded(self.index))
        with self.assertRaisesRegex(ValueError, 'changed during'):
            cli.apply_index(self.root, self.index, None)

    def cost_inputs(self):
        base=dict(benchmark_version='1.2.0',models=[dict(model_id=native.MODEL,total_usd=7,known_usd=7,
            status='observed',coverage=dict(planned=42,complete=42,partial=0,missing=0,not_run=0),seconds=123,scores={})])
        display=dict(benchmark_version='1.3.0',models=[self.new['models'][-1]])
        return base,display

    def test_missing_new_usage_is_unknown_for_three_rounds_not_free_or_unrun(self):
        base,display=self.cost_inputs()
        result=independent_research_reference(self.root,display,base,adoption=None,
                                             native_additions=select_additions(self.root,self.selected))
        [row]=result['models']
        self.assertIsNone(row['total_usd'])
        self.assertEqual(row['known_usd'],7)
        self.assertEqual(row['coverage'],dict(planned=45,complete=42,partial=0,missing=3,not_run=0))
        self.assertEqual(row['seconds'],123)

    def test_additional_resource_pair_counts_full_cost_once_and_rejects_rebinding(self):
        tokens=dict(uncached_input_tokens=10,cached_input_tokens=20,cache_write_input_tokens=0,
                    output_tokens=4,total_tokens=34,reasoning_output_tokens=2)
        document=dict(schema=resources.NATIVE_SCHEMA,edition='1.3.0',base_edition='1.2.0',
            pricing_basis=resources.PRICING_BASIS,native_adoption_sha256=native.digest(encoded(self.index)),
            source_evidence_sha256='a'*64,review_overhead=resources.REVIEW_OVERHEAD,
            models={native.MODEL:dict(status='observed',total_usd=.25,known_usd=.25,tokens=tokens,
                known_tokens=tokens,coverage=dict(planned=3,complete=3,partial=0,missing=0,not_run=0))})
        path=self.write(native.PUBLIC_PATH.with_name('gemini-4-carbon-medium-resources.json'),encoded(document))
        self.manifest['additions'][0]['resources']=descriptor(path,self.root)
        self.write(ADDITIONS_PATH,encoded(self.manifest))
        additions=select_additions(self.root,self.selected)
        base,display=self.cost_inputs()
        result=independent_research_reference(self.root,display,base,adoption=None,native_additions=additions)
        self.assertEqual(result['models'][0]['total_usd'],7.25)
        self.assertEqual(result['models'][0]['coverage']['complete'],45)
        with self.assertRaisesRegex(ValueError,'overlap'):
            independent_research_reference(self.root,display,base,adoption=None,native_additions=additions+additions)
        document['native_adoption_sha256']='b'*64
        path.write_bytes(encoded(document))
        self.manifest['additions'][0]['resources']=descriptor(path,self.root)
        self.write(ADDITIONS_PATH,encoded(self.manifest))
        with self.assertRaises(ValueError):select_additions(self.root,self.selected)


