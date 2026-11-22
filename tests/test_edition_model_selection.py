"""Explicit target-edition membership, independent of scores and old archives."""
from contextlib import ExitStack
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from math_gauge import neutral_revision as owner
from math_gauge.editions import NATIVE_MODEL
from scripts import export_revision_bundles as exports
from scripts import results_editions as display
from scripts import score_neutral_revisions as scorer
from scripts import adopt_neutral_revision_batch as batches


GONE = ['gemini-3.8-flash-high', 'glm-5.3-max', 'gemini-4-argon']


def reference(path):
    return dict(path=path, bytes=0, sha256='0'*64)


def fixture(*, legacy=False):
    source = dict(version='1.1.0', status='local-assessment-candidate',
        selected_result_models=['kept', 'kept-partial', *GONE],
        current_assessment_admissions={'new-admission': {}})
    edition = dict(deepcopy(source), version='1.2.0',
                   neutral_revision_transition=reference(owner.TRANSITION_PATH))
    transition = dict(schema='math-gauge.neutral-revision-transition/v1', version=owner.VERSION,
        source_scoring_edition=owner.SOURCE, target_scoring_edition=owner.TARGET,
        task_suite_version='1.0.0', attempt_condition=owner.CONDITION, post_observation=True,
        adoption_new_candidate_calls=0, original_bytes_rewritten=False,
        human_review='pending', formal_comparison_eligible=False,
        source_edition=reference(owner.SOURCE_EDITION_PATH), policy=reference(owner.POLICY_PATH),
        adoptions={}, pending_models=['kept', 'kept-partial', 'new-admission', NATIVE_MODEL])
    if legacy:
        transition['pending_models'].extend(GONE)
    else:
        transition['withdrawn_models'] = list(GONE)
    return edition, source, transition


def checked(edition, source, transition):
    def document(root, ref):
        return deepcopy(transition if ref['path'] == owner.TRANSITION_PATH else source)
    with patch.object(owner, 'document', side_effect=document), patch.object(owner, 'load_policy'):
        return owner.load_transition(Path('/unused-fixture'), edition)


class EditionMembershipTests(unittest.TestCase):
    def test_legacy_transition_without_new_field_remains_valid(self):
        e, s, t = fixture(legacy=True)
        loaded = checked(e, s, t)
        self.assertNotIn('withdrawn_models', loaded)
        self.assertTrue(set(GONE) <= owner.current_model_ids(loaded))

    def test_explicit_withdrawal_keeps_source_and_dynamic_admissions(self):
        e, s, t = fixture()
        before = deepcopy(s)
        loaded = checked(e, s, t)
        self.assertFalse(set(GONE) & owner.current_model_ids(loaded))
        self.assertIn('new-admission', owner.current_model_ids(loaded))
        self.assertEqual(s, before)
        # A later initial admission must not require a hardcoded cohort count.
        s['current_assessment_admissions']['later-neon'] = {}
        e['current_assessment_admissions']['later-neon'] = {}
        t['pending_models'].append('later-neon')
        self.assertIn('later-neon', owner.current_model_ids(checked(e, s, t)))

    def test_unknown_duplicate_overlap_missing_or_bad_id_rejected(self):
        for kind in ('unknown', 'duplicate', 'overlap', 'missing', 'nonstring'):
            with self.subTest(kind=kind):
                e, s, t = fixture()
                if kind == 'unknown': t['withdrawn_models'].append('foreign-model')
                elif kind == 'duplicate': t['withdrawn_models'].append(GONE[0])
                elif kind == 'overlap': t['pending_models'].append(GONE[0])
                elif kind == 'missing': t['pending_models'].remove('new-admission')
                else: t['withdrawn_models'].append(None)
                with self.assertRaises(ValueError): checked(e, s, t)

    def test_adopted_model_cannot_also_be_withdrawn(self):
        e, s, t = fixture()
        t['pending_models'].remove('kept')
        t['adoptions']['kept'] = reference(owner.DIRECTORY+'/kept/fixture/public.json')
        t['withdrawn_models'].append('kept')
        with self.assertRaises(ValueError): checked(e, s, t)

    def test_historical_edition_has_no_current_transition_projection(self):
        _, s, _ = fixture()
        with patch.object(owner, 'document') as read:
            self.assertIsNone(owner.load_transition('/unused-fixture', s))
        read.assert_not_called()

    def test_default_exports_follow_current_cohort_and_history_is_retained(self):
        _, s, t = fixture()
        with patch.object(exports, 'load_transition', return_value=t):
            self.assertEqual(set(exports.selected_models('/unused')), owner.current_model_ids(t))
        with patch.object(exports, 'load_transition', return_value=None), \
             patch.object(exports, 'source_assessment_edition', return_value=s), \
             patch.object(exports, 'load_assessment_transition', return_value={'calibrations':{mid:{} for mid in GONE}}):
            self.assertTrue(set(GONE) <= set(exports.selected_models('/unused')))

    def test_explicit_withdrawn_export_fails_before_output_or_package(self):
        _, _, t = fixture()
        with tempfile.TemporaryDirectory() as temp:
            base=Path(temp)
            for mid in GONE:
                dest=base/mid
                with patch.object(exports, 'load_transition', return_value=t), \
                     patch.object(exports, 'export_revision_bundle') as package:
                    with self.assertRaisesRegex(ValueError, 'outside the selected'):
                        exports.export_all(base/'public', base/'private', dest, models=[mid])
                package.assert_not_called()
                self.assertFalse(dest.exists())

    def test_rebuild_and_old_frozen_batch_reject_withdrawn_before_writes(self):
        _, _, t = fixture()
        with tempfile.TemporaryDirectory() as temp:
            base=Path(temp); public=base/'public'; public.mkdir()
            (public/'benchmark.json').write_text(json.dumps({'version':'1.2.0'}))
            for mid in GONE:
                with patch.object(scorer, 'load_transition', return_value=t), patch.object(scorer, 'write') as write:
                    with self.assertRaisesRegex(ValueError, 'outside the selected'):
                        scorer.prepare(public, base/'private', models=[mid])
                write.assert_not_called()
            run=base/'run'; run.mkdir()
            (run/'runtime-freeze.json').write_text(json.dumps({'cells':[{'model_id':GONE[0]}]}))
            with patch.object(batches, 'load_transition', return_value=t), patch.object(batches, 'Proposal') as proposal:
                with self.assertRaisesRegex(ValueError, 'outside the selected'):
                    batches.prepare(public, base/'private', run, base/'new-proposal', models=[GONE[0]])
            proposal.assert_not_called()
            self.assertFalse((base/'new-proposal').exists())

    def test_adoption_write_boundary_preserves_current_withdrawal(self):
        _, _, t = fixture()
        with tempfile.TemporaryDirectory() as temp:
            base=Path(temp); public=base/'public'; public.mkdir(); proposal=base/'proposal'; proposal.mkdir()
            raw=b'{"version":"1.2.0"}\n'; (public/'benchmark.json').write_bytes(raw)
            report=dict(schema='math-gauge.neutral-revision-batch-proposal/v1', candidate_calls=0,
                prepared_only=True, benchmark_before_sha256=hashlib.sha256(raw).hexdigest(),
                resources_index_before_sha256=None, new_models=[GONE[0]],
                review_selection={'path':'unused'}, protected_originals=[])
            (proposal/'proposal.json').write_text(json.dumps(report))
            path=proposal/'public'/owner.TRANSITION_PATH; path.parent.mkdir(parents=True)
            path.write_text(json.dumps(t))
            with patch.object(batches, 'external_bytes'), patch.object(batches, 'load_transition', return_value=t):
                with self.assertRaisesRegex(ValueError, 'preserve the explicitly selected'):
                    batches.adopt(public, base/'private', proposal)
            self.assertEqual((public/'benchmark.json').read_bytes(),raw)

    def test_staged_transition_can_authenticate_its_unchanged_source_before_writes(self):
        e,s,t=fixture()
        with tempfile.TemporaryDirectory() as temp:
            base=Path(temp);public=base/'public';private=base/'private'
            source=public/owner.SOURCE_EDITION_PATH;source.parent.mkdir(parents=True)
            source.write_text(json.dumps(s))
            t['source_edition']=owner.descriptor(public,source)
            proposal=batches.Proposal(public,private)
            proposal.bind('public',t['source_edition'])
            ref=proposal.add('public',owner.TRANSITION_PATH,t)
            e['neutral_revision_transition']=ref
            proposal.add('public','benchmark.json',e)
            proposal.materialize(base/'staged')
            with patch.object(owner,'load_policy'):
                loaded=owner.load_transition(base/'staged/public')
            self.assertEqual(loaded['_source_edition'],s)
            self.assertEqual(loaded['withdrawn_models'],GONE)
            self.assertEqual(source.read_text(),json.dumps(s))


class EditionProjectionTests(unittest.TestCase):
    def base(self):
        _, source, transition=fixture()
        ids=source['selected_result_models']+list(source['current_assessment_admissions'])+[NATIVE_MODEL]
        models=[dict(id=mid,label=mid,logo={},display_order=i,presentation_eligibility={'ranked':mid not in {'kept-partial',GONE[1]}},
                     ranking_values={},answer_delivery={},combined={},retry={'combined':{}},
                     capability={'single_attempt':{},'nonlogical_retry_3':{}},
                     strict={'single_attempt':{},'nonlogical_retry_3':{}}) for i,mid in enumerate(ids)]
        return dict(schema='fixture',benchmark_version='1.1.0',models=models,
            score_modes=['partial','capability','strict'],sources=[],policy={'groups':[]},
            mathematical_profile={'models':[{'id':mid} for mid in ids]}), transition

    def test_current_lists_and_all_profile_companions_filter_only_membership(self):
        base, t=self.base(); original=deepcopy(base)
        with tempfile.TemporaryDirectory() as temp, ExitStack() as stack:
            root=Path(temp)
            resource=root/'results/continuation-resources/v0.1.0/current.json'
            resource.parent.mkdir(parents=True); resource.write_text('{}')
            stack.enter_context(patch('scripts.results_revision_resources.load_public', return_value={'models':[]}))
            stack.enter_context(patch('scripts.results_revision_completion.load_completion', return_value=None))
            stack.enter_context(patch('scripts.render_results_site.gap_diagnostics', return_value={}))
            stack.enter_context(patch('scripts.render_results_site.selected_result', return_value={'metrics':{'earned':{'confirmed':0}}}))
            stack.enter_context(patch('scripts.results_rankings.category_rankings', return_value=[]))
            stack.enter_context(patch('scripts.results_rankings.model_display_key', side_effect=lambda row:row['id']))
            stack.enter_context(patch.object(display, 'eligibility', side_effect=lambda mid:{'ranked':mid not in {'kept-partial',GONE[1]}}))
            stack.enter_context(patch('math_gauge.mathematical_profile_corrections.apply_public', side_effect=lambda root,p:deepcopy(p)))
            stack.enter_context(patch('math_gauge.mathematical_profile_revision.load_public_profiles', return_value={'models':[]}))
            stack.enter_context(patch('math_gauge.open_research.load_public', return_value={'models':deepcopy(base['mathematical_profile']['models']),'source':reference('fixture')}))
            current=display.neutral_revision_data(root,base,transition=t)
        selected=owner.current_model_ids(t)
        for key in ('models','pending_models','partial_models','profile_models'):
            self.assertFalse(set(GONE)&{row['id'] for row in current[key]})
        for key in ('mathematical_profile','mathematical_profile_baseline','mathematical_profile_revision','open_research'):
            self.assertFalse(set(GONE)&{row['id'] for row in current[key]['models']})
        self.assertEqual({row['id'] for row in current['profile_models']},selected)
        self.assertEqual({row['id'] for row in current['partial_models']},{'kept-partial'})
        self.assertTrue(all(value==0 for value in current['partial_models'][0]['score_values'].values()))
        self.assertEqual(base,original,'Current projection cannot mutate the historical source')
        for mid in GONE:
            unavailable=display._neutral_payload('models/'+mid+'/index.html',{'model':{'id':mid}},current,{})
            self.assertEqual(unavailable['edition_unavailable_reason'],'not_selected_for_edition')
            self.assertEqual(unavailable['edition_fallback'],'1.1.0')

    def test_historical_display_path_is_unchanged(self):
        base,_=self.base()
        with patch.object(owner, 'load_transition', return_value=None):
            projected=display.neutral_revision_data('/unused',base)
        self.assertEqual(projected,base)
        self.assertTrue(set(GONE)<={row['id'] for row in projected['models']})

    def test_bare_historical_model_and_case_links_default_to_available_source(self):
        base,_=self.base()
        current=dict(benchmark_version='1.2.0',models=[],pending_models=[{'id':'kept'}],
                     partial_models=[],score_modes=base['score_modes'])
        pages={'index.html':{'models':base['models']},'models/kept/index.html':{'model':{'id':'kept'}}}
        for mid in GONE:
            pages['models/'+mid+'/index.html']={'model':{'id':mid},'retained_marker':mid}
            pages['models/'+mid+'/cases/fixture.html']={'model':{'id':mid},'case':{'id':'fixture'}}
        prepared={'assets/versioned/edition-notes.fixture.js':'',
                  'editions.json':json.dumps({'latest':'1.1.0','editions':[{'version':'1.1.0'},{'version':'1.0.0'}]})}
        for page,payload in pages.items():
            entry=dict(key='a'*64,payload='prior.js',label={'zh':'1.1.0','en':'1.1.0'},status={'zh':'','en':''})
            config=dict(schema='math-gauge.edition-view-config/v1',latest='1.1.0',page=page,
                        versions={'1.1.0':entry,'1.0.0':dict(entry,key='b'*64)},scripts=['core.js'])
            prepared[page]='<html><head><script type="application/json" id="edition-config">'+json.dumps(config)+'</script></head><main></main></html>'
            prepared['data/editions/1.1.0/'+page.removesuffix('.html')+'.json']=json.dumps(dict(
                schema='math-gauge.edition-page-data/v1',edition='1.1.0',page=page,data=payload,supplemental={}))
        with tempfile.TemporaryDirectory() as temp, ExitStack() as stack:
            root=Path(temp);(root/'benchmark.json').write_text(json.dumps({'neutral_revision_transition':reference(owner.TRANSITION_PATH)}))
            stack.enter_context(patch.object(display,'prepare_edition_publication',return_value=deepcopy(prepared)))
            stack.enter_context(patch.object(display,'display_harness_labels',side_effect=deepcopy))
            stack.enter_context(patch.object(display,'project_payload',side_effect=deepcopy))
            stack.enter_context(patch.object(display,'chart_scenes',return_value={}))
            stack.enter_context(patch.object(display,'_neutral_evidence_sections',return_value={}))
            stack.enter_context(patch('scripts.results_revision_resources.load_public',return_value={'models':[]}))
            result=display.prepare_neutral_publication({},root,current,base_data=base,base_timing={},
                base_cost={},current_timing={},current_cost={})
        for page in pages:
            self.assertIn(page,result,'Historical page routes cannot be deleted')
            match=__import__('re').search(r'id="edition-config">([\s\S]*?)</script>',result[page])
            config=json.loads(match[1])
            is_withdrawn=any('/'+mid+'/' in page for mid in GONE)
            self.assertEqual(config['latest'],'1.1.0' if is_withdrawn else '1.2.0')
            self.assertIn('1.0.0',config['versions'])
            self.assertIn('1.1.0',config['versions'])
            explicit=json.loads(result['data/editions/1.2.0/'+page.removesuffix('.html')+'.json'])['data']
            retained=json.loads(result['data/editions/1.1.0/'+page.removesuffix('.html')+'.json'])['data']
            if is_withdrawn:
                self.assertTrue(explicit['edition_unavailable'])
                self.assertEqual(explicit['edition_unavailable_reason'],'not_selected_for_edition')
                self.assertEqual(explicit['edition_fallback'],'1.1.0')
                self.assertEqual(retained['model'],pages[page]['model'])


if __name__=='__main__':
    unittest.main()
