"""Initial current assessment never manufactures a historical score or new math."""
from contextlib import ExitStack
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from math_gauge import current_assessment_admissions as admissions
from math_gauge.current_results import apply_current_assessment, selected_current_record_paths
from scripts.results_editions import prior_payload


class InitialAdmissionTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name).resolve()
        self.mid = 'new-model'
        self.folder = Path('results/v1.0.0/new-model/run')
        self.policy = {'standards':{'sha256':'1'*64}, 'private_standards':{'sha256':'2'*64}}
        self.policy_ref = self.write('protocol/theorem-extension-calibration.json', self.policy)
        self.scores = {m:{c:{'benchmark_version':'0.6.0','metrics':{'overall':{'exact':12}},
                            'mode':m,'condition':c,'source_bindings':{'retained':'unchanged'}}
                          for c in admissions.CONDITIONS} for m in admissions.MODES}
        self.record = {'model_id':self.mid,'record_id':'run','benchmark_version':'1.0.0','initial_assessment_edition':'1.1.0'}
        refs = {}
        for mode in admissions.MODES:
            refs[mode] = {c:self.write(self.folder / (mode+'-'+c+'.json'), v)
                          for c,v in self.scores[mode].items()}
            self.record[admissions.SCORE_FIELDS[mode]] = {c:self.local(ref) for c,ref in refs[mode].items()}
        public_tasks = self.write(self.folder/'public-task-scores.json', {'fixture':'validated separately'})
        self.record['evidence'] = [self.local(public_tasks)]
        tx_rows, wrappers = [], []
        for cid in admissions.PUBLIC_CASES:
            answer = self.write(self.folder/(cid+'.md'), b'original mathematical answer', raw=True)
            source = self.write(self.folder/(cid+'-review.json'),
                {'stage':'A1','B':2,'R':1,'answer_sha256':answer['sha256']})
            wrapper = self.write('results/current-assessment-admissions/v1.1.0/'+cid+'.json',
                {'initial_assessment_edition':'1.1.0','policy_sha256':self.policy_ref['sha256'],
                 'standard_sha256':'1'*64,'source_review':source,'baseline_B':2,'research_R':1,
                 'response_sha256':answer['sha256'],'new_candidate_calls':0,'metadata_projection_only':True})
            tx_rows.append(dict(case_id=cid,baseline_B=2,research_R=1,response=self.local(answer),review=self.local(source)))
            wrappers.append({'case_id':cid,'review':wrapper})
        tx = self.write(self.folder/'tx-evidence.json', {'records':tx_rows})
        self.record['theorem_extension_evidence'] = self.local(tx)
        freeze = self.write(self.folder/'freeze.json', {'initial_assessment_edition':'1.1.0',
            'initial_assessment_policy_sha256':self.policy_ref['sha256']})
        first = self.write(self.folder/'first.json', {'initial_assessment_edition':'1.1.0','source_freeze':self.local(freeze)})
        self.record['first_assessment_source'] = self.local(first)
        self.manifest = dict(schema='math-gauge.current-assessment-admission/v1',version='0.1.0',
            assessment_kind='initial',benchmark_version='1.1.0',source_task_version='1.0.0',model_id=self.mid,
            record=self.write(self.folder/'record.json',self.record),policy=self.policy_ref,scores=refs,
            public_tasks=public_tasks,public_reviews={c:wrappers for c in admissions.CONDITIONS},
            private_manifest_sha256='3'*64,private_inputs_sha256='4'*64,
            reviewer_kind='ai',human_review='pending',formal_comparison_eligible=False)
        self.publish()
        stack = self.enterContext(ExitStack())
        stack.enter_context(patch('math_gauge.editions.source_edition',return_value={'selected_result_models':['legacy']}))
        stack.enter_context(patch('math_gauge.editions.load_assessment_transition',return_value={'policy':self.policy_ref}))
        stack.enter_context(patch.object(admissions,'load_policy',return_value=self.policy))
        self.validator = stack.enter_context(patch('math_gauge.records.validate_record'))
        stack.enter_context(patch('math_gauge.records.load_assessment_results',side_effect=lambda root,record,mode:self.scores[mode]))

    def write(self,path,value,raw=False):
        data=value if raw else json.dumps(value,sort_keys=True).encode()
        target=self.root/path;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
        return dict(path=str(path),bytes=len(data),sha256=hashlib.sha256(data).hexdigest())

    def local(self,ref):
        return dict(ref,path=str(Path(ref['path']).relative_to(self.folder)))

    def publish(self):
        ref=self.write(admissions.DIRECTORY+self.mid+'.json',self.manifest)
        self.write('benchmark.json',{'version':'1.1.0',admissions.FIELD:{self.mid:ref}})

    def test_initial_projection_changes_only_metadata_and_keeps_existing_validator(self):
        original=deepcopy(self.scores)
        result=admissions.load(self.root,self.mid)
        self.assertEqual(self.scores,original)
        self.validator.assert_called_once_with(self.root/self.folder)
        for mode in admissions.MODES:
            for condition in admissions.CONDITIONS:
                view=result['_scores'][mode][condition]
                self.assertEqual(view,admissions.project_score(original[mode][condition]))
                self.assertEqual(view['benchmark_version'],'1.1.0')
        self.assertNotIn('old_R',result)

    def test_no_overlay_is_called_for_initial_assessment(self):
        with patch('math_gauge.current_results.load_public',side_effect=AssertionError('old R overlay')):
            views,manifest=apply_current_assessment(self.root,self.mid,self.record,self.scores)
        self.assertEqual(manifest['assessment_kind'],'initial')
        self.assertEqual(views['partial']['single_attempt']['metrics'],self.scores['partial']['single_attempt']['metrics'])

    def test_portable_first_review_uses_verified_returned_source_without_a_git_freeze(self):
        from math_gauge.portable_assessment_sources import PUBLIC_SCHEMA
        current = json.loads((Path(__file__).resolve().parents[1] / 'protocol/scoring-policy.json').read_bytes())
        original = dict(current, version='0.8.0', capability_policy_version='0.2.0')
        original.pop('submission_policy_version')
        old_policy = self.write(self.folder/'original-policy.json', original)
        current_policy = self.write(self.folder/'assessment-policy.json', current)
        proof = self.write(self.folder/'portable-first.json', dict(schema=PUBLIC_SCHEMA, version='0.1.0',
            model_id=self.mid, source_benchmark_version='1.0.0', assessment_method_version='0.9.0',
            post_observation=True, new_candidate_calls=0, private_source_proof_sha256='a'*64,
            original_assessment_policy=self.local(old_policy)))
        self.record.update(first_assessment_source=self.local(proof),
            first_assessment_source_private_sha256='a'*64, assessment_policy=self.local(current_policy),
            retention=dict(user_requested=True), scope='public-answers-and-combined-aggregates')
        self.manifest['record'] = self.write(self.folder/'record.json', self.record)
        self.publish()
        result = admissions.load(self.root, self.mid)
        self.assertEqual(result['_scores']['partial']['single_attempt']['metrics'],
                         self.scores['partial']['single_attempt']['metrics'])
        self.assertNotIn('source_freeze', json.loads((self.root/proof['path']).read_bytes()))
        self.record['first_assessment_source_private_sha256'] = 'b'*64
        self.manifest['record'] = self.write(self.folder/'record.json', self.record)
        self.publish()
        with self.assertRaisesRegex(ValueError, 'opaque projection'):
            admissions.load(self.root, self.mid)

    def test_wrong_tier_wrong_standard_and_reassessment_fields_are_rejected(self):
        ref=self.manifest['public_reviews']['single_attempt'][0]['review']
        original=json.loads((self.root/ref['path']).read_bytes())
        for change in ({'research_R':3},{'standard_sha256':'f'*64},{'old_R':0},{'metadata_projection_only':False}):
            with self.subTest(change=change):
                bad=self.write(ref['path'],dict(original,**change))
                for condition in admissions.CONDITIONS:
                    self.manifest['public_reviews'][condition][0]['review']=bad
                self.publish()
                with self.assertRaises(ValueError):admissions.load(self.root,self.mid)

    def test_missing_mode_unresolved_or_arithmetic_changed_cannot_be_admitted(self):
        saved=deepcopy(self.manifest)
        del self.manifest['scores']['strict'];self.publish()
        with self.assertRaises(ValueError):admissions.load(self.root,self.mid)
        self.manifest=deepcopy(saved)
        original=self.scores['partial']['single_attempt']
        for exact in (None,99):
            altered=deepcopy(original);altered['metrics']['overall']['exact']=exact
            self.manifest['scores']['partial']['single_attempt']=self.write('projection.json',altered)
            self.publish()
            with self.assertRaises(ValueError):admissions.load(self.root,self.mid)

    def test_current_selection_is_disjoint_and_source_selection_is_unchanged(self):
        with patch('math_gauge.current_results.selected_source_record_paths',return_value={'legacy':'old/record.json'}):
            current=selected_current_record_paths(self.root)
        self.assertEqual(current,{'legacy':'old/record.json',self.mid:str(self.folder/'record.json')})
        edition=json.loads((self.root/'benchmark.json').read_bytes())
        with self.assertRaises(ValueError):admissions.configured(self.root,edition,{'selected_result_models':[self.mid]})
        edition['version']='1.0.0'
        with self.assertRaises(ValueError):admissions.configured(self.root,edition,{'selected_result_models':[]})

    def test_old_standard_cannot_be_relabelled_as_initial_by_wrapper_alone(self):
        first=json.loads((self.root/self.folder/'first.json').read_bytes())
        freeze=self.write(self.folder/'freeze.json',{'initial_assessment_edition':'1.0.0',
            'initial_assessment_policy_sha256':'f'*64})
        first['source_freeze']=self.local(freeze)
        self.record['first_assessment_source']=self.local(self.write(self.folder/'first.json',first))
        self.manifest['record']=self.write(self.folder/'record.json',self.record)
        self.publish()
        with self.assertRaisesRegex(ValueError,'source freeze'):
            admissions.load(self.root,self.mid)

    def test_new_model_historical_payload_contains_no_scores_or_answers(self):
        payload=prior_payload('models/new/index.html',{'model':{'id':self.mid},'cases':[{'secret':'answer'}]},
                              {'benchmark_version':'1.0.0'}, {})
        self.assertEqual(payload,{'benchmark_version':'1.0.0','edition_unavailable':True,'model_id':self.mid})

    def test_historical_snapshot_is_unchanged_and_a_score_change_is_rejected(self):
        from scripts.results_editions import retained_source_data
        old_record='results/v0.6.0/legacy/run/record.json'
        old_model={'id':'legacy','source_record':old_record,
            'combined':self.scores['partial']['single_attempt'],
            'retry':{'combined':self.scores['partial']['nonlogical_retry_3']},
            'capability':self.scores['capability'],'strict':self.scores['strict']}
        snapshot={'benchmark_version':'1.0.0','models':[old_model],
                  'sources':[{'path':'historical-index.json','sha256':'a'*64}]}
        self.manifest['historical_display_source']=self.write('historical-display.json',snapshot)
        self.publish()
        manifests={'legacy':{'base_reports':self.manifest['scores']}}
        with patch('math_gauge.current_results.selected_source_record_paths',return_value={'legacy':old_record}):
            result=retained_source_data(self.root,{'models':[{'id':self.mid}], 'sources':[]},{},manifests)
            self.assertEqual(result,snapshot)
            changed=deepcopy(snapshot);changed['models'][0]['combined']['metrics']['overall']['exact']=91
            self.manifest['historical_display_source']=self.write('historical-display.json',changed)
            self.publish()
            with self.assertRaisesRegex(ValueError,'original shared-scoring'):
                retained_source_data(self.root,{}, {},manifests)

    def test_historical_cost_source_rejects_extra_current_model(self):
        costs={'models':[{'model_id':'legacy'},{'model_id':self.mid}]}
        self.manifest['historical_cost_source']=self.write('historical-costs.json',costs)
        self.publish()
        with patch('math_gauge.current_results.selected_source_record_paths',return_value={'legacy':'old/record.json'}):
            with self.assertRaisesRegex(ValueError,'sealed source cohort'):
                admissions.historical_cost_source(self.root)
            costs['models'].pop()
            self.manifest['historical_cost_source']=self.write('historical-costs.json',costs)
            self.publish()
            self.assertEqual(admissions.historical_cost_source(self.root),costs)

    def test_metadata_projection_is_allowed_but_source_record_stays_canonical(self):
        before=(self.root/self.manifest['record']['path']).read_bytes()
        score=self.scores['partial']['single_attempt']
        self.manifest['scores']['partial']['single_attempt']=self.write('projection.json',admissions.project_score(score))
        self.publish();admissions.load(self.root,self.mid)
        self.assertEqual((self.root/self.manifest['record']['path']).read_bytes(),before)


class HistoricalCompanionTests(unittest.TestCase):
    def test_new_admission_without_optional_history_cannot_replace_existing_history(self):
        source = {'benchmark_version':'1.0.0', 'models':[{'id':'legacy',
            'model_id':'legacy','source_record':'old/record.json'}]}
        for key, load in [('historical_display_source', admissions.historical_display_source),
                          ('historical_cost_source', admissions.historical_cost_source)]:
            with self.subTest(companion=key):
                documents = {'existing':{key:'retained'}, 'new':{}, 'retained':source,
                             'other':deepcopy(source)}
                with patch.object(admissions, 'selections', return_value={'existing':'existing','new':'new'}), \
                     patch.object(admissions, 'document', side_effect=lambda root, ref:documents[ref]), \
                     patch('math_gauge.current_results.selected_source_record_paths',
                           return_value={'legacy':'old/record.json'}):
                    self.assertEqual(load(None), source)
                    documents['new'][key] = 'other'
                    with self.assertRaisesRegex(ValueError, 'unchanged historical'):
                        load(None)
                    documents['new'].clear();documents['existing'].clear()
                    with self.assertRaisesRegex(ValueError, 'unchanged historical'):
                        load(None)

    def test_history_replaces_timing_population_and_inputs_as_well_as_costs(self):
        from scripts.results_editions import edition_supplemental
        old_time={'models':[{'id':'legacy'}], 'score_inputs':[{'path':'legacy.json'}]}
        new_time={'models':[{'id':'legacy'},{'id':'new'}],
                  'link_prefix':'', 'data_link':'downloads/timing-reference.json',
                  'score_inputs':[{'path':'legacy.json'},{'path':'new.json'}]}
        source={'timing-reference-data':new_time,'cost-reference-data':{'models':['legacy','new']}}
        original=deepcopy(source)
        result=edition_supplemental(source,historical=True,unavailable=False,timing=old_time,cost={'models':['legacy']})
        self.assertEqual(result['timing-reference-data'],dict(old_time,
            link_prefix='',data_link='downloads/timing-reference.json'))
        self.assertEqual(result['cost-reference-data'],{'models':['legacy']})
        self.assertEqual(source,original)
        self.assertEqual(edition_supplemental(source,historical=False,unavailable=False,timing=old_time,cost=None),source)
        self.assertEqual(edition_supplemental(source,historical=True,unavailable=True,timing=old_time,cost=None),{})


class BackgroundDetailLayoutTests(unittest.TestCase):
    def test_fixed_legacy_and_stem_layouts_bind_exact_bytes(self):
        from scripts.results_details import background_source_review
        for relative in ('research-reviews/source-review.json',
                         'research-reviews/MG-BC001/source-review.json'):
            with self.subTest(relative=relative), tempfile.TemporaryDirectory() as temp:
                root=Path(temp);path=root/relative;path.parent.mkdir(parents=True);path.write_bytes(b'original detailed review')
                digest=hashlib.sha256(path.read_bytes()).hexdigest()
                actual,raw=background_source_review(root,'research-reviews/MG-BC001.json',digest)
                self.assertEqual(actual,path);self.assertEqual(raw,b'original detailed review')

    def test_missing_or_damaged_legacy_cannot_scan_or_fall_back(self):
        from scripts.results_details import background_source_review
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);other=root/'unrelated/source-review.json';other.parent.mkdir();other.write_bytes(b'valid')
            digest=hashlib.sha256(b'valid').hexdigest()
            with self.assertRaisesRegex(ValueError,'Missing retained'):
                background_source_review(root,'research-reviews/MG-BC001.json',digest)
            stem=root/'research-reviews/MG-BC001/source-review.json';stem.parent.mkdir(parents=True);stem.write_bytes(b'valid')
            legacy=root/'research-reviews/source-review.json';legacy.write_bytes(b'damaged')
            with self.assertRaisesRegex(ValueError,'does not match'):
                background_source_review(root,'research-reviews/MG-BC001.json',digest)


if __name__ == '__main__':
    unittest.main()
