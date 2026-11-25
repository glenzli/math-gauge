"""Additive native-profile source, privacy and gate tests; no candidate calls."""
from copy import deepcopy
from pathlib import Path
import json
import tempfile
import unittest
from unittest.mock import patch

from math_gauge import dot_native_profiles as owner


class DotNativeProfileTests(unittest.TestCase):
    def test_shared_review_is_scoped_to_exact_named_case(self):
        raw = json.dumps({'cases':[{'case_id':'MG-X','reason':'first'},
                                  {'case_id':'MG-Y','reason':'second'}]}).encode()
        self.assertEqual(owner._review_scopes(raw, 'MG-X'), ['/cases/0'])
        self.assertEqual(owner._review_scopes(raw, 'MG-Z'), [])

    def test_root_case_review_preserves_its_own_descendants(self):
        raw = json.dumps({'case_id':'MG-X','criteria':[{'reason':'own fact'}]}).encode()
        self.assertEqual(owner._review_scopes(raw, 'MG-X'), [''])

    def test_source_mapping_never_relabels_a_cli_record(self):
        ref = dict(path='candidate/X/answer.md', bytes=17, sha256='a'*64)
        bound = owner._source(ref)
        self.assertEqual(bound['path'], owner.SOURCE+'/candidate/X/answer.md')
        self.assertEqual(bound['repository'], 'private')
        self.assertEqual(bound['sha256'], ref['sha256'])

    def _quote_fixture(self, root):
        raw = json.dumps({'cases':[{'case_id':'MG-X','reason':'正确甲'},
                                  {'case_id':'MG-Y','reason':'正确乙'}]},ensure_ascii=False).encode()
        (root/'review.json').write_bytes(raw)
        source = owner.reference('review.json',raw,'private')
        return {'sources':{'review':source},'evidence_prefixes':{'review':['/cases/0']}}

    def test_exact_utf8_quote_and_case_scope_are_accepted(self):
        with tempfile.TemporaryDirectory() as path:
            root=Path(path);material=self._quote_fixture(root)
            owner._evidence([dict(source_id='review',pointer='/cases/0/reason',quote='正确甲')],
                            material,dict(private=root))

    def test_another_task_in_same_review_file_is_rejected(self):
        with tempfile.TemporaryDirectory() as path:
            root=Path(path);material=self._quote_fixture(root)
            with self.assertRaisesRegex(ValueError,'another mathematical task'):
                owner._evidence([dict(source_id='review',pointer='/cases/1/reason',quote='正确乙')],
                                material,dict(private=root))

    def test_source_changed_after_binding_is_rejected(self):
        with tempfile.TemporaryDirectory() as path:
            root=Path(path);material=self._quote_fixture(root)
            (root/'review.json').write_text('substituted')
            with self.assertRaisesRegex(ValueError,'source bytes changed'):
                owner._evidence([dict(source_id='review',pointer='/cases/0/reason',quote='正确甲')],
                                material,dict(private=root))

    def test_quote_not_in_selected_source_is_rejected(self):
        with tempfile.TemporaryDirectory() as path:
            root=Path(path);material=self._quote_fixture(root)
            with self.assertRaisesRegex(ValueError,'quotation differs'):
                owner._evidence([dict(source_id='review',pointer='/cases/0/reason',quote='invented')],
                                material,dict(private=root))

    def test_append_preserves_incumbents_and_labels_its_own_binding(self):
        original={'models':[{'id':'retained','metrics':{'exact':12.5}}],
                  'source':{'path':'old-index.json','sha256':'b'*64}}
        old=deepcopy(original)
        binding={'path':owner.INDEX_PATH,'sha256':'c'*64}
        owner._append(original,dict(id=owner.MODEL,metric={'exact':0}),binding)
        self.assertEqual(original['models'][0],old['models'][0])
        self.assertEqual(original['source'],old['source'])
        self.assertEqual(original['additions'],[binding])
        with self.assertRaisesRegex(ValueError,'cannot replace'):
            owner._append(original,dict(id=owner.MODEL),binding)

    def test_historical_editions_cannot_activate_the_new_profile(self):
        for edition in ('1.0.0','1.1.0'):
            data=dict(benchmark_version=edition,models=[{'id':'retained'}])
            before=deepcopy(data)
            with patch.object(owner,'load_public',side_effect=AssertionError('must not load')):
                owner.append_edition_120('.',data)
                owner.append_edition_130('.',data)
            self.assertEqual(data,before)

    def test_subclasses_keep_the_shared_scorer_type_gates(self):
        self.assertTrue(issubclass(owner.DotProfileInputs,owner.base.ProfileInputs))
        self.assertTrue(issubclass(owner.DotRevisionProfileInputs,owner.revision.RevisionProfileInputs))
        self.assertTrue(issubclass(owner.DotOpenResearchInputs,owner.research.ResearchInputs))
        self.assertTrue(issubclass(owner.DotStructureInputs,owner.structure.ProfileStructureInputs))



class DotNativeOriginalGateTests(unittest.TestCase):
    def fixture(self, root):
        raw='Actual synthetic test statement, not a model judgment. αβ\n'.encode()
        (root/'answer.md').write_bytes(raw)
        evidence=[dict(source_id='answer',pointer='',quote='αβ')]
        judgment=dict(grade=1,assessment_status='reviewed',reason='Synthetic contract fixture only.',evidence=evidence)
        row=dict(id='synthetic:A1',axes={axis:deepcopy(judgment)for axis in owner.base.BEHAVIOR},
            goals=[dict(id='synthetic-goal',passed=False,assessment_status='reviewed',
                        reason='Synthetic contract fixture only.',evidence=deepcopy(evidence))])
        row['axes']['proof']['core_status']='unresolved_core'
        row['axes']['fidelity']['core_scope_failure']=False
        material=dict(selected_state=dict(submission_assessment=dict(classification='active_final')),
            sources=dict(answer=owner.reference('answer.md',raw,'private')),
            evidence_prefixes=dict(answer=['']),contract=dict(goals=[dict(id='synthetic-goal')]))
        return row,material

    def test_independent_goal_and_all_axis_gate_acceptance(self):
        with tempfile.TemporaryDirectory()as path:
            root=Path(path);row,material=self.fixture(root)
            owner._validate_baseline_row(row,material,dict(private=root))

    def test_missing_original_goal_cannot_disappear(self):
        with tempfile.TemporaryDirectory()as path:
            root=Path(path);row,material=self.fixture(root);row['goals']=[]
            with self.assertRaisesRegex(ValueError,'complete goals'):
                owner._validate_baseline_row(row,material,dict(private=root))

    def test_refuted_required_core_cannot_receive_high_proof_grade(self):
        with tempfile.TemporaryDirectory()as path:
            root=Path(path);row,material=self.fixture(root)
            row['axes']['proof'].update(grade=3,core_status='refuted_core')
            with self.assertRaisesRegex(ValueError,'core cannot receive'):
                owner._validate_baseline_row(row,material,dict(private=root))

    def test_unbridged_scope_cannot_receive_high_fidelity_grade(self):
        with tempfile.TemporaryDirectory()as path:
            root=Path(path);row,material=self.fixture(root)
            row['axes']['fidelity'].update(grade=4,core_scope_failure=True)
            with self.assertRaisesRegex(ValueError,'drift'):
                owner._validate_baseline_row(row,material,dict(private=root))

    def test_unknown_evidence_keeps_its_actual_missing_reason(self):
        with tempfile.TemporaryDirectory()as path:
            root=Path(path);row,material=self.fixture(root)
            row['axes']['closure'].update(grade=None,assessment_status='source_unresolved')
            with self.assertRaisesRegex(ValueError,'unavailable evidence'):
                owner._validate_baseline_row(row,material,dict(private=root))


class DotNativeCurrentPublicationTests(unittest.TestCase):
    def test_current_reconstruction_gets_all_native_axes_without_changing_incumbents(self):
        binding=dict(path=owner.INDEX_PATH,bytes=1,sha256='d'*64)
        report_ref=dict(path=owner.DIRECTORY+'/baseline.json',bytes=1,sha256='e'*64)
        metric=dict(exact=0)
        reports=dict(baseline=dict(metrics={'proof':metric}),
            revision=dict(metrics={'proof':metric},revision_coverage=dict(selected_tasks=6)),
            open=dict(first=metric,revision=metric),formalization=dict(metric=metric),
            structure=dict(first={'depth':metric,'open_research':metric},revision={'depth':metric,'open_research':metric},
                           revision_coverage={},independent_delivery={}),
            initiative=dict(metric=metric,legacy_metric=metric,extension_metric=metric,legacy_weight='27/28',extension_weight='1/28'))
        selected=dict(reports=reports,source=binding,index=dict(profiles=dict(baseline=report_ref,revision=report_ref)))
        fields=('mathematical_profile','mathematical_profile_baseline','mathematical_profile_revision',
                'open_research','formalization_profile','profile_structure','research_initiative')
        data=dict(benchmark_version='1.3.0',models=[dict(id='retained',score=9),dict(id=owner.MODEL,score=7)],
                  profile_models=[dict(id='retained')])
        for field in fields:
            data[field]=dict(models=[dict(id='retained',metric={'exact':12})],source={'path':'unchanged-'+field})
        original=deepcopy(data)
        with patch.object(owner,'load_public',return_value=selected):
            owner.append_edition_130('.',data)
        for field in fields:
            self.assertEqual(data[field]['models'][0],original[field]['models'][0])
            self.assertEqual(data[field]['source'],original[field]['source'])
            self.assertEqual(data[field]['models'][-1]['id'],owner.MODEL)
            self.assertEqual(data[field]['additions'],[binding])
        self.assertEqual(data['models'],original['models'])
        self.assertEqual(data['sources'],[binding])
        self.assertEqual(data['profile_models'][-1]['id'],owner.MODEL)

    def test_no_public_additive_index_means_no_new_profile(self):
        data=dict(benchmark_version='1.2.0',models=[dict(id=owner.MODEL)],sources=[])
        original=deepcopy(data)
        with patch.object(owner,'load_public',return_value=None):owner.append_edition_120('.',data)
        self.assertEqual(data,original)


if __name__=='__main__':unittest.main()
