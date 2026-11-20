"""Common research opportunities, noncompensating gates and source privacy."""
from copy import deepcopy
import unittest

from math_gauge.open_research import (
    ResearchInputs, FACETS, BOUNDARIES, validate_judgment, validate_public,
    pending_metric, project_public,
)
from math_gauge.scoring import score_open_research


def inputs(grades, *, revisions=None, available=True):
    value=object.__new__(ResearchInputs)
    value.policy={'original_weight':'4/5','revision_weight':'1/5'}
    value.contracts={'families':[{'case_id':str(i),'family_id':str(i),'weight':'1/5'} for i in range(5)]}
    revisions=revisions or {}
    value.materials={'revision':[{'case_id':str(i)} for i in revisions],
                     'revision_available':available}
    value.review={'model_id':'candidate','tasks':[
        {'stage':'first','case_id':str(i),'grade':grade} for i,grade in enumerate(grades)]+[
        {'stage':'revision','case_id':str(i),'grade':grade} for i,grade in revisions.items()]}
    return value


def judgment(grade=4):
    return {'model_id':'candidate','stage':'first','case_id':'case','grade':grade,
        'assessment_status':'reviewed','core_status':'established','core_scope_failure':False,
        'facets':{key:{'status':'established','reason':'The requested mechanism and its scope are proved.'}
                  for key in FACETS},
        'reason':'The explicitly requested open development is independently established.',
        'evidence':[{'source_id':'answer:case:A1','pointer':'','quote':'actual proof'}],
        'limitations':[], 'optional_errors_disposition':'No optional assertion is used as a required premise.'}


def material():
    return {'classification':'active_final','content_index':3,'goal_index':2,'report_index':4,
        'sources':{'answer:case:A1':{'repository':'private','path':'original.md','sha256':'a'*64},
                   'content_review':{'repository':'private','path':'review.json','sha256':'b'*64}}}


class ResearchScoringTests(unittest.TestCase):
    def test_fixed_five_family_denominator(self):
        score=score_open_research(inputs([4,4,4,2,0]))
        self.assertEqual(score['first']['exact'],70)
        self.assertEqual(score['first']['coverage'],
                         {'unit':'open_research_family','planned':5,'reviewed':5})

    def test_unknown_family_is_not_rescaled_or_called_a_failure(self):
        score=score_open_research(inputs([4,4,4,4,None]))['first']
        self.assertIsNone(score['exact'])
        self.assertEqual((score['confirmed'],score['lower'],score['upper']),(80,80,100))
        self.assertEqual(score['coverage']['reviewed'],4)

    def test_adopted_continuation_decrease_counts(self):
        result=score_open_research(inputs([4]*5,revisions={0:0}))
        self.assertEqual(result['first']['exact'],100)
        self.assertEqual(result['revision']['exact'],96)
        self.assertEqual(result['tasks'][0]['revision']['exact'],3.2)

    def test_unknown_selected_revision_cannot_inherit_the_first_grade(self):
        result=score_open_research(inputs([4]*5,revisions={0:None}))['revision']
        self.assertIsNone(result['exact'])
        self.assertEqual((result['lower'],result['upper']),(96,100))
        self.assertEqual(result['coverage']['reviewed'],4)

    def test_pending_configuration_has_no_revised_value(self):
        self.assertIsNone(score_open_research(inputs([4]*5,available=False))['revision'])

    def test_exempt_families_keep_their_actual_nonfull_capacity(self):
        result=score_open_research(inputs([2,4,4,4,4]))
        self.assertEqual(result['revision'],result['first'])
        self.assertEqual(result['first']['exact'],90)


class ResearchEvidenceTests(unittest.TestCase):
    def check(self,row,source=None):
        return validate_judgment(row,source or material(),stage='first',
            read_source=lambda ref:b'actual proof and exact scope')

    def test_complete_requested_research_does_not_need_extra_theory(self):
        self.assertEqual(self.check(judgment())['grade'],4)

    def test_essential_core_failure_cannot_be_compensated_by_other_facets(self):
        for state in ('refuted_core','unresolved_core'):
            row=judgment(3);row['core_status']=state
            with self.assertRaises(ValueError):self.check(row)
            row['grade']=2
            self.check(row)

    def test_unbridged_core_scope_drift_caps_high_grades(self):
        row=judgment();row['core_scope_failure']=True
        with self.assertRaises(ValueError):self.check(row)

    def test_grade_four_requires_all_four_requested_facets(self):
        row=judgment();row['facets']['closure']['status']='local_gap'
        with self.assertRaises(ValueError):self.check(row)
        row['grade']=3;row['core_status']='local_gap';self.check(row)
        row['facets']['closure']['status']='unresolved_core'
        with self.assertRaises(ValueError):self.check(row)

    def test_quotes_cannot_be_invented_or_taken_from_another_task(self):
        row=judgment();row['evidence'][0]['quote']='invented theorem'
        with self.assertRaises(ValueError):self.check(row)
        row=judgment();row['evidence']=[{'source_id':'content_review','pointer':'/tasks/1/reason','quote':'actual proof'}]
        with self.assertRaises(ValueError):self.check(row)

    def test_positive_grade_needs_actual_original_mathematics(self):
        row=judgment();row['evidence']=[{'source_id':'content_review','pointer':'/tasks/3/reason','quote':'actual proof'}]
        def read(ref):return b'{"tasks":[{},{},{},{"reason":"actual proof"}]}'
        with self.assertRaises(ValueError):validate_judgment(row,material(),stage='first',read_source=read)

    def test_settled_blank_cannot_be_filled_with_an_invented_proof(self):
        source=material();source['classification']='blank'
        with self.assertRaises(ValueError):self.check(judgment(),source)

    def test_source_missing_grade_is_explicitly_unknown(self):
        row=judgment(None);row.update(assessment_status='source_unresolved',
            core_status='source_unresolved',core_scope_failure=None,missing_evidence='Original source is unavailable.')
        for facet in row['facets'].values():facet['status']='source_unresolved'
        self.check(row)

    def test_adopted_cutoff_mathematics_can_show_capability_without_becoming_a_normal_final(self):
        row=judgment();row['stage']='revision'
        row['evidence']=[{'source_id':'cutoff_content','pointer':'','quote':'actual proof'}]
        source={'status':'delivery_failed','sources':{'cutoff_content':
            {'repository':'private','path':'original-cutoff.md','sha256':'d'*64}}}
        validate_judgment(row,source,stage='revision',read_source=lambda ref:b'actual proof')
        self.assertEqual(source['status'],'delivery_failed')
        self.assertNotIn('normal_final',row)


class ResearchProjectionTests(unittest.TestCase):
    def report(self):
        score=score_open_research(inputs([4]*5))
        return project_public(score,policy={},policy_sha256='a'*64,
                              review_sha256='b'*64,materials_sha256='c'*64)

    def test_public_projection_has_no_case_inventory_or_private_reasons(self):
        report=self.report()
        for key in ('case_id','tasks','facets','reason','evidence','private_path'):
            self.assertNotIn(key,report)
            unsafe=deepcopy(report);unsafe[key]='private'
            with self.assertRaises(ValueError):validate_public(unsafe,{},'a'*64)

    def test_pending_axis_is_an_unknown_common_opportunity_interval(self):
        metric=pending_metric()
        self.assertIsNone(metric['exact'])
        self.assertEqual((metric['lower'],metric['upper']),(0,100))
        self.assertEqual(metric['coverage']['planned'],5)

    def test_wrong_coverage_unit_or_unknown_zero_is_rejected(self):
        report=self.report();report['first']['coverage']['planned']=35
        with self.assertRaises(ValueError):validate_public(report,{},'a'*64)
        report=self.report();report['first']=pending_metric();report['first']['exact']=0
        with self.assertRaises(ValueError):validate_public(report,{},'a'*64)


if __name__=='__main__':
    unittest.main()
