"""Independent corrected traits are stage-aware and do not rewrite old profiles."""
from copy import deepcopy
import json
from pathlib import Path
import unittest

from math_gauge.mathematical_profile_review_amendments import apply_public,INDEX_PATH,MODEL
from math_gauge.neutral_revision import document

ROOT=Path(__file__).resolve().parents[1]


class ProfileReviewAmendmentTests(unittest.TestCase):
    def setUp(self):
        self.index=json.loads((ROOT/INDEX_PATH).read_bytes())
        first=document(ROOT,self.index['source_first_profile'])
        revised=document(ROOT,self.index['source_revision_profile'])
        self.first=deepcopy(first['metrics']);self.revised=deepcopy(revised['metrics'])
        def profile(metrics):
            return dict(models=[dict(id=MODEL,metrics=deepcopy(metrics)),
                                dict(id='other',metrics=deepcopy(metrics))])
        self.data=dict(benchmark_version='1.2.0',sources=[],
            mathematical_profile=profile(self.first),mathematical_profile_baseline=profile(self.first),
            mathematical_profile_revision=profile(self.revised))

    def test_only_accepted_axes_change_and_each_stage_uses_its_own_source(self):
        original=deepcopy(self.data)
        apply_public(ROOT,self.data)
        for key,stage in [('mathematical_profile','first'),('mathematical_profile_baseline','first'),
                          ('mathematical_profile_revision','revision')]:
            row=self.data[key]['models'][0]
            for axis,metric in row['metrics'].items():
                self.assertEqual(metric,self.index['metrics'][stage][axis] if axis in {'depth','initiative'}
                                 else original[key]['models'][0]['metrics'][axis])
            self.assertEqual(self.data[key]['models'][1],original[key]['models'][1])

    def test_initiative_is_unblended_and_depth_retains_eighty_percent_parent_increment(self):
        new=self.index['metrics']
        self.assertEqual(new['first']['initiative'],new['revision']['initiative'])
        first_delta=new['first']['depth']['confirmed']-self.first['depth']['confirmed']
        revision_delta=new['revision']['depth']['confirmed']-self.revised['depth']['confirmed']
        self.assertGreater(first_delta,0)
        self.assertAlmostEqual(revision_delta,.8*first_delta)
        self.assertGreater(new['first']['initiative']['confirmed'],self.first['initiative']['confirmed'])

    def test_historical_profile_and_source_artifacts_remain_unchanged(self):
        self.data['benchmark_version']='1.1.0';before=deepcopy(self.data)
        apply_public(ROOT,self.data)
        self.assertEqual(self.data,before)
        for key in ('source_first_profile','source_revision_profile'):
            document(ROOT,self.index[key])


if __name__=='__main__':unittest.main()
