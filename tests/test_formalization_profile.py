"""Full Lean SMC projection, fixed unknowns and source integrity."""
from copy import deepcopy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from math_gauge.scoring import profile_formalization_metric
from math_gauge.formalization_profile import (
    reference, encoded, prepare, install, load_public, INDEX_PATH, BASE_INDEX,
)

ROOT = Path(__file__).resolve().parents[1]


def report(value=25):
    return dict(schema='math-gauge.assessment-score-aggregate/v1', score_mode='strict',
        attempt_condition='nonlogical_retry_3', contributions={
            'lean':dict(confirmed=value, exact=value, lower=value, upper=value,
                complete=True, coverage=dict(planned=3, adjudicated=3)),
            'lean-formalization':dict(confirmed=15),
            'lean-selfcheck':dict(confirmed=0), 'lean-audit':dict(confirmed=10)})


class FormalizationMetricTests(unittest.TestCase):
    def test_projects_full_lean_smc_including_audit_and_whole_trajectory(self):
        r=report();original=deepcopy(r)
        self.assertAlmostEqual(profile_formalization_metric(r)['exact'],100*25/35)
        self.assertEqual(r,original)
        r=report(32.5)
        r['contributions']['lean-audit']['confirmed']=7.5
        r['contributions']['lean-selfcheck']['confirmed']=10
        self.assertAlmostEqual(profile_formalization_metric(r)['exact'],100*32.5/35)
        # Project the official aggregate, not a display-side recombination.
        r['contributions']['lean-formalization']['confirmed']=0
        self.assertAlmostEqual(profile_formalization_metric(r)['exact'],100*32.5/35)

    def test_complete_unrounded_credit_does_not_acquire_rounding_uncertainty(self):
        r=report(25);s=r['contributions']['lean']
        s.update(exact=25,lower=24.9999999999,upper=25.0000000001)
        m=profile_formalization_metric(r)
        self.assertAlmostEqual(m['exact'],100*25/35)
        self.assertEqual(m['unknown_weight'],0)

    def test_unknown_retains_full_lean_weight_and_known_zero_stays_zero(self):
        r=report();s=r['contributions']['lean']
        s.update(complete=False,exact=None,confirmed=0,lower=0,upper=10)
        s['coverage']['adjudicated']=2
        m=profile_formalization_metric(r)
        self.assertIsNone(m['exact']);self.assertEqual(m['lower'],0)
        self.assertAlmostEqual(m['upper'],100*10/35)
        self.assertEqual(m['coverage'],dict(unit='lean_subcategory',planned=3,reviewed=2))
        self.assertEqual(profile_formalization_metric(report(0))['exact'],0)

    def test_other_score_modes_attempts_and_obligation_denominators_are_rejected(self):
        for key,value in [('score_mode','capability'),('score_mode','partial'),('attempt_condition','single_attempt')]:
            r=report();r[key]=value
            with self.assertRaises(ValueError):profile_formalization_metric(r)
        r=report();r['contributions']['lean']['coverage']['planned']=184
        with self.assertRaises(ValueError):profile_formalization_metric(r)


class FormalizationSourceTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name)
        for name in ('formalization-profile.json','formalization-profile.md','scoring-policy.json'):
            out=self.root/'protocol'/name;out.parent.mkdir(exist_ok=True)
            out.write_bytes((ROOT/'protocol'/name).read_bytes())
        self.refs={}
        for name,data in [('baseline',{'model_id':'candidate'}),('manifest',{}),('record',{'record_kind':'cli'})]:
            self.refs[name]=self.put(name+'.json',data)
        r=report();r['source_bindings']={'assessment_policy_sha256':
            json.loads((self.root/'protocol/formalization-profile.json').read_bytes())['assessment_policy']['sha256']}
        self.refs['report']=self.put('report.json',r)
        self.put(BASE_INDEX,{'models':{'candidate':self.refs['baseline']}})
        self.source=patch('math_gauge.formalization_profile.selected_source',return_value={
            k:self.refs[k] for k in ('manifest','record','report')})
        self.source_mock=self.source.start();self.addCleanup(self.source.stop)

    def put(self,name,data):
        raw=encoded(data);p=self.root/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)
        return reference(name,raw)

    def test_paired_source_projection_reproduces_and_historical_views_are_untouched(self):
        install(self.root)
        value=load_public(self.root,benchmark_version='1.2.0')
        self.assertAlmostEqual(value['models'][0]['metric']['exact'],100*25/35)
        self.assertIsNone(load_public(self.root,benchmark_version='1.1.0'))
        self.assertIsNone(load_public(self.root,benchmark_version='1.0.0'))
        index=json.loads((self.root/INDEX_PATH).read_bytes())
        ref=index['models']['candidate'];payload=json.loads((self.root/ref['path']).read_bytes())
        payload['metric']['exact']=99
        raw=encoded(payload);(self.root/ref['path']).write_bytes(raw)
        index['models']['candidate']=reference(ref['path'],raw)
        (self.root/INDEX_PATH).write_bytes(encoded(index))
        with self.assertRaises(ValueError):load_public(self.root,benchmark_version='1.2.0')

    def test_modified_actual_source_is_rejected_without_replacement_or_regrading(self):
        (self.root/'report.json').write_text('{}')
        with self.assertRaises(ValueError):prepare(self.root)
        self.assertFalse((self.root/INDEX_PATH).exists())

    def test_native_observation_uses_its_own_bound_assessment_policy(self):
        r=json.loads((self.root/'report.json').read_bytes());r.pop('source_bindings')
        raw=encoded(r);(self.root/'report.json').write_bytes(raw)
        self.source_mock.return_value['report']=reference('report.json',raw)
        policy=(self.root/'protocol/scoring-policy.json').read_bytes()
        (self.root/'assessment-policy.json').write_bytes(policy)
        self.source_mock.return_value['record']=self.put('record.json',dict(record_kind='native_harness',
            assessment_policy=reference('assessment-policy.json',policy)))
        files=prepare(self.root)
        value=json.loads(files[next(k for k in files if k.endswith('/profile.json'))])
        self.assertAlmostEqual(value['metric']['exact'],100*25/35)


if __name__ == '__main__':
    unittest.main()
