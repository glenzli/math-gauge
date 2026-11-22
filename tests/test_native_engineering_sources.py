"""Opaque native engineering sources do not expose or replace private inputs."""
import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from math_gauge.native_engineering_sources import PUBLIC_SCHEMA,MODES,CONDITIONS,validate,validate_sources
from math_gauge.native_assessment_sources import PUBLIC_SCHEMA as FIRST
from math_gauge.records import descriptor


class NativeEngineeringProjectionTests(unittest.TestCase):
    def put(self,name,obj):
        raw=(json.dumps(obj,ensure_ascii=False)+'\n').encode()
        p=self.root/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)
        return descriptor(self.root,p)

    def setUp(self):
        temporary=tempfile.TemporaryDirectory();self.addCleanup(temporary.cleanup)
        self.root=Path(temporary.name)
        self.source=dict(schema=PUBLIC_SCHEMA,version='0.1.0',model_id='native-fixture',model_label='Native fixture',
            source_benchmark_version='1.0.0',mathematical_inputs_kind='post_observation_evaluator_projection',
            post_observation=True,execution_freeze_claimed=False,mathematical_judgments_changed=False,
            reviewer_kind='ai',human_review='pending',formal_comparison_eligible=False,new_candidate_calls=0,
            engineering_review=self.put('engineering.json',dict(model_label='Native fixture',policy_sha256='b'*64)),
            private_source_sha256='a'*64,scoring_inputs_sha256='c'*64,source_math_policy_sha256='b'*64,
            alignment_review_sha256='d'*64,selected_alignment_review_sha256={c:'e'*64 for c in CONDITIONS},
            private_report_sha256={c:{m:'f'*64 for m in MODES} for c in CONDITIONS},reports={})
        self.record=dict(model_id='native-fixture',model=dict(requested_label='Native fixture'),benchmark_version='1.0.0',
            scope='public-answers-and-combined-aggregates',formalization_evidence_location=None,
            formalization_review=self.source['engineering_review'],native_engineering_sources_private_sha256='a'*64,
            first_assessment_source=self.put('first.json',dict(schema=FIRST,model_id='native-fixture')))
        for c in CONDITIONS:
            self.source['reports'][c]={}
            for m,field in MODES.items():
                ref=self.put(c+'/'+m+'.json',dict(source_bindings=dict(private_report_sha256='f'*64,
                    engineering_review_sha256=self.source['engineering_review']['sha256'],scoring_inputs_sha256='c'*64,
                    source_math_policy_sha256='b'*64,alignment_review_sha256='d'*64)))
                self.source['reports'][c][m]=ref
                self.record.setdefault(field,{})[c]=ref
        self.save()

    def save(self):
        self.record['native_engineering_sources']=self.put('native-engineering.json',self.source)

    def test_valid_opaque_projection_requires_private_pair(self):
        result=validate(self.root,self.record)
        self.assertTrue(result['public_projection'])
        self.assertTrue(result['private_validation_required'])
        self.assertEqual(result['report_views'],6)

    def test_public_full_input_descriptor_is_rejected(self):
        self.source['scoring_inputs']=dict(path='private-inputs.json',bytes=0,sha256='0'*64)
        with self.assertRaisesRegex(ValueError,'opaque private mathematical inputs'):
            validate_sources(self.root,self.record,self.source)

    def test_substituted_input_digest_is_rejected(self):
        self.source['scoring_inputs_sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'opaque source bindings'):
            validate_sources(self.root,self.record,self.source)

    def test_missing_condition_or_mode_is_rejected(self):
        del self.source['reports']['single_attempt']['strict']
        with self.assertRaisesRegex(ValueError,'two-condition three-mode'):
            validate_sources(self.root,self.record,self.source)

    def test_portable_source_cannot_select_native_branch(self):
        self.record['first_assessment_source']=self.put('portable.json',dict(schema='math-gauge.portable-first-assessment-source-public/v1',model_id='native-fixture'))
        with self.assertRaisesRegex(ValueError,'explicit native first-assessment'):
            validate_sources(self.root,self.record,self.source)

    def test_model_source_swap_is_rejected(self):
        self.source['model_id']='another-native'
        with self.assertRaisesRegex(ValueError,'actual model, scope'):
            validate_sources(self.root,self.record,self.source)

    def test_component_cannot_escape_its_source_root(self):
        self.record['native_engineering_sources']=dict(self.record['native_engineering_sources'],path='../native-engineering.json')
        with self.assertRaises(ValueError):validate(self.root,self.record)


if __name__=='__main__':unittest.main()
