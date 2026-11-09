"""Attempt bundles preserve source selection; no synthetic row is model evidence."""
import copy
import hashlib
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from math_gauge.attempt_conditions import load_sources


class AttemptSourcesTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def keep(self, name, value):
        raw = value if isinstance(value, bytes) else json.dumps(value).encode()
        (self.root / name).write_bytes(raw)
        return dict(path=name, bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())

    def fixture(self):
        conditions = {}
        for condition, prefix in [('single_attempt', ''), ('nonlogical_retry_3', 'retry-')]:
            response = None if not prefix else self.keep('answer.md', b'First normal final')
            completion = dict(lower=0, upper=0, exact=0)
            slot = dict(slot_id='S:A1', response_sha256=(response or {}).get('sha256'),
                        completion=completion, strict_pass=False)
            source = dict(id='S:A1', response=response,
                          evaluation=dict(completion=completion, strict_pass=False))
            conditions[condition] = dict(
                scoring_inputs=self.keep(prefix + 'scoring-inputs.json', dict(
                    plan={'synthetic_contract_fixture': True}, model_label='fixture', slots=[slot])),
                formalization_review=self.keep(prefix + 'formal.json', {'cases': []}),
                alignment_review=self.keep(prefix + 'alignment.json', {'rounds': []}),
                manuscript_completion_inputs={'sha256': 'b' * 64},
                source_records=self.keep(prefix + 'records.json', {'records': [source]}))
        manifest = dict(schema='math-gauge.attempt-condition-sources/v1',
            selection='first_normal_delivery_after_counted_operational_failures', conditions=conditions,
            human_review='pending', formal_comparison_eligible=False)
        record = dict(model={'requested_label': 'fixture'},
                      formalization_review=conditions['single_attempt']['formalization_review'],
                      attempt_condition_sources=self.keep('conditions.json', manifest))
        return record, manifest

    def load(self, record, condition='nonlogical_retry_3'):
        # Frozen-plan validation is tested by its owner. These tests isolate
        # source bindings and the split between operational conditions.
        with patch('math_gauge.benchmarks.validate_plan', side_effect=lambda p: p):
            return load_sources(self.root, record, condition)

    def test_first_timeout_and_first_normal_final_are_distinct(self):
        record, _ = self.fixture()
        self.assertIsNone(self.load(record, 'single_attempt')['inputs']['slots'][0]['response_sha256'])
        self.assertIsNotNone(self.load(record)['inputs']['slots'][0]['response_sha256'])

    def test_retry_cannot_change_plan_or_answer_binding(self):
        for field in ('plan', 'answer'):
            with self.subTest(field=field):
                record, manifest = self.fixture()
                bundle = manifest['conditions']['nonlogical_retry_3']
                inputs = json.loads((self.root / bundle['scoring_inputs']['path']).read_bytes())
                if field == 'plan':
                    inputs['plan']['different_frozen_plan'] = True
                else:
                    inputs['slots'][0]['response_sha256'] = 'f' * 64
                bundle['scoring_inputs'] = self.keep('retry-scoring-inputs.json', inputs)
                record['attempt_condition_sources'] = self.keep('conditions.json', manifest)
                with self.assertRaises(ValueError):
                    self.load(record)

    def test_public_manuscript_projection_remains_opaque(self):
        record, manifest = self.fixture()
        manifest['conditions']['nonlogical_retry_3']['manuscript_completion_inputs']['case_id'] = 'PRIVATE'
        record['attempt_condition_sources'] = self.keep('conditions.json', manifest)
        with self.assertRaises(ValueError):
            self.load(record)

    def test_public_research_conditions_remain_paired_and_opaque(self):
        record, manifest = self.fixture()
        for bundle in manifest['conditions'].values():
            bundle['theorem_extension_inputs'] = {'sha256': 'c' * 64}
        record['attempt_condition_sources'] = self.keep('conditions.json', manifest)
        self.load(record)
        manifest['conditions']['nonlogical_retry_3']['theorem_extension_inputs']['case_id'] = 'PRIVATE'
        record['attempt_condition_sources'] = self.keep('conditions.json', manifest)
        with self.assertRaises(ValueError):
            self.load(record)

    def test_retried_research_answer_cannot_enter_first_attempt_component(self):
        record, manifest = self.fixture()
        record['formalization_evidence_location'] = 'public_archive'
        for condition, bundle in manifest['conditions'].items():
            inputs = json.loads((self.root / bundle['scoring_inputs']['path']).read_bytes())
            inputs['slots'][0]['case_id'] = 'S'
            bundle['scoring_inputs'] = self.keep(bundle['scoring_inputs']['path'], inputs)
            records = json.loads((self.root / bundle['source_records']['path']).read_bytes())
            records['records'][0]['native_delivery'] = {'response': records['records'][0]['response']}
            bundle['source_records'] = self.keep(bundle['source_records']['path'], records)
            bundle['manuscript_completion_inputs'] = self.keep(condition + '-manuscript', {'slots': []})
            bundle['theorem_extension_inputs'] = self.keep(condition + '-research', dict(
                model_label='fixture', slots=[dict(case_id='S', response=records['records'][0]['response'])]))
        first = manifest['conditions']['single_attempt']
        record.update(manuscript_completion_inputs=first['manuscript_completion_inputs'],
                      theorem_extension_inputs=first['theorem_extension_inputs'],
                      attempt_condition_sources=self.keep('conditions.json', manifest))
        with patch('math_gauge.benchmarks.validate_plan', side_effect=lambda p: p), \
                patch('math_gauge.claude_code_evidence.validate_failure'), \
                patch('math_gauge.claude_code_evidence.validate_delivery'):
            selected = load_sources(self.root, record, 'single_attempt', public_root=self.root)
            self.assertIsNone(selected['theorem_extension_inputs']['slots'][0]['response'])
            first['theorem_extension_inputs'] = manifest['conditions']['nonlogical_retry_3']['theorem_extension_inputs']
            record['attempt_condition_sources'] = self.keep('conditions.json', manifest)
            with self.assertRaisesRegex(ValueError, 'selected A1 answers'):
                load_sources(self.root, record, 'single_attempt', public_root=self.root)
