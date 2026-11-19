"""A changed assessment edition still resolves the exact old result archives."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from math_gauge.editions import (
    ASSESSMENT_DIRECTORY, CALIBRATION_POLICY_PATH, NATIVE_MODEL, SOURCE_EDITION_PATH,
    TRANSITION_PATH, load_assessment_transition, result_archive, source_edition,
    verify_compatibility,
)
from math_gauge.result_admissions import COUNTS
from scripts.validate_protocol import check_plan


class AssessmentTransitionTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.source = dict(
            schema='math-gauge.benchmark-edition/v1', version='1.0.0', status='frozen-release',
            release=dict(version='1.0.0', status='sealed'),
            public=dict(tasks=COUNTS['public_a1'], suite_sha256='public-fixture'),
            private=dict(tasks=COUNTS['private_a1'], suite_sha256='private-fixture'),
            selected_result_models=['legacy', 'fresh'],
            selected_result_record_ids={'legacy': 'old', 'fresh': 'new'},
            selected_result_source_versions={'fresh': '1.0.0'},
            result_compatibility=dict(source_benchmark_version='0.6.0', archive_root='results/v0.6.0',
                path='releases/v1.0.0/compatibility.json', new_candidate_calls=0,
                mathematical_judgments_changed=False),
        )
        bindings, adopted = [], []
        for model, record_id in (('legacy', 'old'), (NATIVE_MODEL, '20261108')):
            parent = f'results/v0.6.0/{model}/{record_id}/'
            record_path = parent + 'record.json'
            score_paths = [parent + f'view-{number}.json' for number in range(6)]
            bindings.extend(self.write(path, {'benchmark_version': '0.6.0'})
                            for path in [record_path, *score_paths])
            adopted.append(dict(model_id=model, record_id=record_id, record_path=record_path,
                                score_paths=score_paths))
        self.compatibility = self.write(self.source['result_compatibility']['path'], dict(
            schema='math-gauge.edition-compatibility/v1', benchmark_version='1.0.0',
            source_benchmark_version='0.6.0', archive_root='results/v0.6.0', new_candidate_calls=0,
            mathematical_judgments_changed=False, counts=COUNTS,
            source_suites=dict(public_current_sha256='public-fixture', private_current_sha256='private-fixture'),
            selected_records=adopted, source_bindings=bindings))
        self.write('results/v1.0.0/fresh/new/record.json', {'benchmark_version': '1.0.0'})
        self.transition = dict(
            schema='math-gauge.assessment-transition/v1', version='0.1.0',
            source_benchmark_version='1.0.0', target_benchmark_version='1.1.0', task_suite_version='1.0.0',
            post_observation=True, new_candidate_calls=0, source_raw_bytes_rewritten=False,
            original_judgments_rewritten=False, research_judgments_changed=True, human_review='pending',
            formal_comparison_eligible=False, counts=COUNTS,
            source_edition=self.write(SOURCE_EDITION_PATH, self.source),
            policy=self.write(CALIBRATION_POLICY_PATH, {'fixture': 'policy'}),
            calibrations={model: self.write(f'{ASSESSMENT_DIRECTORY}/{model}/public.json', {'model_id': model})
                          for model in ('legacy', 'fresh', NATIVE_MODEL)},
        )
        self.current = dict(self.source, version='1.1.0', status='local-assessment-candidate',
                            source_task_version='1.0.0')
        self.select_transition()

    def write(self, name, data):
        content = json.dumps(data).encode()
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)
        return dict(path=name, bytes=len(content), sha256=hashlib.sha256(content).hexdigest())

    def select_transition(self):
        self.current['assessment_transition'] = self.write(TRANSITION_PATH, self.transition)
        self.write('benchmark.json', self.current)

    def test_routes_by_source_without_moving_results_to_assessment_edition(self):
        self.assertEqual(verify_compatibility(self.root), self.current)
        self.assertEqual(source_edition(self.root), self.source)
        self.assertEqual(load_assessment_transition(self.root), self.transition)
        self.assertEqual(result_archive(self.current, 'legacy', root=self.root), 'results/v0.6.0')
        self.assertEqual(result_archive(self.current, NATIVE_MODEL, root=self.root), 'results/v0.6.0')
        self.assertEqual(result_archive(self.current, 'fresh', root=self.root), 'results/v1.0.0')
        with self.assertRaisesRegex(ValueError, 'repository root'):
            result_archive(self.current, 'legacy')

    def test_rejects_retargeted_source_selection_and_suite(self):
        for changes in (dict(selected_result_record_ids={'legacy': 'substitute', 'fresh': 'new'}),
                        dict(public={'tasks': COUNTS['public_a1'], 'suite_sha256': 'other-suite'}),
                        dict(result_corrections={'legacy': {'sha256': 'different-correction'}})):
            with self.subTest(changes=changes), self.assertRaisesRegex(ValueError, 'source selection'):
                source_edition(self.root, self.current | changes)

    def test_transition_authenticates_source_snapshot_and_selected_manifests(self):
        source = self.root / SOURCE_EDITION_PATH
        original = source.read_bytes()
        source.write_bytes(original + b'\n')
        with self.assertRaisesRegex(ValueError, 'source failed verification'):
            load_assessment_transition(self.root)
        source.write_bytes(original)
        model_manifest = self.root / self.transition['calibrations'][NATIVE_MODEL]['path']
        other = model_manifest.with_name('elsewhere.json')
        model_manifest.rename(other)
        model_manifest.symlink_to(other)
        with self.assertRaisesRegex(ValueError, 'source failed verification'):
            verify_compatibility(self.root)

    def test_rejects_partial_transition_and_arbitrary_reassessment_versions(self):
        self.transition['calibrations'].pop(NATIVE_MODEL)
        self.select_transition()
        with self.assertRaisesRegex(ValueError, 'every selected source model'):
            verify_compatibility(self.root)
        with self.assertRaisesRegex(ValueError, 'supported only for benchmark 1.1.0'):
            result_archive(self.current | {'version': '1.2.0'}, root=self.root)

    def test_legacy_compatibility_is_still_verified(self):
        path = self.root / self.compatibility['path']
        data = json.loads(path.read_bytes())
        (self.root / data['source_bindings'][0]['path']).write_bytes(b'changed original record')
        with self.assertRaisesRegex(ValueError, 'compatibility source changed'):
            verify_compatibility(self.root)

    def test_material_plan_retains_original_task_suite_version(self):
        public_count = self.source['public']['tasks']
        cases = [{'case_id': f'fixture-{i}'} for i in range(public_count)]
        plan = dict(
            schema='math-gauge.reliability-material-plan/v3', protocol_version='0.5.0', suite_version='1.0.0',
            cases=cases, candidate_calls=0, execution_authorized=False, human_approved=False,
            actual_results=None, runtime_configuration_frozen=False, repeat_case_ids=[],
            independent_attempts=['A1'], rounds_per_arm=0, planned_slots_per_model=public_count,
            attempt_schedule={case['case_id']: ['A1'] for case in cases},
        )
        check_plan(plan, root=self.root)
        with self.assertRaisesRegex(ValueError, 'Current material plan'):
            check_plan(plan | {'suite_version': '1.1.0'}, root=self.root)
