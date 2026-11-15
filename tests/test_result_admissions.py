"""Additional legacy-source admission never rewrites sealed result identities.

These are offline identity fixtures, not model answers or mathematical reviews.
Normal records/native/scoring validation remains a separate mandatory boundary.
"""
import copy
import hashlib
import json
from pathlib import Path
import shutil
import tempfile
import unittest

import math_gauge.catalog
from math_gauge.catalog import Suite
from math_gauge.editions import result_archive, verify_compatibility
from math_gauge.records import public_assessment_case_ids, selected_cli_records
from math_gauge.result_admissions import (CONDITIONS, COUNTS, MODES, POLICIES,
    SCHEMA, VERSION)

ROOT = Path(math_gauge.catalog.__file__).resolve().parents[1]
MODEL = 'admitted-offline-fixture'
RID = 'identity-fixture'


def dump(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, sort_keys=True) + '\n')


def descriptor(root, path):
    raw = path.read_bytes()
    return dict(path=path.relative_to(root).as_posix(), bytes=len(raw),
                sha256=hashlib.sha256(raw).hexdigest())


class ResultAdmissionTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name).resolve()
        root = self.root
        shutil.copytree(ROOT / 'cases', root / 'cases')
        for path, _ in POLICIES.values():
            target = root / path
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / path, target)
        suite = Suite.load(root / 'cases')
        self.edition = dict(version='1.0.0',
            public={'suite_sha256': suite.sha256},
            selected_result_models=['legacy', 'fresh', MODEL],
            selected_result_record_ids={'legacy': 'old', 'fresh': 'new', MODEL: RID},
            selected_result_source_versions={'fresh': '1.0.0'},
            result_compatibility=dict(source_benchmark_version='0.6.0',
                archive_root='results/v0.6.0', path='releases/v1.0.0/compatibility.json',
                new_candidate_calls=0, mathematical_judgments_changed=False))
        adopted, bindings = [], []
        for model, rid in [('legacy', 'old'), ('dot-underlying-model-20261108', '20261108')]:
            parent = root / f'results/v0.6.0/{model}/{rid}'
            names = ['record.json'] + [f'view{n}.json' for n in range(6)]
            for name in names:
                path = parent / name
                dump(path, {'benchmark_version': '0.6.0', 'fixture_only': True})
                bindings.append({k: v for k, v in descriptor(root, path).items() if k != 'bytes'})
            adopted.append(dict(model_id=model, record_id=rid,
                record_path=(parent / names[0]).relative_to(root).as_posix(),
                score_paths=[(parent / n).relative_to(root).as_posix() for n in names[1:]]))
        dump(root / 'results/v1.0.0/fresh/new/record.json',
             {'benchmark_version': '1.0.0', 'fixture_only': True})
        self.sealed = root / self.edition['result_compatibility']['path']
        dump(self.sealed, dict(schema='math-gauge.edition-compatibility/v1',
            benchmark_version='1.0.0', source_benchmark_version='0.6.0',
            archive_root='results/v0.6.0', new_candidate_calls=0,
            mathematical_judgments_changed=False, counts=COUNTS,
            selected_records=adopted, source_bindings=bindings))
        self.sealed_bytes = self.sealed.read_bytes()
        self.folder = root / f'results/v0.6.0/{MODEL}/{RID}'
        self.record = dict(schema='math-gauge.result-record/v1',
            benchmark_version='0.6.0', model_id=MODEL, record_id=RID,
            human_review='pending', formal_comparison_eligible=False, fixture_only=True)
        for name, (path, field) in POLICIES.items():
            target = self.folder / name / Path(path).name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(root / path, target)
            self.record[field] = descriptor(self.folder, target)
        views = {}
        for mode, field in MODES.items():
            self.record[field], views[mode] = {}, {}
            for condition in CONDITIONS:
                path = self.folder / 'views' / f'{mode}-{condition}.json'
                dump(path, dict(benchmark_version='0.6.0', score_mode=mode,
                    attempt_condition=condition, fixture_only=True))
                self.record[field][condition] = descriptor(self.folder, path)
                views[mode][condition] = descriptor(root, path)
        dump(self.folder / 'record.json', self.record)
        policy = json.loads((root / POLICIES['assessment'][0]).read_bytes())
        contracts = []
        for case_id in public_assessment_case_ids(policy):
            case = suite.cases[case_id]
            request = self.folder / 'public-contracts' / case_id / 'request.json'
            contract = request.parent / 'contract.json'
            dump(request, suite.request(case))
            current_contract = suite.case_file(case, case['group_contract'])
            contract.write_bytes(current_contract.read_bytes())
            contracts.append(dict(case_id=case_id,
                current_task=descriptor(root, suite.case_file(case, case['task'])),
                current_contract=descriptor(root, current_contract),
                source_request=descriptor(root, request),
                source_contract=descriptor(root, contract)))
        disclosure = self.folder / 'selection-disclosure.json'
        dump(disclosure, {'fixture_only': True,
            'meaning': 'Offline source identity fixture; no actual run or attempt waiver'})
        self.document = dict(schema=SCHEMA, version=VERSION, visibility='public',
            model_id=MODEL, record_id=RID, target_benchmark_version='1.0.0',
            source_benchmark_version='0.6.0', archive_root='results/v0.6.0',
            record=descriptor(root, self.folder / 'record.json'), score_views=views,
            current_policies={name: descriptor(root, root / path)
                              for name, (path, _) in POLICIES.items()},
            public_case_contracts=contracts,
            selection_disclosure=dict(kind='source_bound_selection_disclosure_only',
                retry3_policy_changed=False, actual_ordinals_rewritten=False,
                formal_comparison_eligible=False, evidence=[descriptor(root, disclosure)]),
            sealed_compatibility_sha256=hashlib.sha256(self.sealed_bytes).hexdigest(),
            counts=COUNTS,
            migration=dict(post_observation=True, new_candidate_calls=0,
                source_raw_bytes_rewritten=False, mathematical_judgments_changed=False,
                human_review='pending', formal_comparison_eligible=False))
        self.admission = root / f'results/edition-admissions/v{VERSION}/{MODEL}/{RID}/admission.json'
        self.edition['selected_result_admissions'] = {MODEL: dict(
            source_benchmark_version='0.6.0', archive_root='results/v0.6.0', admission={})}
        self.save()

    def save(self):
        dump(self.admission, self.document)
        self.edition['selected_result_admissions'][MODEL]['admission'] = descriptor(self.root, self.admission)
        dump(self.root / 'benchmark.json', self.edition)

    def save_record(self):
        dump(self.folder / 'record.json', self.record)
        self.document['record'] = descriptor(self.root, self.folder / 'record.json')
        self.save()

    def assert_rejected(self, pattern):
        with self.assertRaisesRegex(ValueError, pattern):
            verify_compatibility(self.root)

    def test_unchanged_old_routes_and_explicit_addition_keep_real_source_identity(self):
        before = (self.folder / 'record.json').read_bytes()
        self.assertEqual(verify_compatibility(self.root), self.edition)
        self.assertEqual(result_archive(self.edition), 'results/v0.6.0')
        self.assertEqual(result_archive(self.edition, 'legacy'), 'results/v0.6.0')
        self.assertEqual(result_archive(self.edition, 'fresh'), 'results/v1.0.0')
        self.assertEqual(result_archive(self.edition, MODEL), 'results/v0.6.0')
        self.assertEqual(result_archive({'version': '1.0.0'}), 'results/v1.0.0')
        selected = dict(selected_cli_records(self.root))
        self.assertEqual(selected[MODEL], self.folder)
        self.assertEqual(selected['legacy'], self.root / 'results/v0.6.0/legacy/old')
        self.assertEqual(selected['fresh'], self.root / 'results/v1.0.0/fresh/new')
        self.assertEqual(self.sealed.read_bytes(), self.sealed_bytes)
        self.assertEqual((self.folder / 'record.json').read_bytes(), before)

    def test_record_and_six_view_byte_tampering_is_rejected(self):
        paths = [self.folder / 'record.json'] + [self.root / d['path']
            for conditions in self.document['score_views'].values() for d in conditions.values()]
        for path in paths:
            original = path.read_bytes()
            with self.subTest(path=path.name):
                path.write_bytes(original + b' ')
                self.assert_rejected('source bytes changed')
                path.write_bytes(original)

    def test_bound_manifest_bytes_and_descriptor_are_checked(self):
        self.admission.write_bytes(self.admission.read_bytes() + b' ')
        self.assert_rejected('source bytes changed')
        self.save()
        self.sealed.write_bytes(self.sealed_bytes + b' ')
        self.assert_rejected('sealed manifest')

    def test_paths_reject_escape_wrong_identity_and_symbolic_links(self):
        original = copy.deepcopy(self.document['record'])
        for path in ('../record.json', '/tmp/record.json',
                     f'results/v0.6.0/other/{RID}/record.json'):
            with self.subTest(path=path):
                self.document['record']['path'] = path
                self.save()
                self.assert_rejected('record path')
        self.document['record'] = original
        view = self.document['score_views']['partial']['nonlogical_retry_3']
        path = self.root / view['path']
        real = path.with_suffix('.original')
        path.rename(real)
        path.symlink_to(real.name)
        self.save()
        self.assert_rejected('linked')

    def test_configuration_has_only_the_supported_explicit_edition_boundary(self):
        original = copy.deepcopy(self.edition)
        changes = [('source_benchmark_version', '1.0.0'), ('source_benchmark_version', '0.7.0'),
                   ('archive_root', 'results/v1.0.0'), ('archive_root', '../private')]
        for key, value in changes:
            with self.subTest(key=key, value=value):
                self.edition = copy.deepcopy(original)
                self.edition['selected_result_admissions'][MODEL][key] = value
                self.save()
                self.assert_rejected('edition boundary')
        self.edition = copy.deepcopy(original)
        self.edition['version'] = '1.0.1'
        self.edition['selected_result_source_versions']['fresh'] = '1.0.1'
        self.save()
        self.assert_rejected('edition boundary')

    def test_manifest_namespace_and_required_seal_cannot_be_bypassed(self):
        self.edition['selected_result_admissions'][MODEL]['admission']['path'] = '../admission.json'
        dump(self.root / 'benchmark.json', self.edition)
        self.assert_rejected('relative|path')
        self.save()
        del self.edition['result_compatibility']
        dump(self.root / 'benchmark.json', self.edition)
        self.assert_rejected('sealed compatibility')
        with self.assertRaisesRegex(ValueError, 'sealed compatibility'):
            result_archive(self.edition, MODEL)

    def test_fresh_and_sealed_models_cannot_be_relocated_by_an_admission(self):
        original = copy.deepcopy(self.edition)
        self.edition['selected_result_source_versions'][MODEL] = '1.0.0'
        self.save()
        self.assert_rejected('distinct explicit')
        self.edition = original
        row = copy.deepcopy(self.edition['selected_result_admissions'][MODEL])
        row['admission']['path'] = f'results/edition-admissions/v{VERSION}/legacy/old/admission.json'
        self.edition['selected_result_admissions']['legacy'] = row
        dump(self.root / 'benchmark.json', self.edition)
        self.assert_rejected('sealed legacy')

    def test_original_selection_stays_exact(self):
        self.edition['selected_result_record_ids']['legacy'] = 'different-original'
        self.save()
        self.assert_rejected('every selected record')

    def test_six_views_cannot_be_dropped_reused_or_relabelled(self):
        original = copy.deepcopy(self.document)
        del self.document['score_views']['strict']['single_attempt']
        self.save()
        self.assert_rejected('both original attempt conditions')
        self.document = copy.deepcopy(original)
        self.document['score_views']['strict']['single_attempt'] = self.document['score_views']['partial']['single_attempt']
        self.save()
        self.assert_rejected('differs from its source record')
        self.document = copy.deepcopy(original)
        view = self.document['score_views']['strict']['single_attempt']
        path = self.root / view['path']
        value = json.loads(path.read_text())
        value['attempt_condition'] = 'nonlogical_retry_3'
        dump(path, value)
        self.record['strict_results']['single_attempt'] = descriptor(self.folder, path)
        self.document['score_views']['strict']['single_attempt'] = descriptor(self.root, path)
        self.save_record()
        self.assert_rejected('mode, or condition')

    def test_rebinding_hashes_cannot_pretend_original_execution_used_current_edition(self):
        self.record['benchmark_version'] = '1.0.0'
        self.save_record()
        self.assert_rejected('original record edition')

    def test_current_policy_cannot_rewrite_original_scoring_contract(self):
        item = self.record['assessment_policy']
        path = self.folder / item['path']
        altered = json.loads(path.read_text())
        altered['version'] = 'changed-fixture'
        dump(path, altered)
        self.record['assessment_policy'] = descriptor(self.folder, path)
        self.save_record()
        self.assert_rejected('policy differs from the current policy')

    def test_public_membership_and_source_request_are_bound_to_current_contract(self):
        original = copy.deepcopy(self.document)
        self.document['public_case_contracts'].pop()
        self.save()
        self.assert_rejected('fixed public case membership')
        self.document = original
        row = self.document['public_case_contracts'][0]
        path = self.root / row['source_request']['path']
        value = json.loads(path.read_text())
        value['instruction'] += '\nExtra assistance would change the candidate task.'
        dump(path, value)
        row['source_request'] = descriptor(self.root, path)
        self.save()
        self.assert_rejected('source request differs')

    def test_rebound_source_contract_cannot_weaken_the_current_contract(self):
        row = self.document['public_case_contracts'][0]
        path = self.root / row['source_contract']['path']
        value = json.loads(path.read_text())
        value['admission_fixture_added_weaker_contract'] = True
        dump(path, value)
        row['source_contract'] = descriptor(self.root, path)
        self.save()
        self.assert_rejected('source case contract differs')

    def test_disclosure_cannot_waive_retry_rules_ordinals_or_qualification(self):
        for key in ('retry3_policy_changed', 'actual_ordinals_rewritten', 'formal_comparison_eligible'):
            with self.subTest(key=key):
                self.document['selection_disclosure'][key] = True
                self.save()
                self.assert_rejected('cannot grant an attempt-policy')
                self.document['selection_disclosure'][key] = False
        self.document['migration']['mathematical_judgments_changed'] = True
        self.save()
        self.assert_rejected('migration changed')
