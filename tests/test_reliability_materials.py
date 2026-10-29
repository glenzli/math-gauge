"""Offline material revision chains; no candidate or compiler execution."""
import copy
import importlib.util
import json
from pathlib import Path
import shutil
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
SUITE = ROOT / 'drafts/progressive-groups-20261030'
SCRIPT = ROOT / 'protocol/reliability-20261030/validate_materials.py'
SPEC = importlib.util.spec_from_file_location('reliability_material_checks', SCRIPT)
V = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(V)


class ReliabilityRevisionTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        shutil.copytree(SUITE / 'MG-GR001', self.root / 'MG-GR001')
        for name in ['suite.json', 'reviews/strict-amendment-0.1.2.json',
                     'history/0.1.1-gr001.json', 'history/0.1.1-gr001.tar.gz']:
            target = self.root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(SUITE / name, target)

    def rewrite(self, path, data):
        path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n')

    def receipt(self):
        path = self.root / 'reviews/strict-amendment-0.1.2.json'
        return path, V.read(path)

    def test_editorial_identity_is_checked_on_the_archived_base(self):
        files, amendments = V.strict_baseline(self.root)
        editorial = V.read(SUITE / 'reviews/editorial-amendment-0.1.1.json')
        entry = next(x for x in editorial['cases'] if x['case_id'] == 'MG-GR001')
        self.assertEqual(V.sha(files['MG-GR001/task.md']), entry['new_task_sha256'])
        self.assertNotEqual(V.sha((self.root / 'MG-GR001/task.md').read_bytes()), entry['new_task_sha256'])
        self.assertEqual(json.loads(files['MG-GR001/case.json'])['version'], '0.1.1')
        self.assertEqual(amendments['MG-GR001']['version'], '0.1.2')

    def test_extra_contract_change_is_rejected_even_with_refreshed_receipt_hash(self):
        path = self.root / 'MG-GR001/contract.json'
        contract = V.read(path)
        contract['stages'][4]['expected'] = 'true'
        self.rewrite(path, contract)
        receipt_path, receipt = self.receipt()
        receipt['cases'][0]['new_files_sha256']['MG-GR001/contract.json'] = V.sha(path.read_bytes())
        self.rewrite(receipt_path, receipt)
        with self.assertRaisesRegex(AssertionError, 'Unrecorded strict contract change'):
            V.strict_baseline(self.root)

    def test_extra_task_change_is_rejected_even_with_refreshed_receipt_hash(self):
        path = self.root / 'MG-GR001/task.md'
        path.write_text(path.read_text() + '\nAssume an additional boundedness condition.\n')
        receipt_path, receipt = self.receipt()
        receipt['cases'][0]['new_files_sha256']['MG-GR001/task.md'] = V.sha(path.read_bytes())
        self.rewrite(receipt_path, receipt)
        with self.assertRaisesRegex(AssertionError, 'Unrecorded strict task change'):
            V.strict_baseline(self.root)

    def test_suite_membership_cannot_change_under_a_version_only_amendment(self):
        path = self.root / 'suite.json'
        suite = V.read(path)
        suite['cases'].reverse()
        self.rewrite(path, suite)
        with self.assertRaisesRegex(AssertionError, 'Unrecorded suite change'):
            V.strict_baseline(self.root)

    def packet_inputs(self):
        packet = ROOT / 'protocol/reliability-20261030'
        receipt = V.read(packet / 'reviews/strict-revalidation-20261030.json')
        for relative in receipt['archived_reviewed_files'].values():
            target = self.root / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / relative, target)
        return V.read(packet / 'plan.json'), V.read(packet / 'selection.json'), receipt

    def test_packet_identity_refresh_does_not_authorize_execution(self):
        plan, selection, receipt = self.packet_inputs()
        V.validate_packet_revalidation(self.root, plan, selection, receipt)
        changed = copy.deepcopy(plan)
        changed['execution_authorized'] = True
        with self.assertRaisesRegex(AssertionError, 'Unrecorded plan change'):
            V.validate_packet_revalidation(self.root, changed, selection, receipt)

    def test_selected_claim_cannot_change_during_suite_hash_refresh(self):
        plan, selection, receipt = self.packet_inputs()
        selection['cases'][0]['target_claim'] += ' Additional conclusion.'
        plan['files_sha256']['selection.json'] = V.sha(
            json.dumps(selection, ensure_ascii=False, indent=2).encode() + b'\n')
        with self.assertRaisesRegex(AssertionError, 'eight selected cases'):
            V.validate_packet_revalidation(self.root, plan, selection, receipt)

    def test_historical_runner_hash_cannot_replace_current_source_identity(self):
        relative = Path('results/strict-review-20261030/engineering/current-evidence.json')
        evidence = V.read(ROOT / relative)
        old = V.read(ROOT / evidence['historical_runner']['receipt'])
        for name in evidence['current_source_files_sha256']:
            target = self.root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / name, target)
        evidence['current_source_files_sha256']['math_gauge/execution.py'] = old['files_sha256']['math_gauge/execution.py']
        target = self.root / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        self.rewrite(target, evidence)
        with self.assertRaisesRegex(AssertionError, 'Current engineering source drift'):
            V.validate_runner_evidence(self.root)


if __name__ == '__main__':
    unittest.main()
