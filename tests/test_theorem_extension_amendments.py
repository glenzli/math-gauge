"""Review corrections preserve source selection, gates and actual continuations."""
from copy import deepcopy
import hashlib
import json
import unittest
from unittest.mock import patch
from pathlib import Path

from math_gauge import scoring
from math_gauge.benchmarks import identity
from math_gauge.theorem_extension_amendments import ReviewAmendmentInputs, project_score
from math_gauge import theorem_extension_amendments as amendments
from math_gauge.neutral_revision import RevisionInputs, MODES, CONDITION
import test_theorem_extension_calibration as fixtures
import test_neutral_revision as neutral


class ReviewAmendmentTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        fixtures.CalibrationTests.setUpClass()

    def setUp(self):
        self.fixture = fixtures.CalibrationTests()
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)

    def corrected(self, *, new_R=3):
        f = self.fixture
        raw = json.loads(f.load()._payload)
        base = {m:deepcopy(f.effective[m][CONDITION]) for m in MODES}
        for mode, report in base.items():
            # A previous calibration is provenance, not permission to overwrite it.
            report['tx_calibration'] = dict(inputs_sha256='1'*64)
            raw['base_identities'][mode][CONDITION] = identity(report)
            raw['base_sha256'][mode][CONDITION] = hashlib.sha256(
                (json.dumps(report,ensure_ascii=False,indent=2)+'\n').encode()).hexdigest()
        for row in raw['conditions'][CONDITION]:
            row['new_R'] = new_R
        amendment = ReviewAmendmentInputs(json.dumps(raw).encode())
        corrected = {m:scoring.score_theorem_extension_calibration_overlay(base[m],f.policy,
            calibration=amendment,mode=m,condition=CONDITION) for m in MODES}
        return base, corrected

    def revision(self, base, corrected):
        value = json.loads(neutral.inputs(base,scores=dict.fromkeys(MODES,1))._payload)
        value['base_sha256'] = {m:corrected[m]['tx_review_amendment']['base_report_sha256'] for m in MODES}
        return RevisionInputs(json.dumps(value).encode())

    def test_current_tier_correction_keeps_historical_calibration_and_fixed_weights(self):
        base, corrected = self.corrected(new_R=2)
        for mode in MODES:
            result = corrected[mode]
            self.assertEqual(result['tx_calibration'],base[mode]['tx_calibration'])
            self.assertEqual(result['contributions']['theorem-extension']['confirmed'],
                             0 if mode=='strict' else 20/3)
            self.assertEqual([r for r in result['tasks'] if r['subcategory']!='theorem-extension'],
                             [r for r in base[mode]['tasks'] if r['subcategory']!='theorem-extension'])
            self.assertEqual(result['source_bindings']['mathematical_input_sha256'],
                             base[mode]['source_bindings']['mathematical_input_sha256'])

    def test_same_actual_revision_reblends_with_eighty_percent_corrected_parent(self):
        base, corrected = self.corrected()
        revision = self.revision(base,corrected)
        before = revision._payload
        for mode in MODES:
            old = scoring.score_neutral_revision_overlay(base[mode],self.fixture.policy,revision=revision,mode=mode)
            new = scoring.score_neutral_revision_after_review_amendment(base[mode],corrected[mode],
                self.fixture.policy,revision=revision,mode=mode)
            expected_delta = 8 if mode=='strict' else 16/3
            self.assertAlmostEqual(new['contributions']['theorem-extension']['confirmed']-
                                   old['contributions']['theorem-extension']['confirmed'],expected_delta)
            self.assertEqual(new['contributions']['lean'],old['contributions']['lean'])
            for a,b in zip(old['tasks'],new['tasks']):
                self.assertEqual(a.get('response_sha256'),b.get('response_sha256'))
                if a.get('neutral_revision'):
                    for key in ('revision_completion','response_sha256','review_sha256'):
                        self.assertEqual(a['neutral_revision'][key],b['neutral_revision'][key])
        self.assertEqual(revision._payload,before)

    def test_wrong_parent_or_replaced_answer_cannot_be_reblended(self):
        base, corrected = self.corrected()
        revision=self.revision(base,corrected)
        wrong=deepcopy(corrected['partial'])
        wrong['tx_review_amendment']['base_report_sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'different original parents'):
            scoring.score_neutral_revision_after_review_amendment(base['partial'],wrong,
                self.fixture.policy,revision=revision,mode='partial')
        wrong=deepcopy(corrected['partial'])
        next(t for t in wrong['tasks'] if t['subcategory']=='theorem-extension')['response_sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'replaced an original answer'):
            scoring.score_neutral_revision_after_review_amendment(base['partial'],wrong,
                self.fixture.policy,revision=revision,mode='partial')

    def test_public_projection_excludes_private_task_inventory(self):
        _, corrected=self.corrected()
        projected=project_score(corrected['partial'])
        self.assertNotIn('tasks',projected)
        self.assertNotIn('conditions',projected)
        self.assertEqual(projected['tx_review_amendment'],corrected['partial']['tx_review_amendment'])
        self.assertNotIn('MG-TXP',json.dumps(projected))


class PublishedAmendmentBindingTests(unittest.TestCase):
    def setUp(self):
        self.root=Path(__file__).resolve().parents[1]
        index=json.loads((self.root/amendments.INDEX_PATH).read_bytes())
        self.mid=next(iter(index['models']))
        self.manifest=amendments.document(self.root,index['models'][self.mid])
        self.read=amendments.document

    def changed_document(self,target,change):
        def read(root,ref):
            value=self.read(root,ref)
            if ref['path']==target:
                value=deepcopy(value)
                change(value)
            return value
        return patch.object(amendments,'document',side_effect=read)

    def test_revised_projection_cannot_borrow_another_report(self):
        target=self.manifest['public_tasks']['revised']['path']
        def change(value):
            value['views']['partial'][CONDITION]['source_report_sha256']='0'*64
        with self.changed_document(target,change):
            with self.assertRaisesRegex(ValueError,'another source score report'):
                amendments.load_public(self.root,self.mid)

    def test_revised_projection_cannot_smuggle_private_fields(self):
        target=self.manifest['public_tasks']['revised']['path']
        def change(value):
            value['views']['partial'][CONDITION]['tasks'][0]['private_reason']='confidential'
        with self.changed_document(target,change):
            with self.assertRaisesRegex(ValueError,'Private fields leaked'):
                amendments.load_public(self.root,self.mid)

    def test_public_review_cannot_point_to_another_answer(self):
        target=self.manifest['public_reviews'][CONDITION][0]['review']['path']
        def change(value):
            value['answer_sha256']='0'*64
        with self.changed_document(target,change):
            with self.assertRaisesRegex(ValueError,'actual answer and score'):
                amendments.load_public(self.root,self.mid)


if __name__=='__main__':
    unittest.main()
