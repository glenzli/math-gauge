"""Synthetic exact-source, fixed-denominator and privacy checks for legacy taste."""
import copy
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from math_gauge import legacy_taste as taste
from math_gauge.open_research import encoded, reference

MARKER = 'LEGACY_TASTE_PRIVATE_SYNTHETIC_MARKER'


class LegacyTasteTests(unittest.TestCase):
    def setUp(self):
        temporary = TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.roots = dict(public=self.root, private=self.root)
        self.policy, self.policy_sha = taste.load_policy()
        self.baseline = dict(models=[dict(id='evaluated'), dict(id='unknown')],
                             profile_models=[dict(id='retained-first')])
        self.baseline_sha = taste.sha256(encoded(self.baseline))
        self.families = ['fixture-' + str(n) for n in range(1, 7)]
        self.first, self.revision = {}, {}
        for index, cid in enumerate(self.families):
            self.first[cid] = self.manuscript('first-' + str(index), 'The baseline quote')
        self.revision[self.families[0]] = self.manuscript('later', 'The accepted later quote', attach=True)
        self.revision[self.families[1]] = self.manuscript('unreviewed-later', 'Another actual delivery')
        self.catalog = dict(source_binding=dict(edition='1.2.0', sha256=self.baseline_sha), models={
            'evaluated': dict(first=self.first, revision=self.revision),
            'unknown': dict(first=self.first, revision={}),
            'retained-first': dict(first=self.first, revision=None)})
        self.rows = []
        self.review = dict(schema=taste.REVIEW_SCHEMA, version=taste.VERSION, edition=taste.EDITION,
                           condition=taste.CONDITION, reviewer_id='synthetic Sol reviewer fixture',
                           actual_context=MARKER, judgments=self.rows, **taste.REVIEWER)

    def manuscript(self, path, content, *, attach=False):
        raw = (content + ' ' + MARKER).encode()
        (self.root / path).write_bytes(raw)
        descriptor = reference(path, raw, 'private')
        evidence = dict(answer=descriptor)
        if attach:
            raw = ('Original attachment claim. ' + MARKER).encode()
            (self.root / 'attachment.md').write_bytes(raw)
            evidence['attachment:0'] = reference('attachment.md', raw, 'private')
        return dict(status='normal_final', evidence=evidence, response_sha256=descriptor['sha256'])

    def judgment(self, index, grade, *, stage='first', mid='evaluated', attachment=False):
        cid = self.families[index]
        source = (self.first if stage == 'first' else self.revision)[cid]
        quote = dict(quote='The baseline quote')
        if attachment:
            quote = dict(source_id='attachment:0', quote='Original attachment claim.')
        status = 'reviewed' if grade is not None else 'evidence_insufficient'
        return dict(model_id=mid, stage=stage, case_id=cid, response_sha256=source['response_sha256'],
                    assessment_status=status, score=grade, enough_evidence=grade is not None,
                    reason=MARKER, valid_scope='Verified synthetic scope',
                    choice_value='Synthetic value', condition_cost='Synthetic condition', evidence=[quote])

    def project(self):
        catalogue = encoded(self.catalog)
        self.review['source_catalog_sha256'] = taste.sha256(catalogue)
        review_files = [encoded(self.review)] if self.rows else []
        result = taste.prepare_public(self.roots, catalogue, review_files, self.policy, self.policy_sha)
        return taste.validate_public(result, self.policy_sha, self.baseline, self.baseline_sha)

    def test_fixed_weight_and_unknown_continuation_preserve_signed_change(self):
        self.rows.extend([self.judgment(0, 80), self.judgment(1, 0), self.judgment(2, None),
                          self.judgment(0, 20, stage='revision', attachment=True)])
        model = self.project()['models']['evaluated']
        first, revised = model['first'], model['revision']
        self.assertIsNone(first['exact'])
        self.assertIsNone(revised['exact'])
        self.assertAlmostEqual(first['lower'], 80 / 6)
        self.assertAlmostEqual(first['upper'], (80 + 400) / 6)
        self.assertAlmostEqual(revised['lower'], 68 / 6)
        self.assertAlmostEqual(revised['upper'], (68 + 20 + 400) / 6)
        self.assertEqual((first['coverage']['planned'], first['coverage']['reviewed']), (6, 2))
        self.assertEqual((revised['coverage']['observed'], revised['coverage']['reviewed']), (2, 1))

    def test_known_zero_and_first_only_are_preserved_without_private_fields(self):
        self.rows.extend(self.judgment(i, 0, mid='retained-first') for i in range(6))
        result = self.project()
        model = result['models']['retained-first']
        self.assertEqual(model['first']['exact'], 0)
        self.assertEqual(model['first']['coverage']['reviewed'], 6)
        self.assertIsNone(model['revision'])
        evaluated = result['models']['evaluated']['first']
        self.assertEqual((evaluated['lower'], evaluated['upper'], evaluated['exact']), (0, 100, None))
        self.assertNotIn(MARKER, json.dumps(result))
        self.assertNotIn('fixture-1', json.dumps(result))
        bad = copy.deepcopy(result)
        bad['models']['evaluated']['first']['review_reason'] = MARKER
        with self.assertRaisesRegex(ValueError, 'unsupported private fields'):
            taste.validate_public(bad, self.policy_sha, self.baseline, self.baseline_sha)

    def test_reject_unbound_evidence_missing_and_duplicate_judgments(self):
        row = self.judgment(0, 45)
        self.rows.append(row)
        row['evidence'][0]['quote'] = 'Absent original quote'
        with self.assertRaisesRegex(ValueError, 'quote differs'):
            self.project()
        row['evidence'][0]['quote'] = 'The baseline quote'
        row['enough_evidence'] = False
        with self.assertRaisesRegex(ValueError, 'reviewable choice'):
            self.project()
        row['enough_evidence'] = True
        row['response_sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'exact delivered response'):
            self.project()
        row['response_sha256'] = self.first[self.families[0]]['response_sha256']
        self.rows.append(copy.deepcopy(row))
        with self.assertRaisesRegex(ValueError, 'Duplicate'):
            self.project()
        self.rows.pop()
        self.first[self.families[0]]['status'] = 'known_delivery_failure'
        with self.assertRaisesRegex(ValueError, 'exact delivered response'):
            self.project()
