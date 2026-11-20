"""Continuation full counts retain exact scores, failures and opaque sources."""
from copy import deepcopy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from math_gauge.neutral_revision import RevisionInputs
from math_gauge.scoring import score_neutral_revision_completion
from scripts import results_revision_completion as completion
from test_neutral_revision import fixture_reports, inputs, MODES


class RevisionCompletionTests(unittest.TestCase):
    def revision(self, continuations):
        reports = fixture_reports()
        payload = json.loads(inputs(reports, scores=dict.fromkeys(MODES, 1))._payload)
        parent = payload['rows'][0]
        payload['rows'] = [dict(deepcopy(parent), case_id='synthetic-' + str(i), continuation=value)
                           for i, value in enumerate(continuations)]
        return RevisionInputs(json.dumps(payload).encode()), reports['partial']

    def reviewed(self, **scores):
        return dict(status='reviewed', scores=dict(dict.fromkeys(MODES, 1), **scores))

    def test_all_three_own_unrounded_scores_must_be_exactly_full(self):
        revision, base = self.revision([self.reviewed(),
            self.reviewed(capability=.99999999999), self.reviewed(partial=.99999999999),
            self.reviewed(strict=0), dict(status='delivery_failed', scores=None),
            dict(status='not_run', scores=None)])
        before = revision._payload
        result = score_neutral_revision_completion(revision, base=base)
        self.assertEqual({key: result[key] for key in ('selected','reviewed','delivery_failed','pending')},
                         dict(selected=6, reviewed=4, delivery_failed=1, pending=1))
        self.assertEqual(result['full_count'], dict(lower=1, upper=2, exact=None))
        self.assertEqual(result['full_rate'], dict(lower=1/6, upper=2/6, exact=None))
        self.assertFalse(result['settled'])
        self.assertEqual(revision._payload, before)

    def test_failed_delivery_counts_in_the_settled_denominator(self):
        revision, base = self.revision([self.reviewed(), dict(status='delivery_failed', scores=None)])
        result = score_neutral_revision_completion(revision, base=base)
        self.assertEqual(result['full_count']['exact'], 1)
        self.assertEqual(result['full_rate']['exact'], .5)
        self.assertTrue(result['settled'])

    def test_empty_selection_has_no_full_rate(self):
        revision, base = self.revision([])
        result = score_neutral_revision_completion(revision, base=base)
        self.assertEqual(result['full_count'], dict(lower=0, upper=0, exact=0))
        self.assertEqual(result['full_rate'], dict(lower=None, upper=None, exact=None))

    def test_summary_retains_the_authenticated_parent(self):
        revision, base = self.revision([self.reviewed()])
        base['tasks'][0]['response_sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'exact mode/condition/source'):
            score_neutral_revision_completion(revision, base=base)

    def fixture(self, root):
        public_ref = dict(path='results/adoption/public.json', bytes=10, sha256='a' * 64)
        transition = dict(adoptions={'fixture': public_ref})
        adoption = dict(private_inputs_sha256='b' * 64, policy=dict(sha256='c' * 64),
            revision_counts=dict(selected=3, reviewed=2, delivery_failed=1, pending=0),
            _scores={mode: dict(metrics=dict(earned=dict(complete=True, exact=90))) for mode in MODES})
        row = dict(id='fixture', selected=3, reviewed=2, delivery_failed=1, pending=0,
            full_count=dict(lower=1, upper=1, exact=1),
            full_rate=dict(lower=1/3, upper=1/3, exact=1/3), settled=True,
            inputs_sha256='b' * 64, policy_sha256='c' * 64, public_manifest_sha256='a' * 64)
        data = dict(completion.FIXED, models=[row])
        path = root / completion.DATA_PATH
        path.parent.mkdir(parents=True)
        path.write_text(json.dumps(data))
        return path, data, transition, adoption

    def test_public_loader_authenticates_all_three_opaque_bindings(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            path, data, transition, adoption = self.fixture(root)
            with patch.object(completion, 'load_public', return_value=adoption):
                result = completion.load_completion(root, transition=transition)
                self.assertEqual(result['models'], data['models'])
                self.assertEqual(result['source']['path'], completion.DATA_PATH)
                for field in ('inputs_sha256','policy_sha256','public_manifest_sha256'):
                    changed = deepcopy(data)
                    changed['models'][0][field] = 'd' * 64
                    path.write_text(json.dumps(changed))
                    with self.assertRaisesRegex(ValueError, 'exact inputs, policy or public adoption'):
                        completion.load_completion(root, transition=transition)

    def test_public_loader_rejects_private_rows_and_false_settlement(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            path, data, transition, adoption = self.fixture(root)
            with patch.object(completion, 'load_public', return_value=adoption):
                changed = deepcopy(data)
                changed['models'][0]['private_case_id'] = 'SYNTHETIC-PRIVATE'
                path.write_text(json.dumps(changed))
                with self.assertRaisesRegex(ValueError, 'anonymous counts'):
                    completion.load_completion(root, transition=transition)
                adoption['_scores']['capability']['metrics']['earned']['exact'] = None
                path.write_text(json.dumps(data))
                with self.assertRaisesRegex(ValueError, 'settle an unknown continuation'):
                    completion.load_completion(root, transition=transition)


if __name__ == '__main__':
    unittest.main()
