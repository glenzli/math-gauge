"""Explicit source identity when a settled base edition gains another model."""
import copy
import hashlib
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

from math_gauge import independent_research_adoption as adoption
from math_gauge import independent_research_score_modes as modes
from math_gauge.research_profile import POLICY_FILE as PROFILE_FILE, POLICY_PATH as PROFILE_PATH
from math_gauge.taste_v130 import POLICY_FILE
from scripts.results_research_baseline import (CURRENT_PATH, POLICY_PATH as SELECTION_PATH,
    baseline_homepage, select_baseline)
from scripts.results_research_preview import prepare_research_preview
from test_research_ability_projection import baseline, selection


def encoded(value):
    return json.dumps(value, ensure_ascii=False, indent=2) + '\n'


def descriptor(path, raw):
    return dict(path=path, bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())


class ResearchBaselineSelectionTests(unittest.TestCase):
    def setUp(self):
        self.directory = TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.data = baseline()
        self.data.update(schema='math-gauge.results/v1', manuscript_observations=dict(models=[]))
        self.data['gap_diagnostics']['tables'] = []
        for model in self.data['models']:
            model['harness'] = dict(name='Synthetic')
            model['logo']['sha256'] = 'd' * 64
            model['combined'] = copy.deepcopy(model['retry']['combined'])
            for report in [model['combined'], model['retry']['combined'],
                           *model['capability'].values(), *model['strict'].values()]:
                report['contributions'] = {}
        self.raw = encoded(self.data).encode()
        self.adopted = selection(self.raw, POLICY_FILE.read_bytes())
        self.index_raw = encoded(self.adopted).encode()
        self.policy = dict(schema='math-gauge.independent-research-baseline-selection/v1',
            version='0.1.0', edition='1.3.0', selection='retained-original-adoption-baseline',
            baseline=dict(edition='1.2.0', **descriptor('site/data.json', self.raw)),
            settled_index=descriptor(adoption.PUBLIC_PATH, self.index_raw),
            current_base_publication=dict(edition='1.2.0', data_path=CURRENT_PATH),
            original_grade_bindings_modified=False, new_candidate_calls=0, new_mathematical_judgments=0)
        for name, raw in [('site/data.json', self.raw), (adoption.PUBLIC_PATH, self.index_raw),
                          (SELECTION_PATH.as_posix(), encoded(self.policy).encode()),
                          (POLICY_FILE.relative_to(POLICY_FILE.parents[3]).as_posix(), POLICY_FILE.read_bytes()),
                          (PROFILE_PATH.as_posix(), PROFILE_FILE.read_bytes()),
                          (modes.POLICY_PATH.as_posix(), modes.POLICY_FILE.read_bytes())]:
            self.write(name, raw)
        for name in ('research-preview.js', 'research-preview.css', 'edition-notes.js',
                     'board-controls.js', 'results-core.js', 'home-results.js',
                     'mathematical-profile.js', 'mathematical-profile.css'):
            self.write('scripts/templates/' + name, (POLICY_FILE.parents[3] / 'scripts/templates' / name).read_bytes())
        self.current = copy.deepcopy(self.data)
        added = copy.deepcopy(self.current['models'][0])
        added['id'] = 'fixture-added'
        self.current['models'].append(added)

    def write(self, name, raw):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)

    def files(self, data=None):
        data = self.current if data is None else data
        envelope = dict(edition='1.2.0', page='index.html', data=data)
        config = dict(versions={'1.2.0': {}}, scripts=[])
        return {'data.json': encoded(data), 'data/editions/1.2.0/index.json': encoded(envelope),
                'index.html': '<head><script type="application/json" id="edition-config">' + encoded(config)
                              + '</script></head><main></main>',
                'editions.json': encoded(dict(editions=[dict(version='1.2.0', data='data.json')]))}

    def test_split_cohort_preserves_original_source_and_every_research_result(self):
        original = prepare_research_preview(self.files(self.data), self.root)
        files = self.files()
        result = prepare_research_preview(files, self.root)
        self.assertEqual(result['data.json'].encode(), self.raw)
        self.assertEqual(result[CURRENT_PATH], files['data.json'])
        self.assertEqual(result['data/editions/1.2.0/index.json'], files['data/editions/1.2.0/index.json'])
        for name, value in original.items():
            if name.startswith(('versions/1.3.0/', 'data/editions/1.3.0/')):
                self.assertEqual(result[name], value, name)
        research = json.loads(result['versions/1.3.0/data.json'])
        self.assertNotIn('fixture-added', [m['id'] for m in research['models']])
        self.assertEqual(research['research_preview']['source_binding']['sha256'],
                         hashlib.sha256(self.raw).hexdigest())
        self.assertEqual((self.root / 'site/data.json').read_bytes(), self.raw)
        self.assertEqual(prepare_research_preview(files, self.root), result)
        self.assertEqual(json.loads(result['editions.json'])['editions'][1]['data'], CURRENT_PATH)

    def test_current_retained_model_must_be_exactly_unchanged(self):
        changed = copy.deepcopy(self.current)
        changed['models'][0]['retry']['combined']['metrics']['earned']['confirmed'] -= 1
        with self.assertRaisesRegex(ValueError, 'modified retained research model'):
            select_baseline(self.files(changed), self.root, self.adopted)
        typed = copy.deepcopy(self.current)
        typed['models'][0]['display_order'] = False
        with self.assertRaisesRegex(ValueError, 'modified retained research model'):
            select_baseline(self.files(typed), self.root, self.adopted)
        removed = copy.deepcopy(self.current)
        removed['models'].pop(0)
        with self.assertRaisesRegex(ValueError, 'removed a retained'):
            select_baseline(self.files(removed), self.root, self.adopted)

    def test_no_selector_does_not_fall_back_to_old_disk_source(self):
        (self.root / SELECTION_PATH).unlink()
        with self.assertRaisesRegex(ValueError, 'different baseline'):
            prepare_research_preview(self.files(), self.root)

    def test_missing_damaged_or_substituted_originals_fail(self):
        path = self.root / 'site/data.json'
        path.unlink()
        with self.assertRaisesRegex(ValueError, 'Missing or unreadable'):
            select_baseline(self.files(), self.root, self.adopted)
        path.write_bytes(self.raw + b'\n')
        with self.assertRaisesRegex(ValueError, 'source bytes differ'):
            select_baseline(self.files(), self.root, self.adopted)
        path.write_bytes(self.raw)
        index = self.root / adoption.PUBLIC_PATH
        index.write_bytes(self.index_raw + b'\n')
        with self.assertRaisesRegex(ValueError, 'source bytes differ'):
            select_baseline(self.files(), self.root, self.adopted)

    def test_traversal_symlink_and_wrong_descriptor_are_rejected(self):
        policy = copy.deepcopy(self.policy)
        policy['baseline']['path'] = '../data.json'
        self.write(SELECTION_PATH.as_posix(), encoded(policy).encode())
        with self.assertRaisesRegex(ValueError, 'differs from the original adoption'):
            select_baseline(self.files(), self.root, self.adopted)
        self.write(SELECTION_PATH.as_posix(), encoded(self.policy).encode())
        path = self.root / 'site/data.json'
        path.unlink()
        target = self.root / 'other.json'
        target.write_bytes(self.raw)
        path.symlink_to(target)
        with self.assertRaisesRegex(ValueError, 'symlinks'):
            select_baseline(self.files(), self.root, self.adopted)

    def test_incremental_input_keeps_current_versioned_edition(self):
        files = self.files(self.data)
        current = encoded(self.current)
        files[CURRENT_PATH] = current
        selected = select_baseline(files, self.root, self.adopted)
        self.assertEqual(selected.raw.encode(), self.raw)
        self.assertEqual(selected.current_raw, current)

    def test_unknown_selection_contract_or_wrong_declared_size_fails(self):
        for key, value in [('version', '9.0.0'), ('new_candidate_calls', True)]:
            policy = dict(self.policy, **{key: value})
            self.write(SELECTION_PATH.as_posix(), encoded(policy).encode())
            with self.assertRaisesRegex(ValueError, 'Invalid explicit research baseline selection'):
                select_baseline(self.files(), self.root, self.adopted)
        policy = copy.deepcopy(self.policy)
        policy['baseline']['bytes'] += 1
        self.write(SELECTION_PATH.as_posix(), encoded(policy).encode())
        with self.assertRaisesRegex(ValueError, 'source bytes differ'):
            select_baseline(self.files(), self.root, self.adopted)

    def test_companions_are_rebuilt_for_retained_cohort_instead_of_filtering_new_sample(self):
        selected = select_baseline(self.files(), self.root, self.adopted)
        envelope = json.loads(self.files()['data/editions/1.2.0/index.json'])
        envelope['supplemental'] = {'timing-reference-data': dict(daily_case_ids=['new-sample']),
                                    'cost-reference-data': dict(models=[])}
        timing = dict(models=[dict(id=m['id']) for m in self.data['models']], daily_case_ids=['old-sample'])
        costs = dict(models=[dict(model_id=m['id']) for m in self.data['models']])
        with (patch('scripts.timing_reference.build_reference', return_value=timing) as time,
              patch('scripts.cost_reference.build_reference', return_value=costs) as cost):
            result = baseline_homepage(envelope, selected, self.root)
        self.assertEqual(time.call_args.kwargs['display_data'], self.data)
        self.assertEqual(cost.call_args.kwargs['display_data'], self.data)
        self.assertEqual(result['supplemental']['timing-reference-data']['daily_case_ids'], ['old-sample'])
        self.assertEqual(envelope['supplemental']['timing-reference-data']['daily_case_ids'], ['new-sample'])


if __name__ == '__main__':
    unittest.main()
