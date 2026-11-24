"""Synthetic native-source boundary tests; no private manuscripts or model calls."""
from copy import deepcopy
import json
from pathlib import Path
import tempfile
import unittest

from math_gauge import independent_research_native as native
from math_gauge import independent_research_value as value
from scripts import adopt_independent_research_native as cli
from scripts import adopt_independent_research_native_resources as resource_cli
from scripts import results_independent_research_resources as resources
from scripts.cost_reference import independent_research_reference
from unittest.mock import patch


MODEL = 'gemini-4-hydrogen-xhigh'


def public_fixture():
    return dict(schema=native.SCHEMA, version='0.1.0', edition='1.3.0', source_kind=native.SOURCE_KIND,
        source_binding=dict(base_edition='1.2.0', baseline_sha256='a' * 64, adoption_sha256='b' * 64),
        policy_bindings=dict.fromkeys(native.external.POLICY_PATHS, 'c' * 64), cohort=[MODEL],
        models={MODEL: dict(status='reviewed',
            axes=dict(taste=dict(mc=90, rmc=72, strict=False), capacity=dict(mc=94, rmc=73, strict=True)),
            criteria=dict(taste=dict(planned=3, passed=1, unknown=0), capacity=dict(planned=5, passed=5, unknown=0)),
            strict_credit=dict(taste=dict(lower=55, upper=55, exact=55), capacity=dict(lower=73, upper=73, exact=73)),
            extension_level='E1', autonomy_score=100, normal_rounds=3, round_dispatches=3, source_sha256='d' * 64)},
        reviewer_kind='ai', human_review='pending', candidate_calls_by_adoption=0)


class NativeAggregateTests(unittest.TestCase):
    def test_preserves_net_credit_and_shared_two_to_one_projection(self):
        public = native.validate_public(public_fixture())
        policy, _ = value.load_policy()
        policy = dict(policy, item_weights=dict(taste=2, capacity=1))
        reports = {mode: dict(metrics={group: dict(exact=60) for group in ('overall', 'written', 'lean', 'research')})
                   for mode in ('MC', 'RMC', 'SMC')}
        result = native.project_model(reports, policy, public['models'][MODEL])
        self.assertAlmostEqual(result['score_modes']['MC']['item']['exact'], 274 / 3)
        self.assertAlmostEqual(result['score_modes']['RMC']['item']['exact'], 217 / 3)
        self.assertEqual(result['score_modes']['SMC']['item']['exact'], 61)
        self.assertEqual(result['score_modes']['SMC']['components']['capacity']['exact'], 73)
        self.assertEqual(result['composite_by_base']['SMC']['exact'], 60.1)
        self.assertNotIn('external_source_sha256', result)
        self.assertEqual(result['native_source_sha256'], 'd' * 64)

    def test_public_projection_rejects_private_inventory_and_unapproved_status(self):
        for where, key, item in [('root', 'case_id', 'SYNTHETIC-PRIVATE-ID'),
                                 ('model', 'evidence', ['SYNTHETIC-PRIVATE-QUOTE']),
                                 ('root', 'human_review', 'approved')]:
            public = public_fixture()
            target = public if where == 'root' else public['models'][MODEL]
            target[key] = item
            with self.assertRaises(ValueError):
                native.validate_public(public)

    def test_all_checkpoints_passed_retains_rmc_instead_of_automatic_full_marks(self):
        public = public_fixture()
        public['models'][MODEL]['strict_credit']['capacity'] = dict(lower=100, upper=100, exact=100)
        with self.assertRaises(ValueError):
            native.validate_public(public)

    def test_separate_native_cohort_cannot_admit_pending_or_foreign_model(self):
        for change in ('model', 'normal-final', 'calls', 'baseline'):
            public = public_fixture()
            if change == 'model':
                public['models']['gemini-4-neon-xhigh'] = public['models'].pop(MODEL)
                public['cohort'] = ['gemini-4-neon-xhigh']
            elif change == 'normal-final':
                public['models'][MODEL]['normal_rounds'] = 2
            elif change == 'calls':
                public['candidate_calls_by_adoption'] = 1
            else:
                public['source_binding']['baseline_sha256'] = 'e' * 64
            with self.assertRaises(ValueError):
                native.validate_public(public, baseline_hash='a' * 64, model_ids=[MODEL])

    def test_unknown_baseline_stays_unknown_without_changing_the_fixed_frame(self):
        public = public_fixture()
        policy, _ = value.load_policy()
        policy = dict(policy, item_weights=dict(taste=2, capacity=1))
        reports = {mode: dict(metrics={group: dict(exact=60) for group in ('overall', 'written', 'lean', 'research')})
                   for mode in ('MC', 'RMC', 'SMC')}
        reports['SMC']['metrics']['written'] = dict(exact=None, lower=0, upper=100, confirmed=0)
        result = native.project_model(reports, policy, public['models'][MODEL])
        self.assertIsNone(result['composite_by_base']['SMC']['exact'])
        self.assertEqual(result['composite_by_base']['SMC']['lower'], 42.1)
        self.assertEqual(result['composite_by_base']['SMC']['upper'], 72.1)

    def test_atomic_install_preserves_settled_bytes_and_rejects_stale_writer(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / 'site').mkdir()
            baseline = native.encoded(dict(benchmark_version='1.2.0', models=[dict(id=MODEL)]))
            (root / 'site/data.json').write_bytes(baseline)
            for name in native.external.POLICY_PATHS.values():
                target = root / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes((value.POLICY_FILE.parents[3] / name).read_bytes())
            public = public_fixture()
            public['source_binding']['baseline_sha256'] = native.digest(baseline)
            public['policy_bindings'] = native.external.policy_bindings(root)
            cli.apply_index(root, public, expected=None)
            target = root / native.PUBLIC_PATH
            original = target.read_bytes()
            with self.assertRaisesRegex(ValueError, 'changed during'):
                cli.apply_index(root, public, expected=None)
            changed = deepcopy(public)
            changed['models'][MODEL]['axes']['taste']['mc'] = 91
            with self.assertRaisesRegex(ValueError, 'settled native'):
                cli.apply_index(root, changed, expected=original)
            self.assertEqual(target.read_bytes(), original)
            self.assertEqual(native.load_public(root), public)

    def test_proposal_cannot_overwrite_original_sources(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            source = root / 'sources'
            source.mkdir()
            selection = root / 'selection.json'
            selection.write_text(json.dumps(dict(registration=dict(path=str(source / 'registration.json')),
                review_policy=dict(path=str(source / 'policy.json')), models=[])))
            with self.assertRaisesRegex(ValueError, 'outside all source'):
                cli.protect_output(source / 'replacement.json', root / 'public', selection)

    def test_native_resource_projection_cannot_borrow_a_different_adoption(self):
        tokens = dict(uncached_input_tokens=10, cached_input_tokens=20, cache_write_input_tokens=0,
                      output_tokens=4, total_tokens=34, reasoning_output_tokens=2)
        counted = dict(status='observed', total_usd=.25, known_usd=.25, tokens=tokens, known_tokens=tokens,
                       coverage=dict(planned=3, complete=3, partial=0, missing=0, not_run=0))
        document = dict(schema=resources.NATIVE_SCHEMA, edition='1.3.0', base_edition='1.2.0',
            pricing_basis=resources.PRICING_BASIS, native_adoption_sha256='a' * 64,
            source_evidence_sha256='b' * 64, review_overhead=resources.REVIEW_OVERHEAD, models={MODEL: counted})
        adopted = public_fixture()
        self.assertEqual(resources.validate_native_public(document, adopted, 'a' * 64), document)
        with self.assertRaises(ValueError):
            resources.validate_native_public(document, adopted, 'c' * 64)
        with self.assertRaises(ValueError):
            resources.validate_native_public(dict(document, native_conversation_id='PRIVATE-ID'), adopted, 'a' * 64)
        report = dict(metrics=dict(earned=dict(confirmed=40), overall=dict(exact=40, lower=40, upper=40)))
        model = dict(id=MODEL, retry=dict(combined=report), strict=dict(nonlogical_retry_3=report),
                     capability=dict(nonlogical_retry_3=report))
        base = dict(benchmark_version='1.2.0', models=[dict(model_id=MODEL, total_usd=7, known_usd=7,
            status='observed', coverage=dict(planned=42, complete=42, partial=0, missing=0, not_run=0),
            seconds=123, scores={})])
        with patch.object(resources, 'load_public', return_value=None), \
             patch.object(resources, 'load_external_public', return_value=None), \
             patch.object(resources, 'load_native_public', return_value=document):
            result = independent_research_reference('.', dict(benchmark_version='1.3.0', models=[model]),
                base, adoption=None, native_adoption=adopted)
        self.assertEqual(result['models'][0]['total_usd'], 7.25)
        self.assertEqual(result['models'][0]['coverage']['complete'], 45)
        self.assertEqual(result['models'][0]['seconds'], 123)

    def test_resource_admission_rechecks_original_bytes_and_unique_responses(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / native.PUBLIC_PATH).parent.mkdir(parents=True)
            adopted = public_fixture()
            (root / native.PUBLIC_PATH).write_bytes(native.encoded(adopted))
            def descriptor(path):
                raw = path.read_bytes()
                return dict(path=str(path), bytes=len(raw), sha256=native.digest(raw))
            database = root / 'synthetic-history.bin'
            database.write_bytes(b'SYNTHETIC-RESOURCE-HISTORY')
            history = root / 'history.json'
            history.write_bytes(native.encoded(dict(native_conversation_id='synthetic-context',
                                                    sha256=native.digest(database.read_bytes()))))
            retention = root / 'retention.json'
            retention.write_bytes(native.encoded(dict(original_runtime_root=str(root / 'runtime'), retained_source_root='source')))
            selection = root / 'selection.json'
            selection.write_bytes(native.encoded(dict(models=[dict(id=MODEL, native_history=descriptor(history), retention=descriptor(retention))])))
            price = root / 'price.json'
            rates = dict(input=1.5, cached_input=.075, cache_write=None, output=7.5)
            price.write_bytes(native.encoded(dict(models=[dict(revision=dict(price_id='reference', rates_per_million=rates))])))
            one = dict(input_tokens=2, cached_input_tokens=3, cache_write_input_tokens=0,
                       output_tokens=1, reasoning_output_tokens=1)
            total = {key: v * 3 for key, v in one.items()}
            amount, tokens = resource_cli.unit_cost(dict(usage=total, convention='input_excludes_cache', price_id='reference'),
                {'reference': dict(rates_per_million=rates)})
            proposed = dict(status='observed', total_usd=amount, known_usd=amount, tokens=tokens, known_tokens=tokens,
                            coverage=dict(planned=3, complete=3, partial=0, missing=0, not_run=0))
            files = [descriptor(database), descriptor(price)]
            source = dict(schema='math-gauge.hydrogen-research-resource-recovery-proposal/v1',
                extraction_only=True, new_native_receipt=False, new_candidate_calls=0, logical_rounds=3,
                model_id=MODEL, source_database=descriptor(database), source_conversation_id='synthetic-context',
                source_files=files,
                source_manifest_sha256=native.digest(json.dumps(files, sort_keys=True, separators=(',', ':')).encode()),
                physical_usage_records=[dict(native_response_id=rid, counted_once=True, round=rid, usage=one)
                                        for rid in native.flow.ROUNDS], usage_bearing_unique_responses=3,
                normalized_usage=total, normalized_tokens=tokens,
                round_resources={rid: dict(usage=one) for rid in native.flow.ROUNDS},
                pricing=dict(source=descriptor(price), price_id='reference', rates_per_million=rates),
                total_usd=amount, known_usd=amount, suggested_public_resource_row=proposed)
            source_path = root / 'source.json'
            source_path.write_bytes(native.encoded(source))
            with patch.object(native, 'prepare', return_value=adopted), \
                 patch.object(native, 'load_public', return_value=adopted):
                checked = resource_cli.prepare(source_path, selection, root)
                self.assertEqual(checked['models'][MODEL], proposed)
                duplicate = deepcopy(source)
                duplicate['physical_usage_records'][1]['native_response_id'] = 'R1'
                source_path.write_bytes(native.encoded(duplicate))
                with self.assertRaisesRegex(ValueError, 'counted once'):
                    resource_cli.prepare(source_path, selection, root)
                source_path.write_bytes(native.encoded(source))
                database.write_bytes(b'SUBSTITUTED-HISTORY')
                with self.assertRaisesRegex(ValueError, 'source bytes changed'):
                    resource_cli.prepare(source_path, selection, root)


    def test_fresh_acp_requires_three_actual_normal_turns_and_one_fresh_context(self):
        manifest = dict(schema='math-gauge.agy-fresh-three-round-execution/v1', model='gemini-4-neon',
            effort='xhigh', fresh_session_new=True, same_native_conversation=True, normal_finals=3,
            native_prompt_requests=3, failure=None, rounds=[{}, {}, {}])
        for key, changed in [('fresh_session_new', False), ('same_native_conversation', False),
                             ('normal_finals', 2), ('native_prompt_requests', 0), ('failure', 'ERROR')]:
            source = dict(manifest, **{key: changed})
            with self.assertRaisesRegex(ValueError, 'actual three completed'):
                native._validate_execution(None, None, None, None, source, None, None, 'gemini-4-neon-xhigh')

    def test_archived_execution_reads_exact_retained_bytes_without_runtime_fallback(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            runtime, archived = root / 'original-runtime', root / 'retained'
            runtime.mkdir(); archived.mkdir()
            (runtime / 'wire.json').write_bytes(b'ORIGINAL-SYNTHETIC-WIRE')
            (archived / 'wire.json').write_bytes(b'ORIGINAL-SYNTHETIC-WIRE')
            ref = dict(path=str(runtime / 'wire.json'), bytes=23,
                       sha256=native.digest(b'ORIGINAL-SYNTHETIC-WIRE'))
            ref['bytes'] = len(b'ORIGINAL-SYNTHETIC-WIRE')
            retained = dict(original_runtime_root=str(runtime))
            self.assertEqual(native._archived_native(archived, retained, ref), b'ORIGINAL-SYNTHETIC-WIRE')
            (archived / 'wire.json').write_bytes(b'DAMAGED-ARCHIVE')
            with self.assertRaises(ValueError):
                native._archived_native(archived, retained, ref)


if __name__ == '__main__':
    unittest.main()
