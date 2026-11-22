"""Offline 1.3 ability companion and download contracts on synthetic data."""
import hashlib
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from math_gauge.independent_research_adoption import KIND, PUBLIC_PATH, SCHEMA
from math_gauge import independent_research_score_modes as modes
from math_gauge import independent_research_value as value
from math_gauge import legacy_taste as taste, legacy_taste_strict as strict_taste
from math_gauge.open_research import encoded, reference
from math_gauge.research_profile import POLICY_FILE as PROFILE_POLICY_FILE, POLICY_PATH as PROFILE_POLICY_PATH, VALUE_POLICY_PATH
from math_gauge.taste_v130 import POLICY_FILE
from scripts.preview_open_research_v130 import ABILITY_FIELD, baseline_projection
from scripts.results_research_preview import CONFIG, prepare_research_preview
from scripts.results_rankings import category_rankings


MEASURED, MISSING_STAGE, UNMEASURED = 'fixture-reviewed', 'fixture-first-only', 'fixture-unmeasured'
PROFILE_ONLY = 'fixture-profile-only'
MARKER = 'SYNTHETIC-PRIVATE-ABILITY-EVIDENCE'


def point(value):
    return dict(lower=value, upper=value, exact=value)


def baseline():
    models = []
    for index, identifier in enumerate((MEASURED, MISSING_STAGE, UNMEASURED)):
        metrics = {key: point(80) for key in ('overall', 'written', 'lean', 'research')}
        metrics['earned'] = dict(point(80), confirmed=80)
        report = dict(metrics=metrics)
        models.append(dict(id=identifier, label=identifier, display_order=index,
            ranking_values=dict(strict=8000, partial=8000, capability=8000),
            logo=dict(label='Fixture', data_url='fixture-logo.svg'), theme=dict(color='#336699', ink='#223344'),
            capability=dict(nonlogical_retry_3=report), retry=dict(combined=report),
            strict=dict(nonlogical_retry_3=report)))
    research_coverage = dict(unit='open_research_family', planned=5, reviewed=3)
    def family(value):
        return dict(point(value), coverage=dict(unit='mathematical_family', planned=35, reviewed=35))
    first_only = dict(id=MISSING_STAGE, metrics=dict(discernment=family(10), initiative=family(95)))
    modes_display = [dict(id=key, abbreviation=label) for key, label in
                     [('strict', 'SMC'), ('partial', 'RMC'), ('capability', 'MC')]]
    groups = [dict(id=key, title=key, weight=weight, children=[]) for key, weight in
              [('written', 35), ('lean', 35), ('research', 30)]]
    return dict(benchmark_version='1.2.0', models=models,
        profile_models=[*models, dict(id=PROFILE_ONLY)],
        score_modes=['strict', 'partial', 'capability'], display_score_modes=modes_display, chart_scenes={},
        category_leaderboards=category_rankings(models, groups), policy=dict(groups=groups, subcategories=[]),
        gap_diagnostics=dict(axis={}, tables={}),
        mathematical_profile_baseline=dict(schema='math-gauge.mathematical-profile-baseline/v1',
            benchmark_version='1.2.0', models=[first_only,
                dict(id=MEASURED, metrics=dict(discernment=family(50), initiative=family(90), depth=family(70))),
                dict(id=PROFILE_ONLY, metrics=dict(initiative=family(95)))]),
        mathematical_profile_revision=dict(schema='math-gauge.mathematical-profile-revision/v1',
            benchmark_version='1.2.0', models=[dict(id=MEASURED, metrics=dict(
                discernment=family(75), initiative=family(90), depth=family(80)))]),
        open_research=dict(schema='math-gauge.open-research/v1', benchmark_version='1.2.0', models=[
            dict(id=MEASURED, first=point(10), revision=dict(lower=40, upper=60, exact=None,
                                                          coverage=research_coverage)),
            dict(id=MISSING_STAGE, first=point(10), revision=None)]))


def selection(raw, policy):
    models = {}
    for identifier, grades in [(MEASURED, (0, 50, 70)), (MISSING_STAGE, (20, None, 0))]:
        axes = {axis: dict(score=value, strict=None if value is None else value > 0)
                for axis, value in zip(('autonomy', 'taste', 'capacity'), grades)}
        models[identifier] = dict(status='reviewed', axes=axes, normal_rounds=3,
                                  round_dispatches=3, source_sha256='a' * 64)
    return dict(schema=SCHEMA, edition='1.3.0', kind=KIND,
        source_binding=dict(edition='1.2.0', path='site/data.json', sha256=hashlib.sha256(raw).hexdigest()),
        policy_sha256=hashlib.sha256(policy).hexdigest(), review_policy_sha256='b' * 64,
        batch_sha256='c' * 64, planned_cohort=[MEASURED, MISSING_STAGE, UNMEASURED],
        cohort=list(models), models=models, native_round_dispatches=6,
        candidate_calls_by_adoption=0, reviewer=dict(requested_model='gpt-6.1-sol',
            requested_effort='max', reviewer_kind='ai', human_review='pending',
            backend_identity_independently_verified=False))


def overlay(original):
    _, policy_hash = modes.load_policy()
    old = json.loads(original)['models'][MEASURED]
    return json.dumps(dict(schema=modes.SCHEMA, edition='1.3.0', base_index_sha256=hashlib.sha256(original).hexdigest(),
        policy_sha256=policy_hash, cohort=[MEASURED], candidate_calls_by_adoption=0, models={MEASURED: dict(
            original_source_sha256=old['source_sha256'], effective_source_sha256=old['source_sha256'],
            recheck_sha256=None, mc_source_sha256='b' * 64,
            axes={axis: dict(mc=mc, rmc=grade['score'], strict=grade['strict'])
                  for (axis, grade), mc in zip(old['axes'].items(), (0, 60, 76))},
            criteria={axis: dict(planned=n, passed=p, unknown=0)
                      for (axis, n), p in zip(modes.REQUIRED_CRITERIA.items(), (1, 3, 5))})})).encode()


def legacy_fixture(root, data, raw):
    private = root / 'private-fixture'
    private.mkdir()
    proof = private / 'exact-final.md'
    proof.write_text('A synthetic trade-off. ' + MARKER)
    source = reference(proof.name, proof.read_bytes(), 'private')
    final = dict(evidence=dict(answer=source), response_sha256=source['sha256'], status='normal_final')
    cases = {MARKER + str(i): final for i in range(6)}
    selected_case = next(iter(cases))
    unrun = {cid: dict(status='unrun') for cid in cases}
    models = {mid: dict(first=cases if mid == MEASURED else unrun, revision={})
              for mid in sorted(taste.profile_model_ids(data))}
    models[PROFILE_ONLY]['revision'] = None
    models[MEASURED]['revision'] = {selected_case: final}
    private_catalogue = encoded(dict(source_binding=dict(edition='1.2.0', sha256=taste.sha256(raw)), models=models))
    review = dict(schema=taste.REVIEW_SCHEMA, version=taste.VERSION, edition=taste.EDITION,
                  condition=taste.CONDITION, source_catalog_sha256=taste.sha256(private_catalogue),
                  reviewer_id='Synthetic fixture', actual_context=MARKER, **taste.REVIEWER)
    review['judgments'] = [dict(model_id=MEASURED, stage=stage, case_id=case_id,
        response_sha256=source['sha256'], assessment_status='reviewed', score=score, enough_evidence=True,
        reason=MARKER, valid_scope=MARKER, choice_value=MARKER, condition_cost=MARKER,
        evidence=[dict(quote=MARKER)]) for stage, records in (('first', {cid:75 for cid in cases}),
                                                                ('revision', {selected_case:0}))
        for case_id, score in records.items()]
    policy, digest = taste.load_policy()
    strict_policy, strict_digest = strict_taste.load_policy()
    previous_review = encoded(review)
    strict_review = dict(review, schema=strict_taste.REVIEW_SCHEMA, version=strict_taste.VERSION,
                         policy_sha256=strict_digest, previous_review_sha256=taste.sha256(previous_review))
    strict_review['judgments'] = []
    for row in review['judgments']:
        first = row['stage'] == 'first'
        criteria = {name: dict(points=points, reason=MARKER, evidence=row['evidence']) for name, points in
                    zip(strict_taste.DIMENSIONS, (30, 20, 10) if first else (0, 0, 0))}
        strict_review['judgments'].append(dict(row, score=60 if first else 0, criteria=criteria,
            strict_checks=dict(credited_work_closed=first, scope_faithful=True, no_silent_repair=True), unresolved_kind=None))
    roots = dict(public=root, private=private)
    legacy = taste.prepare_public(roots, private_catalogue, [previous_review], policy, digest)
    strict = strict_taste.prepare_public(roots, private_catalogue, [encoded(strict_review)], [previous_review],
                                         strict_policy, strict_digest, policy, digest)
    return encoded(legacy), encoded(strict)


class ResearchAbilityProjectionTests(unittest.TestCase):
    def test_fixed_stage_denominators_and_no_feedback_into_total(self):
        data = baseline()
        raw = json.dumps(data).encode()
        selected = selection(raw, POLICY_FILE.read_bytes())
        selected_raw = json.dumps(selected).encode()
        board, companion, _ = baseline_projection(data, source_bytes=raw, adopted=selected,
                                                  adopted_bytes=selected_raw, overlay_bytes=overlay(selected_raw))
        self.assertEqual(companion['source_stages'], dict(first='first-answer', revision='revision-inclusive'))
        self.assertEqual(companion['source_binding'], board['source_binding'])
        axes = companion['by_model'][MEASURED]
        self.assertEqual(axes['open_research_autonomy']['exact'], 0)
        self.assertTrue(axes['open_research_autonomy']['comparable'])
        self.assertEqual(axes['open_research_autonomy']['observed'], 1)
        self.assertEqual(axes['open_research_autonomy']['denominator']['planned'], 1)
        self.assertEqual(axes['independent_taste']['exact'], 50)
        self.assertEqual(axes['independent_taste']['denominator']['planned'], 3)
        self.assertEqual(axes['independent_taste']['observed'], 3)
        self.assertEqual(axes['independent_taste_smc']['exact'], 100)
        first, revision = (axes['stages'][stage] for stage in ('first', 'revision'))
        self.assertEqual(first['discernment_v130']['exact'], 50)
        self.assertEqual(revision['discernment_v130']['exact'], 70)
        self.assertEqual(revision['discernment_v130']['base_coverage'],
                         dict(unit='mathematical_family', planned=35, reviewed=35))
        self.assertEqual((first['depth_v130']['exact'], revision['depth_v130']['exact']), (70, 78))
        self.assertEqual(revision['initiative_v130']['exact'], 72)
        self.assertEqual(revision['initiative_v130']['base_metric']['exact'], 90)
        capacity = revision['open_research_v130']
        self.assertAlmostEqual(capacity['lower'], 41 + 1 / 3)
        self.assertAlmostEqual(capacity['upper'], 57 + 1 / 3)
        self.assertIsNone(capacity['exact'])
        self.assertEqual(capacity['base_coverage'], dict(unit='open_research_family', planned=5, reviewed=3))
        self.assertEqual(capacity['task_coverage'], dict(unit='independent_open_research_task', planned=1,
                         reviewed=1, components_planned=2, components_reviewed=2))
        self.assertEqual(capacity['component_weights'], dict(autonomy=1, capacity=2))
        self.assertNotIn('initiative', axes)
        row = next(row for row in board['rows'] if row['id'] == MEASURED)
        self.assertEqual(row['composites']['MC']['exact'], 77.3)
        self.assertEqual(row['composites']['RMC']['exact'], 76.75)
        self.assertEqual(axes['completion_v130']['exact'], 80.75)
        self.assertEqual(axes['completion_v130']['exact'], row['strict_overall']['exact'])
        self.assertEqual(axes['completion_v130']['additional_projection_weight'], 0)
        self.assertNotIn(ABILITY_FIELD, row)

    def test_missing_stage_and_unmeasured_axes_stay_unknown(self):
        data = baseline()
        raw = json.dumps(data).encode()
        _, companion, _ = baseline_projection(data, source_bytes=raw, adopted=selection(raw, POLICY_FILE.read_bytes()))
        missing = companion['by_model'][MISSING_STAGE]
        taste = missing['independent_taste']
        self.assertEqual((taste['exact'], taste['observed'], taste['comparable']), (None, 0, False))
        self.assertAlmostEqual(missing['stages']['first']['open_research_v130']['exact'], 9 + 1 / 3)
        missing = missing['stages']['revision']
        for axis in ('discernment_v130', 'open_research_v130'):
            self.assertIsNone(missing[axis]['exact'])
            self.assertIsNone(missing[axis]['base_coverage'])
        capacity = missing['open_research_v130']
        self.assertAlmostEqual(capacity['lower'], 1 + 1 / 3)
        self.assertAlmostEqual(capacity['upper'], 81 + 1 / 3)
        self.assertEqual(capacity['task_coverage']['reviewed'], 1)
        unmeasured = companion['by_model'][UNMEASURED]
        self.assertIsNone(unmeasured['open_research_autonomy']['exact'])
        self.assertEqual(unmeasured['open_research_autonomy']['observed'], 0)
        profile_only = companion['by_model'][PROFILE_ONLY]
        initiative = profile_only['stages']['first']['initiative_v130']
        self.assertEqual((initiative['lower'], initiative['upper'], initiative['exact']), (76, 96, None))
        self.assertEqual(initiative['task_coverage']['reviewed'], 0)
        self.assertIsNone(profile_only['completion_v130']['exact'])

    def test_public_outputs_include_only_versioned_aggregates_and_keep_old_edition(self):
        data = baseline()
        raw = json.dumps(data).encode()
        previous = dict(edition='1.2.0', page='index.html', data=data)
        controllers = [f'assets/versioned/{name}.aaaaaaaaaaaa.js' for name in
                       ('results-core', 'board-controls', 'home-results', 'mathematical-profile')]
        config = json.dumps(dict(versions={'1.2.0':{}}, scripts=controllers))
        page = ('<head><link rel="stylesheet" href="assets/versioned/mathematical-profile.aaaaaaaaaaaa.css">'
                '<script type="application/json" id="edition-config">'+config+'</script></head>'
                '<main><section id="category-leaderboards"></section></main>')
        files = {'index.html': page,
                 'editions.json': '{"editions":[{"version":"1.2.0"}]}',
                 'data.json': raw.decode(), 'data/editions/1.2.0/index.json': json.dumps(previous)}
        with TemporaryDirectory() as directory:
            root = Path(directory)
            policy = json.loads(POLICY_FILE.read_bytes())
            policy['new_axis_denominators']['mathematical_taste']['review_locator'] = MARKER
            policy_bytes = json.dumps(policy).encode()
            adopted_bytes = json.dumps(selection(raw, policy_bytes)).encode()
            inputs = {str(POLICY_FILE.relative_to(POLICY_FILE.parents[3])): policy_bytes,
                      PROFILE_POLICY_PATH.as_posix(): PROFILE_POLICY_FILE.read_bytes(),
                      PUBLIC_PATH: adopted_bytes, modes.POLICY_PATH.as_posix(): modes.POLICY_FILE.read_bytes(),
                      modes.PUBLIC_PATH.as_posix(): overlay(adopted_bytes)}
            for name in ('research-preview.js', 'research-preview.css', 'edition-notes.js', 'board-controls.js',
                         'results-core.js', 'home-results.js', 'mathematical-profile.js', 'mathematical-profile.css'):
                target = 'scripts/templates/' + name
                inputs[target] = (POLICY_FILE.parents[3] / target).read_bytes()
            for name, content in inputs.items():
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(content)
            previous_legacy, strict_legacy = legacy_fixture(root, data, raw)
            (root / taste.POLICY_PATH).write_bytes(taste.POLICY_FILE.read_bytes())
            (root / taste.PUBLIC_PATH).write_bytes(previous_legacy)
            before = prepare_research_preview(files, root)
            (root / strict_taste.POLICY_PATH).write_bytes(strict_taste.POLICY_FILE.read_bytes())
            (root / strict_taste.PUBLIC_PATH).write_bytes(strict_legacy)
            outputs = prepare_research_preview(files, root)
            value_policy, _ = value.load_policy()
            value_policy['base_results_sha256'] = value._hash(inputs[modes.PUBLIC_PATH.as_posix()])
            value_policy_raw = encoded(value_policy)
            (root / value.POLICY_PATH).write_bytes(value_policy_raw)
            (root / VALUE_POLICY_PATH).write_bytes((POLICY_FILE.parents[3] / VALUE_POLICY_PATH).read_bytes())
            pending = prepare_research_preview(files, root)
            revised_result = dict(schema=value.PUBLIC, version=value.VERSION, edition='1.3.0',
                policy_sha256=value._hash(value_policy_raw), base_results_sha256=value_policy['base_results_sha256'],
                candidate_calls_by_adoption=0, cohort=[MEASURED], models={MEASURED: dict(
                    taste=dict(mc=10, rmc=0, strict=False), criteria=dict(planned=3, passed=1, unknown=0),
                    extension_level='E1', source_sha256=value._hash(MARKER.encode()))})
            (root / value.PUBLIC_PATH).write_bytes(encoded(revised_result))
            revised = prepare_research_preview(files, root)

        self.assertEqual(outputs['data.json'], files['data.json'])
        self.assertEqual(outputs['data/editions/1.2.0/index.json'], files['data/editions/1.2.0/index.json'])
        view = json.loads(outputs['data/editions/1.3.0/index.json'])['data']
        for key in ('mathematical_profile_baseline', 'mathematical_profile_revision', 'open_research'):
            self.assertEqual(view[key], data[key])
        old_view = json.loads(before['data/editions/1.3.0/index.json'])['data']
        for key in ('models', 'research_preview', 'chart_scenes', 'category_leaderboards'):
            self.assertEqual(view[key], old_view[key])
        companion = view[ABILITY_FIELD]
        self.assertNotIn('legacy_taste_binding', old_view[ABILITY_FIELD])
        before_taste = old_view[ABILITY_FIELD]['by_model'][MEASURED]['stages']['first']['mathematical_taste']
        self.assertEqual((before_taste['lower'], before_taste['upper'], before_taste['exact']), (80, 100, None))
        self.assertFalse(before_taste['legacy_review_available'])
        profiles = companion['by_model'][MEASURED]['stages']
        self.assertEqual(profiles['first']['mathematical_taste']['exact'], 92)
        self.assertEqual(profiles['revision']['mathematical_taste']['exact'], 91.6)
        self.assertTrue(profiles['first']['mathematical_taste']['legacy_review_available'])
        self.assertEqual(companion['legacy_taste_binding']['review_coverage']['assessed'], 7)
        self.assertEqual(profiles['revision']['mathematical_taste']['legacy_metric']['coverage']['planned'], 6)
        self.assertEqual(json.loads(outputs['versions/1.3.0/data.json'])[ABILITY_FIELD], companion)
        completion = companion['by_model'][MEASURED]['completion_v130']
        model = next(model for model in view['models'] if model['id'] == MEASURED)
        overall = model['strict']['nonlogical_retry_3']['metrics']['overall']
        for field in ('exact', 'lower', 'upper', 'coverage'):
            self.assertEqual(completion[field], overall[field])
        for suffix, mode, total, points in (('', 'partial', 76.75, 4.75),
                ('-strict', 'strict', 80.75, 8.75), ('-capability', 'capability', 77.3, 5.3)):
            download = json.loads(outputs[f'versions/1.3.0/downloads/{MEASURED}-combined{suffix}-retry.json'])
            self.assertEqual(download[ABILITY_FIELD], dict(companion, by_model={MEASURED: companion['by_model'][MEASURED]}))
            report = model['retry']['combined'] if mode == 'partial' else model[mode]['nonlogical_retry_3']
            self.assertEqual(report['metrics']['earned']['exact'], total)
            self.assertEqual(view['chart_scenes']['chart-groups']['bars'][MEASURED][mode]['value'], total)
            self.assertEqual(model['ranking_values'][mode], round(total * 100))
            self.assertEqual(report['contributions'][modes.ITEM]['exact'], points)
            self.assertEqual(download['category_points'][modes.ITEM]['exact'], points)
            self.assertEqual(download['metric']['exact'], total)
            self.assertEqual(download['score_modes_binding'], companion['score_modes_binding'])
        groups = [group['id'] for group in view['category_leaderboards']]
        self.assertEqual(groups, [*modes.BASE_GROUPS, modes.ITEM])
        self.assertEqual(view['policy']['groups'][-1]['children'], [])
        self.assertEqual(view['policy']['groups'][-1]['weight'], 10)
        item_board = view['category_leaderboards'][-1]
        item_chart = view['chart_scenes']['category-chart-groups-'+modes.ITEM]
        for mode, expected in zip(view['score_modes'], (87.5, 47.5, 53.0)):
            by_id = {row['model_id']: row for row in item_board['views'][mode]}
            self.assertEqual(by_id[MEASURED]['value'], expected)
            self.assertEqual(by_id[MEASURED]['rank'], 1)
            self.assertIsNone(by_id[UNMEASURED]['value'])
            self.assertIsNone(by_id[UNMEASURED]['rank'])
            self.assertEqual(item_chart['bars'][MEASURED][mode]['value'], expected)
        page = outputs['index.html']
        self.assertIn('id="category-tab-'+modes.ITEM+'"', page)
        self.assertIn('id="category-ranking-'+modes.ITEM+'"', page)
        self.assertNotIn('id="category-subcategories-'+modes.ITEM+'"', page)
        self.assertNotIn('id="independent-research-leaderboards"', page)
        installed = json.loads(CONFIG.search(page)[2])
        scripts = [Path(path).name.split('.')[0] for path in installed['scripts']]
        self.assertLess(scripts.index('results-core'), scripts.index('research-preview'))
        self.assertLess(scripts.index('research-preview'), scripts.index('board-controls'))
        payload = installed['versions']['1.3.0']['payload']
        self.assertIn(ABILITY_FIELD, outputs[payload])
        self.assertTrue(all(MARKER not in contents for contents in outputs.values()))
        self.assertTrue(all(MARKER not in contents for contents in revised.values()))
        view = json.loads(revised['data/editions/1.3.0/index.json'])['data']
        pending_view = json.loads(pending['data/editions/1.3.0/index.json'])['data']
        pending_row = next(row for row in pending_view['research_preview']['rows'] if row['id'] == MEASURED)
        row = next(row for row in view['research_preview']['rows'] if row['id'] == MEASURED)
        self.assertIsNone(pending_row['components']['taste']['value'])
        self.assertEqual(row['components'], dict(taste=dict(value=0, strict=False, state='reviewed'),
                                                   capacity=dict(value=70, strict=True, state='reviewed')))
        self.assertEqual(row['coverage']['components_planned'], 2)
        model_path = f'versions/1.3.0/downloads/{MEASURED}-combined-retry.json'
        revised_download = json.loads(revised[model_path])
        self.assertEqual(revised_download['item_weights'], dict(taste=1, capacity=2))
        self.assertEqual(revised_download[ABILITY_FIELD]['by_model'][MEASURED]['autonomous_extension']['level'], 'E1')
        self.assertEqual(revised['data/editions/1.2.0/index.json'], files['data/editions/1.2.0/index.json'])
