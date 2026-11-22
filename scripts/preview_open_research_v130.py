#!/usr/bin/env python3
"""Project published baselines as unmeasured new-task rows, plus synthetic fixtures."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from math_gauge import independent_research_adoption as adoption
from math_gauge import independent_research_score_modes as modes
from math_gauge import legacy_taste
from math_gauge.taste_v130 import POLICY_FILE
from math_gauge.research_profile import POLICY_FILE as PROFILE_POLICY_FILE, SCHEMA as PROFILE_SCHEMA
from math_gauge.research_profile import STAGES, load_policy as load_profile_policy, project_models

ABILITY_FIELD = 'independent_research_abilities'


def public_row(identifier, label, report, *, kind="synthetic-fixture"):
    """Deliberate display projection. No manuscript, gate, reason, quote or task ID."""
    states = {
        'not-run': 'not-tested', 'review-pending': 'unreviewed',
        'invalid': 'insufficient-evidence', 'reviewed': 'insufficient-evidence',
        'delivery-failed': 'delivery-failed',
    }
    row = dict(id=identifier, label=label, kind=kind, delivery=dict(planned=45,normal=0,unknown=45),
        base_smc=report['legacy_scores']['SMC'],
        components={axis: dict(state='reviewed' if value is not None else states[report['status']],
                              value=value, strict=report['strict_verdicts'][axis]) for axis, value in report['subscores'].items()},
        task_strict=report['item_strict'], item=report['item_composite'],
        coverage={k: report['coverage'][k] for k in ('planned', 'reviewed', 'components_planned', 'components_reviewed')},
        strict_overall=report['strict_overall'], composites=report['composite_by_base'],
        confirmed=report['confirmed_by_base'], strict_confirmed=report['strict_confirmed'],
        composite=report['composite_by_base']['RMC'])
    if 'score_modes' in report:
        row['score_modes'] = report['score_modes']
        row['criteria'] = report['criteria']
        for axis, value in row['components'].items():
            state = row['score_modes']['RMC']['components'][axis]['state']
            value['state'] = 'unreviewed' if state == 'review-pending' else state
    return row


def fixture_data():
    policy, _ = modes.load_policy()
    rows = []
    specs = [('fixture-alpha', '示例 A', 85, (45, 65, 80), (2, 3, 4), 'reviewed'),
             ('fixture-beta', '示例 B', 75, (0, 40, 20), (0, 1, 2), 'reviewed'),
             ('fixture-gamma', '示例 C', 65, (70, None, 60), (2, None, 4), 'reviewed'),
             ('fixture-delta', '示例 D', 55, None, None, 'not-run'),
             ('fixture-epsilon', '示例 E', 45, None, None, 'review-pending')]
    for identifier, label, score, values, passed_counts, status in specs:
        adopted, overlay = None, None
        if values is not None:
            rmc = dict(zip(modes.AXES, values))
            criteria = {}
            for axis, passed in zip(modes.AXES, passed_counts):
                planned = policy['strict_criteria'][axis]
                criteria[axis] = dict(planned=planned, passed=passed or 0, unknown=planned if passed is None else 0)
            strict = {axis: modes._criteria_flag(value) for axis, value in criteria.items()}
            axes = {axis: dict(mc=v + 5 if axis == 'capacity' else v, rmc=v, strict=strict[axis])
                    for axis, v in rmc.items()}
            adopted = dict(status=status, axes={axis: dict(score=v, strict=strict[axis]) for axis, v in rmc.items()})
            overlay = dict(axes=axes, criteria=criteria, mc_source_sha256='a' * 64)
        elif status == 'review-pending':
            adopted = dict(status=status, axes={axis: dict(score=None, strict=None) for axis in modes.AXES})
        base = {mode: dict(metrics={key: dict(exact=score) for key in ('overall', *modes.BASE_GROUPS)})
                for mode in modes.MODES}
        rows.append(public_row(identifier, label, modes.project_scores(base, policy, adopted=adopted, overlay=overlay)))
    return dict(schema='math-gauge.research-board-preview/v2', edition='1.3.0',
        kind='synthetic-fixture', category=json.loads(POLICY_FILE.read_bytes())['category'], rank_eligible=False,
        default_order='retained-base-SMC', weights_ratified=False, rows=rows)


def baseline_projection(source_data=None, *, policy_path=POLICY_FILE, profile_policy_path=PROFILE_POLICY_FILE,
                        score_modes_policy_path=modes.POLICY_FILE, source_bytes=None, adopted=None,
                        adopted_bytes=None, overlay_bytes=None, legacy_taste_policy_path=legacy_taste.POLICY_FILE,
                        legacy_taste_bytes=None):
    """Build versioned public rows, ability aggregates and group points from the same score result."""
    source = ROOT / 'site/data.json'
    raw = (source_bytes if source_bytes is not None else source.read_bytes() if source_data is None
           else json.dumps(source_data, ensure_ascii=False, separators=(',', ':')).encode())
    data = json.loads(raw)
    if source_data is not None and data != source_data:
        raise ValueError('Baseline bytes differ from the supplied data')
    if data['benchmark_version'] != '1.2.0':
        raise ValueError('Explicit 1.2 baseline projection required')
    source_binding = dict(edition='1.2.0', sha256=hashlib.sha256(raw).hexdigest())
    score_policy_raw = Path(policy_path).read_bytes()
    policy_sha256 = hashlib.sha256(score_policy_raw).hexdigest()
    profile_policy, profile_policy_sha256 = load_profile_policy(profile_policy_path)
    score_modes_policy, score_modes_policy_sha256 = modes.load_policy(score_modes_policy_path)
    selected, overlay, score_modes_binding = {}, {}, None
    kind = 'existing-model-unmeasured'
    if adopted is not None:
        adoption.validate_public(adopted)
        if (adopted['source_binding']['sha256'] != source_binding['sha256']
                or adopted['policy_sha256'] != policy_sha256
                or not set(adopted['cohort']) <= {m['id'] for m in data['models']}):
            raise ValueError('Adopted grades bind a different baseline, policy or selected model')
        adopted_bytes = adopted_bytes if adopted_bytes is not None else adoption.encoded(adopted)
        if json.loads(adopted_bytes) != adopted:
            raise ValueError('Adoption bytes differ from the supplied source')
        selected, kind = adopted['models'], adopted['kind']
    if overlay_bytes is not None:
        if adopted is None:
            raise ValueError('Score modes need the original settled index')
        base_index_hash = hashlib.sha256(adopted_bytes).hexdigest()
        overlay = modes.validate_public(json.loads(overlay_bytes), adopted, base_index_hash,
                                        score_modes_policy, score_modes_policy_sha256)['models']
        score_modes_binding = dict(policy_sha256=score_modes_policy_sha256,
            index_sha256=hashlib.sha256(overlay_bytes).hexdigest(), base_index_sha256=base_index_hash)
    def order(model):
        ranks = model['ranking_values']
        return tuple((ranks.get(k) is None, -(ranks.get(k) or 0))
                     for k in ('strict', 'partial', 'capability')) + ((False, model['display_order']),)
    rows, profile_reports, category_points = [], {}, {}
    for model in sorted(data['models'], key=order):
        reports = dict(MC=model['capability']['nonlogical_retry_3'],
                       RMC=model['retry']['combined'], SMC=model['strict']['nonlogical_retry_3'])
        identifier = model['id']
        result = modes.project_scores(reports, score_modes_policy, adopted=selected.get(identifier),
                                      overlay=overlay.get(identifier))
        rows.append(public_row(identifier, model['label'], result, kind=kind))
        profile_reports[identifier] = result
        category_points[identifier] = result['category_points']
    legacy_policy = json.loads(score_policy_raw)
    board = dict(schema='math-gauge.research-board-preview/v2', edition='1.3.0',
        kind=kind, category={k: legacy_policy['category'][k] for k in ('id', 'zh', 'en')}, rank_eligible=False,
        default_order='retained-base-SMC', weights_ratified=False,
        source_binding=source_binding, rows=rows, weight_frame=score_modes_policy['group_weights'])
    if adopted is not None:
        board['adoption'] = dict(batch_sha256=adopted['batch_sha256'],
            index_sha256=hashlib.sha256(adopted_bytes).hexdigest(), cohort=adopted['cohort'],
            planned_cohort=adopted['planned_cohort'], human_review='pending')
    legacy_results = None
    if legacy_taste_bytes is not None:
        _, taste_policy_sha = legacy_taste.load_policy(legacy_taste_policy_path)
        legacy_results = legacy_taste.validate_public(json.loads(legacy_taste_bytes), taste_policy_sha,
                                                      data, source_binding['sha256'])
    abilities = project_models(data, profile_reports, profile_policy, legacy_policy['new_axis_denominators'],
                              legacy_taste=legacy_results['models'] if legacy_results is not None else None)
    companion = dict(schema=PROFILE_SCHEMA, edition='1.3.0', base_edition='1.2.0', source_stages=dict(STAGES),
        source_binding=source_binding, policy_sha256=policy_sha256, profile_policy_sha256=profile_policy_sha256,
        score_modes_policy_sha256=score_modes_policy_sha256,
        taste_blend=dict(profile_policy['mathematical_taste']), by_model=abilities)
    if legacy_results is not None:
        companion['legacy_taste_binding'] = dict(policy_sha256=taste_policy_sha,
            index_sha256=hashlib.sha256(legacy_taste_bytes).hexdigest(),
            source_catalog_sha256=legacy_results['source_catalog_sha256'])
    if score_modes_binding is not None:
        board['score_modes_binding'] = score_modes_binding
        companion['score_modes_binding'] = score_modes_binding
    return board, companion, category_points


def baseline_data(source_data=None, *, policy_path=POLICY_FILE, source_bytes=None, adopted=None):
    board, _, _ = baseline_projection(source_data, policy_path=policy_path,
                                  source_bytes=source_bytes, adopted=adopted)
    del board['weight_frame']
    return board


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, default=ROOT / 'tests/fixtures/research-preview-v130.js')
    args = parser.parse_args()
    fixtures = json.dumps(fixture_data(), ensure_ascii=False, indent=2, allow_nan=False)
    baselines = json.dumps(baseline_data(), ensure_ascii=False, indent=2, allow_nan=False)
    # A standalone file:// page needs no server, fetch, network, or private source.
    args.out.write_text('globalThis.MGResearchPreviewData = ' + fixtures + ';\n'
                       + 'globalThis.MGResearchBaselineData = ' + baselines + ';\n')
    print(f'Wrote {len(baseline_data()["rows"])} unmeasured baseline rows and 5 synthetic rows; candidate calls: 0')


if __name__ == '__main__':
    main()
