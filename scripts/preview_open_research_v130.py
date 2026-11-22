#!/usr/bin/env python3
"""Project published baselines as unmeasured new-task rows, plus synthetic fixtures."""
import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from math_gauge.taste_v130 import POLICY_FILE, preview


def public_row(identifier, label, report, *, kind="synthetic-fixture"):
    """Deliberate display projection. No manuscript, gate, reason, quote or task ID."""
    states = {
        'not-run': 'not-tested', 'review-pending': 'unreviewed',
        'invalid': 'insufficient-evidence', 'reviewed': 'insufficient-evidence',
        'delivery-failed': 'delivery-failed',
    }
    return dict(id=identifier, label=label, kind=kind, delivery=dict(planned=45,normal=0,unknown=45),
        base_smc=report['legacy_scores']['SMC'],
        components={axis: dict(state='reviewed' if value is not None else states[report['status']],
                              value=value, strict=report['strict_verdicts'][axis]) for axis, value in report['subscores'].items()},
        task_strict=report['item_strict'], item=report['item_composite'],
        coverage={k: report['coverage'][k] for k in ('planned', 'reviewed', 'components_planned', 'components_reviewed')},
        strict_overall=report['strict_overall'], composites=report['composite_by_base'],
        confirmed=report['confirmed_by_base'], strict_confirmed=report['strict_confirmed'],
        composite=report['composite_by_base']['RMC'])


def fixture_data():
    rows = []
    specs = [('fixture-alpha', '示例 A', 85, (45, 65, 80), (True, True, True), 'reviewed'),
             ('fixture-beta', '示例 B', 75, (0, 40, 20), (False, False, False), 'reviewed'),
             ('fixture-gamma', '示例 C', 65, (70, None, 60), (True, None, False), 'reviewed'),
             ('fixture-delta', '示例 D', 55, None, None, 'not-run'),
             ('fixture-epsilon', '示例 E', 45, None, None, 'review-pending')]
    for identifier, label, score, values, strict, status in specs:
        review = None if values is None else {axis: dict(score=v, strict=s)
            for axis, v, s in zip(('autonomy', 'taste', 'capacity'), values, strict)}
        result = preview(dict(MC=score, RMC=score, SMC=score),
            dict(initiative=50, discernment=50, open_research=50), status=status, review=review, base_groups={m:dict.fromkeys(('written','lean','research'),score) for m in ('MC','RMC','SMC')})
        rows.append(public_row(identifier, label, result))
    policy = json.loads(POLICY_FILE.read_bytes())
    return dict(schema='math-gauge.research-board-preview/v1', edition='1.3.0',
        kind='synthetic-fixture', category=policy['category'], rank_eligible=False,
        default_order='retained-base-SMC', weights_ratified=False, rows=rows)


def baseline_data(source_data=None, *, policy_path=POLICY_FILE):
    import hashlib
    source = ROOT / 'site/data.json'
    raw = source.read_bytes() if source_data is None else json.dumps(source_data, ensure_ascii=False, separators=(',', ':')).encode()
    data = json.loads(raw)
    if data['benchmark_version'] != '1.2.0':
        raise ValueError('Explicit 1.2 baseline projection required')
    def order(model):
        ranks = model['ranking_values']
        return tuple((ranks.get(k) is None, -(ranks.get(k) or 0))
                     for k in ('strict', 'partial', 'capability')) + ((False, model['display_order']),)
    rows = []
    for model in sorted(data['models'], key=order):
        reports = dict(MC=model['capability']['nonlogical_retry_3'],
                       RMC=model['retry']['combined'], SMC=model['strict']['nonlogical_retry_3'])
        base, groups = {}, {}
        for mode, report in reports.items():
            value = report['metrics']['overall']
            # Exact source values are authoritative; do not use rounded ranking cells.
            base[mode] = value['exact'] if value['exact'] is not None else {
                key: value[key] for key in ('lower', 'upper', 'exact')}
        for mode, report in reports.items():
            groups[mode] = {g: (report['metrics'][g]['exact'] if report['metrics'][g]['exact'] is not None else {k: report['metrics'][g][k] for k in ('lower','upper','exact')}) for g in ('written','lean','research')}
        result = preview(base, {}, status='not-run', base_groups=groups, policy_path=policy_path)
        rows.append(public_row(model['id'], model['label'], result, kind='existing-model-unmeasured'))
    return dict(schema='math-gauge.research-board-preview/v1', edition='1.3.0',
        kind='existing-model-unmeasured', category=fixture_data()['category'], rank_eligible=False,
        default_order='retained-base-SMC', weights_ratified=False,
        source_binding=dict(edition='1.2.0', sha256=hashlib.sha256(raw).hexdigest()), rows=rows)


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
