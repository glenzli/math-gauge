"""Source-bound, anonymous completion counts for adopted neutral revisions.

The private builder uses the shared scorer and authenticated adoption inputs.
The public loader only authenticates the companion and its adoption bindings.
Neither path calls a model or changes any answer, review or adopted score.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from math_gauge.neutral_revision import (MODES, CONDITION, descriptor, document,
    load_transition, load_public, verify_pair, require)
from math_gauge.scoring import score_neutral_revision_completion

DATA_PATH = 'results/continuation-completion/v0.1.0/current.json'
SCHEMA = 'math-gauge.neutral-revision-completion-public/v1'
FIXED = dict(schema=SCHEMA, version='0.1.0', benchmark_version='1.2.0',
    source_scoring_edition='1.1.0', attempt_condition=CONDITION,
    selection='all_selected_neutral_continuations',
    full_definition='all_three_unrounded_continuation_scores_equal_one',
    denominator_includes_delivery_failures=True, new_candidate_calls=0)


def _settled(adoption):
    return all(score['metrics']['earned'].get('complete') is True
               and score['metrics']['earned'].get('exact') is not None
               for score in adoption['_scores'].values())


def build_completion(root, private_root, *, transition=None):
    """Verify each whole-model adoption and reduce its selected rows privately."""
    root, private_root = Path(root), Path(private_root)
    transition = load_transition(root) if transition is None else transition
    require(transition is not None, 'Completion counts belong only to neutral revision edition 1.2.0')
    policy = json.loads((root / 'protocol/scoring-policy.json').read_bytes())
    models = []
    for mid, public_ref in transition['adoptions'].items():
        public = load_public(root, public_ref)
        private_path = Path(public_ref['path']).with_name('private.json')
        private_ref = descriptor(private_root, private_root / private_path)
        require(private_ref['sha256'] == public['private_manifest_sha256'],
                'Completion summary private manifest differs from the selected adoption')
        private = document(private_root, private_ref)
        inputs = document(private_root, private['inputs'])
        base = {mode: document(private_root, inputs['base_reports'][mode]) for mode in MODES}
        pair = verify_pair(root, private_root, public_ref, private_ref,
                           base_reports=base, assessment_policy=policy)
        summary = score_neutral_revision_completion(pair['inputs'], base=base['partial'])
        summary['settled'] = summary['settled'] and _settled(pair['public'])
        models.append(dict(id=mid, **summary, inputs_sha256=private['inputs']['sha256'],
            policy_sha256=public['policy']['sha256'], public_manifest_sha256=public_ref['sha256']))
    return dict(FIXED, models=models)


def _validate_interval(value, *, maximum, integer=False, empty=False):
    require(isinstance(value, dict) and set(value) == {'lower','upper','exact'},
            'Completion summary needs an explicit interval')
    if empty:
        require(all(v is None for v in value.values()), 'Empty selection has no full rate')
        return
    def valid(v):
        return (type(v) is int if integer else type(v) in {int,float} and math.isfinite(v)) and 0 <= v <= maximum
    lo, hi, exact = (value[key] for key in ('lower','upper','exact'))
    require(valid(lo) and valid(hi) and lo <= hi
            and (exact is None or valid(exact) and lo == hi == exact),
            'Completion summary has invalid bounds')


def load_completion(root, *, transition=None):
    """Read public aggregate data only after checking its exact source bindings."""
    root = Path(root)
    path = root / DATA_PATH
    if not path.is_file():
        return None
    transition = load_transition(root) if transition is None else transition
    require(transition is not None, 'Completion companion belongs only to edition 1.2.0')
    source = descriptor(root, path)
    data = document(root, source)
    require(isinstance(data, dict) and set(data) == set(FIXED) | {'models'}
            and all(type(data.get(k)) is type(v) and data[k] == v for k,v in FIXED.items()),
            'Invalid neutral continuation completion companion')
    rows = data['models']
    require(isinstance(rows, list) and all(isinstance(row, dict) for row in rows)
            and len({row.get('id') for row in rows}) == len(rows)
            and {row.get('id') for row in rows} == set(transition['adoptions']),
            'Completion companion lost the selected adoption model set')
    fields = {'id','selected','reviewed','delivery_failed','pending','full_count','full_rate',
              'settled','inputs_sha256','policy_sha256','public_manifest_sha256'}
    for row in rows:
        require(set(row) == fields and all(type(row[key]) is int and row[key] >= 0
            for key in ('selected','reviewed','delivery_failed','pending')),
            'Completion companion exposes only anonymous counts and opaque bindings')
        require(row['selected'] == row['reviewed'] + row['delivery_failed'] + row['pending'],
                'Completion summary changed its selected-task denominator')
        public_ref = transition['adoptions'][row['id']]
        adoption = load_public(root, public_ref)
        require(row['inputs_sha256'] == adoption['private_inputs_sha256']
                and row['policy_sha256'] == adoption['policy']['sha256']
                and row['public_manifest_sha256'] == public_ref['sha256']
                and all(row[key] == adoption['revision_counts'][key]
                        for key in ('selected','reviewed','delivery_failed','pending')),
                'Completion summary lost its exact inputs, policy or public adoption binding')
        _validate_interval(row['full_count'], maximum=row['reviewed'] + row['pending'], integer=True)
        _validate_interval(row['full_rate'], maximum=1, empty=row['selected'] == 0)
        require(row['full_count']['lower'] <= row['reviewed']
                and row['full_count']['upper'] == row['full_count']['lower'] + row['pending']
                and (row['full_count']['exact'] is None) == bool(row['pending'])
                and type(row['settled']) is bool
                and row['settled'] == (not row['pending'] and _settled(adoption)),
                'Completion summary cannot settle an unknown continuation')
    return dict(models=rows, source=source)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--private-root', type=Path, required=True)
    parser.add_argument('--out', type=Path)
    args = parser.parse_args()
    data = build_completion(args.root, args.private_root)
    out = args.out or args.root / DATA_PATH
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(data, ensure_ascii=False, indent=2, allow_nan=False) + '\n')
    if out.resolve() == (args.root / DATA_PATH).resolve():
        load_completion(args.root)
    print(json.dumps(dict(status='passed', models=len(data['models']), candidate_calls=0)))


if __name__ == '__main__':
    main()
