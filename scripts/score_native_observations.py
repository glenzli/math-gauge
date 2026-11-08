#!/usr/bin/env python3
"""Verify selected native-harness sources and recompute with shared scoring.py."""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from math_gauge.content_rates import project_rates, validate_review, verify_sources
from math_gauge.goal_attainment import validate_goal_review
from math_gauge.native_observations import (digest, load_public_record, project_score,
    read_artifact, require, validate_math_inputs, validate_record)
from math_gauge.scoring import score_content_rates, score_native_observation

MODEL = 'dot-underlying-model-20261108'
RECORD = '20261108'


def read(path):
    return json.loads(Path(path).read_bytes())


def encoded(value):
    return json.dumps(value, ensure_ascii=False, indent=2) + '\n'


def run(private_root, *, public_root=ROOT, write=False):
    public, private = Path(public_root).resolve(), Path(private_root).resolve()
    relative = Path('results/v0.6.0') / MODEL / RECORD
    pub, pri = public / relative, private / relative
    record = validate_record(read(pub / 'native-observation.json'))
    source = read(pri / 'native-observation.json')
    require(source['public_record_sha256'] == digest(pub / 'native-observation.json'),
            'Private native source binds another public record')
    math = json.loads(read_artifact(pri, source['mathematical_inputs']))
    require(record['mathematical_input_sha256'] == source['mathematical_inputs']['sha256'],
            'Native mathematical inputs changed')
    require(digest(pri / source['source_package']['path']) == source['source_package']['sha256']
            == record['source_package_sha256'], 'Original native source ZIP changed')
    original_run = json.loads(read_artifact(pri, source['run']))
    original_plan = json.loads(read_artifact(pri, source['plan']))
    inventory = json.loads(read_artifact(pri, source['raw_inventory']))
    raw_paths = {str(p.relative_to(pri)) for p in (pri / 'raw').rglob('*') if p.is_file()}
    require(raw_paths == {item['path'] for item in inventory['files']}
            and len(raw_paths) == len(inventory['files']),
            'Native raw archive lost or duplicated a source file')
    for item in inventory['files']:
        read_artifact(pri, item)
    require(source['run']['sha256'] == record['source_run_sha256']
            and source['plan']['sha256'] == record['source_plan_sha256']
            and original_plan['runtime_frozen'] is False and original_plan['runtime'] is None,
            'Original native run or preparation-only plan changed')
    deliveries = []
    for item in original_run['attempts']:
        deliveries.append((pri / 'raw/run' / item['case'] / 'sealed/answer.md', item))
    for item in original_run['selfchecks']:
        deliveries.append((pri / 'raw/run/MG-C003' / ('sealed-round-' + str(item['round'])) / 'answer.md', item))
    require(len(original_run['attempts']) == 38 and len(original_run['selfchecks']) == 3,
            'Native run lost a prescribed delivery')
    for path, item in deliveries:
        raw = path.read_bytes()
        require(len(raw) == item['answer_bytes']
                and hashlib.sha256(raw).hexdigest() == item['answer_sha256'],
                'Native sealed answer differs from its original run ledger')
    policy = json.loads(read_artifact(pub, record['assessment_policy']))
    strict = read(pub / 'strict-scoring-policy.json')
    capability = read(pub / 'capability-scoring-policy.json')
    claim = read(pub / 'claim-penalty-policy.json')
    require(digest(pub / 'assessment-policy.json') == digest(public / 'protocol/scoring-policy.json'),
            'Native mathematical aggregation must use the selected common policy')
    validate_math_inputs(math, policy)
    require({t['case_id'] for t in math['tasks']} == {t['case_id'] for t in original_plan['case_index']},
            'Native mathematical tasks differ from their original frozen case selection')
    for task in math['tasks']:
        read_artifact(pri, task['response'])
        read_artifact(pri, task['review'])
    for descriptor in math['integration_reviews']:
        read_artifact(pri, descriptor)
    verify_sources({'sources': math['source_inventory'], 'tasks': []}, {'public': public, 'private': private})
    content_path, goal_path = pri / 'content-rate-review.json', pri / 'goal-attainment-review.json'
    content, goals = read(content_path), read(goal_path)
    expected = dict(record_sha256=digest(pub / 'native-observation.json'),
        assessment_result_sha256=record['assessment_results']['nonlogical_retry_3']['sha256'],
        assessment_policy_sha256=digest(pub / 'assessment-policy.json'),
        method_policy_sha256=digest(pub / 'content-rate-policy.json'))
    require(content['source_bindings'] == expected, 'Native content review lost its source binding')
    expected.update(method_policy_sha256=digest(pub / 'goal-attainment-policy.json'),
        content_review_sha256=digest(content_path),
        content_method_policy_sha256=digest(pub / 'content-rate-policy.json'))
    require(goals['source_bindings'] == expected, 'Native complete-goal review lost its source binding')
    products, totals = [], {}
    for mode, field in (('capability', 'capability_results'), ('partial', 'assessment_results'),
                        ('strict', 'strict_results')):
        score = score_native_observation(math, policy, strict, capability, claim, mode=mode)
        totals[mode] = score['metrics']['earned']['exact']
        for condition in ('single_attempt', 'nonlogical_retry_3'):
            full = copy.deepcopy(score)
            full.update(attempt_condition=condition,
                retry_summary={'slots_with_reruns': 0, 'effective_attempts': 38},
                source_bindings={'mathematical_input_sha256': source['mathematical_inputs']['sha256'],
                    'source_plan_sha256': source['plan']['sha256'], 'source_run_sha256': source['run']['sha256']})
            name = mode + ('-retry' if condition == 'nonlogical_retry_3' else '') + '-result.json'
            raw = encoded(full)
            projection = project_score(full)
            projection['source_bindings']['private_report_sha256'] = hashlib.sha256(raw.encode()).hexdigest()
            products.extend(((pri / name, raw), (pub / record[field][condition]['path'], encoded(projection))))
            require(hashlib.sha256(encoded(projection).encode()).hexdigest() == record[field][condition]['sha256'],
                    'Recomputed native score differs from its selected record')
        if mode == 'partial':
            validate_review(content, policy, score)
            validate_goal_review(goals, content, policy, score)
    verified = verify_sources(content, {'public': public, 'private': private})
    verified += verify_sources(goals, {'public': public, 'private': private})
    rates = score_content_rates(content, policy, goals)
    rates.update(private_review_sha256=digest(content_path), private_goal_review_sha256=digest(goal_path))
    products.extend(((pri / 'content-rates-report.json', encoded(rates)),
                     (pub / 'content-rates.json', encoded(project_rates(rates)))))
    for path, raw in products:
        if write:
            path.write_text(raw)
        else:
            require(path.is_file() and path.read_text() == raw, 'Saved native report differs from shared recomputation')
    load_public_record(pub)
    return {'status': 'passed', 'harness': 'Dot native harness', 'deliveries': len(deliveries),
        'new_candidate_calls': 0, 'transport_import_validated': False,
        'scores': totals, 'rates': rates['metrics'], 'verified_source_files': len(verified), 'written': write}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--private-root', required=True, type=Path)
    parser.add_argument('--public-root', type=Path, default=ROOT)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    print(json.dumps(run(args.private_root, public_root=args.public_root, write=args.write), ensure_ascii=False, indent=2))
