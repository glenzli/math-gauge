#!/usr/bin/env python3
"""Verify supplemental audit sources and recompute private/public rate reports."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from math_gauge.content_rates import project_rates, validate_review, verify_sources
from math_gauge.goal_attainment import goal_contract, validate_goal_review
from math_gauge.scoring import score_content_rates
from math_gauge.records import selected_cli_records


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(private_root, *, public_root=ROOT, write=False, version='0.2.0'):
    public, private = Path(public_root).resolve(), Path(private_root).resolve()
    policy_path = public / 'protocol/scoring-policy.json'
    policy = json.loads(policy_path.read_bytes())
    contracts, products, summaries, goals_contract = {}, [], [], None
    for model, folder in selected_cli_records(public):
        relative = folder.relative_to(public)
        public_folder, private_folder = public / relative, private / relative
        review_path = private_folder / 'content-rate-review.json'
        review = json.loads(review_path.read_bytes())
        source = json.loads((private_folder / 'retry-result.json').read_bytes())
        expected = {
            'record_sha256': sha(public_folder / 'record.json'),
            'assessment_result_sha256': sha(public_folder / 'retry-combined-aggregate.json'),
            'assessment_policy_sha256': sha(policy_path),
            'method_policy_sha256': sha(public / 'protocol/content-rate-policy.json'),
        }
        if review['source_bindings'] != expected or review['model_id'] != model:
            raise ValueError('Supplemental audit binds another record or policy')
        validate_review(review, policy, source)
        verified = verify_sources(review, {'public': public, 'private': private})
        for task in review['tasks']:
            contract = (task['case_id'], task['subcategory'], task['family_id'],
                        [(u['id'], u['label'], u['delivery_weight'], u['claim_weight'])
                         for u in task['units']])
            if contracts.setdefault(task['id'], contract) != contract:
                raise ValueError('Models must share exact target units and weights')
        report = score_content_rates(review, policy)
        report['private_review_sha256'] = sha(review_path)
        legacy = project_rates(report)
        # The old fine-unit coverage remains reproducible under its original name
        # and policy. Never rename its numbers as complete-goal attainment.
        products.extend(((private_folder / 'content-rates-report-v0.1.0.json', report),
                         (public_folder / 'content-rate-coverage-v0.1.0.json', legacy),
                         (public_folder / 'content-rate-policy.json',
                          (public / 'protocol/content-rate-policy.json').read_text())))
        if version == '0.2.0':
            goals_path = private_folder / 'goal-attainment-review.json'
            goals = json.loads(goals_path.read_bytes())
            expected.update(method_policy_sha256=sha(public / 'protocol/goal-attainment-policy.json'),
                            content_review_sha256=sha(review_path),
                            content_method_policy_sha256=sha(public / 'protocol/content-rate-policy.json'))
            if goals['source_bindings'] != expected:
                raise ValueError('Whole-goal audit binds another source or method')
            validate_goal_review(goals, review, policy, source)
            verified += verify_sources(goals, {'public': public, 'private': private})
            contract = goal_contract(goals['tasks'])
            if goals_contract is not None and contract != goals_contract:
                raise ValueError('Models must share exact complete goals and weights')
            goals_contract = contract
            report = score_content_rates(review, policy, goals)
            report.update(private_review_sha256=sha(review_path),
                          private_goal_review_sha256=sha(goals_path))
            products.append((public_folder / 'goal-attainment-policy.json',
                             (public / 'protocol/goal-attainment-policy.json').read_text()))
        elif version != '0.1.0':
            raise ValueError('Unsupported content-rate method')
        projection = project_rates(report)
        if version == '0.2.0':
            products.extend(((private_folder / 'content-rates-report.json', report),
                             (public_folder / 'content-rates.json', projection)))
        summaries.append({'model': model, 'metrics': projection['metrics'],
                          'verified_source_files': len(verified)})
    # Resolve and validate every source before changing either repository's outputs.
    for path, value in products:
        raw = value if isinstance(value, str) else json.dumps(value, ensure_ascii=False, indent=2) + '\n'
        if write:
            path.write_text(raw)
        elif not path.is_file() or path.read_text() != raw:
            raise ValueError('Saved content rates differ from source-bound recomputation')
    return {'status': 'passed', 'version': version, 'candidate_calls': 0,
            'models': summaries, 'written': write}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--private-root', type=Path, required=True)
    parser.add_argument('--public-root', type=Path, default=ROOT)
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--version', choices=('0.1.0', '0.2.0'), default='0.2.0',
                        help='v0.1 checks only the preserved fine-unit coverage archive')
    args = parser.parse_args()
    print(json.dumps(run(args.private_root, public_root=args.public_root, write=args.write, version=args.version),
                     ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
