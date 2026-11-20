"""Source-bound resource accounting for adopted neutral continuations.

Candidate resource use is additive, independently of mathematical score weights.
Private receipts are reduced to anonymous totals and public-case clocks here;
the website consumes the resulting public companion without reading private data.
"""
from __future__ import annotations

import argparse
from collections import Counter
import copy
from datetime import datetime, timedelta
import hashlib
import json
import math
from pathlib import Path

from math_gauge.costs import unit_cost
from math_gauge.evidence_retention import read_bytes

DATA_PATH = 'results/continuation-resources/v0.1.0/current.json'
INDEX_PATH = 'results/continuation-resources/v0.1.0/index.json'
SCHEMA = 'math-gauge.neutral-revision-resources-public/v1'
SYSTEM_EXCLUSION_REASONS = frozenset({'capacity', 'network', 'system'})


def _read(path):
    return json.loads(read_bytes(Path(path)))


def _sha(path):
    return hashlib.sha256(read_bytes(Path(path))).hexdigest()


def _number(value):
    return type(value) in (int, float) and math.isfinite(value) and value >= 0


def combine_costs(base, revision):
    """Retain unknowns and estimates while adding the actual selected usage cost."""
    complete = base.get('total_usd') is not None and revision.get('total_usd') is not None
    total = base['total_usd'] + revision['total_usd'] if complete else None
    estimated = base.get('status') == 'estimated' or revision.get('status') == 'estimated'
    interval = None
    if complete and estimated:
        a = base.get('estimate_range_usd') or [base['total_usd']] * 2
        b = revision.get('estimate_range_usd') or [revision['total_usd']] * 2
        interval = [a[0] + b[0], a[1] + b[1]]
    return {'status': 'estimated' if complete and estimated else 'observed' if complete else 'partial',
            'total_usd': total, 'known_usd': base['known_usd'] + revision['known_usd'],
            'estimate_range_usd': interval}


def combine_durations(base, revision):
    a, b = base.get('candidate_execution_seconds'), revision.get('candidate_execution_seconds')
    return {'candidate_execution_seconds': None if a is None or b is None else a + b,
            'known_candidate_execution_seconds': (base['known_candidate_execution_seconds']
                                                   + revision['known_candidate_execution_seconds']),
            'timed_calls': base['timed_calls'] + revision['timed_calls'],
            'planned_calls': base['planned_calls'] + revision['planned_calls']}


def _duration(rows):
    values = [row['seconds'] for row in rows if row.get('seconds') is not None]
    if any(not _number(value) for value in values):
        raise ValueError('Candidate duration must be observed nonnegative seconds')
    known = sum(values)
    return {'candidate_execution_seconds': known if len(values) == len(rows) else None,
            'known_candidate_execution_seconds': known, 'timed_calls': len(values),
            'planned_calls': len(rows)}


def _stamp(value):
    stamp = datetime.fromisoformat(value.replace('Z', '+00:00'))
    if stamp.tzinfo is None:
        raise ValueError('Continuation timing requires timezone-bound execution clocks')
    return stamp


def build_public(root, private_root, study):
    """Reconcile the selected 19 new calls and three original neutral pilot calls."""
    root, private_root, study = Path(root), Path(private_root), Path(study)
    selection_path = study / 'selection-evaluator-only.json'
    selection = _read(selection_path)
    selected = [row for row in selection['rows']
                if row['plan'] in {'new_written_revision', 'reuse_existing_neutral_pilot'}]
    if (len(selected) != 22 or sum(row['plan'] == 'new_written_revision' for row in selected) != 19
            or len({row['id'] for row in selected}) != 22):
        raise ValueError('Resource adoption requires the selected 19 new and three reused neutral calls')
    index_path = private_root / 'results/costs/v0.1.0/current.json'
    index = _read(index_path)
    cost_path = index_path.parent / index['selected']
    if _sha(cost_path) != index['sha256']:
        raise ValueError('Original cost inventory changed')
    inventory = _read(cost_path)
    prices = {price['id']: price for price in inventory['prices']}
    public_cost_path = root / 'results/costs/v0.1.0/current.json'
    public_costs = {row['model_id']: row for row in _read(public_cost_path)['models']}
    price_ids = {'sol-6.1-max': 'sol-standard', 'sol-6.2-max': 'sol62-standard',
                 'terra-6.1-max': 'terra-standard'}
    model_sources = {}
    evidence = {str(selection_path): _sha(selection_path), str(cost_path): _sha(cost_path),
                str(public_cost_path): _sha(public_cost_path)}
    all_new_starts, all_new_ends = [], []
    for row in selected:
        mid, cid = row['model_id'], row['case_id']
        reused = row['plan'] == 'reuse_existing_neutral_pilot'
        binding = None
        if reused:
            binding_path = study / 'reused' / mid / 'source-binding.json'
            binding = _read(binding_path)
            evidence[str(binding_path)] = _sha(binding_path)
            if binding.get('arm') != 'neutral' or binding.get('not_a_new_candidate_call') is not True:
                raise ValueError('Only the original neutral pilot arm is adopted')
            execution_path = Path(binding['native_evidence_source_bindings']['runtime/execution.json']['path'])
            events_path = Path(binding['native_evidence_source_bindings']['output/events.ndjson']['path'])
            for path, key in ((execution_path, 'runtime/execution.json'), (events_path, 'output/events.ndjson')):
                if _sha(path) != binding['native_evidence_source_bindings'][key]['sha256']:
                    raise ValueError('Reused neutral pilot resource bytes changed')
        else:
            session = study / 'engineering/sessions' / row['id']
            execution_path, events_path = session / 'runtime/execution.json', session / 'output/events.ndjson'
        execution = _read(execution_path)
        if execution.get('status') != 'completed' or execution.get('request_count') != 1:
            raise ValueError('Adopted resource receipt must retain its actual completed request')
        evidence[str(execution_path)], evidence[str(events_path)] = _sha(execution_path), _sha(events_path)
        native = [json.loads(line) for line in read_bytes(events_path).decode().splitlines()]
        terminals = [event for event in native if event.get('type') == 'turn.completed']
        if len(terminals) != 1 or terminals[0].get('usage') != execution.get('usage'):
            raise ValueError('Execution usage differs from the original native terminal receipt')
        if reused:
            seconds = binding['selection_contract']['native_terminal_seconds_from_request']
        else:
            seal_path = session / 'runtime/seal.json'
            seal = _read(seal_path)
            if seal.get('trigger') != 'first-native-terminal':
                raise ValueError('Continuation timing must stop at the first observed native terminal')
            evidence[str(seal_path)] = _sha(seal_path)
            seconds = (_stamp(seal['trigger_observed_utc']) - _stamp(execution['started_utc'])).total_seconds()
        if not _number(seconds):
            raise ValueError('Adopted continuation has no observed candidate duration')
        usage = execution['usage']
        unit = {'usage': usage, 'convention': 'input_includes_cache', 'price_id': price_ids[mid]}
        cost, tokens = unit_cost(unit, prices)
        start = _stamp(execution['started_utc'])
        end = start + timedelta(seconds=seconds)
        if not reused:
            all_new_starts.append(start)
            all_new_ends.append(end)
        model_sources.setdefault(mid, []).append({'case_id': cid, 'seconds': seconds, 'cost_usd': cost,
            'tokens': tokens, 'reused': reused, 'start': start, 'end': end,
            'requested_model': execution.get('requested_model'), 'observed_model': execution.get('observed_model')})
    models = []
    for mid, calls in model_sources.items():
        base_cost = public_costs[mid]
        original = next(model for model in inventory['models'] if model['model_id'] == mid)
        if original['record_id'] != base_cost['record_id']:
            raise ValueError('Resource base cost selects another source record')
        archive = 'results/v1.0.0' if mid == 'sol-6.2-max' else 'results/v0.6.0'
        timing_path = private_root / archive / mid / original['record_id'] / 'answer-timings.json'
        timing = _read(timing_path)
        slots = {slot['id']: slot for slot in original['slots']}
        if (len(timing['rows']) != 42 or {row['id'] for row in timing['rows']} != set(slots)
                or any(row['answer_sha256'] != slots[row['id']]['answer_sha256'] for row in timing['rows'])):
            raise ValueError('Original candidate timings do not bind the selected 39 plus three answers')
        evidence[str(timing_path)] = _sha(timing_path)
        base = {**_duration(timing['rows']), **{key: copy.deepcopy(base_cost[key]) for key in
            ('status', 'total_usd', 'known_usd', 'estimate_range_usd', 'coverage', 'pricing_basis')}}
        total = sum(call['cost_usd'] for call in calls)
        new = [call for call in calls if not call['reused']]
        revision = {**_duration(calls), 'status': 'observed', 'total_usd': total, 'known_usd': total,
            'estimate_range_usd': None, 'new_calls': len(new), 'reused_calls': len(calls) - len(new),
            'batch_span_seconds': (max(call['end'] for call in new) - min(call['start'] for call in new)).total_seconds(),
            'tokens': {key: sum(call['tokens'][key] for call in calls) for key in
                       ('uncached_input_tokens', 'cached_input_tokens', 'cache_write_input_tokens', 'output_tokens', 'total_tokens')},
            'pricing_basis': 'unchanged_standard_api_reference',
            'duration_basis': 'request_start_to_first_observed_native_terminal',
            'price_id': price_ids[mid], 'rates_per_million': copy.deepcopy(prices[price_ids[mid]]['rates_per_million']),
            'actual_backend_sku': None,
            'observed_model': next(iter({call['observed_model'] for call in calls}))
                              if len({call['observed_model'] for call in calls}) == 1 else None}
        task_path = root / archive / mid / original['record_id'] / 'public-task-scores.json'
        public_ids = {task['case_id'] for task in _read(task_path)['views']['partial']['nonlogical_retry_3']['tasks']}
        models.append({'id': mid, 'record_id': original['record_id'], 'base': base, 'revision': revision,
            'combined': {**combine_costs(base, revision), **combine_durations(base, revision)},
            'public_cases': [{'case_id': call['case_id'], 'seconds': call['seconds'],
                              'reused': call['reused']} for call in calls if call['case_id'] in public_ids]})
    evidence_hash = hashlib.sha256(json.dumps(evidence, sort_keys=True).encode()).hexdigest()
    return {'schema': SCHEMA, 'version': '0.1.0', 'benchmark_version': '1.2.0',
        'base_assessment_version': '1.1.0', 'selection': 'adopted_neutral_continuations_once',
        'selected_calls': 22, 'new_calls': 19, 'reused_calls': 3,
        'new_candidate_calls_for_accounting': 0, 'score_weight_applied_to_resources': False,
        'review_calls_included': False, 'grade_feedback_arm_included': False,
        'batch_span_seconds': (max(all_new_ends) - min(all_new_starts)).total_seconds(),
        'batch_span_scope': 'nineteen_new_continuations_excludes_earlier_reused_pilot',
        'source_evidence_sha256': evidence_hash, 'models': models}


def _validate_public(document):
    if (document.get('schema') != SCHEMA or document.get('benchmark_version') != '1.2.0'
            or document.get('score_weight_applied_to_resources') is not False
            or document.get('grade_feedback_arm_included') is not False
            or sum(row['revision']['planned_calls'] for row in document['models']) != document['selected_calls']):
        raise ValueError('Invalid adopted continuation resource companion')
    for model in document['models']:
        revision = model['revision']
        if 'system_exclusions' in revision:
            counts = revision['system_failure_reasons']
            if (not counts or set(counts) - SYSTEM_EXCLUSION_REASONS
                    or any(type(count) is not int or count <= 0 for count in counts.values())
                    or sum(counts.values()) != revision['system_exclusions']
                    or revision['physical_requests'] != revision['effective_attempts'] + revision['system_exclusions']):
                raise ValueError('Invalid continuation system-retry counts')
    return document


def load_public(root):
    """Compose disjoint immutable companions; never overwrite a bound old file."""
    from math_gauge.records import evidence_bytes
    root = Path(root)
    index_path = root / INDEX_PATH
    if not index_path.is_file():
        return _validate_public(_read(root / DATA_PATH))
    index = _read(index_path)
    if (index.get('schema') != 'math-gauge.neutral-revision-resources-index/v1'
            or index.get('version') != '0.1.0' or index.get('benchmark_version') != '1.2.0'
            or not isinstance(index.get('sources'), list) or not index['sources']
            or len({item['path'] for item in index['sources']}) != len(index['sources'])
            or DATA_PATH not in {item['path'] for item in index['sources']}):
        raise ValueError('Invalid immutable continuation resource index')
    documents = [_validate_public(json.loads(evidence_bytes(root, ref))) for ref in index['sources']]
    models, seen = [], set()
    for document in documents:
        for model in document['models']:
            if model['id'] in seen:
                raise ValueError('Continuation resource companions overlap by model')
            seen.add(model['id'])
            models.append(copy.deepcopy(model))
    if len(documents) == 1:
        return documents[0]
    return {'schema': SCHEMA, 'version': '0.1.0', 'benchmark_version': '1.2.0',
        'base_assessment_version': '1.1.0', 'selection': 'adopted_neutral_continuations_once',
        'selected_calls': sum(item['selected_calls'] for item in documents),
        'new_calls': sum(item['new_calls'] for item in documents),
        'reused_calls': sum(item['reused_calls'] for item in documents),
        'new_candidate_calls_for_accounting': 0, 'score_weight_applied_to_resources': False,
        'review_calls_included': False, 'grade_feedback_arm_included': False,
        'batch_span_seconds': None, 'batch_span_scope': 'multiple_separately_frozen_native_batches',
        'source_evidence_sha256': hashlib.sha256(json.dumps(index['sources'], sort_keys=True).encode()).hexdigest(),
        'source_companions': copy.deepcopy(index['sources']), 'models': models}


def _system_exclusions(private_root, model_id, record_id, deliveries, evidence):
    from math_gauge.neutral_revision import DIRECTORY
    from math_gauge.records import evidence_bytes

    path = private_root / DIRECTORY / model_id / record_id / 'resource-system-exclusions.json'
    if not path.is_file():
        return {}
    raw = read_bytes(path)
    decision = json.loads(raw)
    if (decision.get('schema') != 'math-gauge.neutral-revision-system-exclusions/v1'
            or decision.get('benchmark_version') != '1.2.0'
            or decision.get('authority') != 'user_confirmed_after_observation'
            or decision.get('model_id') != model_id or decision.get('record_id') != record_id
            or not decision.get('attempts')):
        raise ValueError('Invalid continuation system exclusion')
    priors = {attempt['native_execution']['sha256']: attempt
              for delivery in deliveries for attempt in delivery.get('prior_attempts', [])}
    excluded = {}
    for item in decision['attempts']:
        digest = item['native_execution']['sha256']
        prior = priors.get(digest)
        if (prior is None or digest in excluded or item['reason'] not in SYSTEM_EXCLUSION_REASONS
                or prior['model_id'] != model_id or prior['case_id'] != item['case_id']
                or prior.get('normal_final_delivered') is True):
            raise ValueError('System exclusion must bind one failed attempt before the selected delivery')
        for key in ('native_execution', 'seal', 'native_events'):
            ref = item[key]
            evidence_bytes(private_root, ref)
            if any(ref[field] != prior[key][field] for field in ('bytes', 'sha256')):
                raise ValueError('System exclusion evidence differs from the retained attempt')
        excluded[digest] = item['reason']
    evidence[str(path)] = hashlib.sha256(raw).hexdigest()
    return excluded


def build_batch_public(root, private_root, run_root, model_id, source, deliveries):
    """Account one fully settled new model using retained tariffs and real clocks.

    The caller supplies only that model's settled source-bound deliveries. The
    returned provenance stays private; the companion has anonymous private totals
    and public-case clocks only. Missing old clocks remain unknown.
    """
    from math_gauge.records import public_assessment_case_ids
    root, private_root, run_root = Path(root), Path(private_root), Path(run_root)
    selected_ids = {row['case_id'] for row in source['selection']}
    if (not deliveries or {row['case_id'] for row in deliveries} != selected_ids
            or len(deliveries) != len(selected_ids)
            or any(row['model_id'] != model_id for row in deliveries)):
        raise ValueError('Resource companion requires the entire selected model')
    index_path = private_root / 'results/costs/v0.1.0/current.json'
    index = _read(index_path)
    cost_path = index_path.parent / index['selected']
    if _sha(cost_path) != index['sha256']:
        raise ValueError('Selected cost inventory changed')
    inventory = _read(cost_path)
    original = next(row for row in inventory['models'] if row['model_id'] == model_id)
    base_path = root / 'results/costs/v0.1.0/current.json'
    base_cost = next(row for row in _read(base_path)['models'] if row['model_id'] == model_id)
    if original['record_id'] != source['record_id'] or base_cost['record_id'] != source['record_id']:
        raise ValueError('Resource base selects another original record')
    price_ids = {unit['price_id'] for slot in original['slots'] for unit in slot.get('units', [])}
    if len(price_ids) != 1:
        raise ValueError('New continuation needs an unambiguous retained model tariff')
    price_id = next(iter(price_ids))
    prices = {row['id']: row for row in inventory['prices']}
    evidence = {str(index_path): _sha(index_path), str(cost_path): _sha(cost_path),
                str(base_path): _sha(base_path), str(run_root / 'runtime-freeze.json'): _sha(run_root / 'runtime-freeze.json')}
    timing_path = private_root / Path(source['source_record']['path']).parent / 'answer-timings.json'
    if timing_path.is_file():
        timing = _read(timing_path)
        slots = {slot['id']: slot for slot in original['slots']}
        if (len(timing['rows']) != 42 or {row['id'] for row in timing['rows']} != set(slots)
                or any(row['answer_sha256'] != slots[row['id']]['answer_sha256'] for row in timing['rows'])):
            raise ValueError('Retained base clocks differ from the actual selected answers')
        base_duration = _duration(timing['rows'])
        evidence[str(timing_path)] = _sha(timing_path)
        base_clock_status = 'retained_source_clocks'
    else:
        base_duration = _duration([{'seconds': None} for _ in range(42)])
        base_clock_status = 'original_clocks_unavailable_remain_unknown'
    base = {**base_duration, **{key: copy.deepcopy(base_cost[key]) for key in
        ('status', 'total_usd', 'known_usd', 'estimate_range_usd', 'coverage', 'pricing_basis')}}
    physical = [attempt for row in deliveries for attempt in [*row.get('prior_attempts', []), row]]
    if len({row['native_execution']['sha256'] for row in physical}) != len(physical):
        raise ValueError('A physical continuation request was counted twice')
    exclusions = _system_exclusions(private_root, model_id, source['record_id'], deliveries, evidence)
    system_failures = Counter()
    calls, token_rows, starts, ends = [], [], [], []
    observed = set()
    physical_requests = 0
    for selected in deliveries:
        if selected.get('recovery_supplement'):
            item = selected['recovery_supplement']
            if _sha(item['path']) != item['sha256']:
                raise ValueError('Capacity recovery source supplement changed')
            evidence[item['path']] = item['sha256']
    for row in physical:
        execution_path, seal_path, events_path = (Path(row[key]['path']) for key in
            ('native_execution', 'seal', 'native_events'))
        for key, path in (('native_execution', execution_path), ('seal', seal_path), ('native_events', events_path)):
            if _sha(path) != row[key]['sha256']:
                raise ValueError('Closed continuation resource source changed')
            evidence[str(path)] = _sha(path)
        execution, seal = _read(execution_path), _read(seal_path)
        physical_requests += execution.get('request_count', 0)
        reason = exclusions.get(row['native_execution']['sha256'])
        if reason:
            if execution.get('status') != 'failed' or execution.get('request_count') != 1:
                raise ValueError('System exclusion must identify one failed physical request')
            system_failures[reason] += 1
            continue
        if seal.get('trigger') not in {'first-native-terminal', 'fixed-controller-deadline'}:
            raise ValueError('New continuation requires its actual native-terminal or deadline clock')
        start, end = _stamp(execution['started_utc']), _stamp(seal['trigger_observed_utc'])
        seconds = (end - start).total_seconds()
        if not _number(seconds):
            raise ValueError('New continuation clock is unavailable or reversed')
        starts.append(start); ends.append(end)
        observed.add(execution.get('observed_model'))
        usage = execution.get('usage')
        cost = None
        if usage is not None:
            native = [json.loads(line) for line in read_bytes(events_path).decode().splitlines()]
            terminals = [event for event in native if event.get('type') == 'turn.completed']
            if len(terminals) != 1 or terminals[0].get('usage') != usage:
                raise ValueError('Continuation usage differs from its native terminal')
            cost, tokens = unit_cost({'usage': usage, 'convention': 'input_includes_cache', 'price_id': price_id}, prices)
            token_rows.append(tokens)
        calls.append({'case_id': row['case_id'], 'seconds': seconds, 'cost_usd': cost})
    known_cost = sum(row['cost_usd'] for row in calls if row['cost_usd'] is not None)
    complete_cost = all(row['cost_usd'] is not None for row in calls)
    known_tokens = {key: sum(row[key] for row in token_rows) for key in
        ('uncached_input_tokens', 'cached_input_tokens', 'cache_write_input_tokens', 'output_tokens', 'total_tokens')}
    revision = {**_duration(calls), 'status': 'observed' if complete_cost else 'partial',
        'total_usd': known_cost if complete_cost else None, 'known_usd': known_cost,
        'estimate_range_usd': None, 'new_calls': len(calls), 'reused_calls': 0,
        'selected_tasks': len(deliveries), 'physical_requests': physical_requests,
        'effective_attempts': len(calls),
        'batch_span_seconds': (max(ends) - min(starts)).total_seconds(),
        'tokens': known_tokens if complete_cost else None, 'known_tokens': known_tokens,
        'usage_complete_calls': len(token_rows), 'pricing_basis': 'unchanged_standard_api_reference',
        'duration_basis': 'request_start_to_first_observed_native_terminal_or_cutoff',
        'price_id': price_id, 'rates_per_million': copy.deepcopy(prices[price_id]['rates_per_million']),
        'actual_backend_sku': None, 'observed_model': next(iter(observed)) if len(observed) == 1 else None}
    if system_failures:
        revision.update(system_exclusions=sum(system_failures.values()),
                        system_failure_reasons=dict(sorted(system_failures.items())))
    public_ids = set(public_assessment_case_ids(_read(root / 'protocol/scoring-policy.json')))
    provenance = {'schema': 'math-gauge.neutral-revision-resource-sources/v1',
        'model_id': model_id, 'record_id': source['record_id'], 'base_clock_status': base_clock_status,
        'original_timing_path': str(timing_path), 'price_id': price_id, 'evidence': evidence,
        'old_clocks_not_remeasured': True, 'candidate_calls_for_accounting': 0}
    public_clocks = {}
    for call in calls:
        if call['case_id'] in public_ids:
            public_clocks[call['case_id']] = public_clocks.get(call['case_id'], 0) + call['seconds']
    companion = {'schema': SCHEMA, 'version': '0.1.0', 'benchmark_version': '1.2.0',
        'base_assessment_version': '1.1.0', 'selection': 'adopted_neutral_continuations_once',
        'selected_calls': len(calls), 'selected_tasks': len(deliveries), 'new_calls': len(calls), 'reused_calls': 0,
        'new_candidate_calls_for_accounting': 0, 'score_weight_applied_to_resources': False,
        'review_calls_included': False, 'grade_feedback_arm_included': False,
        'batch_span_seconds': revision['batch_span_seconds'], 'batch_span_scope': 'one_model_frozen_gpt_batch',
        'source_evidence_sha256': hashlib.sha256(json.dumps(provenance, sort_keys=True).encode()).hexdigest(),
        'models': [{'id': model_id, 'record_id': source['record_id'], 'base': base, 'revision': revision,
            'combined': {**combine_costs(base, revision), **combine_durations(base, revision)},
            'public_cases': [{'case_id': cid, 'seconds': seconds, 'reused': False}
                for cid, seconds in sorted(public_clocks.items())]}]}
    return _validate_public(companion), provenance


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--private-root', type=Path, required=True)
    parser.add_argument('--study', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    data = build_public(args.root, args.private_root, args.study)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({'status': 'passed', 'selected_calls': data['selected_calls'], 'candidate_calls': 0}))


if __name__ == '__main__':
    main()
