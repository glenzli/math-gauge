"""Account for adopted independent research without exposing private native evidence."""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
import math
from pathlib import Path
import re

from math_gauge.costs import normalize_usage, unit_cost
from math_gauge.evidence_retention import read_bytes
from math_gauge.independent_research_adoption import PUBLIC_PATH as ADOPTION_PATH, validate_public as validate_adoption
from scripts.results_revision_resources import load_public as load_base_resources

DATA_PATH = 'protocol/mathematical-taste/v1.3.0/independent-research-resources.json'
EXTERNAL_DATA_PATH = 'protocol/mathematical-taste/v1.3.0/external-resources.json'
NATIVE_DATA_PATH = 'protocol/mathematical-taste/v1.3.0/native-resources.json'
EXTERNAL_SCHEMA = 'math-gauge.independent-research-external-resources-public/v1'
NATIVE_SCHEMA = 'math-gauge.independent-research-native-resources-public/v1'
SCHEMA = 'math-gauge.independent-research-resources-public/v1'
PRICING_BASIS = 'unchanged_standard_api_reference'
ROUNDS = ('R1', 'R2', 'R3')
USAGE_KEYS = {
    'input_tokens': 'inputTokens', 'cached_input_tokens': 'cachedInputTokens',
    'cache_write_input_tokens': 'cacheWriteInputTokens', 'output_tokens': 'outputTokens',
}
COUNTERS = (*USAGE_KEYS, 'total_tokens')
REASONING = 'reasoning_output_tokens'
TOKEN_FIELDS = ('uncached_input_tokens', 'cached_input_tokens', 'cache_write_input_tokens',
                'output_tokens', 'total_tokens', REASONING)
COVERAGE_FIELDS = ('planned', 'complete', 'partial', 'missing', 'not_run')
REVIEW_OVERHEAD = {'total_usd': None, 'tokens': None, 'candidate_cost_includes_review': False}


def _require(condition, message):
    if not condition:
        raise ValueError(message)


def _sha(raw):
    return hashlib.sha256(raw).hexdigest()


def _digest(value):
    return isinstance(value, str) and re.fullmatch(r'[0-9a-f]{64}', value) is not None


def _amount(value):
    return type(value) in (int, float) and math.isfinite(value) and value >= 0


def _count(value):
    return type(value) is int and value >= 0


def _usage(counters):
    if not isinstance(counters, dict) or not all(
        counters.get(key) is not None for key in (*USAGE_KEYS.values(), 'totalTokens')
    ):
        return None
    usage = {key: counters[native] for key, native in USAGE_KEYS.items()}
    usage[REASONING] = counters.get('reasoningOutputTokens')
    normalized = normalize_usage(usage, 'input_includes_cache')
    total = counters['totalTokens']
    _require(_count(total) and total == normalized['total_tokens'], 'Inconsistent native token total')
    return {**usage, 'total_tokens': total}


def summarize_usage(rounds, price_id, prices):
    """Count fresh usage once and preserve gaps in the reported native counters."""
    _require(0 < len(rounds) <= len(ROUNDS), 'Resource observation needs one prescribed trajectory')
    previous = dict.fromkeys((*COUNTERS, REASONING), 0)
    previous_last = None
    known = dict.fromkeys((*COUNTERS, REASONING), 0)
    coverage = dict.fromkeys(COVERAGE_FIELDS, 0)
    coverage.update(planned=len(ROUNDS), not_run=len(ROUNDS) - len(rounds))
    gap = False
    reasoning_complete = True
    for events in rounds:
        observed = incomplete = False
        for notice in events:
            total, last = _usage(notice.get('total')), _usage(notice.get('last'))
            if total is None or last is None:
                gap = incomplete = True
                continue
            if total == previous and last == previous_last and last['total_tokens'] > 0:
                continue  # An exact resend of the last cumulative snapshot.
            keys = [key for key in (*COUNTERS, REASONING)
                    if all(item[key] is not None for item in (total, last, previous))]
            delta = {key: total[key] - previous[key] for key in keys}
            _require(all(delta[key] == last[key] or gap and delta[key] > last[key] for key in keys),
                     'Native cumulative usage does not reconcile with its last update')
            for key in (*COUNTERS, REASONING):
                known[key] += last[key] if last[key] is not None else 0
            observed = True
            reasoning_complete = reasoning_complete and last[REASONING] is not None
            previous, previous_last = total, last
            gap = False
        coverage['partial' if incomplete and observed else 'complete' if observed else 'missing'] += 1
        gap = gap or not observed
    amount, tokens = unit_cost({'usage': known, 'convention': 'input_includes_cache', 'price_id': price_id}, prices)
    complete = not (coverage['missing'] or coverage['partial'])
    exact_tokens = {**tokens, REASONING: tokens[REASONING] if reasoning_complete else None} if complete else None
    return {'status': 'observed' if complete else 'partial', 'total_usd': amount if complete else None,
            'known_usd': amount, 'tokens': exact_tokens, 'known_tokens': tokens, 'coverage': coverage}


def _valid_tokens(tokens, *, exact):
    return (isinstance(tokens, dict) and set(tokens) == set(TOKEN_FIELDS)
            and all(_count(tokens[key]) for key in TOKEN_FIELDS if key != REASONING)
            and tokens['total_tokens'] == sum(tokens[key] for key in TOKEN_FIELDS if key not in ('total_tokens', REASONING))
            and (exact and tokens[REASONING] is None or _count(tokens[REASONING])
                 and tokens[REASONING] <= tokens['output_tokens']))


def validate_public(document, adoption, adoption_sha256):
    """Accept only the aggregate resource and provenance fields used publicly."""
    _require(isinstance(document, dict) and set(document) == {'schema', 'edition', 'base_edition',
        'pricing_basis', 'adoption_sha256', 'source_evidence_sha256', 'review_overhead', 'models'}
        and document['schema'] == SCHEMA and document['edition'] == '1.3.0' and document['base_edition'] == '1.2.0'
        and document['pricing_basis'] == PRICING_BASIS and document['adoption_sha256'] == adoption_sha256
        and _digest(adoption_sha256) and _digest(document['source_evidence_sha256'])
        and document['review_overhead'] == REVIEW_OVERHEAD,
        'Invalid independent research resource projection or adoption binding')
    _validate_resource_rows(document['models'], adoption)
    return document


def _validate_resource_rows(models, adoption):
    _require(isinstance(models, dict) and set(models) == set(adoption['models']),
             'Resources must cover exactly the adopted configurations')
    for mid, row in models.items():
        _require(isinstance(row, dict) and set(row) == {'status', 'total_usd', 'known_usd', 'tokens',
            'known_tokens', 'coverage'} and isinstance(row['coverage'], dict)
            and set(row['coverage']) == set(COVERAGE_FIELDS), 'Unexpected resource row fields')
        c = row['coverage']
        _require(all(_count(v) for v in c.values()) and c['planned'] == len(ROUNDS)
                 and sum(c[key] for key in COVERAGE_FIELDS[1:]) == c['planned']
                 and c['planned'] - c['not_run'] == adoption['models'][mid]['round_dispatches'],
                 'Resource coverage disagrees with the adopted round dispatches')
        _require(_amount(row['known_usd']) and _valid_tokens(row['known_tokens'], exact=False)
                 and (c['complete'] + c['partial'] > 0
                      or row['known_usd'] == row['known_tokens']['total_tokens'] == 0),
                 'Known resources require observed usage')
        if c['partial'] or c['missing']:
            _require(row['status'] == 'partial' and row['total_usd'] is None and row['tokens'] is None,
                     'Missing usage must keep exact resources unknown')
        else:
            tokens = row['tokens']
            _require(row['status'] == 'observed' and _amount(row['total_usd']) and row['total_usd'] == row['known_usd']
                     and _valid_tokens(tokens, exact=True)
                     and all(v is None or v == row['known_tokens'][key] for key, v in tokens.items()),
                     'Fully observed resources require the exact counted totals')


def load_public(root, adoption):
    root = Path(root)
    path = root / DATA_PATH
    if not path.is_file():
        return None
    raw = (root / ADOPTION_PATH).read_bytes()
    _require(adoption is not None and json.loads(raw) == adoption, 'Resource adoption is not the selected scoreboard source')
    return validate_public(json.loads(path.read_bytes()), adoption, _sha(raw))


def validate_external_public(document, adoption, adoption_sha256):
    _require(isinstance(document, dict) and set(document) == {'schema', 'edition', 'base_edition',
        'pricing_basis', 'external_adoption_sha256', 'source_evidence_sha256', 'review_overhead', 'models'}
        and document['schema'] == EXTERNAL_SCHEMA and document['edition'] == '1.3.0'
        and document['base_edition'] == '1.2.0' and document['pricing_basis'] == PRICING_BASIS
        and document['external_adoption_sha256'] == adoption_sha256 and _digest(adoption_sha256)
        and _digest(document['source_evidence_sha256']) and document['review_overhead'] == REVIEW_OVERHEAD,
        'Invalid external resource source or private fields')
    _validate_resource_rows(document['models'], adoption)
    return document


def load_external_public(root, adoption):
    from math_gauge import independent_research_external as external
    root = Path(root)
    path = root / EXTERNAL_DATA_PATH
    if not path.is_file():
        return None
    raw = (root / external.PUBLIC_PATH).read_bytes()
    _require(adoption is not None and external.load_public(root) == adoption,
             'External resources need the separate selected external adoption')
    return validate_external_public(json.loads(path.read_bytes()), adoption, _sha(raw))


def validate_native_public(document, adoption, adoption_sha256):
    _require(isinstance(document, dict) and set(document) == {'schema', 'edition', 'base_edition',
        'pricing_basis', 'native_adoption_sha256', 'source_evidence_sha256', 'review_overhead', 'models'}
        and document['schema'] == NATIVE_SCHEMA and document['edition'] == '1.3.0'
        and document['base_edition'] == '1.2.0' and document['pricing_basis'] == PRICING_BASIS
        and document['native_adoption_sha256'] == adoption_sha256 and _digest(adoption_sha256)
        and _digest(document['source_evidence_sha256']) and document['review_overhead'] == REVIEW_OVERHEAD,
        'Invalid native resource source or private fields')
    _validate_resource_rows(document['models'], adoption)
    return document


def load_native_public(root, adoption):
    from math_gauge import independent_research_native as native
    root = Path(root)
    path = root / NATIVE_DATA_PATH
    if not path.is_file():
        return None
    raw = (root / native.PUBLIC_PATH).read_bytes()
    _require(adoption is not None and native.load_public(root) == adoption,
             'Native resources need their separately selected native adoption')
    return validate_native_public(json.loads(path.read_bytes()), adoption, _sha(raw))


def summarize_external_cumulative(snapshots, price_id, prices, convention):
    """One final session cumulative counter, with all three deltas checked."""
    _require(len(snapshots) == len(ROUNDS), 'Account for the whole prescribed external trajectory')
    previous = dict.fromkeys(TOKEN_FIELDS, 0)
    for usage in snapshots:
        current = normalize_usage(usage, convention)
        _require(all(current[key] is not None and current[key] >= previous[key] for key in TOKEN_FIELDS),
                 'External cumulative counters must be explicit and nondecreasing')
        previous = current
    amount, tokens = unit_cost(dict(usage=snapshots[-1], convention=convention, price_id=price_id), prices)
    return dict(status='observed', total_usd=amount, known_usd=amount, tokens=tokens, known_tokens=tokens,
                coverage=dict(planned=3, complete=3, partial=0, missing=0, not_run=0))


def build_external_public(root, selection):
    """Read sealed operator counters; never add external models to the native plan."""
    from math_gauge import independent_research_external as external
    root, selection = map(Path, (root, selection))
    index = external.prepare(selection, root)
    adopted_raw = (root / external.PUBLIC_PATH).read_bytes()
    _require(external.encoded(index) == adopted_raw, 'External resources bind different selected source bytes')
    plan = json.loads(selection.read_bytes())
    manifests = [row for row in plan['source_evidence'] if Path(row['path']).name == 'archive-manifest.json']
    _require(len(manifests) == 1, 'External resources require the original archive manifest')
    manifest = json.loads(Path(manifests[0]['path']).read_bytes())['files']
    evidence = [index['source_binding']['adoption_sha256'], _sha(adopted_raw)]

    def read(path):
        path = Path(path)
        _require(path.is_relative_to(selection.parent), 'External resources must stay in the private archive')
        name = path.relative_to(selection.parent).as_posix()
        ref = manifest.get(name)
        raw = path.read_bytes()
        _require(ref is not None and ref['bytes'] == len(raw) and ref['sha256'] == _sha(raw),
                 'External resource receipt differs from the original retained bytes')
        evidence.append(_sha(raw))
        return raw

    base = {row['id']: row['revision'] for row in load_base_resources(root)['models']}
    models = {}
    for row in plan['models']:
        mid, state = row['id'], Path(row['state'])
        snapshots = []
        ds = mid == 'deepseek-v4.1-flash-1017'
        for rid in ROUNDS:
            if ds:
                events = [json.loads(line) for line in read(state / rid / 'evidence/events.jsonl').splitlines()]
                observed = [event['usage'] for event in events if event.get('type') == 'turn.completed']
                _require(len(observed) == 1, 'DeepSeek needs the selected normal terminal usage')
                usage = observed[0]
            else:
                observed = json.loads(read(state / rid / 'evidence/native-usage.json'))
                usage = dict(input_tokens=observed['input_tokens'], output_tokens=observed['output_tokens'],
                    cached_input_tokens=observed['cache_read_input_tokens'],
                    cache_write_input_tokens=observed['cache_creation_input_tokens'],
                    reasoning_output_tokens=observed['thinking_tokens'])
                _require(normalize_usage(usage, 'input_excludes_cache')['total_tokens'] == observed['total_tokens'],
                         'External native cumulative token total disagrees')
            snapshots.append(usage)
        price = base[mid]
        evidence.append(_sha(json.dumps(dict(price_id=price['price_id'], rates_per_million=price['rates_per_million']),
                                       sort_keys=True).encode()))
        models[mid] = summarize_external_cumulative(snapshots, price['price_id'],
            {price['price_id']: price}, 'input_includes_cache' if ds else 'input_excludes_cache')
    return validate_external_public(dict(schema=EXTERNAL_SCHEMA, edition='1.3.0', base_edition='1.2.0',
        pricing_basis=PRICING_BASIS, external_adoption_sha256=_sha(adopted_raw),
        source_evidence_sha256=_sha(json.dumps(evidence).encode()), review_overhead=REVIEW_OVERHEAD,
        models=models), index, _sha(adopted_raw))


def build_public(root, archive, checkpoint, cost_index):
    """Verify frozen archive receipts and emit only per-configuration aggregate resources."""
    from math_gauge.independent_research_execution import NATIVE_ORIGIN, parse_turn

    root, archive, checkpoint, cost_index = map(Path, (root, archive, checkpoint, cost_index))
    evidence = []

    def read(path, *refs):
        raw = read_bytes(path)
        sha = _sha(raw)
        _require(all(ref['bytes'] == len(raw) and ref['sha256'] == sha for ref in refs),
                 'Resource evidence differs from its retained descriptor')
        evidence.append(sha)
        return raw

    adopted_raw = read(root / ADOPTION_PATH)
    adopted = validate_adoption(json.loads(adopted_raw))
    frozen = json.loads(read(checkpoint))
    frozen_adoption = frozen['checkpoint_files'][f'repositories/public/{ADOPTION_PATH}']
    _require(frozen_adoption['bytes'] == len(adopted_raw) and frozen_adoption['sha256'] == _sha(adopted_raw),
             'Archive is attached to a different adoption')
    batch_manifest = json.loads(read(archive / 'batch.json'))
    replay = archive / 'replay'
    batch = json.loads(read(replay / 'batch-summary.json', batch_manifest['files']['batch-summary.json']))
    _require(batch['plan_sha256'] == adopted['batch_sha256'] and batch['origin'] == NATIVE_ORIGIN
             and [r['model_id'] for r in batch['cohort']] == adopted['cohort']
             and set(frozen['configurations']) == set(adopted['cohort']), 'Archive must match the adopted cohort and plan')
    cost = json.loads(read(cost_index))
    inventory_path = cost_index.parent / cost['selected']
    _require(inventory_path.resolve().is_relative_to(cost_index.parent.resolve()), 'Invalid cost inventory path')
    inventory_raw = read(inventory_path)
    _require(_sha(inventory_raw) == cost['sha256'], 'Retained cost inventory differs from its index')
    inventory = json.loads(inventory_raw)
    prices = {price['id']: price for price in inventory['prices']}
    base = {model['id']: model for model in load_base_resources(root)['models']}
    models, contexts, turns = {}, set(), set()
    for row in batch['cohort']:
        mid = row['model_id']
        adoption = adopted['models'][mid]
        config = json.loads(read(archive / 'configurations' / f'{mid}.json'))
        control = f'control/{mid}'
        path = f'{control}/execution.json'
        dispatches = adoption['round_dispatches']
        _require(config['model'] == mid and config['execution']['path'] == row['execution']['path'] == path
                 and config['execution_validation'] == 'passed-at-original-run-root'
                 and config['physical_round_requests'] == dispatches,
                 'Configuration lacks its original native execution validation')
        execution = json.loads(read(replay / path, row['execution'], config['execution'], config['files'][path],
                                    frozen['files'][path]))
        context = execution['native_context_id']
        outcome = 'normal-finals' if adoption['status'] == 'reviewed' else 'delivery-failed'
        _require(row['outcome'] == config['outcome'] == execution['outcome'] == outcome
                 and execution['model_id'] == mid and execution['origin'] == NATIVE_ORIGIN
                 and execution['plan_sha256'] == batch['plan_sha256']
                 and execution['registration_sha256'] == batch['registration_sha256']
                 and len(execution['rounds']) == dispatches and context not in contexts,
                 'Execution contradicts the adopted trajectory or repeats a native context')
        contexts.add(context)
        usage = []
        for index, (rid, entry) in enumerate(zip(ROUNDS[:dispatches], execution['rounds'], strict=True)):
            request_path, wire_path = f'{control}/{rid}.request.ndjson', f'{control}/{rid}.native.ndjson'
            _require(entry['round'] == rid and entry['request']['path'] == request_path
                     and entry['wire_events']['path'] == wire_path, 'Resource source uses another round')
            request = json.loads(read(replay / request_path, entry['request'], config['files'][request_path]))
            events = read(replay / wire_path, entry['wire_events'], config['files'][wire_path])
            parsed = parse_turn(request, events.splitlines(), cutoff=entry['cutoff'])
            parsed.pop('final')
            delivery = 'normal-final' if index < adoption['normal_rounds'] else 'delivery-failed'
            _require(request['method'] == 'turn/start' and request['params']['threadId'] == context
                     and request['params']['model'] == execution['requested_model']
                     and request['params']['effort'] == execution['requested_effort']
                     and all(entry[key] == value for key, value in parsed.items())
                     and parsed['turn_id'] not in turns and parsed['delivery'] == delivery,
                     'Native round usage or dispatch contradicts sealed evidence')
            turns.add(parsed['turn_id'])
            usage.append(parsed['usage_events'])
        revision = base[mid]['revision']
        price_id = revision['price_id']
        _require(prices[price_id]['rates_per_million'] == revision['rates_per_million'],
                 'Independent research must use the retained 1.2 tariff for this configuration')
        models[mid] = summarize_usage(usage, price_id, prices)
    return validate_public({'schema': SCHEMA, 'edition': '1.3.0', 'base_edition': '1.2.0',
        'pricing_basis': PRICING_BASIS, 'adoption_sha256': _sha(adopted_raw),
        'source_evidence_sha256': _sha(json.dumps(evidence).encode()),
        'review_overhead': REVIEW_OVERHEAD, 'models': models}, adopted, _sha(adopted_raw))


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path.cwd())
    parser.add_argument('--archive', type=Path)
    parser.add_argument('--checkpoint', type=Path)
    parser.add_argument('--cost-index', type=Path)
    parser.add_argument('--external-selection', type=Path)
    parser.add_argument('--out', type=Path)
    args = parser.parse_args(argv)
    if args.external_selection:
        _require(not any((args.archive, args.checkpoint, args.cost_index)), 'Select one resource source format')
        result = build_external_public(args.root, args.external_selection)
        target = EXTERNAL_DATA_PATH
    else:
        _require(all((args.archive, args.checkpoint, args.cost_index)), 'Native resources need all frozen source paths')
        result = build_public(args.root, args.archive, args.checkpoint, args.cost_index)
        target = DATA_PATH
    if args.out:
        with args.out.open('x', encoding='utf-8') as handle:
            json.dump(result, handle, ensure_ascii=False, indent=2)
            handle.write('\n')
    else:
        _require(result == json.loads((args.root / target).read_bytes()), 'Published resource counts differ from source')
        print(f"Verified {len(result['models'])} adopted cost rows from retained evidence; candidate calls: 0")


if __name__ == '__main__':
    main()
