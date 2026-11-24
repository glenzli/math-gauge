#!/usr/bin/env python3
"""Bind a reviewed native usage extraction to its selected three-round source."""
import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from math_gauge import independent_research_native as native
from math_gauge.costs import unit_cost
from scripts.adopt_independent_research_batch import current_index, write_projection
from scripts.adopt_independent_research_external import adoption_lock
from scripts import results_independent_research_resources as resources


def _read(base, ref):
    return native._read(base, {key: ref[key] for key in ('path', 'bytes', 'sha256')})


def _prepare_source(source_path, selection_path, public_root):
    source_path, selection_path, public_root = map(native.flow._safe_absolute,
        (source_path, selection_path, public_root))
    raw = source_path.read_bytes()
    source = native.value._json(raw)
    hydrogen = source['schema'] == 'math-gauge.hydrogen-research-resource-recovery-proposal/v1'
    neon = source['schema'] == 'math-gauge.neon-research-resource-check-proposal/v1'
    native.flow._need((hydrogen or neon) and source['extraction_only'] is True
        and source['new_candidate_calls'] == 0
        and (not hydrogen or source['new_native_receipt'] is False and source['logical_rounds'] == 3)
        and set(source['round_resources']) == set(native.flow.ROUNDS),
        'Use the retained native resource extraction, without a new execution receipt')
    adopted = native.prepare(selection_path, public_root)
    adoption_raw = (public_root / native.PUBLIC_PATH).read_bytes()
    native.flow._need(native.encoded(adopted) == adoption_raw, 'Resource selection differs from the installed native scores')
    selected = native.value._json(selection_path.read_bytes())
    mid = source['model_id']
    native.flow._need(mid in adopted['models'],
        'Resource extraction must match its one separately selected native trajectory')
    row = next(item for item in selected['models'] if item['id'] == mid)
    history_path, history_raw = _read(selection_path.parent, row['native_history'])
    history = native.value._json(history_raw)
    _, retained_raw = _read(selection_path.parent, row['retention'])
    retained = native.value._json(retained_raw)
    archive = Path(row['retention']['path']).parent
    runtime = Path(retained['original_runtime_root'])

    def read_source(ref):
        original = Path(ref['path'])
        mapped = original
        if original.is_relative_to(runtime):
            relative = original.relative_to(runtime)
            if relative.as_posix() == 'control/closed-native-history/' + history['native_conversation_id'] + '.db':
                mapped = history_path.parent / history['retained_path']
            elif relative.as_posix() == 'control/closed-native-history/retention.json':
                mapped = source_path.parent / 'source-files/closed-native-history-retention.json'
            else:
                mapped = archive / retained['retained_source_root'] / relative
        return _read(source_path.parent, dict(ref, path=str(mapped)))

    if hydrogen:
        read_source(source['source_database'])
        native.flow._need(history['native_conversation_id'] == source['source_conversation_id']
            and history['sha256'] == source['source_database']['sha256'],
            'Native resources cannot borrow a different conversation')
    else:
        native.flow._need(mid == 'gemini-4-neon-xhigh' and history['sha256'] == source['retained_database_sha256'],
            'Native resources cannot borrow a different retained conversation')
    for ref in source['source_files']:
        read_source(ref)
    manifest = json.dumps(source['source_files'], sort_keys=True,
                          **(dict(separators=(',', ':')) if hydrogen else {})).encode()
    native.flow._need(native.digest(manifest) == source['source_manifest_sha256'], 'Resource source manifest changed')
    records = source['physical_usage_records'] if hydrogen else source['private_physical_usage_records']
    count = source['usage_bearing_unique_responses'] if hydrogen else source['unique_metered_responses']
    ids = [record['native_response_id'] for record in records]
    native.flow._need(len(ids) == len(set(ids)) == count
        and all(record['counted_once'] is True and record['round'] in native.flow.ROUNDS for record in records),
        'Every metered generation, including compaction, must be counted once')
    usage = source['normalized_usage']
    native.flow._need(all(sum(record['usage'][key] for record in records) == total for key, total in usage.items())
        and all(sum(source['round_resources'][rid]['usage'][key] for rid in native.flow.ROUNDS) == total
                for key, total in usage.items()), 'Native per-response and round usage do not reconcile')
    pricing = source['pricing']
    _, price_raw = read_source(pricing['source'])
    tariff = native.value._json(price_raw)['models'][0]['revision']
    native.flow._need(pricing['price_id'] == tariff['price_id']
        and pricing['rates_per_million'] == tariff['rates_per_million'], 'Do not replace the retained API reference tariff')
    amount, tokens = unit_cost(dict(usage=usage, convention='input_excludes_cache', price_id=pricing['price_id']),
        {pricing['price_id']: dict(rates_per_million=tariff['rates_per_million'])})
    proposed_row = dict(status='observed', total_usd=amount, known_usd=amount, tokens=tokens, known_tokens=tokens,
        coverage=dict(planned=3, complete=3, partial=0, missing=0, not_run=0))
    native.flow._need(tokens == source['normalized_tokens'] and amount == source['total_usd'] == source['known_usd']
        and proposed_row == source['suggested_public_resource_row'], 'Shared cost arithmetic differs from the retained extraction')
    native.flow._need(source_path.read_bytes() == raw, 'Native usage source changed during verification')
    return mid, proposed_row, native.digest(raw)


def prepare(source_paths, selection_path, public_root):
    paths = source_paths if isinstance(source_paths, (tuple, list)) else [source_paths]
    rows, bindings = {}, {}
    for path in paths:
        mid, row, binding = _prepare_source(path, selection_path, public_root)
        native.flow._need(mid not in rows, 'Duplicate native resource extraction')
        rows[mid], bindings[mid] = row, binding
    root = native.flow._safe_absolute(public_root)
    adopted = native.load_public(root)
    raw = (root / native.PUBLIC_PATH).read_bytes()
    order = adopted['cohort']
    native.flow._need(set(rows) == set(order), 'Resource proposals must cover exactly the selected native cohort')
    evidence = next(iter(bindings.values())) if len(bindings) == 1 else native.digest(native.encoded(
        {mid: bindings[mid] for mid in order}))
    result = dict(schema=resources.NATIVE_SCHEMA, edition='1.3.0', base_edition='1.2.0',
        pricing_basis=resources.PRICING_BASIS, native_adoption_sha256=native.digest(raw),
        source_evidence_sha256=evidence, review_overhead=resources.REVIEW_OVERHEAD,
        models={mid: rows[mid] for mid in order})
    return resources.validate_native_public(result, adopted, native.digest(raw))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, required=True, action='append')
    parser.add_argument('--selection', type=Path, required=True)
    parser.add_argument('--public-root', type=Path, default=ROOT)
    parser.add_argument('--out', type=Path, required=True)
    action = parser.add_mutually_exclusive_group()
    action.add_argument('--apply', action='store_true')
    action.add_argument('--check', action='store_true')
    args = parser.parse_args()
    root, output = map(native.flow._safe_absolute, (args.public_root, args.out))
    from scripts.adopt_independent_research_native import protect_output
    protect_output(output, root, native.flow._safe_absolute(args.selection))
    source_paths = [native.flow._safe_absolute(path) for path in args.source]
    if any(output.is_relative_to(path.parent) for path in source_paths):
        raise ValueError('Keep the original private resource extraction unchanged')
    target = root / resources.NATIVE_DATA_PATH
    expected = current_index(target)
    proposal = prepare(source_paths, args.selection, root)
    raw = native.encoded(proposal)
    if args.apply or args.check:
        with adoption_lock(root):
            if current_index(target) != expected:
                raise ValueError('Native resources changed during source verification')
            adoption_raw = (root / native.PUBLIC_PATH).read_bytes()
            resources.validate_native_public(proposal, native.load_public(root), native.digest(adoption_raw))
            if args.check and expected != raw:
                raise ValueError('Installed native resources differ from the selected extraction')
            if args.apply and expected is not None:
                prior = native.value._json(expected)
                subset = dict(models={mid: native.load_public(root)['models'][mid] for mid in prior['models']})
                resources.validate_native_public(prior, subset, prior['native_adoption_sha256'])
                if any(proposal['models'].get(mid) != row for mid, row in prior['models'].items()):
                    raise ValueError('Changing settled native resources requires a source-bound correction')
            if args.apply and expected != raw:
                write_projection(target, raw, replace=expected is not None)
    write_projection(output, raw)
    print(f'Checked {len(proposal["models"])} native resource rows; candidate calls: 0; applied: {args.apply}')


if __name__ == '__main__':
    main()
