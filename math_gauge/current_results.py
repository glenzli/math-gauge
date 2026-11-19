"""Compose the explicitly selected assessment layer over immutable source views.

The CLI, paper and native owners continue validating their own source records.
This owner selects only an evaluator-side current projection; it never runs a
candidate, changes an original record or performs scoring arithmetic.
"""
from pathlib import Path
import json

from .editions import load_assessment_transition
from .theorem_extension_calibration import load_policy, load_public


def selected_source_record_paths(root):
    """Resolve only explicitly adopted CLI/paper/native source identities."""
    from .editions import source_edition
    from .records import selected_cli_records, selected_paper_records
    root = Path(root).resolve()
    selected = {model:(folder/'record.json').relative_to(root).as_posix()
                for model,folder in selected_cli_records(root)+selected_paper_records(root)}
    source = source_edition(root)
    compatibility = source.get('result_compatibility')
    if compatibility is not None:
        manifest = json.loads((root/compatibility['path']).read_bytes())
        native = next((row for row in manifest['selected_records']
                       if row['model_id']=='dot-underlying-model-20261108'),None)
        if native is not None:
            selected[native['model_id']] = native['record_path']
    return selected


def selected_current_record_paths(root):
    """Disjoint union for the current assessment only; source selection stays sealed."""
    from .current_assessment_admissions import record_paths
    old, fresh = selected_source_record_paths(root), record_paths(root)
    if set(old).intersection(fresh):
        raise ValueError('Initial assessments cannot replace source models')
    return dict(old, **fresh)


def selected_current_cli_records(root):
    from .records import selected_cli_records
    from .current_assessment_admissions import record_paths
    root = Path(root).resolve()
    return selected_cli_records(root) + [(mid,(root/path).parent)
                                        for mid,path in record_paths(root).items()]


def load_source_assessment(root, model_id, record_path):
    """Validate each harness's original views, then its selected older supplements."""
    from .catalog import relative_name
    from .records import load_assessment_results, load_content_rates, validate_record
    from .native_observations import load_public_record as load_native
    from .paper_observations import load_public_record as load_paper
    from .result_corrections import load_selected as load_correction
    from .c003_continuations import load_selected_public as load_c003
    root = Path(root).resolve()
    relative_name(str(record_path))
    if selected_current_record_paths(root).get(model_id) != str(record_path):
        raise ValueError('Source assessment must use the officially selected model and record')
    folder = (root / record_path).parent
    record = json.loads((root / record_path).read_bytes())
    correction = continuation = None
    if record.get('schema') == 'math-gauge.native-harness-record/v1':
        record, scores, rates = load_native(folder)
    elif record.get('record_kind') == 'paper_observation':
        record, scores, rates = load_paper(folder)
    else:
        validate_record(folder)
        scores = {mode:load_assessment_results(folder,record,mode=mode)
                  for mode in ('capability','partial','strict')}
        if any(view is None for view in scores.values()):
            raise ValueError('Current assessment requires all six original source views')
        rates = load_content_rates(folder,record)
        if record.get('initial_assessment_edition') is not None:
            from .current_assessment_admissions import load
            load(root, model_id, record=record, scores=scores)
            return record,scores,rates,None,None
        correction = load_correction(root,model_id,folder,record=record)
        if correction is not None:
            for mode in scores:
                scores[mode]['nonlogical_retry_3'] = correction['_scores'][mode]
            rates = correction.get('_rates',rates)
        continuation = load_c003(root,model_id,folder,record=record,
            effective_scores={mode:views['nonlogical_retry_3'] for mode,views in scores.items()})
        if continuation is not None:
            for mode in scores:
                scores[mode]['nonlogical_retry_3'] = continuation['_scores'][mode]
            rates = continuation.get('_rates',rates)
    return record,scores,rates,correction,continuation


def apply_current_assessment(root, model_id, record, scores):
    """Return six current views and their optional public reassessment manifest."""
    root = Path(root).resolve()
    from .current_assessment_admissions import selections, load
    if model_id in selections(root):
        current = load(root, model_id, record=record, scores=scores)
        return current['_scores'], current
    if record.get('initial_assessment_edition') is not None:
        raise ValueError('Unselected initial assessment cannot enter historical TX reassessment')
    transition = load_assessment_transition(root)
    if transition is None:
        return scores, None
    selected = transition['calibrations'].get(model_id)
    if selected is None:
        raise ValueError('Current edition has no settled TX reassessment for ' + model_id)
    policy = load_policy(root, transition['policy'])
    current = load_public(root, selected, policy=policy,
                          effective_scores=scores, source_record=record)
    if current['model_id'] != model_id:
        raise ValueError('Current reassessment selected another model')
    current['_selection'] = selected
    return current['_scores'], current


def public_reassessment_metadata(current):
    """Keep detail-page references public-only and bound to the checked layer."""
    if current is None:
        return None
    score = current['_scores']['partial']['nonlogical_retry_3']
    return {'manifest': current['_selection'], 'policy': current['policy'],
            'public_tasks': current['public_tasks'],
            'public_reviews': current['public_reviews'],
            'source_assessment_version': '1.0.0',
            'source_benchmark_version': score['source_benchmark_version'],
            'benchmark_version': current['benchmark_version']}
