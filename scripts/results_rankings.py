"""Presentation order and ranks from retained rule-selected score reports.

No score weights, families or arithmetic are reconstructed here. ``value`` and
its bounds are copied from metrics[group_id]; rounding affects ordering/ties
only. Source result objects are never modified.
"""
from decimal import Decimal
import math
import re
from scripts.results_eligibility import ranked_models

SCORE_MODES = ("capability", "partial", "strict")
PUBLISHED_PRECISION = 2
TIE_PRIORITY = ("strict", "partial", "capability")
EFFORT_ORDER = ("max", "xhigh", "high", "medium", "low", "minimal")
VERSIONED_LABEL = re.compile(r"(.+?)\s+v?(\d+(?:\.\d+)*)(?:\s+(.*))?", re.IGNORECASE)


def mode_order(primary):
    if primary not in SCORE_MODES:
        raise ValueError("Unknown score sort mode")
    return (primary, *(mode for mode in TIE_PRIORITY if mode != primary))


def published_value(value, precision=PUBLISHED_PRECISION):
    return None if value is None else int(Decimal(f'{value:.{precision}f}') * 10 ** precision)


def model_display_key(model):
    """Group vendor and series, then order named versions and configurations."""
    label = model.get('label', model['id'])
    provider = (model.get('logo') or {}).get('label', '').casefold()
    base, separator, suffix = label.rpartition(' (')
    effort = suffix[:-1].casefold() if separator and suffix.endswith(')') else ''
    name = base if effort in EFFORT_ORDER else label
    match = VERSIONED_LABEL.fullmatch(name)
    family, version, variant = name, (), ''
    if match:
        family, number, variant = match.groups()
        number = re.sub(r'(?:\.0)+$', '', number)
        version = (*(-int(component) for component in number.split('.')), 1)
    level = EFFORT_ORDER.index(effort) if effort in EFFORT_ORDER else len(EFFORT_ORDER)
    return (not provider, provider, family.casefold(), not version, version,
            (variant or '').casefold(), level, label.casefold(), model['id'])


def set_model_display_order(models):
    for index, model in enumerate(sorted(models, key=model_display_key)):
        model['display_order'] = index


def _score_key(values, primary, precision=PUBLISHED_PRECISION):
    ordered = (published_value(values.get(mode), precision) for mode in mode_order(primary))
    return tuple((value is None, 0 if value is None else -value) for value in ordered)


def _overall_scores(model):
    earned = {mode: _selected_result(model, mode)['metrics']['earned'] for mode in SCORE_MODES}
    return ({mode: metric['confirmed'] if metric.get('confirmed') is not None else metric.get('exact')
             for mode, metric in earned.items()},
            all(metric.get('exact') is not None and metric.get('complete') is not False
                for metric in earned.values()))


def set_published_scores(model):
    values, complete = _overall_scores(model)
    model['ranking_values'] = {mode: published_value(value) for mode, value in values.items()}
    model['ranking_complete'] = complete


def overall_key(model, primary='strict'):
    values, complete = _overall_scores(model)
    return _score_key(values, primary), not complete, model_display_key(model)


def _places(signatures):
    previous, place = None, 0
    for index, signature in enumerate(signatures, 1):
        if signature is None or signature != previous:
            place = index
        yield place
        previous = signature


def overall_places(models, primary='strict'):
    ordered = sorted(ranked_models(models), key=lambda model: overall_key(model, primary))
    values = [_overall_scores(model) for model in ordered]
    signatures = (_score_key(scores, primary) if complete else None for scores, complete in values)
    return [(model, place if scores[primary] is not None else None)
            for model, (scores, _), place in zip(ordered, values, _places(signatures))]


def _selected_result(model, mode):
    # Delay this import so render_results_site may import this display helper.
    # Reuse its source-selection contract, including an equal/lower retry.
    from scripts.render_results_site import selected_result
    return selected_result(model, mode)


def _number(value):
    if value is not None and (type(value) not in (int, float) or not math.isfinite(value)):
        raise ValueError("Category metric values must be finite saved numbers or null")
    return value


def _metric_row(model_id, metric):
    exact = _number(metric.get("exact"))
    confirmed = _number(metric.get("confirmed"))
    coverage = metric.get("coverage", {})
    adjudicated = coverage.get("adjudicated", 0)
    if type(adjudicated) is not int or adjudicated < 0:
        raise ValueError("Category metric needs its saved adjudicated coverage")
    # This counts complete child categories, not all known mathematical credit.
    # Thus nonzero confirmed credit survives even when adjudicated is zero.
    value = exact if exact is not None else confirmed
    if (exact is None and (confirmed is None or confirmed == 0)
            and adjudicated == 0 and metric.get("complete") is not True):
        value = None
    incomplete = value is None or exact is None or metric.get("complete") is False
    return {"model_id": model_id, "value": value,
            "lower": _number(metric.get("lower")), "upper": _number(metric.get("upper")),
            "incomplete": incomplete, "rank": None,
            "status": "unknown" if value is None else "partial" if incomplete else "complete"}


def _rank(rows, precision, *, primary, views, models):
    def scores(mid):
        selected = {mode: views[mode][mid] for mode in SCORE_MODES}
        return (_score_key({mode: row['value'] for mode, row in selected.items()}, primary, precision),
                all(row['status'] == 'complete' for row in selected.values()))

    keys = {row['model_id']: scores(row['model_id']) for row in rows}
    ordered = sorted(rows, key=lambda row: (keys[row['model_id']][0], not keys[row['model_id']][1],
                                            model_display_key(models[row['model_id']])))
    signatures = (key if complete else None for key, complete in (keys[row['model_id']] for row in ordered))
    for row, place in zip(ordered, _places(signatures)):
        if row['value'] is not None:
            row['rank'] = place
    return ordered


def category_rankings(models, groups, *, result_selector=None, precision=PUBLISHED_PRECISION):
    """Return policy groups with independent MC/RMC/SMC ranked views.

    Two arguments suffice in render_results_site. An injected selector supports
    isolated tests; otherwise the existing selected_result(model, mode) is used.
    Group titles/weights are source metadata, never applied to metric values.
    """
    if type(precision) is not int or not 0 <= precision <= 10:
        raise ValueError("Published score precision must be between zero and ten")
    models, groups = tuple(ranked_models(models)), tuple(groups)
    ids = [model["id"] for model in models]
    if len(set(ids)) != len(ids) or any(not isinstance(mid, str) or not mid for mid in ids):
        raise ValueError("Category leaderboards need distinct source model IDs")
    group_ids = [group["id"] for group in groups]
    if len(set(group_ids)) != len(group_ids):
        raise ValueError("Category leaderboards need distinct policy groups")
    selector = _selected_result if result_selector is None else result_selector
    # Select each actual report once and use its same snapshot for every group.
    results = {(model["id"], mode): selector(model, mode)
               for model in models for mode in SCORE_MODES}
    boards = []
    for group in groups:
        rows_by_mode = {mode: [_metric_row(model['id'], results[model['id'], mode]['metrics'][group['id']])
                              for model in models] for mode in SCORE_MODES}
        lookup = {mode: {row['model_id']: row for row in rows} for mode, rows in rows_by_mode.items()}
        views = {}
        for mode in SCORE_MODES:
            views[mode] = _rank(rows_by_mode[mode], precision, primary=mode,
                                views=lookup, models={model['id']:model for model in models})
        boards.append({"id": group["id"], "title": group["title"], "weight": group["weight"], "views": views})
    return boards
