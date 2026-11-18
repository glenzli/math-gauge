"""Read-only category leaderboards from retained rule-selected score reports.

No score weights, families or arithmetic are reconstructed here. ``value`` and
its bounds are copied from metrics[group_id]; rounding affects ordering/ties
only. Source result objects are never modified.
"""
from decimal import Decimal
from datetime import date
import math

SCORE_MODES = ("capability", "partial", "strict")
PUBLISHED_PRECISION = 2
TIE_PRIORITY = ("partial", "strict", "capability")


def mode_order(primary):
    if primary not in SCORE_MODES:
        raise ValueError("Unknown score sort mode")
    return (primary, *(mode for mode in TIE_PRIORITY if mode != primary))


def published_value(value, precision=PUBLISHED_PRECISION):
    return None if value is None else int(Decimal(f'{value:.{precision}f}') * 10 ** precision)


def test_date(model):
    value = model.get('test_order', {}).get('date')
    if value is not None:
        date.fromisoformat(value)
    return value


def ranking_key(values, primary, model, *, precision=PUBLISHED_PRECISION):
    """Selected score, other RMC/SMC/MC scores, then a known test day.

    Only display precision participates in ties. Equal/unknown dates preserve
    source order through the stable sort; no model-name preference is added.
    """
    scores = tuple((values.get(mode) is None,
                    0 if values.get(mode) is None else -published_value(values[mode], precision))
                   for mode in mode_order(primary))
    day = test_date(model)
    return (*scores, day is None, day or '')


def overall_key(model, primary='partial'):
    values = {mode: (_selected_result(model, mode)['metrics']['earned'].get('confirmed')
                     if 'confirmed' in _selected_result(model, mode)['metrics']['earned'] else
                     _selected_result(model, mode)['metrics']['earned'].get('exact'))
              for mode in SCORE_MODES}
    return ranking_key(values, primary, model)


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
    # Use the same formatting precision as the published static score labels.
    # Decimal keys avoid hidden binary differences between identical labels.
    known = [(Decimal(f'{row["value"]:.{precision}f}'), row)
             for row in rows if row["value"] is not None]
    def key(row):
        mid = row['model_id']
        return ranking_key({mode: views[mode][mid]['value'] for mode in SCORE_MODES},
                           primary, models[mid], precision=precision)
    known.sort(key=lambda item: key(item[1]))
    for position, (_, row) in enumerate(known, 1):
        row["rank"] = position
    unknown = sorted((row for row in rows if row["value"] is None), key=key)
    return [row for _, row in known] + unknown


def category_rankings(models, groups, *, result_selector=None, precision=PUBLISHED_PRECISION):
    """Return policy groups with independent MC/RMC/SMC ranked views.

    Two arguments suffice in render_results_site. An injected selector supports
    isolated tests; otherwise the existing selected_result(model, mode) is used.
    Group titles/weights are source metadata, never applied to metric values.
    """
    if type(precision) is not int or not 0 <= precision <= 10:
        raise ValueError("Published score precision must be between zero and ten")
    models, groups = tuple(models), tuple(groups)
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
