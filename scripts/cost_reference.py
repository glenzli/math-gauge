"""Join public total-cost observations with source-owned scores and sample clocks."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

from math_gauge.costs import PUBLIC_SCHEMA, pareto_frontier
from math_gauge.editions import result_archive, source_edition
from math_gauge.records import evidence_bytes

DATA_PATH = "results/costs/v0.1.0/current.json"
SCORE_MODES = ("capability", "partial", "strict")


def _frontiers(rows):
    result = {}
    for mode in SCORE_MODES:
        points = [{**row, "score": row["scores"][mode]["value"],
                   "score_complete": row["scores"][mode]["complete"]} for row in rows
                  if row.get("presentation_eligibility", {}).get("ranked", True)]
        result[mode] = {axis: pareto_frontier(points, axis=axis) for axis in ("cost", "time")}
    return result


def selected_cost_source(folder, model, base):
    """Read an explicitly selected companion; arithmetic stays in costs.py."""
    source = model.get("c003_continuation", {}).get("cost_source")
    if source is None:
        return base, None
    document = json.loads(evidence_bytes(folder, source))
    component = model["retry"]["combined"].get("c003_continuation", {}).get("source_component_sha256")
    matches = document.get("models", [])
    if (document.get("schema") != PUBLIC_SCHEMA or document.get("version") != "0.1.0"
            or document.get("selection_rule") != "one_retained_attempt_per_slot"
            or document.get("other_retries_included") is not False
            or document.get("selected_scope") != "unchanged_selected39_A1_plus_new3_selfchecks"
            or not component or document.get("source_component_sha256") != component
            or document.get("base_record", {}).get("sha256") != base.get("record_sha256")
            or len(matches) != 1
            or any(matches[0].get(key) != base.get(key) for key in
                   ("model_id", "record_id", "record_sha256"))):
        raise ValueError("Cost companion binds another selected model, record or C003 source")
    return matches[0], document


def build_reference(root, *, display_data, timing_reference, base_reference=None):
    if display_data.get('benchmark_version') == '1.2.0':
        if base_reference is None:
            baseline = Path(root) / 'site/versions/1.1.0/data.json'
            if not baseline.is_file():
                raise ValueError('Continuation costs need the retained first-answer display')
            from scripts.timing_reference import build_reference as build_time
            first_data = json.loads(baseline.read_bytes())
            first_time = build_time(root, display_data=first_data)
            base_reference = build_reference(root, display_data=first_data, timing_reference=first_time)
        return revision_reference(root, display_data, timing_reference, base_reference)
    edition = source_edition(root)
    path = Path(root) / DATA_PATH
    if not path.is_file():
        return None
    document = json.loads(path.read_text())
    from math_gauge.current_assessment_admissions import record_paths, historical_cost_source
    fresh = record_paths(root)
    if display_data.get('benchmark_version') == '1.0.0' and fresh:
        document = historical_cost_source(root)
    current_fresh = fresh if display_data.get('benchmark_version') == '1.1.0' else {}
    if document.get("schema") != PUBLIC_SCHEMA or document.get("other_retries_included") is not False:
        raise ValueError("Cost display requires a selected-attempt public projection")
    costs = {row["model_id"]: row for row in document["models"]}
    if len(costs) != len(document["models"]):
        raise ValueError("Duplicate model cost reference")
    timings = {row["id"]: row for row in timing_reference["models"]}
    rows, overrides = [], {}
    for model in display_data["models"]:
        row = costs.get(model["id"])
        if row is None:
            raise ValueError("Missing model in cost reference: " + model["id"])
        folder = ((Path(root) / current_fresh[model['id']]).parent if model['id'] in current_fresh else
                  Path(root) / result_archive(edition, model["id"]) / model["id"] / row["record_id"])
        if folder.name != row['record_id']:
            raise ValueError('Cost reference selects another admission record')
        row, companion = selected_cost_source(folder, model, row)
        source = folder / ("record.json" if (folder / "record.json").is_file() else "native-observation.json")
        if not source.is_file() or hashlib.sha256(source.read_bytes()).hexdigest() != row.get("record_sha256"):
            raise ValueError("Cost reference binds a different public model record")
        item = {key: row[key] for key in ("model_id", "record_id", "status", "total_usd", "known_usd",
                    "estimate_range_usd", "coverage", "pricing_basis")}
        item.update(label=model["label"], theme=model["theme"], logo=model["logo"], scores={},
                    seconds=timings[model["id"]]["summaries"]["daily"]["weighted_mean_seconds"])
        item['presentation_eligibility'] = model.get('presentation_eligibility', {})
        if companion is not None:
            selected = model["c003_continuation"]["cost_source"]
            overrides[model["id"]] = dict(selected, path=(folder / selected["path"]).relative_to(root).as_posix(),
                private_source_sha256=companion["private_source_sha256"],
                source_component_sha256=companion["source_component_sha256"])
            item["supplemental_study"] = companion.get("supplemental_study")
        submission = (model["retry"]["combined"].get("submission_summary")
                      or model.get("answer_delivery") or {})
        normal_finals = submission.get("active_final")
        item["answer_delivery"] = {"planned": 39, "active_final": normal_finals,
                                   "complete": submission.get("planned") == 39 and normal_finals == 39}
        for mode in SCORE_MODES:
            result = model["retry"]["combined"] if mode == "partial" else model[mode]["nonlogical_retry_3"]
            metrics = result["metrics"]
            item["scores"][mode] = {"value": metrics["earned"]["confirmed"],
                "complete": metrics.get("overall", {}).get("exact") is not None and
                            not model["evaluation_progress"]["nonlogical_retry_3"]["incomplete"]}
        rows.append(item)
    if set(costs) != {row["model_id"] for row in rows}:
        raise ValueError("Cost reference has a retired or duplicate model")
    return {"schema": "math-gauge.cost-presentation/v1", "version": "0.1.0", "currency": "USD",
            "as_of": document["as_of"], "models": rows, "frontiers": _frontiers(rows),
            "source": DATA_PATH, "source_evidence_sha256": document["private_source_sha256"],
            "prices": document["prices"], **({"source_overrides": overrides} if overrides else {})}


def revision_reference(root, display_data, timing_reference, base_reference):
    """Project the full additive candidate cost; score blending is source-owned."""
    import copy
    from scripts.results_revision_resources import load_public, DATA_PATH, INDEX_PATH
    resources = load_public(root)
    by_id = {row['id']: row for row in resources['models']}
    display = {model['id']: model for model in display_data['models']}
    clocks = {model['id']: model for model in timing_reference['models']}
    result = copy.deepcopy(base_reference)
    result['benchmark_version'] = '1.2.0'
    result['base_assessment_version'] = '1.1.0'
    result['resource_source'] = INDEX_PATH if (Path(root) / INDEX_PATH).is_file() else DATA_PATH
    result['time_sample_count'] = len(timing_reference['daily_case_ids'])
    result['models'] = [row for row in result['models'] if row['model_id'] in display]
    for row in result['models']:
        mid = row['model_id']
        model, resource = display[mid], by_id[mid]
        row.update(copy.deepcopy({key: resource['combined'][key] for key in
                                  ('status', 'total_usd', 'known_usd', 'estimate_range_usd')}))
        row['revision_resources'] = copy.deepcopy(resource)
        row['seconds'] = clocks[mid]['summaries']['daily']['weighted_mean_seconds']
        revision = resource['revision']
        planned = revision['planned_calls']
        complete = revision.get('usage_complete_calls', planned if revision['total_usd'] is not None else 0)
        row['coverage']['planned'] += planned
        row['coverage']['complete'] += complete
        row['coverage']['missing'] += planned - complete
        for mode in SCORE_MODES:
            score = model['retry']['combined'] if mode == 'partial' else model[mode]['nonlogical_retry_3']
            row['scores'][mode] = {'value': score['metrics']['earned']['confirmed'],
                                  'complete': score['metrics']['overall']['exact'] is not None}
    result['frontiers'] = _frontiers(result['models'])
    return result


def independent_research_reference(root, display_data, base_reference, *, adoption, external_adoption=None,
                                   native_adoption=None):
    """Use the 1.3 scores and add full candidate cost. Retain the shared timing sample."""
    import copy
    from scripts.results_independent_research_resources import (DATA_PATH, EXTERNAL_DATA_PATH, NATIVE_DATA_PATH, ROUNDS,
        REVIEW_OVERHEAD, load_external_public, load_native_public, load_public)
    from scripts.results_revision_resources import combine_costs

    if display_data.get('benchmark_version') != '1.3.0' or base_reference.get('benchmark_version') != '1.2.0':
        raise ValueError('Independent research cost reference requires 1.3 scores and the retained 1.2 costs')
    resource = load_public(root, adoption)
    added = load_external_public(root, external_adoption)
    added_native = load_native_public(root, native_adoption) if native_adoption else None
    resources = dict(resource['models']) if resource else {}
    if added:
        if resources.keys() & added['models'].keys():
            raise ValueError('Native and external cost cohorts overlap')
        resources.update(added['models'])
    if added_native:
        if resources.keys() & added_native['models'].keys():
            raise ValueError('Separate native resource cohorts overlap')
        resources.update(added_native['models'])
    display = {model['id']: model for model in display_data['models']}
    result = copy.deepcopy(base_reference)
    result.update(benchmark_version='1.3.0', base_assessment_version='1.2.0',
                  independent_research_in_time_reference=False,
                  independent_research_resource_source=DATA_PATH if resource else None,
                  independent_research_source_sha256=resource['source_evidence_sha256'] if resource else None,
                  external_research_resource_source=EXTERNAL_DATA_PATH if added else None,
                  external_research_source_sha256=added['source_evidence_sha256'] if added else None,
                  native_research_resource_source=NATIVE_DATA_PATH if added_native else None,
                  native_research_source_sha256=added_native['source_evidence_sha256'] if added_native else None,
                  review_overhead=dict(REVIEW_OVERHEAD))
    result['models'] = [row for row in result['models'] if row['model_id'] in display]
    for row in result['models']:
        mid = row['model_id']
        model = display[mid]
        increment = resources.get(mid)
        if increment is None:
            planned = len(ROUNDS)
            unknown = adoption['models'].get(mid, {}).get('round_dispatches', 0) if adoption else 0
            if external_adoption:
                unknown += external_adoption['models'].get(mid, {}).get('round_dispatches', 0)
            if native_adoption:
                unknown += native_adoption['models'].get(mid, {}).get('round_dispatches', 0)
            coverage = dict(planned=planned, complete=0, partial=0, missing=unknown, not_run=planned - unknown)
            candidate_cost = dict(total_usd=None, known_usd=0, status='partial')
        else:
            coverage, candidate_cost = increment['coverage'], increment
        row.update(combine_costs(row, candidate_cost))
        row['coverage'] = {key: row['coverage'][key] + count for key, count in coverage.items()}
        row['independent_research_resources'] = copy.deepcopy(increment)
        for mode in SCORE_MODES:
            report = model['retry']['combined'] if mode == 'partial' else model[mode]['nonlogical_retry_3']
            metrics = report['metrics']
            overall = metrics['overall']
            row['scores'][mode] = {'value': metrics['earned']['confirmed'], 'complete': overall['exact'] is not None,
                                  'lower': overall['lower'], 'upper': overall['upper']}
    result['frontiers'] = _frontiers(result['models'])
    return result


def render_panel(data):
    if data is None:
        return ""
    payload = json.dumps(data, ensure_ascii=False).replace("<", "\\u003c").replace("&", "\\u0026")
    template = (Path(__file__).parent / "templates/cost-reference.html").read_text()
    argon = next((row for row in data['models'] if row['model_id'] == 'gemini-4-argon'), {})
    total = argon.get('total_usd')
    return (template.replace("@@COST_DATA@@", payload)
            .replace('@@ARGON_CURRENT_COST@@', '—' if total is None else f'${total:.2f}')
            .replace('@@ARGON_REGULAR_COST@@', '—' if total is None else f'${total * 2:.2f}'))
