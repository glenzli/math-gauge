"""A descriptive public timing panel, independent of benchmark scoring.

The same public A1 tasks are used for every model. Known non-delivery
durations remain in the sample; missing clocks are never replaced by budgets.
"""
import copy
from collections import Counter
import hashlib
import json
import math
from pathlib import Path
import re
import statistics
from math_gauge.editions import result_archive, source_edition
from math_gauge.evidence_retention import is_file, iter_files, read_bytes, read_json


CASES = (
    ("MG-GR021", "written-argument", "同时分块与下降", "Simultaneous blocks and descent"),
    ("MG-AR002", "argument-review", "论证审阅", "Argument review"),
    ("MG-BC001", "background-check", "背景核查", "Background check"),
    ("MG-TX001", "theorem-extension", "命题拓展", "Theorem extension"),
    ("MG-MCP003", "manuscript-completion", "想法手稿化", "Idea-to-manuscript completion"),
    ("MG-C003", "lean", "整章形式化", "Whole-chapter formalization"),
)
CASE_IDS = tuple(case[0] for case in CASES)
DAILY_IDS = tuple(cid for cid in CASE_IDS if cid != "MG-C003")
ADDITIONAL_DAILY_CASES = (
    ("written-argument", "书面论证", "Written argument",
     ("MG-GP001", "MG-GP002", "MG-GR005", "MG-GR009", "MG-GR022", "MG-GR023", "MG-PS001")),
    ("argument-review", "论证审阅", "Argument review", ("MG-AR001", "MG-AR003", "MG-AR004")),
    ("background-check", "背景核查", "Background check", ("MG-BC002",)),
    ("theorem-extension", "命题拓展", "Theorem extension", ("MG-TX002",)),
)
REVISION_CASES = CASES + tuple((cid, group, zh, en)
                              for group, zh, en, ids in ADDITIONAL_DAILY_CASES for cid in ids)


def read(path):
    return read_json(path)


def sha(path):
    return hashlib.sha256(read_bytes(path)).hexdigest()


def summarize(rows):
    values = [r["seconds"] for r in rows if r["seconds"] is not None]
    return {
        "planned": len(rows), "timed": len(values),
        "delivered": sum(r["delivery_status"] == "delivered" for r in rows),
        "nondelivery": sum(r["delivery_status"] == "delivery_failed" for r in rows),
        "not_run": sum(r["delivery_status"] == "not_run" for r in rows),
        "strict_passes": sum(r["strict_pass"] is True for r in rows),
        "strict_known": sum(r["strict_pass"] is not None for r in rows),
        "median_seconds": statistics.median(values) if values else None,
        "mean_seconds": statistics.mean(values) if values else None,
        "sum_seconds": sum(values) if values else None,
    }


def daily_summary(rows, weights):
    result = summarize(rows)
    complete = bool(rows) and result["timed"] == len(rows)
    result["weighted_mean_seconds"] = (sum(r["seconds"] * weights[r["case_id"]] for r in rows)
                                        / sum(weights[r["case_id"]] for r in rows)) if complete else None
    if not complete:
        result["median_seconds"] = result["mean_seconds"] = None
    return result


def load_supplement(path, current_record_id, case_ids=CASE_IDS):
    data = read(path)
    if data.get("schema") != "math-gauge.answer-timings/v1" or data.get("visibility") != "public-projection":
        raise ValueError("Timing reference requires a public timing supplement")
    if data["record_id"] != path.parent.name or data["model_id"] != path.parent.parent.name:
        raise ValueError("Timing source identity differs from its folder")
    record = data["record"]
    target = path.parent / record["path"]
    if record["path"] not in {"record.json", "native-observation.json"} or sha(target) != record["sha256"]:
        raise ValueError("Timing supplement binds a different source record")
    # Only the explicit public rows enter this display; combined/private summaries do not.
    allowed = set(data["public_case_ids"])
    rows = {}
    for row in data["rows"]:
        if row["phase"] != "A1" or row["case_id"] not in case_ids:
            continue
        if row["case_id"] not in allowed:
            raise ValueError("Timing panel attempted to expose a nonpublic task")
        seconds = row["seconds"]
        if seconds is not None and (type(seconds) not in (float, int) or not math.isfinite(seconds) or seconds < 0
                                    or row["availability"] != "known" or row["delivery_status"] == "not_run"):
            raise ValueError("Invalid observed timing")
        rows[row["case_id"]] = row
    return {"path": path, "rows": rows, "current": data["record_id"] == current_record_id}


def select_timing(case_id, expected_sha, sources):
    matches = []
    for source in sources:
        row = source["rows"].get(case_id)
        if not row or row["answer_sha256"] != expected_sha:
            continue
        # Null answer hashes cannot identify a failed request in a different snapshot.
        if not source["current"] and expected_sha is None:
            continue
        if row["seconds"] is not None:
            matches.append((source, row))
    current = [pair for pair in matches if pair[0]["current"]]
    if current:
        return current[0]
    if len({(row["method"], row["seconds"]) for _, row in matches}) > 1:
        raise ValueError("Conflicting clocks for the same retained answer")
    return matches[0] if matches else (None, None)


def build_reference(root, *, display_data=None, base_reference=None, revision_models=None):
    root = Path(root)
    payload = display_data or read(root / 'site/data.json')
    if payload.get('benchmark_version') == '1.2.0':
        if base_reference is None:
            baseline = root / 'site/versions/1.1.0/data.json'
            if not is_file(baseline):
                raise ValueError('Continuation clocks need the retained first-answer display')
            base_reference = build_reference(root, display_data=read(baseline),
                                             revision_models={model['id'] for model in payload['models']})
        return revision_reference(root, payload, base_reference)
    edition = source_edition(root)
    selected = dict(edition["selected_result_record_ids"])
    selected["dot-underlying-model-20261108"] = "20261108"
    display = {m["id"]: m for m in payload["models"]}
    from math_gauge.current_assessment_admissions import record_paths
    fresh = record_paths(root) if payload.get('benchmark_version') == '1.1.0' else {}
    for mid, path in fresh.items():
        selected[mid] = Path(path).parent.name
    if set(display) != set(selected):
        raise ValueError('Timing display differs from its edition-selected model cohort')
    case_definitions = CASES if revision_models is None else REVISION_CASES
    case_ids = tuple(case[0] for case in case_definitions)
    cases = [{"id": cid, "group": group, "title": {"zh": zh, "en": en}}
             for cid, group, zh, en in case_definitions]
    policy_path = root / "protocol/scoring-policy.json"
    category_weights = {item["id"]: item["weight"] for item in read(policy_path)["subcategories"]}
    weights = {c["id"]: category_weights[c["group"]] for c in cases if c["group"] != "lean"}
    observations_path = root / "site/timings/observed-clocks.json"
    observations = read(observations_path) if is_file(observations_path) else {"rows": []}
    if observations.get("rows") and observations.get("schema") != "math-gauge.timing-reference-observations/v1":
        raise ValueError("Unknown timing observations")
    models, inputs = [], [{"path": "protocol/scoring-policy.json", "sha256": sha(policy_path)}]
    for model_id, record_id in selected.items():
        if revision_models is not None and model_id not in revision_models:
            continue
        folder = ((root / fresh[model_id]).parent if model_id in fresh else
                  root / result_archive(edition, model_id) / model_id / record_id)
        record_path = folder / ("record.json" if is_file(folder / "record.json") else "native-observation.json")
        task_path = folder / "public-task-scores.json"
        scores = {r["case_id"]: r for r in read(task_path)["views"]["partial"]["nonlogical_retry_3"]["tasks"]}
        inputs.append({"path": task_path.relative_to(root).as_posix(), "sha256": sha(task_path)})
        # Reused answer clocks require the exact same response hash, not just a case ID.
        current = folder / "answer-timings.json"
        sources = [load_supplement(current, record_id, case_ids)] if is_file(current) else []
        needs_history = any(scores[cid].get("response_sha256") is not None
                            and select_timing(cid, scores[cid]["response_sha256"], sources)[1] is None
                            for cid in case_ids)
        if needs_history:
            candidates = sorted((path for path in iter_files(folder.parent)
                                 if path.name == "answer-timings.json" and path != current
                                 and len(path.relative_to(folder.parent).parts) == 2), reverse=True)
            sources.extend(load_supplement(path, record_id, case_ids) for path in candidates)
        rows = []
        for case_id in case_ids:
            score = scores[case_id]
            expected = score.get("response_sha256")
            source, timed = select_timing(case_id, expected, sources)
            exact = score["completion"]["exact"]
            # Some archived engineering deliveries have no textual response hash.
            # A missing text hash alone is never evidence of non-delivery.
            delivery = ("delivered" if expected or exact is not None and exact > 0 else
                        "not_run" if exact is None else "unresolved")
            current_rows = [s["rows"][case_id] for s in sources if s["current"] and case_id in s["rows"]]
            if current_rows:
                delivery = current_rows[0]["delivery_status"]
            row = {"case_id": case_id, "seconds": None, "method": None, "source": None,
                   "source_reused": False, "delivery_status": delivery,
                   "strict_pass": score["strict_pass"], "other_runs": []}
            if timed:
                path = source["path"]
                row.update(seconds=timed["seconds"], method=timed["method"],
                           delivery_status=timed["delivery_status"],
                           source={"path": path.relative_to(root).as_posix(), "sha256": sha(path)},
                           source_reused=not source["current"])
            for clock in observations["rows"]:
                if clock["model_id"] != model_id or clock["case_id"] != case_id or clock["record_id"] != record_id:
                    continue
                # This panel compares only the selected answers. Abandoned runs
                # remain in source evidence, without becoming display samples.
                if clock["kind"] == "other_run":
                    continue
                # A later scoring-only record revision does not change an answer's
                # clock. Keep the historical record hash; selected clocks still
                # require the current exact response bytes below.
                if not re.fullmatch(r"[0-9a-f]{64}", clock["selected_record_sha256"]):
                    raise ValueError("Observed clock needs its historical record identity")
                value = clock["seconds"]
                if (type(value) not in (int, float) or not math.isfinite(value) or value < 0
                        or not re.fullmatch(r"[0-9a-f]{64}", clock["source_sha256"])):
                    raise ValueError("Invalid supplemental observed clock")
                item = {"seconds": value, "method": clock["method"],
                        "source": {"path": observations_path.relative_to(root).as_posix(), "sha256": sha(observations_path)}}
                if clock["kind"] == "selected_answer":
                    if clock["answer_sha256"] != expected or expected is None:
                        raise ValueError("Observed clock belongs to another answer")
                    if row["seconds"] is not None and row["seconds"] != value:
                        if (row["method"], clock["method"]) != ("native_terminal_wall", "execution_elapsed"):
                            raise ValueError("Conflicting selected answer clock")
                        # Keep the published legacy sample. The expanded sample uses
                        # the recovered native cutoff, which excludes cleanup time.
                        if revision_models is not None:
                            continue
                    row.update(item)
                    row["source_reused"] = clock["selected_record_sha256"] != sha(record_path)
                else:
                    raise ValueError("Unknown observation kind")
            rows.append(row)
        meta = display[model_id]
        model = {"id": model_id, "label": meta["label"], "record_id": record_id,
                 "harness": meta["harness_display_name"].rstrip("¹²³⁴⁵*†"), "theme": copy.deepcopy(meta["theme"]),
                 "logo": copy.deepcopy(meta["logo"]), "rows": rows}
        model['presentation_eligibility'] = copy.deepcopy(meta.get('presentation_eligibility', {}))
        model["summaries"] = {"daily": daily_summary([r for r in rows if r["case_id"] in DAILY_IDS], weights),
                              "MG-C003": summarize([r for r in rows if r["case_id"] == "MG-C003"])}
        models.append(model)
    return {"schema": "math-gauge.timing-reference/v1", "version": "0.1.0",
            "benchmark_version": edition["version"], "default_sort": "weighted",
            "cases": cases, "daily_case_ids": list(DAILY_IDS), "daily_weights": weights,
            "models": models, "score_inputs": inputs,
            "new_candidate_calls": 0, "scores_modified": False}


def revision_reference(root, display_data, base_reference):
    """Compare all commonly timed non-Lean tasks and the separate chapter run."""
    from scripts.results_revision_resources import load_public, DATA_PATH, INDEX_PATH
    resources = load_public(root)
    resource_models = {row['id']: row for row in resources['models']}
    selected = {model['id'] for model in display_data['models']}
    ranked = {model['id'] for model in display_data['models']
              if model.get('presentation_eligibility', {}).get('ranked') is not False}
    result = copy.deepcopy(base_reference)
    result['benchmark_version'] = '1.2.0'
    result['base_assessment_version'] = '1.1.0'
    result['resource_source'] = INDEX_PATH if is_file(Path(root) / INDEX_PATH) else DATA_PATH
    result['batch_span_seconds'] = resources['batch_span_seconds']
    result['models'] = [model for model in result['models'] if model['id'] in selected]
    observed = [{row['case_id'] for row in model['rows'] if row['seconds'] is not None}
                for model in result['models'] if model['id'] in ranked]
    common = set.intersection(*observed) if observed else set()
    original_weights = result['daily_weights']
    case_groups = {cid: group for cid, group, _, _ in REVISION_CASES}
    group_order = {group: i for i, (_, group, _, _) in enumerate(CASES)}
    sample = sorted(common & original_weights.keys(), key=lambda cid: (group_order[case_groups[cid]], cid))
    counts = Counter(case_groups[cid] for cid in sample)
    result['daily_case_ids'] = sample
    result['daily_weights'] = {cid: original_weights[cid] / counts[case_groups[cid]] for cid in sample}
    sample_cases = [*sample, 'MG-C003']
    titles = {cid: {'id': cid, 'group': group, 'title': {'zh': zh, 'en': en}}
              for cid, group, zh, en in REVISION_CASES}
    result['cases'] = [titles[cid] for cid in sample_cases]
    for model in result['models']:
        resource = resource_models[model['id']]
        clocks = {row['case_id']: row['seconds'] for row in resource['public_cases']}
        rows = {row['case_id']: row for row in model['rows']}
        model['rows'] = [rows[cid] for cid in sample_cases]
        for row in model['rows']:
            row['base_seconds'] = row['seconds']
            row['revision_seconds'] = clocks.get(row['case_id'], 0)
            row['seconds'] = (None if row['seconds'] is None else row['seconds'] + row['revision_seconds'])
        model['summaries'] = {
            'daily': daily_summary(model['rows'][:-1], result['daily_weights']),
            'MG-C003': summarize([row for row in model['rows'] if row['case_id'] == 'MG-C003'])}
        model['revision_resources'] = copy.deepcopy(resource)
    return result


def render_panel(data, *, link_prefix=""):
    value = copy.deepcopy(data)
    value["link_prefix"] = link_prefix
    value["data_link"] = "data.json" if link_prefix else "downloads/timing-reference.json"
    payload = json.dumps(value, ensure_ascii=False).replace("<", "\\u003c").replace("&", "\\u0026")
    template = (Path(__file__).parent / "templates/timing-reference.html").read_text()
    return template.replace("@@TIMING_DATA@@", payload)
