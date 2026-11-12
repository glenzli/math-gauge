#!/usr/bin/env python3
"""Render the current, source-bound user-selected result records only."""
import argparse
import base64
import copy
import hashlib
import html
import json
import math
import re
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from math_gauge.records import load_assessment_results, load_content_rates, validate_record, selected_cli_records, selected_paper_records
from math_gauge.native_observations import load_public_record
from math_gauge.paper_observations import load_public_record as load_paper_record
from scripts.results_details import build_detail_pages, review_status
from scripts.results_rankings import category_rankings
from scripts.results_i18n import javascript_catalog, language_switch
from scripts.results_surplus import load_observations, render_subboard
from scripts.results_delivery import delivery_progress, load_legacy_projections
from scripts.results_harness import display_harness_labels
from scripts.results_presentation import project_payload
from scripts.results_publication import prepare_publication, write_publication
from scripts.timing_reference import build_reference, render_panel
from scripts.cost_reference import build_reference as build_cost_reference, render_panel as render_cost_panel
from math_gauge.submission_evidence import load_review_completion

MODEL_THEMES = {
    "glm-5.3-max": {"color": "#444b60", "ink": "#363d50", "tint": "#f1f2f5"},
    "kimi-3.1-pro-max": {"color": "#3568d4", "ink": "#244a9b", "tint": "#eef3ff"},
    "astra-6-max": {"color": "#252525", "ink": "#252525", "tint": "#f1f2f3"},
    "astra-6-xhigh": {"color": "#252525", "ink": "#252525", "tint": "#f1f2f3"},
    "claude-opus-5.5-max": {"color": "#d97757", "ink": "#9f4d34", "tint": "#fbf1ec"},
    "claude-sonnet-5.5-max": {"color": "#d97757", "ink": "#9f4d34", "tint": "#fbf1ec"},
    "sol-6.1-max": {"color": "#252525", "ink": "#252525", "tint": "#f1f2f3"},
    "sol-6.1-xhigh": {"color": "#252525", "ink": "#252525", "tint": "#f1f2f3"},
    "terra-6.1-max": {"color": "#252525", "ink": "#252525", "tint": "#f1f2f3"},
    "terra-6.1-xhigh": {"color": "#252525", "ink": "#252525", "tint": "#f1f2f3"},
    "deepseek-v4.1-flash-1017": {"color": "#4b6ed8", "ink": "#3655b2", "tint": "#f1f4fd"},
    "gemini-3.8-flash-high": {"color": "#68b77a", "ink": "#397a4a", "tint": "#f0f8f2"},
    "gemini-4-argon": {"color": "#68b77a", "ink": "#397a4a", "tint": "#f0f8f2"},
    "gemini-4-carbon": {"color": "#68b77a", "ink": "#397a4a", "tint": "#f0f8f2"},
}
MODEL_PROVIDERS = {
    "glm-5.3-max": ("Z.ai", "zai.svg"),
    "kimi-3.1-pro-max": ("Kimi", "kimi.svg"),
    "astra-6-max": ("OpenAI", "openai.svg"),
    "astra-6-xhigh": ("OpenAI", "openai.svg"),
    "claude-opus-5.5-max": ("Anthropic", "anthropic.svg"),
    "claude-sonnet-5.5-max": ("Anthropic", "anthropic.svg"),
    "sol-6.1-max": ("OpenAI", "openai.svg"),
    "sol-6.1-xhigh": ("OpenAI", "openai.svg"),
    "terra-6.1-max": ("OpenAI", "openai.svg"),
    "terra-6.1-xhigh": ("OpenAI", "openai.svg"),
    "deepseek-v4.1-flash-1017": ("DeepSeek", "deepseek.svg"),
    "gemini-3.8-flash-high": ("Google", "google.svg"),
    "gemini-4-argon": ("Google", "google.svg"),
    "gemini-4-carbon": ("Google", "google.svg"),
}
MODEL_LABELS = {
    "dot-underlying-model-20261108": "Dot Underlying (2026-11-08)",
    "glm-5.3-max": "GLM 5.3 (max)",
    "kimi-3.1-pro-max": "Kimi 3.1 Pro (max)",
    "astra-6-max": "Astra 6 (max)",
    "astra-6-xhigh": "Astra 6 (xhigh)",
    "claude-opus-5.5-max": "Claude Opus 5.5 (max)",
    "claude-sonnet-5.5-max": "Claude Sonnet 5.5 (max)",
    "sol-6.1-max": "Sol 6.1 (max)",
    "sol-6.1-xhigh": "Sol 6.1 (xhigh)",
    "terra-6.1-max": "Terra 6.1 (max)",
    "terra-6.1-xhigh": "Terra 6.1 (xhigh)",
    "deepseek-v4.1-flash-1017": "DeepSeek v4.1 Flash (max)",
    "gemini-3.8-flash-high": "Gemini 3.8 Flash (high)",
    "gemini-4-argon": "Gemini 4 Argon (high)",
    "gemini-4-carbon": "Gemini 4 Carbon (high)"
}
MODEL_SHORT_LABELS = {
    "dot-underlying-model-20261108": "Dot (2026-11-08)",
    "glm-5.3-max": "GLM (max)",
    "kimi-3.1-pro-max": "Kimi (max)",
    "astra-6-max": "Astra (max)",
    "astra-6-xhigh": "Astra (xhigh)",
    "claude-opus-5.5-max": "Opus 5.5 (max)",
    "claude-sonnet-5.5-max": "Sonnet 5.5 (max)",
    "sol-6.1-max": "Sol (max)",
    "sol-6.1-xhigh": "Sol (xhigh)",
    "terra-6.1-max": "Terra (max)",
    "terra-6.1-xhigh": "Terra (xhigh)",
    "deepseek-v4.1-flash-1017": "DeepSeek (max)",
    "gemini-3.8-flash-high": "Gemini 3.8 Flash (high)",
    "gemini-4-argon": "Gemini 4 Argon (high)",
    "gemini-4-carbon": "Gemini 4 Carbon (high)"
}


def bound_harness_display(harnesses, model, record_path):
    harness = harnesses['models'][model]
    if harness['record_sha256'] != hashlib.sha256(Path(record_path).read_bytes()).hexdigest():
        raise ValueError('Harness display metadata binds a different retained record')
    return copy.deepcopy(harness)


def build_data(source_root=ROOT):
    root = Path(source_root).resolve()
    from math_gauge.editions import verify_compatibility
    edition = verify_compatibility(root)
    policy = json.loads((root / "protocol/scoring-policy.json").read_bytes())
    strict_policy = json.loads((root / "protocol/strict-scoring-policy.json").read_bytes())
    mode_catalog = json.loads((root / "protocol/score-modes.json").read_bytes())
    if (mode_catalog.get("schema") != "math-gauge.score-modes/v1" or mode_catalog.get("default") != "partial"
            or mode_catalog.get("primary") != "partial"
            or [m.get("id") for m in mode_catalog.get("modes", [])] != ["capability", "partial", "strict"]):
        raise ValueError("Current display requires all three named modes and reliable capability as default")
    harness_path = root / 'site/harnesses.json'
    harnesses = json.loads(harness_path.read_bytes())
    models, sources = [], []
    for model, folder in selected_cli_records(root):
        label = MODEL_LABELS[model]
        validate_record(folder)
        record = json.loads((folder / "record.json").read_bytes())
        harness = bound_harness_display(harnesses, model, folder / 'record.json')
        research_source = json.loads((folder / record["theorem_extension_evidence"]["path"]).read_bytes())
        partial = load_assessment_results(folder, record)
        strict = load_assessment_results(folder, record, mode="strict")
        capability = load_assessment_results(folder, record, mode="capability")
        if partial is None or strict is None or capability is None:
            raise ValueError("Current display requires all three classified assessment modes")
        combined = partial["single_attempt"]
        provider, filename = MODEL_PROVIDERS[model]
        icon_path = root / "site/assets/logos" / filename
        icon_bytes = icon_path.read_bytes()
        models.append({"id": model, "label": label, "short_label": MODEL_SHORT_LABELS[model],
            "theme": dict(MODEL_THEMES[model]), 'harness': harness,
            "logo": {"label": provider, "data_url": "data:image/svg+xml;base64," + base64.b64encode(icon_bytes).decode("ascii"),
                     "sha256": hashlib.sha256(icon_bytes).hexdigest()},
            "combined": combined, "strict": strict, "capability": capability, "trajectory": record["trajectory"],
            "content_rates": load_content_rates(folder, record),
            "evaluation_progress": {condition: evaluation_progress(result)
                                    for condition, result in partial.items()},
            "lean_formalization_breakdown": partial["nonlogical_retry_3"]["lean_formalization_breakdown"],
            "alignment_selfcheck": partial["nonlogical_retry_3"]["alignment_selfcheck"],
            "source_record": str((folder / "record.json").relative_to(root)),
            "retry": {"combined": partial["nonlogical_retry_3"],
                      "note": (f"本批次已收{record['execution_summary'].get('delivered_initial_tasks', record['execution_summary'].get('initial_answers'))}/39道初答及{record['execution_summary'].get('delivered_selfcheck_rounds', record['execution_summary'].get('fixed_selfcheck_rounds'))}/3轮对齐自查；采用规则选定的首次有效交付。全部物理请求和纯系统故障另行留档。"
                               if record.get("execution_summary") else
                               "GR021共3次、采用第3次；GR023共2次、采用第2次。原失败保留，重跑接纳依据为操作者声明，运行细节未独立认证。"
                               if record.get("retry_admission") else
                               "正式研究工具组尚未完成；未测题保持未知，不回填其他条件的答卷。"
                               if research_source.get("source_condition") == "local_tools_no_network"
                                  and research_source.get("current_generation_status") != "completed" else
                               "当前研究工具组已完成六题；本地工具许可已实测，实际使用情况和所有物理请求另有留档。纯系统故障不占模型次数。"
                               if research_source.get("source_condition") == "local_tools_no_network" else
                               "研究源试答曾有15次路由连接失败且无答卷；当前采用修复环境批次的A1。本次整理未重跑，不认证整个历史首次即成功。"
                               if model == "terra-6.1-max" else
                               f"新增研究{research_source['effective_model_attempts']}题均为首次有效模型作答；另有{research_source['excluded_pure_system_failures']}次模型启动前的纯系统故障，不占模型尝试额度，物理请求与原失败保留。"
                               if research_source.get("excluded_pure_system_failures") else
                               "无新增重跑，沿用原答；新增研究题未测，不据此认证全部历史底层调用均一次完成。")}})
        names = ["record.json", record["assessment_policy"]["path"], record["strict_scoring_policy"]["path"],
                 "public-task-scores.json",
                 record["capability_scoring_policy"]["path"], record["score_mode_catalog"]["path"],
                 record["claim_review"]["path"], record["claim_penalty_policy"]["path"],
                 *(item["path"] for item in record["capability_results"].values()),
                 *(item["path"] for item in record["assessment_results"].values()),
                 *(item["path"] for item in record["strict_results"].values())]
        if record.get("retry_admission"):
            names += ["retry-admission.json", "retry-attempts.json", "nonlogical-retry-policy.json"]
        for name in names:
            path = folder / name
            sources.append({"path": str(path.relative_to(root)), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()})
        sources.append({"path": str(icon_path.relative_to(root)), "sha256": hashlib.sha256(icon_bytes).hexdigest()})
        if (folder / 'content-rates.json').exists():
            for name in ('content-rates.json', 'content-rate-policy.json'):
                path = folder / name
                sources.append({'path': str(path.relative_to(root)), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()})
    for name in ("score-modes.json", "capability-scoring-policy.json", "claim-penalty-policy.json"):
        path = root / "protocol" / name
        sources.append({"path": str(path.relative_to(root)), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()})
    for model, folder in selected_paper_records(root):
        record, scores, rates = load_paper_record(folder)
        harness = bound_harness_display(harnesses, model, folder / 'record.json')
        provider, filename = MODEL_PROVIDERS[model]
        icon_path = root / 'site/assets/logos' / filename
        icon = icon_path.read_bytes()
        partial = scores['partial']
        combined = partial['single_attempt']
        models.append({'id': model, 'label': MODEL_LABELS.get(model, record['model_label']), 'short_label': MODEL_SHORT_LABELS[model],
            'record_kind': 'paper_observation', 'comparison_note': record['comparison_note'],
            'theme': dict(MODEL_THEMES[model]), 'harness': harness,
            'logo': {'label': provider, 'data_url': 'data:image/svg+xml;base64,'
                     + base64.b64encode(icon).decode('ascii'), 'sha256': hashlib.sha256(icon).hexdigest()},
            'combined': combined, 'strict': scores['strict'], 'capability': scores['capability'],
            'trajectory': record['trajectory'], 'content_rates': rates,
            'evaluation_progress': {c: evaluation_progress(v) for c, v in partial.items()},
            'lean_formalization_breakdown': partial['nonlogical_retry_3']['lean_formalization_breakdown'],
            'alignment_selfcheck': partial['nonlogical_retry_3']['alignment_selfcheck'],
            'source_record': str((folder / 'record.json').relative_to(root)),
            'retry': {'combined': partial['nonlogical_retry_3'], 'note': record['comparison_note']}})
        for path in [folder / 'record.json', icon_path,
                     *(folder / item['path'] for field in ('assessment_results', 'capability_results', 'strict_results')
                       for item in record[field].values()),
                     *(folder / record[field]['path'] for field in ('assessment_policy', 'strict_scoring_policy',
                        'capability_scoring_policy', 'claim_penalty_policy', 'public_task_scores', 'public_claim_review'))]:
            sources.append({'path': str(path.relative_to(root)), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()})
        if rates is not None:
            for name in ('content-rates.json', 'content-rate-policy.json') + (
                    ('goal-attainment-policy.json',) if rates['version'] == '0.2.0' else ()):
                path = folder / name
                sources.append({'path': str(path.relative_to(root)), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()})
    native_folder = root / 'results/v0.6.0/dot-underlying-model-20261108/20261108'
    if (native_folder / 'native-observation.json').is_file():
        native, scores, rates = load_public_record(native_folder)
        icon_path = root / 'site/assets/logos/openai.svg'
        icon = icon_path.read_bytes()
        partial = scores['partial']
        models.append({'id': native['model_id'], 'label': MODEL_LABELS[native['model_id']], 'source_model_label': native['model_label'], 'short_label': MODEL_SHORT_LABELS[native['model_id']],
            'record_kind': 'native_harness', 'comparison_note': native['comparison_note'],
            'theme': dict(MODEL_THEMES['terra-6.1-max']),
            'harness': native['harness'],
            'logo': {'label': 'OpenAI', 'data_url': 'data:image/svg+xml;base64,'
                     +base64.b64encode(icon).decode('ascii'), 'sha256': hashlib.sha256(icon).hexdigest()},
            'combined': partial['single_attempt'], 'strict': scores['strict'],
            'capability': scores['capability'], 'trajectory': native['trajectory'],
            'content_rates': rates, 'evaluation_progress': {c:evaluation_progress(v) for c,v in partial.items()},
            'lean_formalization_breakdown': partial['nonlogical_retry_3']['lean_formalization_breakdown'],
            'alignment_selfcheck': partial['nonlogical_retry_3']['alignment_selfcheck'],
            'source_record': str((native_folder/'native-observation.json').relative_to(root)),
            'retry': {'combined': partial['nonlogical_retry_3'],
                      'note': f"{native['delivery_counts']['initial']}题首答与三轮固定自查；没有数学重跑。"
                              '原批次和历史补充来源分别留证；Dot native harness独立记录，底层SKU未知。'}})
        for path in [native_folder/'native-observation.json',native_folder/'content-rates.json',icon_path,
                     *(native_folder/item['path'] for field in ('assessment_results','capability_results','strict_results')
                       for item in native[field].values())]:
            sources.append({'path': str(path.relative_to(root)), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()})
    delivery_projections = load_legacy_projections(root)
    for model in models:
        model['harness_display_name'] = harness_display_name(model)
        model['fully_evaluated'] = is_fully_evaluated(model)
        record_bytes = (root / model['source_record']).read_bytes()
        original_record = json.loads(record_bytes)
        completion = load_review_completion((root / model['source_record']).parent, original_record)
        if completion is not None:
            model['review_completion'] = completion
            path = (root / model['source_record']).parent / 'review-completion.json'
            sources.append({'path': str(path.relative_to(root)),
                            'sha256': hashlib.sha256(path.read_bytes()).hexdigest()})
        model['answer_delivery'] = delivery_progress(json.loads(record_bytes), model['retry']['combined'],
            record_sha256=hashlib.sha256(record_bytes).hexdigest(), projection=delivery_projections.get(model['id']),
            review_completion=completion)
        if model.get('record_kind') == 'paper_observation':
            model['comparison_note'] = ''
            model['retry']['note'] = '全部尝试记录与答卷来源见正式档案。'
    display_modes = copy.deepcopy(mode_catalog['modes'])
    next(m for m in display_modes if m['id'] == 'strict')['abbreviation'] = 'SMC'
    sources.append({'path': 'site/harnesses.json', 'sha256': hashlib.sha256(harness_path.read_bytes()).hexdigest()})
    sources.append({'path': 'site/answer-delivery.json',
                    'sha256': hashlib.sha256((root / 'site/answer-delivery.json').read_bytes()).hexdigest()})
    observations = load_observations(root, models)
    if observations:
        sources.append(observations['source'])
    review_path = root / 'protocol/review-process.json'
    review_process = json.loads(review_path.read_bytes())
    sources.append({'path': 'protocol/review-process.json',
                    'sha256': hashlib.sha256(review_path.read_bytes()).hexdigest()})
    return {"schema": "math-gauge.current-results-display/v6", "benchmark_version": edition["version"],
            "result_compatibility": edition.get("result_compatibility"),
            "scoring_method_version": policy["version"], "strict_method_version": strict_policy["version"],
            "human_review": review_process['human_review'], "review_process": review_process,
            "formal_comparison_eligible": False,
            "models": models, "policy": policy, "strict_policy": strict_policy, "sources": sources,
            "manuscript_observations": observations,
            "capacity": copy.deepcopy(models[0]["combined"]["capacity"]),
            "group_capacity": copy.deepcopy(models[0]["combined"]["group_capacity"]),
            "publication_scope": "combined", "score_modes": [m["id"] for m in mode_catalog["modes"]],
            "score_mode_catalog": mode_catalog, "default_score_mode": mode_catalog["default"],
            'display_score_modes': display_modes, 'default_attempt_condition': 'nonlogical_retry_3',
            'gap_diagnostics': gap_diagnostics(models),
            'category_leaderboards': category_rankings(models, policy['groups'], result_selector=selected_result),
            "capability_method_version": next(m['policy_version'] for m in mode_catalog['modes'] if m['id']=='capability'),
            "claim_penalty_method_version": "0.1.0",
            "attempt_conditions": ["single_attempt", "nonlogical_retry_3"]}


def earned_value(result):
    value = result["metrics"]["earned"]
    return value.get("confirmed", value["exact"])


def evaluation_progress(result):
    """Mark unknown built tasks, independently of mistakes or unbuilt capacity."""
    counts = result["whole_task_counts"]
    pending_rounds = sum(row['score']['exact'] is None
                        for row in result.get('alignment_selfcheck', {}).get('rounds', []))
    return {"planned": counts["planned"], "adjudicated": counts["passed"] + counts["failed"],
            "pending": counts["unknown"], "pending_rounds": pending_rounds,
            "incomplete": counts["unknown"] > 0 or pending_rounds > 0}


def harness_display_name(model):
    if model.get('record_kind') == 'native_harness':
        return 'Unknown¹'
    return model['harness']['name'] + model['harness'].get('note_marker', '')


def selected_result(model, mode="partial"):
    """Use the rule-selected retained result, including an equal/lower retry."""
    condition = "nonlogical_retry_3"
    return model["retry"]["combined"] if mode == "partial" else model[mode][condition]


def signed_points(value):
    if value is None:
        return '未知'
    text = f'{value:+.2f}'
    return '0.00' if float(text) == 0 else text.replace('-', '−')


def gap_diagnostics(models):
    """Signed differences of saved totals; no new scoring or reweighting."""
    tables, values = [], []
    definitions = (('RG', '可靠差', 'Reliability Gap', 'partial', 'RMC − MC'),
                   ('DG', '交付差', 'Delivery Gap', 'strict', 'SMC − MC'))
    for code, title, english, mode, formula in definitions:
        rows = []
        for model in models:
            mc = earned_value(selected_result(model, 'capability'))
            target = earned_value(selected_result(model, mode))
            progress = model['evaluation_progress']['nonlogical_retry_3']
            value = (None if mc is None or target is None or progress['adjudicated'] == 0
                     else target - mc)
            eligible = (value is not None and progress['planned'] > 0
                        and progress['adjudicated'] == progress['planned'] and not progress['incomplete'])
            rows.append({'model_id': model['id'], 'label': model['label'], 'mc': mc,
                         'target': target, 'value': value, 'display': signed_points(value),
                         'coverage': dict(progress), 'rank': None,
                         'status': 'ranked' if eligible else 'unknown' if value is None else 'partial'})
            if value is not None:
                values.append(value)
        key = lambda row: (abs(row['value']) if row['value'] is not None else float('inf'),
                           -(row['mc'] or 0), row['model_id'])
        ranked = sorted((row for row in rows if row['status'] == 'ranked'), key=key)
        previous, rank = None, 0
        for index, row in enumerate(ranked, 1):
            distance = abs(row['value'])
            if previous is None or not math.isclose(distance, previous, rel_tol=0, abs_tol=1e-10):
                rank = index
            row['rank'], previous = rank, distance
        rows = ranked + sorted((row for row in rows if row['status'] != 'ranked'), key=key)
        tables.append({'id': code, 'title': title, 'english': english, 'formula': formula,
                       'target_mode': mode, 'rows': rows})
    low, high = min([0] + values), max([0] + values)
    if low == high:
        low = -10
    step = next(step for step in (.01, .02, .05, .1, .2, .5, 1, 2, 5, 10, 20, 50, 100)
                if step >= (high - low) / 5)
    low, high = math.floor(low / step) * step, math.ceil(high / step) * step
    span = high - low
    ticks = []
    for index in range(round(span / step) + 1):
        value = low + index * step
        label = str(round(value)) if math.isclose(value, round(value), abs_tol=1e-10) else f'{value:.2f}'
        ticks.append({'value': value, 'position': (value - low) / span * 100,
                      'label': ('+' if value > 0 else '') + label.replace('-', '−')})
    for table in tables:
        for row in table['rows']:
            value = row['value']
            row['plot'] = None if value is None else {
                'left': (min(0, value) - low) / span * 100, 'width': abs(value) / span * 100}
    return {'unit': 'percentage_points', 'attempt_condition': 'nonlogical_retry_3',
            'baseline': 'capability', 'order': 'absolute_gap_ascending',
            'axis': {'minimum': low, 'maximum': high, 'zero': -low / span * 100, 'ticks': ticks},
            'tables': tables}


def sort_control(key, label, options, selected):
    short = {'reliability': '可靠率', 'attainment': '达成率'}
    choices = ''.join('<button type="button" data-chart-sort="'+html.escape(key, quote=True)
                     +'" data-sort-value="'+html.escape(value, quote=True)+'" aria-pressed="'
                     +str(value == selected).lower()+'" title="'+html.escape(text, quote=True)+'">'
                     +html.escape(short.get(value, text.split(' ')[0]))+'</button>' for value, text in options)
    if key == 'overall':
        choices = choices.replace('data-chart-sort="overall" data-sort-value=', 'data-score-mode=')
    return ('<div class="board-sort"><span class="board-sort-label">排序</span><div class="segmented" role="group" '
            'aria-label="'+html.escape(label, quote=True)+'">'+choices+'</div></div>')


def board_settings(key, items):
    """One display menu per board; it never owns scores or sort choices."""
    options = ''.join('<label class="board-series-option"><input type="checkbox" data-show-score="'
                     +html.escape(value, quote=True)+'" checked><span>'+html.escape(label)+'</span></label>'
                     for value, label in items)
    return ('<button class="board-settings-button" type="button" data-board-settings="'+key
            +'" aria-controls="board-options-'+key+'" aria-expanded="false" aria-label="榜单显示设置">'
            '<svg viewBox="0 0 20 20" width="16" height="16" fill="none" stroke="currentColor" stroke-width="1.4" aria-hidden="true">'
            '<path d="M3 5h14M3 10h14M3 15h14"/><path d="M7 2.5v5M13 7.5v5M8 12.5v5" stroke-width="3"/></svg>'
            '<span>设置</span></button>'
            '<div class="board-options" id="board-options-'+key+'" role="dialog" aria-label="榜单显示设置" hidden>'
            '<div class="board-options-head"><div><strong>显示设置</strong><small>只影响此榜单</small></div>'
            '<button type="button" class="board-options-close" data-board-close aria-label="关闭设置">×</button></div>'
            '<fieldset><legend>展示项目</legend><div class="board-series-options">'+options+'</div>'
            '<button type="button" class="board-show-all" data-show-all>全部显示</button></fieldset></div>')


def score_board_settings(key, modes):
    return board_settings(key, [(m['id'], m['abbreviation']) for m in modes])


def horizontal_chart(groups, chart_id, label, ticks, zero):
    """Shared model-row layout; callers supply source-derived values and axes."""
    step = ticks[1]['position'] - ticks[0]['position']
    labels = ''.join(f'<span style="left:{tick["position"]:.8f}%">'
                     + html.escape(tick['label']) + '</span>' for tick in ticks)
    return ('<div class="horizontal-score-chart" role="group" aria-label="'
            +html.escape(label, quote=True)+f'" style="--score-grid-step:{step:.8f}%;--score-zero:{zero:.8f}%">'
            '<div class="score-x-axis" aria-hidden="true">'+labels+'</div>'
            '<div class="chart-groups" id="'+html.escape(chart_id, quote=True)+'">'
            +''.join(groups)+'</div></div>')


def render_gap_chart(data):
    diagnostic, groups = data['gap_diagnostics'], []
    axis = diagnostic['axis']
    lookup = {table['id']: {row['model_id']: row for row in table['rows']}
              for table in diagnostic['tables']}
    def order(model):
        value = lookup['RG'][model['id']]['value']
        return (value is None, 0 if value is None else abs(value), model['id'])
    ordered = sorted(data['models'], key=order)
    for model in ordered:
        row = lookup['RG'][model['id']]
        bars = []
        for table in diagnostic['tables']:
            item = lookup[table['id']][model['id']]
            plot = item['plot']
            bar = '' if plot is None else (
                '<span class="gap-bar gap-'+table['id'].lower()+'" data-model="'+model['id']+'" '
                f'data-gap-metric="{table["id"]}" data-gap-value="{item["value"]}" '
                f'style="left:{plot["left"]:.8f}%;width:{plot["width"]:.8f}%"></span>')
            bars.append('<div class="gap-metric-row" data-display-mode="'+table['id']+'">'
                '<div class="gap-track" aria-hidden="true">'+bar+'</div>'
                '<span class="score-readout"><small>'+table['id']+'</small><span class="gap-value" '
                'aria-label="'+html.escape(table['id']+' '+item['display'], quote=True)+'" '
                +'>'+item['display']+'</span></span></div>')
        groups.append('<div class="gap-model-group" data-model="'+model['id']+'" style="--model-color:'
            +html.escape(model['theme']['color'], quote=True)+';--model-ink:'
            +html.escape(model['theme']['ink'], quote=True)+'"><div class="gap-model-label"><img class="gap-logo" '
            'alt="" width="24" height="24" src="'+html.escape(model['logo']['data_url'], quote=True)+'"><div><span>'
            +html.escape(model['label'])+'</span></div></div>'
            '<div class="gap-model-bars">'+''.join(bars)+'</div></div>')
    return ('<div class="board-subhead"><p class="panel-desc">RG＝RMC−MC · DG＝SMC−MC · 百分点</p>'
            '<div class="board-toolbar">'
            +sort_control('gap', '分数落差排序', [('RG','RG 接近0优先'),('DG','DG 接近0优先')], 'RG')
            +board_settings('gap', [('RG','RG · 可靠差'),('DG','DG · 交付差')])+'</div></div>'
            '<figure class="gap-figure" aria-labelledby="gap-heading"><figcaption class="gap-caption">'
            '<span>越接近0，分数落差越小</span><span class="chart-legend">'
            '<span class="legend-item" data-display-mode="RG"><i class="legend-swatch rmc" aria-hidden="true"></i>RG · 可靠差</span>'
            '<span class="legend-item" data-display-mode="DG"><i class="legend-swatch smc" aria-hidden="true"></i>DG · 交付差</span></span></figcaption>'
            +horizontal_chart(groups, 'gap-groups', '各模型可靠差与交付差，共用正负轴', axis['ticks'], axis['zero'])
            +'</figure>')


def grouped_bars(data, category=None):
    groups = []
    modes = data['display_score_modes']
    scope = 'overall' if category is None else category['id']
    scope_attr = ' data-score-scope="'+html.escape(scope, quote=True)+'"'
    if category is None:
        ordered = sorted(data['models'], key=lambda m: earned_value(selected_result(m))
                         if earned_value(selected_result(m)) is not None else float('-inf'), reverse=True)
        views = {mode['id']: {m['id']: dict(selected_result(m, mode['id'])['metrics']['overall'],
                    value=earned_value(selected_result(m, mode['id']))) for m in ordered} for mode in modes}
    else:
        by_id = {m['id']: m for m in data['models']}
        ordered = [by_id[row['model_id']] for row in category['views']['partial']]
        views = {mode['id']: {row['model_id']: row for row in category['views'][mode['id']]}
                 for mode in modes}
    values = [row['value'] for view in views.values() for row in view.values() if row['value'] is not None]
    minimum = math.floor(min([0] + values) / 20) * 20
    span, zero = 100 - minimum, -minimum / (100 - minimum) * 100
    for model in ordered:
        bars, spoken = [], []
        for mode in modes:
            bounds = views[mode['id']][model['id']]
            value = bounds['value']
            text = '—' if value is None else f'{value:.2f}'
            position = zero if value is None else (value - minimum) / span * 100
            width = abs(position - zero)
            interval = f"完整分区间 {bounds['lower']:.2f}–{bounds['upper']:.2f}"
            spoken.append(mode['abbreviation'] + ' ' + text)
            bars.append('<div class="metric-bar-row" data-score-mode="'+mode['id']+'" data-display-mode="'+mode['id']+'">'
                '<div class="bar-track">'
                '<div class="score-bar mode-'+mode['id']+'"'+scope_attr+' aria-hidden="true" data-score-mode="'+mode['id']
                +'" data-model="'+html.escape(model['id'], quote=True)+'" data-series="nonlogical_retry_3" '
                +'data-score="'+('' if value is None else str(value))+'" style="width:'+f'{width:.8f}'+'%;left:'
                +f'{min(zero, position):.8f}'+'%"></div></div>'
                '<span class="score-readout"><small>'+mode['abbreviation']+'</small>'
                '<span class="chart-value"'+scope_attr+' data-score-mode="'+mode['id']+'" '
                +'title="'+html.escape(interval, quote=True)+'">'+text+'</span></span></div>')
        label = html.escape(model['label'])
        logo = model['logo']
        theme = model['theme']
        groups.append('<div class="bar-group"'+scope_attr+' data-model="'+html.escape(model['id'], quote=True)+'" role="group" '
            +'aria-label="'+html.escape(model['label']+'。'+'，'.join(spoken), quote=True)+'" '
            +'style="--model-color:'+html.escape(theme['color'], quote=True)+';--model-ink:'+html.escape(theme['ink'], quote=True)
            +'">'
            '<div class="chart-model"><img class="provider-logo"'+scope_attr+' src="'+html.escape(logo['data_url'], quote=True)+'" '
            +'alt="'+html.escape(logo['label'], quote=True)+'" width="24" height="24"><div><span>'+label
            +'</span></div></div><div class="metric-bars">'+''.join(bars)+'</div></div>')
    ticks = [dict(position=(value-minimum)/span*100, label=str(value)) for value in range(minimum, 101, 20)]
    chart_id = 'chart-groups' if category is None else 'category-chart-groups-'+scope
    label = ('各模型' if category is None else category['title']+'各模型')+'MC、RMC、SMC规则成绩'
    return horizontal_chart(groups, chart_id, label+f'，统一{minimum}至100分', ticks, zero)


def render_content_rates(data):
    groups = []
    definitions = (('reliability', '内容可靠率', 'observed', 'partial'),
                   ('attainment', '目标达成率', 'confirmed', 'strict'))
    def order(model):
        value = (model.get('content_rates') or {}).get('metrics', {}).get('reliability', {}).get('observed')
        return (value is None, 0 if value is None else -value, model['id'])
    for model in sorted(data['models'], key=order):
        report = model.get('content_rates')
        if report is not None and report['version'] != '0.2.0':
            raise ValueError('Current rates require a source-bound 0.2.0 report')
        bars, spoken = [], []
        for ident, label, field, style in definitions:
            value = None if report is None else report['metrics'][ident][field]
            text = '—' if value is None else f'{value:.2f}%'
            width = 0 if value is None else value
            spoken.append(label+' '+text)
            bars.append('<div class="metric-bar-row" data-display-mode="'+ident+'"><div class="bar-track"><div '
                'class="content-rate-bar mode-'+style+'" aria-hidden="true" data-model="'+model['id']
                +'" data-rate="'+ident+'" data-rate-value="'+('' if value is None else str(value))
                +'" style="width:'+f'{width:.8f}'+'%;left:0%"></div></div>'
                '<span class="score-readout"><small>'+('可靠' if ident == 'reliability' else '达成')+'</small>'
                '<span class="rate-value">'+text+'</span></span></div>')
        progress = model['evaluation_progress']['nonlogical_retry_3']
        theme = model['theme']
        groups.append('<div class="rate-model-group" data-model="'+model['id']+'" role="group" '
            'aria-label="'+html.escape(model['label']+'。'+'，'.join(spoken), quote=True)+'" '
            'style="--model-color:'+theme['color']+';--model-ink:'+theme['ink']+'">'
            '<div class="chart-model">'
            '<img class="rate-provider-logo" src="'+html.escape(model['logo']['data_url'], quote=True)
            +'" alt="'+html.escape(model['logo']['label'], quote=True)+'" width="24" height="24">'
            '<div><a data-context-link href="models/'+model['id']
            +'/index.html?score=partial&amp;condition=nonlogical_retry_3">'+html.escape(model['label'])
            +'</a></div></div>'
            '<div class="metric-bars">'+''.join(bars)+'</div></div>')
    ticks = [dict(position=value, label=str(value)) for value in range(0, 101, 20)]
    return ('<section class="panel view-board" data-board="rates" id="content-rates"><div class="panel-head"><div><h2 id="rate-heading">内容可靠率与目标达成率</h2>'
            '<p class="panel-desc">内容可靠率衡量已作断言的正确性，目标达成率统计完整成果的交付。</p></div>'
            '<div class="board-toolbar">'
            +sort_control('rates', '两率图排序', [('reliability','内容可靠率 高→低'),('attainment','目标达成率 高→低')], 'reliability')
            +board_settings('rates', [('reliability','内容可靠率'),('attainment','目标达成率')])+'</div></div>'
            '<figure class="score-figure rate-figure" aria-labelledby="rate-heading"><figcaption class="chart-caption">'
            '<span>百分比 · 0–100</span><span class="chart-legend"><span class="legend-item" data-display-mode="reliability">'
            '<i class="legend-swatch rmc" aria-hidden="true"></i>内容可靠率</span><span class="legend-item" data-display-mode="attainment">'
            '<i class="legend-swatch smc" aria-hidden="true"></i>目标达成率</span></span></figcaption>'
            +horizontal_chart(groups, 'rate-groups', '各模型内容可靠率与目标达成率，统一0至100百分比', ticks, 0)
            +'</figure><p class="panel-foot"><a data-context-link href="method.html#content-rate-method">计算方法 →</a></p></section>')


def render_category_leaderboards(data):
    tabs, panels = [], []
    for index, group in enumerate(data['category_leaderboards']):
        cid, title = html.escape(group['id'], quote=True), html.escape(group['title'])
        tabs.append('<button role="tab" id="category-tab-'+cid+'" aria-controls="category-panel-'+cid
                    +'" aria-selected="'+str(index == 0).lower()+'" tabindex="'+('0' if index == 0 else '-1')
                    +'">'+title+'</button>')
        panels.append('<section role="tabpanel" class="category-ranking-panel view-board" data-board="'+cid+'" id="category-panel-'+cid
                      +'" aria-labelledby="category-tab-'+cid+'"'+(' hidden' if index else '')+'>'
                      '<div class="panel-head"><div><h3>'+title+'排行榜</h3><p class="panel-desc">类内满分100 · 总榜权重'
                      +str(group['weight'])+'%</p></div>'
                      +'<div class="board-toolbar">'+sort_control(group['id'], group['title']+'排序', [(m['id'],m['abbreviation']+' 高→低') for m in data['display_score_modes']], 'partial')
                      +score_board_settings(group['id'], data['display_score_modes'])+'</div>'
                      +'</div><figure class="score-figure category-figure" aria-label="'+title+'分类成绩图">'
                      '<figcaption class="chart-caption"><span>类内百分制</span><span class="chart-legend">'
                      +''.join('<span class="legend-item" data-display-mode="'+mode['id']+'"><i class="legend-swatch '+mode['abbreviation'].lower()+'" aria-hidden="true"></i>'
                               +mode['abbreviation']+'</span>' for mode in data['display_score_modes'])
                      +'</span></figcaption>'+grouped_bars(data, group)+'</figure>'
                      '<div class="table-wrap"><table class="compact category-ranking" id="category-ranking-'
                      +cid+'"></table></div>'
                      +(render_subboard(data.get('manuscript_observations'), chart_renderer=horizontal_chart, controls=board_settings('initiative', [('groups','已核实额外成果组'),('coverage','审阅覆盖')])) if group['id']=='research' else '')
                      +'</section>')
    return ('<section id="category-leaderboards" aria-labelledby="category-leaderboards-title">'
            '<div class="section-title"><h2 id="category-leaderboards-title">分类排行榜</h2>'
            '<span class="section-context">三个大类独立排序</span></div><div class="panel">'
            '<div role="tablist" class="segmented category-tabs" aria-label="分类排行榜">'+''.join(tabs)+'</div>'
            '<p class="category-ranking-note">各分类可独立选择排序口径。</p>'
            +''.join(panels)+'<p class="panel-foot">类内成绩满分100；计入总榜的贡献见下表。</p></div></section>')


def is_fully_evaluated(model):
    """Evaluation coverage, not mathematical success or a self-claimed finish."""
    progress = model['evaluation_progress']['nonlogical_retry_3']
    return (not progress['incomplete']
            and selected_result(model)['metrics']['overall']['exact'] is not None)


def render(data, *, timing_reference=None, cost_reference=None):
    # Only escaped data enters the standalone template; scores come from archives.
    payload = json.dumps(display_harness_labels(project_payload(data)), ensure_ascii=False).replace("<", "\\u003c").replace("&", "\\u0026")
    rows = []
    ordered = sorted(data['models'], key=lambda m: earned_value(selected_result(m))
                     if earned_value(selected_result(m)) is not None else float('-inf'), reverse=True)
    for index, model in enumerate(ordered, 1):
        source = html.escape('models/'+model['id']+'/index.html?score=partial&condition=nonlogical_retry_3', quote=True)
        progress = model['evaluation_progress']['nonlogical_retry_3']
        delivery = model['answer_delivery']
        delivered = (str(delivery['active_final'])+'／'+str(delivery['forced_content'])+'／'+str(delivery['planned'])
            if delivery.get('active_final') is not None else
            '—' if delivery['delivered'] is None else str(delivery['delivered'])+'／'+str(delivery['planned']))
        score_cells = []
        for mode in data['display_score_modes']:
            value = earned_value(selected_result(model, mode['id']))
            score_cells.append('<td data-display-mode="'+mode['id']+'" class="numeric score-cell'+(' primary-score' if mode['id']=='partial' else '')+'">'
                '<span class="score-number">'+('—' if value is None else f'{value:.2f}')+'</span></td>')
        rows.append('<tr><td class="rank">'+str(index)+'</td><td class="model-name"><a href="'+source+'">'
            +html.escape(model['label'])+'</a><span class="mobile-harness">'
            +html.escape(harness_display_name(model))+'</span><span class="mobile-delivery">交卷 '+delivered+'</span></td>'
            '<td class="harness-cell">'+html.escape(harness_display_name(model))+'</td>'
            '<td class="numeric delivery-cell">'+delivered+'</td>'+''.join(score_cells)
            +'<td class="numeric"><a href="'+source+'">详细评测 →</a></td></tr>')
    values = {"DATA": payload, "ROWS": ''.join(rows), "TRIPLE_CHART": grouped_bars(data),
              "REVIEW_STATUS": review_status(data, 'method.html#review-process'),
              "LANGUAGE_SWITCH": language_switch(),
              "OVERALL_CONTROLS": sort_control('overall', '总榜排序', [(m['id'],m['abbreviation']+' 高→低') for m in data['display_score_modes']], data['default_score_mode'])+score_board_settings('overall', data['display_score_modes']),
              "GAP_CHART": render_gap_chart(data),
              "CONTENT_RATES": render_content_rates(data),
              "CATEGORY_RANKINGS": render_category_leaderboards(data),
              "MODEL_NOTES": ('<p class="panel-foot" data-model-note="dot-underlying-model-20261108">¹ Dot原生独立运行方式</p>'
                                     if any(m.get('record_kind') == 'native_harness' for m in data['models']) else '')
                                  + ''.join('<p class="panel-foot" data-model-note="'+html.escape(m['id'], quote=True)+'">'
                                             +html.escape(m['harness']['note_marker']+' '+m['harness']['note_text'])+'</p>'
                                             for m in sorted(data['models'], key=lambda m: m['harness'].get('note_marker', ''))
                                             if m['harness'].get('note_text')),
              "MODE_CONTROLS": ''.join(
                  '<button data-score-mode="'+m['id']+'" aria-label="'+html.escape(m['name']+' '+m['abbreviation'], quote=True)
                  +'" aria-pressed="'+str(m['id']==data['default_score_mode']).lower()+'"><span class="mode-name">'
                  +html.escape(m['name'])+'</span><span class="mode-code">'+html.escape(m['abbreviation'])+'</span></button>'
                  for m in data['display_score_modes']),
              "TASKS": str(data["policy"]["scope"]["tasks"]),
              "PUBLIC": str(data["policy"]["scope"]["public_tasks"]),
              "PRIVATE": str(data["policy"]["scope"]["private_tasks"]),
              "FAMILIES": str(data["policy"]["scope"]["parent_families"]),
              "ARGUMENT_FAMILIES": str(next(c['families'] for c in data['policy']['subcategories'] if c['id']=='written-argument')),
              "RESEARCH_TASKS": str(data["policy"]["theorem_extension"]["families"]),
              "COVERAGE_NOTE": html.escape("命题拓展已评：" + "；".join(
                  m["label"] + " " + str(m["combined"]["metrics"]["theorem-extension"]["coverage"]["adjudicated"])
                  + "/" + str(m["combined"]["metrics"]["theorem-extension"]["coverage"]["planned"])
                  for m in data["models"]) + "。背景核查已评：" + "；".join(m["label"]+" "+str(m["combined"]["metrics"]["background-check"]["coverage"]["adjudicated"])+"/4" for m in data["models"])+"。"),
              "RESERVED": str(data['capacity']['under_construction']),
              "BACKGROUND_TASKS": str(data['policy']['background_check']['families']),
              "CAPACITY": str(data["capacity"]["active"]),
              "TIMING_REFERENCE": render_panel(timing_reference) if timing_reference else '',
              "TIMING_CSS": '<link rel="stylesheet" href="assets/timing-reference.css">' if timing_reference else '',
              "TIMING_JS": '<script src="assets/timing-reference.js"></script>' if timing_reference else '',
              "COST_REFERENCE": render_cost_panel(cost_reference),
              "COST_CSS": '<link rel="stylesheet" href="assets/cost-reference.css">' if cost_reference else '',
              "COST_JS": '<script src="assets/cost-reference.js"></script>' if cost_reference else ''}
    template = (Path(__file__).parent / "templates/current-results.html").read_text(encoding="utf-8")
    return re.sub(r"@@MG_(" + '|'.join(re.escape(key) for key in values) + r")@@",
                  lambda match: values[match[1]], template)


def write_site(destination, *, source_root=ROOT):
    dest = Path(destination)
    data = build_data(source_root)
    timings = build_reference(source_root,display_data=data)
    costs = build_cost_reference(source_root,display_data=data,timing_reference=timings)
    # Resolve all evidence before changing navigation or writing any page.
    files = build_detail_pages(data, source_root)
    files["index.html"] = render(data,timing_reference=timings,cost_reference=costs)
    files['downloads/timing-reference.json'] = json.dumps(timings,ensure_ascii=False,indent=2)+'\n'
    if costs is not None:
        files['downloads/cost-reference.json'] = json.dumps(costs,ensure_ascii=False,indent=2)+'\n'
    files["data.json"] = json.dumps(display_harness_labels(data), ensure_ascii=False, indent=2) + "\n"
    for name in ("results.css", "results-i18n.js", "results-core.js", "home-results.js", "board-controls.js", "model-results.js", "case-results.js", "method-results.js", "records.js", "timing-reference.css", "timing-reference.js", "cost-reference.css", "cost-reference.js"):
        files["assets/"+name] = (Path(__file__).parent/"templates"/name).read_text()
    files['assets/results-i18n.js'] = files['assets/results-i18n.js'].replace('@@MG_MESSAGES@@', javascript_catalog())
    for model in data["models"]:
        for scope in ["combined"]:
            files["downloads/"+model["id"]+"-"+scope+".json"] = json.dumps(model[scope], ensure_ascii=False, indent=2)+"\n"
            files["downloads/"+model["id"]+"-"+scope+"-retry.json"] = json.dumps(model["retry"][scope], ensure_ascii=False, indent=2)+"\n"
            for condition, suffix in (("single_attempt", ""), ("nonlogical_retry_3", "-retry")):
                files["downloads/"+model["id"]+"-combined-strict"+suffix+".json"] = json.dumps(model["strict"][condition], ensure_ascii=False, indent=2)+"\n"
                files["downloads/"+model["id"]+"-combined-capability"+suffix+".json"] = json.dumps(model["capability"][condition], ensure_ascii=False, indent=2)+"\n"
    retired = ["downloads/" + model["id"] + suffix for model in data["models"]
               for suffix in ("-public.json", "-public-retry.json")]
    write_publication(dest, prepare_publication(files, source_root), retired=retired)
    return data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=ROOT / "site")
    args = parser.parse_args()
    data = write_site(args.out)
    print(json.dumps({"status": "passed", "benchmark_version": data["benchmark_version"],
                      "models": len(data["models"]), "candidate_calls": 0}))


if __name__ == "__main__":
    main()
