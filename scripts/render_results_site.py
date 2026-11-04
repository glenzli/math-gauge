#!/usr/bin/env python3
"""Own the portable results projection and HTML; read frozen scores, never rescore.

Inputs are exactly four public result files. Only explicitly allowed aggregate
fields and the four public written panels enter the output; evaluator records,
original answers, execution dumps and private task details are never copied.
"""

import argparse
import hashlib
import html
import json
import math
from pathlib import Path
from string import Template


ROOT = Path(__file__).resolve().parents[1]
GITHUB = "https://github.com/glenzli/math-gauge"
ARTICLE = "https://glenzli.com/notes/ai-mathematical-ability-and-the-future/"
MODELS = (("terra", "Terra 6.1 Max"), ("gemini", "Gemini 3.8 Flash High"))
COMPONENTS = {
    "proofs": "书面论证",
    "lean-audit": "Lean 语义审计",
    "lean-formalization": "大 Lean 形式化",
    "exploration": "私有研究探索",
    "answer-review": "真实答卷审阅",
}
OVERALL = {
    "core": "首次答卷能力",
    "repeat": "独立复答",
    "neutral": "中性自查",
    "stance": "立场压力自查",
}
METRICS = tuple(COMPONENTS) + tuple(OVERALL) + (
    "overall", "answer_review_major_error_rate", "answer_review_strict_pass_rate",
)
COVERAGE = (
    "papers_planned", "parent_families", "a1_planned", "a1_reviewed",
    "slots_planned", "slots_reviewed",
)
METRIC_COVERAGE = (
    "planned", "adjudicated", "unknown", "started_slots", "reviewed_slots",
)
PUBLIC_PANEL = ("MG-GR002", "MG-GR014", "MG-GP001", "MG-GP002")
PANEL_SLOTS = (":A1", ":A2", ":neutral:1", ":affirm:1", ":deny:1")


def count(value):
    if type(value) is not int or value < 0:
        raise ValueError("Expected a nonnegative frozen coverage count")
    return value


def number(value, maximum=100):
    if (type(value) not in (int, float) or not math.isfinite(value)
            or not 0 <= value <= maximum):
        raise ValueError("Expected a finite frozen score in range")
    return value


def metric_projection(metric):
    """Copy a metric, including null, without deriving any score or denominator."""
    exact = metric["exact"]
    lower, upper = number(metric["lower"]), number(metric["upper"])
    if lower > upper or type(metric["complete"]) is not bool:
        raise ValueError("Invalid frozen metric bounds or completion status")
    if exact is not None:
        number(exact)
        if exact < lower - 1e-8 or exact > upper + 1e-8:
            raise ValueError("Frozen exact score is outside its bounds")
    return {
        "exact": exact, "lower": lower, "upper": upper,
        "complete": metric["complete"],
        "coverage": {key: count(metric["coverage"][key])
                     for key in METRIC_COVERAGE},
    }


def profile_projection(profile, scope):
    if profile["version"] != "0.6.0" or profile["standard_version"] != "0.6.0":
        raise ValueError("This editorial page is bound to the v0.6.0 draft")
    expected = set(COMPONENTS) - ({"exploration"} if scope == "public" else set())
    if {row["id"] for row in profile["components"]} != expected:
        raise ValueError("Unexpected frozen capability directions")
    if any(row["aggregation"] not in ("family", "parent_family")
           for row in profile["components"]):
        raise ValueError("Unexpected frozen family aggregation")
    if (profile.get("reliability_population") != "written-only"
            or profile.get("repeat_attempt_labels") != ["A1", "A2"]
            or profile.get("self_check_rounds_per_arm") != 1):
        raise ValueError("Unexpected written reliability panel contract")
    return {
        "version": profile["version"],
        "standard_version": profile["standard_version"],
        "components": [
            {"id": row["id"], "weight": number(row["weight"]),
             "case_count": count(row["case_count"]),
             "family_count": count(row["family_count"]),
             "aggregation": row["aggregation"]}
            for row in profile["components"]
        ],
        "overall_weights": {key: number(profile["overall_weights"][key])
                            for key in OVERALL},
        "repeat_attempt_labels": ["A1", "A2"],
        "self_check_rounds_per_arm": 1,
        "reliability_population": "written-only",
    }


def aggregate_projection(source, scope):
    schema = ("math-gauge.public-composite-score/v1" if scope == "public"
              else "math-gauge.combined-aggregate-only/v1")
    if source.get("schema") != schema:
        raise ValueError("Only explicit public and combined aggregate projections are allowed")
    if scope == "public":
        if source.get("score_units") != {"metrics": "percent", "completion": "fraction"}:
            raise ValueError("Unexpected public result units")
        evidence = source["evidence_status"]
        human = evidence["human_approval"]
        eligible = evidence["formal_comparison_eligible"]
        if evidence["backend_identity_independently_verified"] is not False:
            raise ValueError("Review the backend identity wording before changing this page")
    else:
        human = source["human_review"]
        eligible = source["formal_comparison_eligible"]
        if source.get("suite_version") != "0.6.0" or source.get("scope") != "combined":
            raise ValueError("Unexpected combined result identity")
    if human != "pending" or eligible is not False:
        raise ValueError("Review the human-pending wording before changing this page")
    profile = profile_projection(source["profile"], scope)
    allowed = [key for key in METRICS if key != "exploration" or scope == "combined"]
    result = {
        "profile": profile,
        "metrics": {key: metric_projection(source["metrics"][key]) for key in allowed},
        "coverage": {key: count(source["coverage"][key]) for key in COVERAGE},
        "human_review": human,
        "formal_comparison_eligible": eligible,
    }
    if scope == "combined":
        result["private_coverage_counts"] = {
            key: count(source["private_coverage_counts"][key])
            for key in ("planned", "responses_present", "reviews_present", "adjudicated")
        }
    return result


def written_panel_projection(source):
    """Select only known public case IDs and whole-answer completion fractions."""
    wanted = {case + suffix for case in PUBLIC_PANEL for suffix in PANEL_SLOTS}
    selected = [row for row in source["slot_evidence"] if row.get("slot_id") in wanted]
    rows = {row["slot_id"]: row for row in selected}
    if len(selected) != len(wanted) or set(rows) != wanted:
        raise ValueError("The four public written panels must be complete and unique")
    panels = []
    for case in PUBLIC_PANEL:
        values = []
        for suffix in PANEL_SLOTS:
            value = rows[case + suffix]["completion"]["exact"]
            values.append(None if value is None else number(value, 1))
        panels.append({"public_case_id": case, "whole_answer_completion": values})
    return panels


def load_data(source_root=ROOT):
    """Read exactly the four frozen public files; do not import the runner."""
    source_root = Path(source_root)
    models, sources = [], []
    for model, label in MODELS:
        projections = {}
        for scope, filename in (("public", "result.json"),
                                ("combined", "combined-aggregate.json")):
            relative = f"docs/results/{model}-v0.6.0/{filename}"
            raw = (source_root / relative).read_bytes()
            source = json.loads(raw)
            if scope == "public" and not source.get("id", "").startswith(model + "-"):
                raise ValueError("Unexpected public model label")
            if scope == "combined" and source.get("model") != model:
                raise ValueError("Unexpected combined model label")
            projections[scope] = aggregate_projection(source, scope)
            if scope == "public":
                projections["written_panel"] = written_panel_projection(source)
            sources.append({
                "model": model, "scope": scope, "path": relative,
                "url": f"{GITHUB}/blob/main/{relative}",
                "sha256": hashlib.sha256(raw).hexdigest(),
            })
        # One direction table may show shared direction scores only if they agree.
        for key in set(COMPONENTS) - {"exploration"}:
            if projections["public"]["metrics"][key] != projections["combined"]["metrics"][key]:
                raise ValueError("Public and combined direction scores diverged; update the display")
        models.append({"id": model, "requested_model_label": label, **projections})
    for scope in ("public", "combined"):
        if models[0][scope]["profile"] != models[1][scope]["profile"]:
            raise ValueError("Models do not share the same frozen display profile")
    return {
        "schema": "math-gauge.portable-results/v1",
        "suite_version": "0.6.0",
        "status": "local-draft-human-pending",
        "formal_comparison_eligible": False,
        "backend_identity_independently_verified": False,
        "score_units": {"metrics": "percent", "whole_answer_completion": "fraction"},
        "models": models, "sources": sources,
    }


def escape(value):
    return html.escape(str(value), quote=True)


def score_html(metric, precision=2):
    if metric["exact"] is None:
        lower = f'{metric["lower"]:.{precision}f}'
        upper = f'{metric["upper"]:.{precision}f}'
        approximate = (float(lower) != metric["lower"]
                       or float(upper) != metric["upper"])
        prefix = "约 " if approximate else ""
        return (f'<strong class="unresolved">未决</strong>'
                f'<span class="bounds">{prefix}[{lower}, {upper}]</span>')
    value = f'{metric["exact"]:.{precision}f}'
    prefix = '<small>约 </small>' if float(value) != metric["exact"] else ""
    return f'<strong class="score">{prefix}{value}</strong>'


def component(profile, key):
    return next(row for row in profile["components"] if row["id"] == key)


def render_html(data):
    terra, gemini = data["models"]
    public, combined = terra["public"], terra["combined"]
    pc, cc = public["coverage"], combined["coverage"]
    score_rows = []
    for model in data["models"]:
        cells = []
        for scope, title in (("public", "公开范围"), ("combined", "合并范围")):
            result = model[scope]
            coverage = result["coverage"]
            cells.append(
                f'<td data-label="{title}">{score_html(result["metrics"]["overall"])}'
                f'<span class="coverage">已审核 {coverage["slots_reviewed"]}'
                f' / {coverage["slots_planned"]} 条记录</span></td>'
            )
        score_rows.append(f'<tr><th scope="row">{escape(model["requested_model_label"])}'
                          '<span class="subtle">请求的模型标签</span></th>'
                          + "".join(cells) + '</tr>')
    capability_rows = []
    for key, title in COMPONENTS.items():
        scope = "combined" if key == "exploration" else "public"
        row = component(combined["profile"], key)
        public_weight = ("—" if key == "exploration"
                         else f'{component(public["profile"], key)["weight"]:g}%')
        weights = f'公开 {public_weight} · 合并 {row["weight"]:g}%'
        values = "".join(f'<td>{score_html(model[scope]["metrics"][key])}</td>'
                         for model in data["models"])
        capability_rows.append(
            f'<tr><th scope="row">{title}<span class="subtle">'
            f'{row["case_count"]} 份任务 · {row["family_count"]} 个家族</span>'
            f'<span class="weight">{weights}</span></th>{values}</tr>'
        )
    weight_items = "".join(
        f'<li><strong>{weight:g}%</strong><span>{OVERALL[key]}</span></li>'
        for key, weight in public["profile"]["overall_weights"].items()
    )
    reliability_cards = []
    for key, title, note in (
        ("repeat", "独立复答", "4 道书面题，各自 A1 / A2 均严格完成"),
        ("neutral", "中性自查", "4 份中性追问，评审重点数学结论与论据"),
        ("stance", "立场压力自查", "8 份肯定 / 否定追问，评审重点数学结论与论据"),
    ):
        scores = "".join(
            f'<div><span>{escape(model["id"].title())}</span>'
            f'{score_html(model["public"]["metrics"][key])}</div>'
            for model in data["models"]
        )
        reliability_cards.append(f'<article class="reliability-card"><h3>{title}</h3>'
                                 f'<p>{note}</p><div class="pair">{scores}</div></article>')
    panels = []
    for index, case in enumerate(PUBLIC_PANEL):
        rows = []
        for model in data["models"]:
            values = model["written_panel"][index]["whole_answer_completion"]
            cells = "".join(f'<td>{"未决" if value is None else f"{value * 100:g}"}</td>'
                            for value in values)
            rows.append(f'<tr><th scope="row">{model["id"].title()}</th>{cells}</tr>')
        panels.append(f'<article class="panel"><h3>{case}</h3><table>'
                      '<caption class="sr-only">全题完成度，百分制</caption><thead>'
                      '<tr><th scope="col">模型</th><th scope="col">A1</th>'
                      '<th scope="col">A2</th><th scope="col">中性</th>'
                      '<th scope="col">肯定</th><th scope="col">否定</th></tr>'
                      f'</thead><tbody>{"".join(rows)}</tbody></table></article>')
    source_items = "".join(
        f'<li><a href="{escape(source["url"])}">{source["model"].title()} · '
        f'{"公开结果" if source["scope"] == "public" else "合并聚合"}</a>'
        f'<code>SHA-256 {source["sha256"]}</code></li>'
        for source in data["sources"]
    )
    major = " / ".join(
        f'{model["id"].title()} '
        f'{model["public"]["metrics"]["answer_review_major_error_rate"]["exact"]:g}%'
        for model in data["models"]
    )
    return PAGE.substitute(
        github=GITHUB, article=ARTICLE, score_rows="".join(score_rows),
        capability_rows="".join(capability_rows), weight_items=weight_items,
        reliability_cards="".join(reliability_cards), panels="".join(panels),
        source_items=source_items, major=major,
        public_tasks=pc["papers_planned"], public_families=pc["parent_families"],
        public_records=pc["slots_planned"], combined_tasks=cc["papers_planned"],
        combined_families=cc["parent_families"], combined_records=cc["slots_planned"],
        private_tasks=combined["private_coverage_counts"]["planned"],
    )


PAGE = Template('''<!doctype html>
<!-- Generated by scripts/render_results_site.py; owner: frozen-result display only. -->
<html lang="zh-CN">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta http-equiv="Content-Security-Policy" content="default-src 'none'; style-src 'unsafe-inline'; base-uri 'none'; form-action 'none'">
<meta name="description" content="Math Gauge 0.6.0 本地开发结果：数学推理、Lean 语义对应、工程交付与书面自查。AI 审核，人审待定。">
<title>Math Gauge：可靠地完成数学工作</title>
<style>
:root{color-scheme:light;--paper:#f7f5ee;--surface:#fffef9;--ink:#182b3b;--muted:#53626b;--line:#d9ded7;--teal:#146860;--wash:#eaf1eb;--amber:#80532d;--amber-wash:#f5eadb}
*{box-sizing:border-box}html{scroll-behavior:smooth;scroll-padding-top:1.5rem}body{margin:0;background:var(--paper);color:var(--ink);font:16px/1.75 -apple-system,BlinkMacSystemFont,"Segoe UI","PingFang SC","Hiragino Sans GB","Microsoft YaHei",sans-serif}a{color:var(--teal);text-underline-offset:.22em}a:hover{text-decoration-thickness:2px}a:focus-visible{outline:3px solid var(--teal);outline-offset:5px;border-radius:2px}p,h1,h2,h3{margin-top:0}p{margin-bottom:1rem}h1,h2,h3{line-height:1.35}h1{font-size:clamp(2rem,4.5vw,3.6rem);letter-spacing:-.045em;margin-bottom:1.2rem;font-weight:650}h2{font-size:1.65rem;letter-spacing:-.025em;margin-bottom:.75rem}h3{font-size:1rem;margin-bottom:.6rem}strong{font-weight:650}.shell{width:min(1080px,calc(100% - 64px));margin:auto}.top{display:flex;align-items:center;justify-content:space-between;gap:1rem;padding:25px 0;border-bottom:1px solid var(--line)}.wordmark{font-size:.88rem;font-weight:750;letter-spacing:.12em;color:var(--ink);text-decoration:none}.wordmark span{font-weight:450;color:var(--muted);letter-spacing:0;margin-left:.8rem}.top nav{display:flex;gap:1.4rem;font-size:.85rem}.top nav a{text-decoration:none}.hero{display:grid;grid-template-columns:1.8fr 1fr;gap:3rem;padding:68px 0 40px;align-items:end}.eyebrow{color:var(--teal);font-size:.76rem;font-weight:700;letter-spacing:.16em;margin-bottom:1rem}.hero h1 span{color:var(--teal)}.lead{max-width:38rem;color:var(--muted);font-size:1.05rem}.scope{padding:1.5rem 0 1.5rem 1.7rem;border-left:2px solid var(--teal)}.scope p{font-size:.8rem;color:var(--muted);margin:0 0 .6rem}.scope dl{display:flex;gap:1.5rem;margin:0}.scope dl div{display:flex;flex-direction:column}.scope dt{font-size:.78rem;color:var(--muted);order:2}.scope dd{font-size:2.15rem;line-height:1.2;margin:0;font-variant-numeric:tabular-nums;letter-spacing:-.04em}.status{display:flex;flex-wrap:wrap;gap:.5rem;align-items:center;margin:0 0 42px;padding:13px 17px;background:var(--amber-wash);border-left:3px solid var(--amber);font-size:.82rem;color:var(--amber)}.status strong{margin-right:.4rem}.status span+span:before{content:"·";margin-right:.5rem}.section{padding:38px 0;border-top:1px solid var(--line)}.intro{color:var(--muted);max-width:55rem}.section-heading{display:flex;align-items:baseline;justify-content:space-between;gap:1rem}.unit{font-size:.8rem;color:var(--muted);white-space:nowrap}.scope-line{display:flex;gap:1rem 2rem;flex-wrap:wrap;font-size:.84rem;color:var(--muted);margin:1rem 0 1.4rem}.scope-line b{font-weight:600;color:var(--ink)}table{width:100%;border-collapse:collapse;font-variant-numeric:tabular-nums;text-align:left}th,td{padding:17px 20px;border-bottom:1px solid var(--line);vertical-align:top}thead th{font-size:.78rem;color:var(--muted);font-weight:500;padding-top:10px;padding-bottom:10px}tbody th{font-weight:600}.results{background:var(--surface);border:1px solid var(--line)}.results thead{background:var(--wash)}.results th:first-child{width:32%}.results td{width:34%}.score{font-variant-numeric:tabular-nums;font-size:1.25rem;line-height:1.4;letter-spacing:-.025em}.results .score{font-size:2.05rem;font-weight:600}.unresolved{color:var(--amber);font-size:1.1rem}.bounds{display:block;color:var(--amber);font-size:.87rem;font-variant-numeric:tabular-nums;line-height:1.55;margin-top:.25rem}.coverage,.subtle,.weight{display:block;font-size:.76rem;font-weight:400;line-height:1.6;color:var(--muted);margin-top:.3rem}.weight{color:var(--teal);margin-top:.5rem}.note{font-size:.84rem;color:var(--muted);margin:1.1rem 0 0}.note strong{color:var(--ink)}.reading-note{margin-top:1.4rem;padding-left:1.1rem;border-left:2px solid var(--line)}.weights{display:grid;grid-template-columns:repeat(4,1fr);list-style:none;padding:0;margin:1.5rem 0 0;border-top:1px solid var(--line);border-bottom:1px solid var(--line)}.weights li{padding:1rem .9rem 1rem 0}.weights strong{font-size:1.5rem;font-variant-numeric:tabular-nums;color:var(--teal);display:block;line-height:1.3}.weights span{font-size:.78rem;color:var(--muted)}.capabilities{table-layout:fixed;margin-top:1.3rem}.capabilities th:first-child{width:44%}.capabilities td{width:28%}.capabilities tbody td{text-align:left}.capabilities th,.capabilities td{padding-left:0;padding-right:16px}.capabilities .score{font-size:1.3rem}.capabilities .bounds{font-size:.78rem}.reliability{display:grid;grid-template-columns:repeat(3,1fr);gap:16px;margin:1.5rem 0}.reliability-card{background:var(--surface);border:1px solid var(--line);padding:20px}.reliability-card p{font-size:.78rem;line-height:1.65;color:var(--muted);min-height:3.3em}.pair{display:flex;gap:1.4rem}.pair div{display:flex;flex-direction:column}.pair span{font-size:.75rem;color:var(--muted)}.pair .score{font-size:1.55rem}.panels{display:grid;grid-template-columns:repeat(2,1fr);gap:1.3rem 2rem;margin-top:1.5rem}.panel h3{font-size:.83rem;letter-spacing:.035em;color:var(--teal);margin-bottom:.5rem}.panel th,.panel td{padding:8px 5px;font-size:.8rem}.panel thead th{font-size:.72rem;background:var(--wash)}.panel td{text-align:center}.panel th:first-child{width:22%}.methods{display:grid;grid-template-columns:repeat(3,1fr);gap:2rem;margin-top:1.5rem}.methods h3{color:var(--teal)}.methods p{font-size:.84rem;color:var(--muted);margin:0}.philosophy{padding:20px 24px;background:var(--wash);font-size:.86rem;line-height:1.85;margin-top:2rem}.philosophy p{margin:0}.resources{display:flex;flex-wrap:wrap;gap:.7rem 1.4rem;margin:1.3rem 0;font-size:.88rem}.download{display:inline-block;border:1px solid var(--teal);padding:7px 13px;border-radius:3px;text-decoration:none;font-weight:600;font-size:.8rem}.sources{list-style:none;padding:0;margin:1.8rem 0 0;display:grid;grid-template-columns:repeat(2,1fr);gap:1rem 2rem}.sources a{font-size:.82rem}.sources code{display:block;margin-top:.25rem;color:var(--muted);font-size:.63rem;overflow-wrap:anywhere;line-height:1.6}.footer{border-top:1px solid var(--line);padding:24px 0 38px;font-size:.76rem;color:var(--muted);display:flex;gap:1rem;justify-content:space-between}.footer p{margin:0}.sr-only{position:absolute;width:1px;height:1px;padding:0;margin:-1px;overflow:hidden;clip:rect(0,0,0,0);white-space:nowrap;border:0}.skip{position:absolute;left:1rem;top:-5rem;background:var(--surface);padding:.5rem 1rem}.skip:focus{top:1rem}
@media(max-width:720px){.shell{width:calc(100% - 40px)}.hero{grid-template-columns:1fr;gap:1.4rem;padding:40px 0 28px}.hero h1{font-size:2.3rem}.scope{padding:.3rem 0 .3rem 1.2rem}.scope dl{gap:2rem}.scope dd{font-size:1.8rem}.status{margin-bottom:28px}.section{padding:28px 0}.reliability{grid-template-columns:1fr}.reliability-card{padding:16px 20px;display:grid;grid-template-columns:1fr auto;column-gap:1rem}.reliability-card h3{margin-bottom:.3rem}.reliability-card p{grid-column:1;min-height:0;margin:0}.reliability-card .pair{grid-column:2;grid-row:1/3;align-self:center;gap:1rem}.pair .score{font-size:1.3rem}.methods{grid-template-columns:1fr;gap:1.3rem}.panels{grid-template-columns:1fr;gap:1.5rem}.sources{grid-template-columns:1fr}.footer{display:block}.footer p+p{margin-top:.4rem}.top{padding:19px 0}.top nav{gap:1rem}.top nav a:last-child{display:none}h2{font-size:1.4rem}.scope-line{display:block}.scope-line span{display:block;margin:.3rem 0}.results,.results tbody{display:block}.results thead{display:none}.results tr{display:grid;grid-template-columns:1fr 1fr}.results tbody th{grid-column:1/-1;background:var(--wash);width:auto!important;padding:12px 16px}.results td{width:auto;padding:15px 16px}.results td+td{border-left:1px solid var(--line)}.results td:before{content:attr(data-label);display:block;font-size:.75rem;color:var(--muted);margin-bottom:.3rem}.results .score{font-size:1.65rem}.results .bounds{font-size:.75rem;overflow-wrap:anywhere}.results .coverage{font-size:.67rem}.results .subtle{display:inline;margin-left:.6rem;font-size:.7rem}.capabilities .score{font-size:1.15rem}.capabilities .bounds{font-size:.68rem;overflow-wrap:anywhere}.capabilities th:first-child{width:44%}.capabilities th,.capabilities td{padding-right:10px;padding-top:13px;padding-bottom:13px}.capabilities tbody th{font-size:.88rem}.capabilities .weight,.capabilities .subtle{font-size:.67rem}.weights{grid-template-columns:repeat(2,1fr)}.weights li:nth-child(-n+2){border-bottom:1px solid var(--line)}.philosophy{padding:17px 18px}}
@media(prefers-reduced-motion:reduce){html{scroll-behavior:auto}}
@media print{body{background:white;font-size:11pt}.shell{width:100%}.top nav,.download{display:none}.hero{padding:24px 0}.section{break-inside:avoid}.score,.results .score{font-size:18pt}a{color:inherit}.status{background:none}.sources code{font-size:7pt}}
</style>
</head>
<body>
<a class="skip" href="#main">跳到结果</a>
<div class="shell">
<header class="top"><a class="wordmark" href="#main">MATH GAUGE <span>0.6.0</span></a><nav aria-label="页内导航"><a href="#results">结果</a><a href="#method">方法</a><a href="#sources">资料</a></nav></header>
<main id="main">
<section class="hero" aria-labelledby="title"><div><p class="eyebrow">数学能力 · 开发观察</p><h1 id="title">Math Gauge：<br><span>可靠地完成数学工作</span></h1><p class="lead">沿着原题的假设、量词与结论，检查数学推理、Lean 语义对应、完整工程交付，以及面对追问时的自查表现。</p></div><aside class="scope" aria-label="公开范围"><p>当前公开范围</p><dl><div><dt>份任务</dt><dd>$public_tasks</dd></div><div><dt>个数学家族</dt><dd>$public_families</dd></div><div><dt>条标准记录</dt><dd>$public_records</dd></div></dl></aside></section>
<p class="status"><strong>本地 0.6.0 草稿</strong><span>AI 审核 / 人审待定</span><span>正式模型比较资格：否</span></p>

<section class="section" id="results" aria-labelledby="results-title">
<div class="section-heading"><h2 id="results-title">标准原答结果</h2><span class="unit">综合分 / 100</span></div>
<p class="intro">能力以首次独立答卷为准。复答与三个独立自查分支按冻结计划另计，后续研究不替换原始答卷。</p>
<div class="scope-line"><span><b>公开</b> $public_tasks 份任务 · $public_families 个家族 · $public_records 条记录</span><span><b>合并</b> 增加 $private_tasks 份私有探索 · 共 $combined_tasks 份任务 / $combined_families 个家族 / $combined_records 条记录</span></div>
<table class="results"><caption class="sr-only">两模型的公开及合并范围综合分和审核覆盖</caption><thead><tr><th scope="col">模型请求标签</th><th scope="col">公开范围</th><th scope="col">合并范围</th></tr></thead><tbody>$score_rows</tbody></table>
<div class="reading-note"><p class="note"><strong>本轮调用与专项研究已结束。</strong>Gemini 的原 92 项首答为 ERROR，未形成有效交付；该标准槽继续未决，完整精确分保留为 null。未决不代表仍在运行。</p><p class="note">方括号表示<strong>固定分母下未知贡献的上下界</strong>，不是统计置信区间，不用中点代替分数，也不把未决补成数学 0。缺测、执行失败与未决均保留完整分母。显示数值经四舍五入，完整精度见下载数据。</p></div>
<ul class="weights" aria-label="冻结综合权重">$weight_items</ul>
</section>

<section class="section" aria-labelledby="capability-title"><div class="section-heading"><h2 id="capability-title">首次答卷的能力方向</h2><span class="unit">方向分 / 100</span></div><p class="intro">同一数学家族内先聚合，再平均方向内家族。表内方向分在公开与合并范围中相同，权重分别列出；私有探索仅显示聚合值。</p>
<table class="capabilities"><caption class="sr-only">能力方向、任务家族数量、公开与合并权重，以及两模型方向分</caption><thead><tr><th scope="col">方向与能力权重</th><th scope="col">Terra</th><th scope="col">Gemini</th></tr></thead><tbody>$capability_rows</tbody></table>
<p class="note">8 / 20 / 40 项形式化梯度共享同一 CH2 家族，92 项属于另一家族；义务数不当作独立样本数。真实编译、语义对齐、AI 审核与人工批准分别记录。</p><p class="note">答卷审阅的重大误判率单列：<strong>$major</strong>。审阅共 4 份既有答卷，按母题家族聚合；这里的样本比例不能解释为一般错误率。</p></section>

<section class="section" aria-labelledby="reliability-title"><div class="section-heading"><h2 id="reliability-title">书面答卷的复答与自查</h2><span class="unit">冻结指标 / 100</span></div><p class="intro">固定 4 道书面题，各有独立 A1 / A2。中性、肯定、否定三臂均从各自 A1 独立展开，每臂追问一次，彼此不可见。</p><div class="reliability">$reliability_cards</div><p class="note">中性与立场指标检查预先指定的重点数学结论及论据，100 分不表示全卷严格通过。下面另列各答卷的<strong>全题阶段完成度（%）</strong>，不以重点指标覆盖原错误。</p><div class="panels">$panels</div><p class="note">A1：首次独立答卷；A2：再次独立作答；中性 / 肯定 / 否定：三个独立追问分支。固定面板不能代表所有任务的一般可靠性。</p></section>

<section class="section" id="method" aria-labelledby="method-title"><h2 id="method-title">如何理解这次观察</h2><div class="methods"><article><h3>观察后的开发组合</h3><p>每模型的标准 42 条由 24 条精确相容旧答复用与 18 条新补考组成，另有 3 条私有探索进入合并范围。保留各来源真实系统、参数与预算；这不是一场同步、全部重新作答的考试。</p></article><article><h3>原答与研究分轨</h3><p>92 项整章的三轮对齐研究、首次归档工程诊断及额外续作均独立报告。它们不进入标准分母，也不拿改好后的工程替换首次答卷。<a href="$github/blob/main/docs/benchmark-comparison-v0.6.0.md">阅读完整结果与来源</a>。</p></article><article><h3>证据仍有边界</h3><p>题目与答卷均人审待定，尚未取得正式比较资格。模型名称是请求标签，后端身份未独立核实。公开参考与 Git 历史保留透明性；历史精确版本的公开可得性尚未核实，不称隐藏留出集。</p></article></div><aside class="philosophy"><p>这里的 Lv1 指计算与执行，Lv2 指既定框架内的证明、反驳与构造；它们不是难度等级，前沿证明也可能属于 Lv2。<a href="$article">数学能力观的背景说明</a>。</p></aside></section>

<section class="section" id="sources" aria-labelledby="sources-title"><div class="section-heading"><h2 id="sources-title">数据、来源与状态</h2><a class="download" href="data.json" download="math-gauge-v0.6.0-summary.json">下载聚合数据 JSON</a></div><p class="intro">本页从四份冻结公开结果读取数值与权重，没有另行评分。下载文件只含白名单聚合、公开书面面板与来源散列；私有部分只保留总分、方向分和覆盖总数。</p><div class="resources"><a href="$github">项目与使用说明</a><a href="$github/blob/main/docs/benchmark-comparison-v0.6.0.md">完整结果与来源</a><a href="$github/blob/main/protocol/evaluation.md">评测协议</a><a href="$github/blob/main/protocol/benchmark-scoring.md">评分合同</a></div><ul class="sources">$source_items</ul><p class="note">此页与下载数据可完整离线阅读；外部链接用于查阅仓库和背景文献。当前仍为本地开发草稿，题目与答卷的人审尚未完成。</p></section>
</main><footer class="footer"><p>Math Gauge · Measure the capability, not just the answer.</p><p>0.6.0 local draft · AI reviewed · Human pending</p></footer>
</div></body></html>
''')


def build_site(source_root, out_dir):
    """Write only the portable HTML and explicitly projected download."""
    data = load_data(source_root)
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "index.html").write_text(render_html(data), encoding="utf-8")
    (out_dir / "data.json").write_text(
        json.dumps(data, ensure_ascii=False, indent=2, allow_nan=False) + "\n",
        encoding="utf-8",
    )
    return data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, default=ROOT,
                        help="repository root containing the four frozen public results")
    parser.add_argument("--out-dir", type=Path, default=ROOT / "site",
                        help="destination directory; default: site/")
    args = parser.parse_args()
    build_site(args.source_root, args.out_dir)
    print(f"Wrote portable index.html and data.json to {args.out_dir}")


if __name__ == "__main__":
    main()
