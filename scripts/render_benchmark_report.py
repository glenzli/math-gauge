#!/usr/bin/env python3
"""Render an already scored, public-only result as standalone HTML and Markdown.

Scoring and private-data projection belong to math_gauge, not this renderer.
The HTML uses no network resources and can be opened directly from disk.
"""

import argparse
from collections import Counter
from decimal import Decimal, ROUND_CEILING, ROUND_FLOOR
import hashlib
import html
import json
from pathlib import Path


COMPONENTS = (
    ("proofs", "书面推理", "证明、反例、构造与分类"),
    ("lean-audit", "Lean 语义审计", "核对形式声明与原命题"),
    ("lean-construction", "Lean 生成与修复", "完整源码及语义对应"),
    ("chapters", "整章形式化", "逐章归一化完整交付"),
    ("exploration", "研究探索", "三份私有任务，各一次初答"),
)
RELIABILITY = (
    ("repeat", "三次全对", "6 题 · 各 A1 / A2 / A3"),
    ("neutral", "中性自查", "6 题 · 12 次后续"),
    ("stance", "立场自查", "6 题 · 24 次后续"),
)


def escape(value):
    return html.escape(str(value), quote=True)


def value(metric):
    """Accept the public score metric and the unchanged historical value metric."""
    return metric.get("exact", metric.get("value"))


def number(item):
    return "待完成" if item is None else f"{item:.2f}"


def score(metric):
    return number(value(metric))


def private_score(record):
    """Display the runner's normalized completion in the table's percent unit."""
    exact = value(record["completion"])
    return number(None if exact is None else exact * 100)


def interval(metric):
    lower = Decimal(str(metric["lower"])).quantize(Decimal(".01"), rounding=ROUND_FLOOR)
    upper = Decimal(str(metric["upper"])).quantize(Decimal(".01"), rounding=ROUND_CEILING)
    return f"{lower:.2f}–{upper:.2f}"


def result_view(report):
    """Prepare display fields only; never derive a score or eligibility decision."""
    if report.get("schema") != "math-gauge.public-composite-score/v1":
        raise ValueError("The renderer requires the explicit public score projection")
    if report.get("score_units") != {"metrics": "percent", "completion": "fraction"}:
        raise ValueError("Expected percent aggregate metrics and fractional paper completion")
    metrics = report["metrics"]
    for key, *_ in COMPONENTS + RELIABILITY:
        if key not in metrics:
            raise ValueError(f"Public result is missing metric {key}")
    for key in ("core", "overall"):
        if key not in metrics:
            raise ValueError(f"Public result is missing metric {key}")
    components = report["profile"]["components"]
    weights = {item["id"]: item["weight"] for item in components}
    if set(weights) != {item[0] for item in COMPONENTS}:
        raise ValueError("Public result must name the five frozen component weights")
    if (weights != {"proofs": 25, "lean-audit": 20, "lean-construction": 20,
                    "chapters": 20, "exploration": 15}
            or report["profile"]["overall_weights"] != {
                "core": 75, "repeat": 5, "neutral": 10, "stance": 10}
            or report["profile"].get("version") != "0.2.0"):
        raise ValueError("This report requires the approved composite profile v0.2.0")
    coverage = report["coverage"]
    if coverage["a1_planned"] != 35 or coverage["slots_planned"] != 83:
        raise ValueError("This dated report template requires 35 A1 papers and 83 slots")
    sources = Counter(item["source_kind"] for item in report["slot_evidence"])
    if sources != {"historical_public": 80, "existing_private": 1, "new_private": 2}:
        raise ValueError("This report requires the frozen 80+1+2 source composition")
    strict = report["strict_passes"]["core_A1"]
    records = sorted(report["private_records"], key=lambda item: item["public_id"])
    if [item["public_id"] for item in records] != ["Private-01", "Private-02", "Private-03"]:
        raise ValueError("The private display projection must use only the three neutral IDs")
    return {
        "metrics": metrics,
        "weights": weights,
        "overall_weights": report["profile"]["overall_weights"],
        "profile_version": report["profile"]["version"],
        "coverage": coverage,
        "strict": strict,
        "private": records,
        "complete": value(metrics["overall"]) is not None,
    }


def private_status(record):
    statuses = {
        "pending": "未返回",
        "not_run": "未运行",
        "execution_failed": "执行失败",
        "execution_failure": "执行失败",
        "review_pending": "待评阅",
        "unresolved": "审核未决",
        "reviewed": "AI 已评阅",
        "complete": "AI 已评阅",
    }
    if record.get("status") in statuses:
        if record["status"] in ("reviewed", "complete") and record.get("human_status") == "reviewed":
            return "人工已评阅"
        return statuses[record["status"]]
    if value(record["completion"]) is None:
        return "待完成"
    return "AI 已评阅"


def human_status(record):
    return {"pending": "待人审", "reviewed": "人工已审阅", "approved": "人工已批准", "rejected": "人工未批准"}.get(
        record.get("human_status"), "待人审")


def runtime_note(report):
    timeouts = report.get("composition", {}).get("source_timeout_seconds", [])
    if not timeouts:
        return ""
    return "各源运行保留各自冻结时限（秒）：" + "、".join(str(item) for item in timeouts) + "。组合没有重置历史预算。"


def all_strict_note(report):
    strict = report["strict_passes"].get("all_selected_slots")
    if not strict:
        return ""
    return (f"全部已裁决材料严格通过 {strict['passed']} / {strict['adjudicated']}"
            f"（含重复与自查，计划共 {strict['total']} 槽）；此诊断不额外计分。")


def formula_terms(view):
    return [f"{view['overall_weights'][key]}% {title}" for key, title in (
        ("core", "能力分"), ("repeat", "三次全对"),
        ("neutral", "中性自查"), ("stance", "立场自查"))]


def weighting_note(view):
    return (f"组合 profile v{view['profile_version']} 的权重是在已知全部结果后作出的方法调整，"
            "属于价值判断，不按 token、篇幅或证明条数估权。")


def bar(metric):
    lower = metric["lower"]
    upper = metric["upper"]
    exact = value(metric)
    label = score(metric) if exact is not None else f"待完成，固定分母范围 {interval(metric)}"
    unknown = "" if exact is not None else (
        f'<span class="unknown" style="left:{lower}%;width:{upper - lower}%"></span>'
    )
    return (
        f'<div class="bar" role="img" aria-label="{escape(label)}">'
        f'<span class="known" style="width:{lower}%"></span>{unknown}</div>'
    )


def render_html(report, source_sha256):
    view = result_view(report)
    metrics, coverage = view["metrics"], view["coverage"]
    overall, core = metrics["overall"], metrics["core"]
    strict = view["strict"]
    status = "结果已汇总" if view["complete"] else "等待剩余答卷与审核"
    result_note = (
        "五方向能力与原六题可靠性面板的加权结果。"
        if view["complete"] else
        f"固定 83 槽分母下的范围 {interval(overall)}；未决贡献仍保留。"
    )
    component_rows = []
    for key, title, description in COMPONENTS:
        metric = metrics[key]
        count = metric["coverage"]["planned"]
        adjudicated = metric["coverage"]["adjudicated"]
        count_label = f"{count} 份 A1" if count == adjudicated else f"{adjudicated} / {count} 份已评阅"
        component_rows.append(
            f'<div class="component"><div><h3>{title}</h3><p>{description}</p></div>'
            f'<div class="component-chart">{bar(metric)}<span>{count_label} · 能力权重 {view["weights"][key]}%</span></div>'
            f'<strong class="component-score {"pending" if value(metric) is None else ""}">{score(metric)}</strong></div>'
        )
    chart_legend = (
        '<p class="footnote">实色表示已确定贡献，斜纹表示未决范围；它们共享完整计划的固定分母。</p>'
        if not view["complete"] else ""
    )
    reliability_cards = "".join(
        f'<article class="reliability-card"><p>{title}</p><strong>{score(metrics[key])}<small>/ 100</small></strong>'
        f'<span>{description}</span></article>' for key, title, description in RELIABILITY
    )
    private_rows = "".join(
        f'<tr><th scope="row">{escape(record["public_id"])}</th><td>研究探索 · A1</td>'
        f'<td class="tabular">{private_score(record)}</td>'
        f'<td>{private_status(record)}</td><td>{human_status(record)}</td></tr>' for record in view["private"]
    )
    formula = formula_terms(view)
    pending_note = (
        "全部计划槽位已接入 AI 审核。"
        if coverage["slots_reviewed"] == coverage["slots_planned"] else
        f'已接入 {coverage["slots_reviewed"]} / {coverage["slots_planned"]} 槽；未完成项不会按已完成部分重新归一化。'
    )
    private_fingerprints = "".join(
        f'<dt>{escape(record["public_id"])} 原始答卷</dt><dd><code>{escape(record["response_sha256"])}</code></dd>'
        for record in view["private"] if record.get("response_sha256")
    )
    budget_fingerprint = (
        f'<dt>源运行时限</dt><dd>{escape(runtime_note(report))}</dd>'
        if runtime_note(report) else ""
    )
    return f'''<!doctype html>
<html lang="zh-CN">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<meta name="color-scheme" content="light">
<meta name="description" content="Terra 6.1 Max 的 Math Gauge 综合开发结果：35份初答、83个计划槽位，五方向能力与六题可靠性面板。">
<title>Terra 6.1 · 首次综合评测 | Math Gauge</title>
<style>
:root{{--paper:#f5f3ed;--white:#fffefa;--ink:#172b3a;--muted:#586770;--line:#d8ddd8;--accent:#b7492c;--blue:#315d78;--pale:#e5eae7;--font:Inter,"Segoe UI","PingFang SC","Microsoft YaHei",sans-serif}}
*{{box-sizing:border-box}}html{{scroll-behavior:smooth}}body{{margin:0;background:var(--paper);color:var(--ink);font-family:var(--font);line-height:1.65;-webkit-font-smoothing:antialiased}}a{{color:var(--blue);text-underline-offset:4px}}a:hover{{color:var(--accent)}}a:focus-visible,summary:focus-visible{{outline:3px solid var(--accent);outline-offset:5px}}.skip{{position:absolute;left:20px;top:-80px;padding:8px;background:var(--white);z-index:5}}.skip:focus{{top:8px}}.shell{{width:min(1120px,calc(100% - 80px));margin:auto}}header{{border-bottom:1px solid var(--line)}}.masthead{{min-height:88px;display:flex;align-items:center;justify-content:space-between;gap:24px}}.brand{{display:flex;align-items:center;gap:12px;color:var(--ink);text-decoration:none;font-weight:750;letter-spacing:.04em}}.mark{{height:32px;width:32px;border:1.5px solid var(--ink);display:grid;place-items:center;font:italic 25px Georgia,serif}}.masthead nav{{display:flex;gap:24px;font-size:13px}}.masthead nav a{{color:var(--muted);text-decoration:none}}.eyebrow{{font-size:11px;letter-spacing:.16em;text-transform:uppercase;color:var(--muted);font-weight:650}}.hero{{padding:60px 0 48px;display:grid;grid-template-columns:1.2fr 1fr;gap:60px;align-items:center}}.hero h1{{font-size:clamp(40px,5vw,62px);line-height:1.1;letter-spacing:-.055em;margin:18px 0 18px;font-weight:730}}.hero h1 span{{display:block;font-size:.46em;font-weight:450;letter-spacing:-.025em;margin-top:16px}}.lede{{font-size:16px;color:var(--muted);max-width:510px;margin:0}}.chips{{display:flex;flex-wrap:wrap;gap:8px;margin-top:22px}}.chip{{font-size:11px;border:1px solid var(--line);border-radius:30px;padding:4px 10px;color:var(--muted)}}.chip.status{{color:var(--accent);border-color:#d6b7a8;background:#f6ece5}}.scorebox{{border-left:1px solid var(--line);padding-left:42px}}.score-label{{display:flex;align-items:center;gap:10px;font-size:13px}}.dot{{width:6px;height:6px;border-radius:50%;background:var(--accent)}}.score-large{{font-size:clamp(64px,8vw,96px);line-height:1.12;letter-spacing:-.065em;font-weight:670;font-variant-numeric:tabular-nums;white-space:nowrap;margin-top:12px}}.score-large.waiting{{font-size:clamp(40px,6vw,64px);letter-spacing:-.035em;margin:22px 0}}.score-large small{{font-size:17px;letter-spacing:0;color:var(--muted);font-weight:400;margin-left:12px}}.score-note{{margin-top:16px;font-size:12px;color:var(--muted);max-width:330px}}.statstrip{{border-top:1px solid var(--line);border-bottom:1px solid var(--line);display:grid;grid-template-columns:repeat(4,1fr);padding:22px 0}}.stat{{padding:0 26px;border-left:1px solid var(--line)}}.stat:first-child{{padding-left:0;border:0}}.stat strong{{font-size:26px;letter-spacing:-.035em;font-weight:620;font-variant-numeric:tabular-nums}}.stat strong small{{font-size:15px;color:var(--muted);font-weight:400;letter-spacing:0}}.stat span{{display:block;font-size:12px;color:var(--muted);margin-top:2px}}section{{padding:42px 0;border-bottom:1px solid var(--line)}}.sectionhead{{display:flex;align-items:flex-end;justify-content:space-between;gap:24px;margin-bottom:26px}}.sectionhead h2{{font-size:23px;font-weight:650;letter-spacing:-.025em;margin:0}}.sectionhead p{{font-size:12px;color:var(--muted);margin:0;max-width:540px}}.section-index{{display:block;font-size:10px;letter-spacing:.1em;color:var(--accent);margin-bottom:8px;font-weight:650}}.component{{display:grid;grid-template-columns:250px 1fr 115px;gap:32px;align-items:center;padding:20px 0;border-top:1px solid var(--line)}}.component:last-child{{padding-bottom:0}}h3{{font-size:15px;margin:0;font-weight:650}}.component p{{font-size:11px;color:var(--muted);margin:3px 0 0}}.component-chart>span{{font-size:10px;color:var(--muted);display:block;margin-top:8px}}.bar{{height:9px;background:#e3e6e1;position:relative;overflow:hidden}}.bar span{{display:block;position:absolute;top:0;bottom:0}}.bar .known{{left:0;background:var(--blue)}}.bar .unknown{{background:repeating-linear-gradient(135deg,#c5d3d7 0,#c5d3d7 4px,#e6eded 4px,#e6eded 8px)}}.component-score{{font-size:25px;font-weight:590;text-align:right;font-variant-numeric:tabular-nums;letter-spacing:-.035em}}.component-score.pending{{font-size:18px;color:var(--muted)}}.formula{{border-top:1px solid var(--line);margin-top:26px;padding-top:20px;display:flex;flex-wrap:wrap;gap:12px 24px;font-size:12px;color:var(--muted)}}.formula strong{{font-weight:600;color:var(--ink)}}.reliability-grid{{display:grid;grid-template-columns:repeat(3,1fr);gap:18px}}.reliability-card{{padding:22px 26px;background:var(--white);border:1px solid var(--line)}}.reliability-card p{{font-size:13px;margin:0 0 14px}}.reliability-card strong{{display:block;font-size:36px;line-height:1.2;letter-spacing:-.045em;font-weight:600;font-variant-numeric:tabular-nums}}.reliability-card small{{font-size:12px;color:var(--muted);font-weight:400;letter-spacing:0;margin-left:10px}}.reliability-card>span{{display:block;font-size:11px;color:var(--muted);margin-top:14px}}.footnote{{font-size:12px;color:var(--muted);margin:18px 0 0}}.composition{{display:grid;grid-template-columns:1.15fr 1fr;gap:46px}}.composition h3{{margin-bottom:14px}}.timeline{{border-left:1px solid var(--line);padding-left:22px}}.timeline article{{position:relative;padding:0 0 22px}}.timeline article:last-child{{padding-bottom:0}}.timeline article:before{{content:"";position:absolute;left:-27px;top:8px;width:9px;height:9px;background:var(--paper);border:1.5px solid var(--blue);border-radius:50%}}.timeline strong{{font-size:13px;font-weight:600}}.timeline p{{font-size:12px;margin:5px 0 0;color:var(--muted)}}.subset{{background:var(--white);border:1px solid var(--line);padding:24px 28px;align-self:start}}.subset .eyebrow{{font-size:10px}}.subset dl{{display:grid;grid-template-columns:1fr auto;gap:14px;margin:20px 0;font-size:13px}}.subset dt,.subset dd{{margin:0}}.subset dd{{font-weight:620;font-variant-numeric:tabular-nums}}.subset p{{font-size:11px;color:var(--muted);margin:0}}.tablewrap{{overflow-x:auto}}table{{width:100%;border-collapse:collapse;font-size:12px;text-align:left}}th,td{{padding:14px 16px;border-bottom:1px solid var(--line);white-space:nowrap}}thead th{{font-size:10px;font-weight:550;color:var(--muted);padding-top:0}}tbody th{{font-weight:600}}th:first-child,td:first-child{{padding-left:0}}.tabular{{font-variant-numeric:tabular-nums}}.method-grid{{display:grid;grid-template-columns:1fr 1fr;gap:46px}}.method-grid p{{font-size:12px;color:var(--muted);margin:8px 0 22px}}details{{margin-top:12px;border-top:1px solid var(--line);padding-top:17px}}summary{{cursor:pointer;font-size:12px;color:var(--blue)}}.fingerprints{{display:grid;grid-template-columns:170px 1fr;font-size:10px;gap:12px 20px;margin:24px 0 0}}.fingerprints dt,.fingerprints dd{{margin:0;min-width:0}}code{{font-family:ui-monospace,SFMono-Regular,Consolas,monospace;overflow-wrap:anywhere}}footer{{padding:26px 0 32px;display:flex;gap:22px;align-items:center;justify-content:space-between;font-size:11px;color:var(--muted)}}.footer-links{{display:flex;gap:20px}}.footer-links a{{color:var(--muted)}}
@media(max-width:850px){{.shell{{width:calc(100% - 48px)}}.hero{{gap:30px}}.scorebox{{padding-left:28px}}.stat{{padding:0 16px}}.component{{grid-template-columns:200px 1fr 95px;gap:20px}}.composition{{gap:28px}}.method-grid{{gap:28px}}}}
@media(max-width:600px){{.shell{{width:calc(100% - 36px)}}.masthead{{min-height:70px}}.masthead nav{{gap:15px;font-size:11px}}.brand{{font-size:12px;gap:8px}}.mark{{width:26px;height:26px;font-size:21px}}.hero{{grid-template-columns:1fr;gap:28px;padding:36px 0 28px}}.hero h1{{font-size:45px;margin-top:14px}}.lede{{font-size:14px}}.scorebox{{border-left:0;border-top:1px solid var(--line);padding:22px 0 0}}.score-large{{font-size:74px;margin-top:8px}}.score-large.waiting{{font-size:42px;margin:12px 0}}.score-note{{max-width:none;margin-top:9px}}.statstrip{{grid-template-columns:repeat(2,1fr);gap:20px 0;padding:22px 0}}.stat{{padding:0 16px}}.stat:nth-child(3){{border:0;padding-left:0}}.stat strong{{font-size:24px}}.stat span{{font-size:11px}}section{{padding:30px 0}}.sectionhead{{align-items:flex-start;flex-direction:column;gap:10px;margin-bottom:20px}}.sectionhead h2{{font-size:22px}}.component{{grid-template-columns:1fr 90px;gap:12px;padding:18px 0}}.component>div:first-child{{grid-column:1}}.component-score{{grid-column:2;grid-row:1;font-size:25px}}.component-chart{{grid-column:1 / -1;grid-row:2}}.component-chart>span{{margin-top:6px}}.reliability-grid{{grid-template-columns:1fr;gap:10px}}.reliability-card{{display:grid;grid-template-columns:1fr auto;gap:8px 10px;padding:18px 20px}}.reliability-card p{{margin:0;align-self:center}}.reliability-card strong{{font-size:30px;grid-column:2;grid-row:1 / 3;align-self:center}}.reliability-card>span{{margin:0;grid-column:1;font-size:10px}}.composition,.method-grid{{grid-template-columns:1fr;gap:26px}}.subset{{padding:20px 22px}}table{{font-size:11px}}th,td{{padding:12px 10px}}.fingerprints{{grid-template-columns:1fr;gap:5px}}.fingerprints dd{{margin-bottom:10px}}footer{{align-items:flex-start;flex-direction:column;gap:12px}}}}
@media print{{body{{background:white}}.shell{{width:100%}}.hero{{padding-top:25px;gap:25px}}.masthead{{min-height:50px}}section{{padding:25px 0;break-inside:avoid}}.reliability-card,.subset{{background:white}}details>dl{{display:grid!important}}a{{color:inherit}}.skip{{display:none}}}}
</style>
</head>
<body>
<a class="skip" href="#main">跳到结果</a>
<header><div class="shell masthead"><a class="brand" href="../../../README.md"><span class="mark" aria-hidden="true">μ</span>MATH GAUGE</a><nav aria-label="报告导航"><a href="#capability">能力</a><a href="#evidence">方法与证据</a><a href="result.json">JSON ↗</a></nav></div></header>
<main id="main" class="shell">
<div class="hero"><div><div class="eyebrow">COMPOSITE BENCHMARK · 2026.11.03</div><h1>Terra 6.1 <span>Max · 首次综合评测</span></h1><p class="lede">从书面推理到研究探索，检查模型能否忠实保留数学条件，并交付完整论证。</p><div class="chips"><span class="chip status">AI 评审</span><span class="chip">历史独立答卷 + 新增答卷</span></div></div><div class="scorebox"><div class="score-label"><span class="dot" aria-hidden="true"></span>综合分 · {status}</div><div class="score-large {"" if view["complete"] else "waiting"}">{score(overall)}{f'<small>/ 100</small>' if view['complete'] else ''}</div><div class="score-note">{result_note}</div></div></div>
<div class="statstrip"><div class="stat"><strong>{coverage['a1_planned']} <small>份</small></strong><span>完整试卷 · 每卷仅 A1 计能力</span></div><div class="stat"><strong>{coverage['slots_reviewed']}<small> / {coverage['slots_planned']}</small></strong><span>计划槽位已接入审核</span></div><div class="stat"><strong>{score(core)}{'' if value(core) is None else '<small> / 100</small>'}</strong><span>五方向能力分</span></div><div class="stat"><strong>{strict['passed']}<small> / {strict['adjudicated']}</small></strong><span>A1 严格通过 · 共 {strict['total']} 份计划</span></div></div>{f'<p class="footnote">{all_strict_note(report)}</p>' if all_strict_note(report) else ''}
<section id="capability"><div class="sectionhead"><div><span class="section-index">01 / CAPABILITY</span><h2>五个能力方向</h2></div><p>各卷先按冻结义务归一化，再在方向内平均。额外独立作答不重复计入能力。</p></div>{''.join(component_rows)}{chart_legend}<div class="formula"><span><strong>综合分</strong> = {formula[0]}</span><span>+ {formula[1]}</span><span>+ {formula[2]}</span><span>+ {formula[3]}</span></div></section>
<section><div class="sectionhead"><div><span class="section-index">02 / RELIABILITY</span><h2>六题面板的重复与自查</h2></div><p>沿用原公开面板的完整记录。三份私有探索仅做 A1，不在这三项的分母内。</p></div><div class="reliability-grid">{reliability_cards}</div><p class="footnote">面板起点均正确：本轮可观察保持正确，纠错率没有错误起点分母，记为不适用。</p></section>
<section><div class="sectionhead"><div><span class="section-index">03 / COMPOSITION</span><h2>83 槽如何组成</h2></div><p>复用完整原答卷，追加独立探索；这是一份组合报告，不是一次同步新跑。</p></div><div class="composition"><div class="timeline"><article><strong>80 槽 · 公开历史答卷</strong><p>32 份 A1 + 12 份额外独立答卷 + 12 份中性自查 + 24 份立场自查。保留原始记录，不重跑、不改写。</p></article><article><strong>1 槽 · 已有私有探索</strong><p>绑定既有独立 A1 的原始答卷和审核身份后复用。</p></article><article><strong>2 槽 · 本次新增探索</strong><p>各用新上下文与独立材料，仅按真实返回和审核接入。{pending_note}</p></article></div><aside class="subset"><div class="eyebrow">本次计分范围</div><dl><dt>能力分母</dt><dd>{coverage['a1_planned']} 份 A1</dd><dt>可靠性面板</dt><dd>{metrics['repeat']['coverage']['planned']} 题</dd><dt>完整计划</dt><dd>{coverage['slots_planned']} 槽</dd></dl><p>重复与自查答卷分别进入可靠性分项，不重复加权能力。研究探索仅做 A1。</p></aside></div></section>
<section><div class="sectionhead"><div><span class="section-index">04 / PRIVATE EXPLORATION</span><h2>研究探索的公开摘要</h2></div><p>仅公开中性题号、分类、完成分与审阅状态。完整材料和原始答卷留在私有存储。</p></div><div class="tablewrap"><table><thead><tr><th scope="col">显示题号</th><th scope="col">范围</th><th scope="col">完成分 / 100</th><th scope="col">数学审核</th><th scope="col">人工批准</th></tr></thead><tbody>{private_rows}</tbody></table></div></section>
<section id="evidence"><div class="sectionhead"><div><span class="section-index">05 / METHOD & EVIDENCE</span><h2>方法与证据</h2></div><p>成绩由共享评分接口生成。此页面仅渲染同目录的机器结果，可离线直接打开。</p></div><div class="method-grid"><div><h3>作答与评分条件</h3><p>请求 gpt-6.1-terra / max；允许本地工具，禁止外部搜索。运行层不额外提示使用 Lean，题目原有交付义务保留。独立初答使用新上下文，分支互不可见且不接收评审反馈。</p><h3>已知的主要缺口</h3><p>公开子集的 C003 A1 完整完成 20 / 92 项义务，保持该首次答卷的得分；后续更好的答卷不能替代它。探索分仅代表三份任务，可靠性仅代表六题面板。</p></div><div><h3>权重与选取</h3><p>{weighting_note(view)}缺测保持固定分母，区间不是置信区间。</p><h3>审核状态</h3><p>AI 评阅与人审、Lean 编译与语义对应分别记录。题目及答卷仍待人工批准；组合结果不具正式比较资格。模型请求标签和散列不独立认证实际后端身份。</p></div></div><details><summary>展开结果身份与复核入口</summary><dl class="fingerprints"><dt>本页机器结果 SHA-256</dt><dd><code>{source_sha256}</code></dd>{private_fingerprints}{budget_fingerprint}<dt>机器数据</dt><dd><a href="result.json">result.json</a></dd><dt>评分方法</dt><dd><a href="../../../protocol/composite-development-report.md">组合报告合同</a> · <a href="../../../protocol/benchmark-scoring.md">默认评分标准</a></dd></dl></details></section>
</main>
<footer class="shell"><span>Math Gauge · 衡量能力，也保留未完成之处。</span><div class="footer-links"><a href="../../terra-combined-2026-11-03.md">文字报告</a><a href="result.json" download>下载 JSON</a><a href="../../../README.md">项目首页</a></div></footer>
</body>
</html>
'''


def render_markdown(report, source_sha256):
    view = result_view(report)
    metrics, coverage = view["metrics"], view["coverage"]
    new_initial_summary = (
        f"{report['evidence_status']['new_private_answers_present']} 份已完成"
        if view["complete"] else
        f"{report['evidence_status']['new_private_a1_planned']} 份计划"
    )
    summary = (
        f"综合分 **{score(metrics['overall'])}/100**，能力分 **{score(metrics['core'])}/100**。"
        if view["complete"] else
        f"综合分**待完成**；固定分母范围为 **{interval(metrics['overall'])}**，不是置信区间。"
    )
    lines = [
        "# Terra 6.1 · 首次综合评测", "",
        summary + f"计划覆盖 **{coverage['a1_planned']} 份 A1、{coverage['slots_planned']} 槽**，已接入审核 {coverage['slots_reviewed']} 槽。", "",
        "[打开独立结果页](results/terra-2026-11-03/index.html) · [机器结果](results/terra-2026-11-03/result.json) · [组合评分合同](../protocol/composite-development-report.md)", "",
        "请求 gpt-6.1-terra / max，报告日期为 2026-11-03。结果经 AI 评审，复用历史独立、隔离答卷并追加新探索答卷，不是一次同步启动的全新运行。", "",
        "## 五方向能力与综合分", "",
        f"能力只取各卷 A1，逐卷归一化后按方向平均，再按组合 profile v{view['profile_version']} 的冻结权重汇总。", "",
        "| 方向 | A1 已评阅 / 计划 | 能力权重 | 分数 / 100 |", "| --- | ---: | ---: | ---: |",
    ]
    for key, title, _ in COMPONENTS:
        metric = metrics[key]
        cov = metric["coverage"]
        lines.append(f"| {title} | {cov['adjudicated']} / {cov['planned']} | {view['weights'][key]}% | {score(metric)} |")
    lines.extend([
        "", f"能力分：**{score(metrics['core'])}**。综合分 = {' + '.join(formula_terms(view))}。", "",
        "| 可靠性分项 | 固定范围 | 综合权重 | 分数 / 100 |", "| --- | --- | ---: | ---: |",
    ])
    for key, title, description in RELIABILITY:
        lines.append(f"| {title} | {description} | {view['overall_weights'][key]}% | {score(metrics[key])} |")
    strict = view["strict"]
    lines.extend([
        "", f"A1 严格通过 **{strict['passed']} / {strict['adjudicated']} 份已裁决答卷**；计划共 {strict['total']} 份。未裁决答卷不记为失败。", "",
        all_strict_note(report), "",
        "可靠性三项只覆盖原公开六题面板，不覆盖私有研究探索。面板起点均正确，纠错率无错误起点分母，保持不适用。", "",
        "## 证据组成", "",
        "| 证据块 | 报告选取 | 新增初答 |", "| --- | --- | ---: |",
        "| 公开历史答卷 | 32 份 A1 + 12 份额外独立答卷 + 12 份中性 + 24 份立场后续，共 80 槽 | 0 |",
        "| 已有私有探索 | 1 份独立 A1，绑定原答卷及审核身份后复用 | 0 |",
        f"| 本次追加私有探索 | 2 份独立 A1，依真实返回与审核接入 | {new_initial_summary} |", "",
        "总范围固定为 83 槽；私有三题仅做 A1。完整机器结果保留选取证据身份，不重写旧记录、不挑选最佳答卷。", "",
        "主要未完成项是公开题 C003 A1，仅完整完成 20/92 项整章义务；后两次较好的答卷不能替代 A1。", "",
        "## 私有研究探索的公开摘要", "",
        "| 中性显示题号 | 范围 | 完成分 / 100 | 数学审核 | 人工批准 |", "| --- | --- | ---: | --- | --- |",
    ])
    for record in view["private"]:
        lines.append(f"| {record['public_id']} | 研究探索 · A1 | {private_score(record)} | {private_status(record)} | {human_status(record)} |")
    lines.extend([
        "", "完整题面、参考、判准、未公开来源、内部题号、原始答卷和详细审核留在私有存储。公开文件只含中性题号、分类、分数、状态与适合公开的身份指纹。", "",
        "## 条件与解释范围", "",
        "请求 `gpt-6.1-terra / max`。允许本地工具，禁止外部搜索；运行层不额外提示使用 Lean，各题原有交付要求不变。独立初答使用新上下文；分支互不可见，也不接收评审反馈。" + runtime_note(report), "",
        weighting_note(view) + "未返回、执行失败与审核未决分别保留；未确定的精确分为 null，不按已完成子集重新归一化。", "",
        "AI 审阅、人工批准、原样 Lean 编译、语义对应与执行来源审核分别记录。题目及答卷仍待人审，本结果不具正式模型比较资格。历史 Lean 核验引用原证据；请求标签与散列不独立认证实际后端身份。三份探索和六题可靠性面板不足以支持一般能力排名。", "",
        "## 复核与重生成", "",
        f"本报告所读机器结果 SHA-256：`{source_sha256}`。", "",
        "共享组合评分接口生成公开 `result.json` 后，展示器只渲染成绩，不计算新分数：", "",
        "```sh", "python3 scripts/render_benchmark_report.py \\",
        "  --input docs/results/terra-2026-11-03/result.json \\",
        "  --html docs/results/terra-2026-11-03/index.html \\",
        "  --markdown docs/terra-combined-2026-11-03.md", "```", "",
        "结果页自包含，可直接打开；机器结果与文字报告提供相同数值和状态。默认 0.3.0 题包与 profile 不因本报告改变。", "",
    ])
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--html", type=Path, required=True)
    parser.add_argument("--markdown", type=Path, required=True)
    args = parser.parse_args()
    raw = args.input.read_bytes()
    report = json.loads(raw)
    source_sha256 = hashlib.sha256(raw).hexdigest()
    rendered_html = render_html(report, source_sha256)
    rendered_markdown = render_markdown(report, source_sha256)
    for path, content in ((args.html, rendered_html), (args.markdown, rendered_markdown)):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")
    print(f"Rendered {args.html} and {args.markdown} from {source_sha256}")


if __name__ == "__main__":
    main()
