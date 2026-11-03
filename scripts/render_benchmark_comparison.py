#!/usr/bin/env python3
"""Render public frozen results as benchmark charts and an offline comparison.

This presentation script does not import the scoring engine or original answers.
SVG generation uses only the Python standard library. Optional PNG export uses
an existing Sharp installation supplied explicitly on the command line.
"""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess

from render_benchmark_report import COMPONENTS, RELIABILITY, escape


MODELS = (("terra", "Terra 6.1 Max", "#315e78"),
          ("gemini", "Gemini 3.8 Flash High", "#bf633e"))
PAPER_COUNTS = {"proofs": 18, "lean-audit": 6, "lean-construction": 6, "chapters": 2, "exploration": 3}
RELIABILITY_COUNTS = {"repeat": "6题 · 各 A1 / A2 / A3", "neutral": "6题 · 12份后续", "stance": "6题 · 24份后续"}


def load_public(path):
    raw = path.read_bytes()
    report = json.loads(raw)
    if report.get("schema") != "math-gauge.public-composite-score/v1":
        raise ValueError("Use the public score projection, never an evaluator report")
    if report["score_units"] != {"metrics": "percent", "completion": "fraction"}:
        raise ValueError("Unexpected public score units")
    if report["profile"]["version"] != "0.2.0" or report["coverage"]["slots_planned"] != 83:
        raise ValueError("This comparison requires the frozen 35-paper / 83-slot profile")
    if report["evidence_status"]["formal_comparison_eligible"] is not False:
        raise ValueError("This page is explicitly a provisional development comparison")
    return report, hashlib.sha256(raw).hexdigest()


def presentation(terra_path, gemini_path):
    sources = {}
    reports = {}
    for key, path in (("terra", terra_path), ("gemini", gemini_path)):
        reports[key], digest = load_public(path)
        sources[key] = {"sha256": digest, "public_result": f"../{key}-2026-11-03/result.json"}
    if reports["terra"]["profile"]["components"] != reports["gemini"]["profile"]["components"]:
        raise ValueError("Component configuration differs")
    if reports["terra"]["profile"]["overall_weights"] != reports["gemini"]["profile"]["overall_weights"]:
        raise ValueError("Overall weights differ")
    models = {}
    for key, title, color in MODELS:
        source = reports[key]
        models[key] = {"title": title, "color": color,
                       "metrics": {metric: source["metrics"][metric]["exact"]
                                   for metric in [row[0] for row in COMPONENTS + RELIABILITY] + ["core", "overall"]},
                       "strict_passes": source["strict_passes"],
                       "private_completion": {row["public_id"]: row["completion"]["exact"]
                                              for row in source["private_records"]}}
    # Counts are the published chapter diagnostics, checked against the exact
    # normalized completion already present in both source projections.
    chapter_counts = {"MG-C002": {"total": 34, "terra": 34, "gemini": 0},
                      "MG-C003": {"total": 92, "terra": 20, "gemini": 0}}
    for public_id, row in chapter_counts.items():
        for key, _, _ in MODELS:
            source_row = next(item for item in reports[key]["slot_evidence"] if item["slot_id"] == public_id + ":A1")
            if abs(source_row["completion"]["exact"] - row[key] / row["total"]) > 1e-12:
                raise ValueError("Published chapter count differs from source completion")
    return {"schema": "math-gauge.public-comparison-display/v1", "date": "2026-11-03",
            "status": "AI-reviewed provisional development comparison; human pending",
            "sources": sources, "models": models,
            "profile": {"version": "0.2.0", "components": reports["terra"]["profile"]["components"],
                        "overall_weights": reports["terra"]["profile"]["overall_weights"]},
            "chapter_completion": chapter_counts,
            "coverage": {"a1_papers": 35, "public_papers": 32, "private_papers": 3,
                         "all_slots": 83, "reliability_panel_papers": 6}}


def text(x, y, value, size=20, color="#243541", weight=400, anchor="start", css=""):
    return (f'<text x="{x}" y="{y}" font-size="{size}" fill="{color}" '
            f'font-weight="{weight}" text-anchor="{anchor}" class="{css}">{escape(value)}</text>')


def svg_start(height, title, desc, data):
    return [f'<svg xmlns="http://www.w3.org/2000/svg" width="1440" height="{height}" viewBox="0 0 1440 {height}" role="img" aria-labelledby="title-{height} desc-{height}">',
            f'<title id="title-{height}">{escape(title)}</title><desc id="desc-{height}">{escape(desc)}</desc>',
            f'<metadata>{escape(json.dumps(data["sources"], ensure_ascii=False))}</metadata>',
            '<style>text{font-family:-apple-system,BlinkMacSystemFont,"PingFang SC","Noto Sans CJK SC","Microsoft YaHei",sans-serif}.num{font-variant-numeric:tabular-nums}</style>',
            f'<rect width="1440" height="{height}" fill="#fbfcfd"/>']


def axis(parts, top, bottom):
    for tick in (0, 25, 50, 75, 100):
        x = 360 + tick * 9
        parts.append(f'<line x1="{x}" y1="{top}" x2="{x}" y2="{bottom}" stroke="#dce3e8" stroke-width="1"/>')
        parts.append(text(x, top - 15, str(tick), 16, "#6b7c88", anchor="middle", css="num"))


def pair(parts, y, scores, labels=None):
    for index, (key, _, color) in enumerate(MODELS):
        value = scores[key]
        center = y + (-13 if index == 0 else 13)
        if value:
            parts.append(f'<rect x="360" y="{center - 8}" width="{value * 9:.6f}" height="16" rx="3" fill="{color}"/>')
        else:
            parts.append(f'<circle cx="360" cy="{center}" r="3" fill="{color}"/>')
        label = labels[key] if labels else f"{value:.2f}"
        parts.append(text(1278, center + 6, label, 20, color, 650, css="num"))


def legend(parts, y):
    for x, (_, title, color) in zip((56, 450), MODELS):
        parts.append(f'<rect x="{x}" y="{y - 15}" width="19" height="13" rx="2" fill="{color}"/>')
        parts.append(text(x + 29, y - 2, title, 19, color, 600))


def main_svg(data):
    p = svg_start(1380, "Math Gauge · Terra / Gemini benchmark comparison",
                  "五个能力方向与六题面板的三项可靠性，共用0至100分尺度。所有成绩为AI审核的暂定开发结果，待人审。", data)
    p += [text(56, 43, "MATH GAUGE  /  DEVELOPMENT BENCHMARK  /  2026.11.03", 15, "#6b7c88", 650),
          text(56, 96, "Terra 6.1 Max × Gemini 3.8 Flash High", 38, weight=700),
          text(56, 134, "同一评分配置 · 35份 A1 / 83槽 · AI 评审 / 待人审", 20, "#61727e")]
    for x, (key, title, color) in zip((56, 748), MODELS):
        p.append(f'<rect x="{x}" y="163" width="636" height="118" rx="9" fill="white" stroke="#dce3e8"/>')
        p.append(f'<rect x="{x}" y="163" width="5" height="118" rx="2" fill="{color}"/>')
        p.append(text(x + 24, 194, title, 20, color, 650))
        p.append(text(x + 24, 249, f'{data["models"][key]["metrics"]["overall"]:.2f}', 38, color, 700, css="num"))
        p.append(text(x + 140, 247, "综合分", 17, "#61727e"))
        p.append(text(x + 322, 247, f'{data["models"][key]["metrics"]["core"]:.2f}', 29, weight=600, css="num"))
        p.append(text(x + 422, 246, "能力分", 17, "#61727e"))
    p += [text(56, 332, "01  五个能力方向", 27, weight=700),
          text(56, 362, "每卷仅 A1 计能力；逐卷归一化后按方向平均。", 17, "#61727e")]
    axis(p, 409, 868)
    weights = {row["id"]: row["weight"] for row in data["profile"]["components"]}
    for y, (key, title, _) in zip((447, 539, 631, 723, 815), COMPONENTS):
        p += [text(56, y - 3, title, 24, weight=600),
              text(56, y + 24, f"{PAPER_COUNTS[key]}份 A1 · 能力权重 {weights[key]}%", 17, "#61727e")]
        pair(p, y, {model: data["models"][model]["metrics"][key] for model, _, _ in MODELS})
    p += [text(56, 921, "02  六题面板的三项可靠性", 27, weight=700),
          text(56, 952, "三次全对看严格交付；中性与立场自查看重点数学正确性。", 17, "#61727e")]
    axis(p, 999, 1266)
    for y, (key, title, _) in zip((1037, 1129, 1221), RELIABILITY):
        p += [text(56, y - 3, title, 24, weight=600),
              text(56, y + 24, RELIABILITY_COUNTS[key], 17, "#61727e")]
        pair(p, y, {model: data["models"][model]["metrics"][key] for model, _, _ in MODELS})
    p += [text(56, 1313, "综合权重：能力75% + 三次全对5% + 中性自查10% + 立场自查10%。", 18, "#61727e"),
          text(56, 1345, "可靠性仅代表六题面板；中性100分不代表整卷全部通过。开发性比较，不具正式比较资格。", 18, "#61727e"), "</svg>"]
    return "\n".join(p)


def chapters_svg(data):
    p = svg_start(620, "Math Gauge · 两章的完整交付",
                  "Terra的C002完成34/34、C003完成20/92；Gemini分别完成0/34、0/92。义务不是独立题数。", data)
    p += [text(56, 43, "MATH GAUGE  /  A1 DELIVERY DIAGNOSTIC", 15, "#6b7c88", 650),
          text(56, 96, "两章的完整交付", 38, weight=700),
          text(56, 134, "按冻结交付门槛计完成；一章是一份相关样本，义务不是独立题数。", 20, "#61727e")]
    legend(p, 178)
    axis(p, 237, 464)
    for y, (public_id, row) in zip((284, 417), data["chapter_completion"].items()):
        p += [text(56, y - 3, public_id.removeprefix("MG-"), 28, weight=650),
              text(56, y + 27, f'{row["total"]}项本章义务 · A1', 18, "#61727e")]
        pair(p, y, {key: row[key] / row["total"] * 100 for key, _, _ in MODELS},
             {key: f'{row[key]}/{row["total"]}' for key, _, _ in MODELS})
    p += [text(56, 521, "尺度：0–100% · 条末为完整满足的义务数 / 本章义务数。后续答卷不替代 A1。", 19, "#61727e"),
          text(56, 557, "Gemini C003 原样工程结果为 compile_error；0/92 不等于92项数学全错。", 19, "#61727e"),
          text(56, 592, "AI 评审 / 待人审 · 诊断展示，不作为额外加权分项。", 17, "#61727e"), "</svg>"]
    return "\n".join(p)


def mobile_rows(data, definitions):
    rows = []
    for key, title, _ in definitions:
        note = f'{PAPER_COUNTS[key]}份 A1' if key in PAPER_COUNTS else RELIABILITY_COUNTS[key]
        bars = []
        for model, name, color in MODELS:
            value = data["models"][model]["metrics"][key]
            bars.append(f'<div class="mbar"><span>{"Terra" if model == "terra" else "Gemini"}</span><div class="track"><i style="width:{value}%;background:{color}"></i></div><b style="color:{color}">{value:.2f}</b></div>')
        rows.append(f'<article><h3>{title} <small>{note}</small></h3>{"".join(bars)}</article>')
    return "".join(rows)


def render_html(data, overview, chapter_chart):
    metric_rows = "".join(f'<tr><th scope="row">{title}</th><td>{data["models"]["terra"]["metrics"][key]:.2f}</td><td>{data["models"]["gemini"]["metrics"][key]:.2f}</td></tr>'
                          for key, title, _ in COMPONENTS + RELIABILITY)
    strict_rows = "".join(f'<tr><th scope="row">{title}</th>' + "".join(
        f'<td>{data["models"][model]["strict_passes"][key]["passed"]}/{data["models"][model]["strict_passes"][key]["total"]}</td>'
        for model, _, _ in MODELS) + '</tr>'
        for key, title in (("core_A1", "A1 严格通过"), ("all_selected_slots", "全部材料严格通过")))
    private_rows = "".join(f'<tr><th scope="row">{private_id}</th><td>{data["models"]["terra"]["private_completion"][private_id] * 100:.2f}</td><td>{data["models"]["gemini"]["private_completion"][private_id] * 100:.2f}</td></tr>'
                           for private_id in sorted(data["models"]["gemini"]["private_completion"]))
    fingerprints = "".join(f'<dt>{title} 公开结果 SHA-256</dt><dd><code>{data["sources"][key]["sha256"]}</code></dd>' for key, title, _ in MODELS)
    return f'''<!doctype html>
<html lang="zh-CN"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><meta name="color-scheme" content="light"><title>Math Gauge · Terra / Gemini 对比</title>
<style>
:root{{--ink:#243541;--muted:#61727e;--line:#dce3e8;--terra:#315e78;--gemini:#bf633e}}*{{box-sizing:border-box}}body{{margin:0;color:var(--ink);background:#fbfcfd;font-family:-apple-system,BlinkMacSystemFont,"PingFang SC","Noto Sans CJK SC",sans-serif;line-height:1.7}}a{{color:var(--terra);text-underline-offset:4px}}.shell{{max-width:1220px;margin:auto;padding:0 32px}}header{{border-bottom:1px solid var(--line)}}nav{{display:flex;gap:24px;align-items:center;min-height:76px;font-size:13px;flex-wrap:wrap}}.brand{{font-weight:750;letter-spacing:.1em;margin-right:auto;text-decoration:none}}h1{{font-size:42px;line-height:1.25;letter-spacing:-.035em;margin:16px 0}}.eyebrow{{font-size:12px;letter-spacing:.12em;color:var(--muted);font-weight:650}}.hero{{padding:48px 0 26px}}.hero p{{max-width:860px;color:var(--muted);margin:14px 0}}.chips{{display:flex;gap:10px;flex-wrap:wrap}}.chip{{border:1px solid var(--line);border-radius:20px;font-size:12px;padding:3px 11px}}figure{{margin:0}}.chart svg{{display:block;width:100%;height:auto}}.chart{{border:1px solid var(--line);border-radius:10px;overflow:hidden}}figcaption{{font-size:12px;color:var(--muted);padding:12px 4px 0}}.downloads{{display:flex;gap:20px;flex-wrap:wrap;font-size:13px;margin:20px 0 0}}section{{border-bottom:1px solid var(--line);padding:36px 0}}h2{{font-size:26px;letter-spacing:-.02em;margin:0 0 12px}}h3{{font-size:17px;margin:0 0 9px}}p{{margin:10px 0 18px}}.note{{font-size:14px;color:var(--muted)}}.grid{{display:grid;grid-template-columns:1fr 1fr;gap:36px}}.tablewrap{{overflow-x:auto}}table{{width:100%;border-collapse:collapse;font-size:14px;font-variant-numeric:tabular-nums}}th,td{{padding:12px 14px;border-bottom:1px solid var(--line);text-align:right;white-space:nowrap}}th:first-child{{text-align:left;padding-left:0}}thead th{{font-weight:500;color:var(--muted);font-size:12px}}tbody th{{font-weight:600}}.method p{{font-size:14px;color:var(--muted)}}.method h3{{margin-top:22px}}details{{font-size:13px;margin-top:24px}}summary{{cursor:pointer;color:var(--terra)}}dl{{font-size:12px}}dt{{color:var(--muted);margin-top:12px}}dd{{margin:4px 0;overflow-wrap:anywhere}}code{{font-family:ui-monospace,SFMono-Regular,monospace;font-size:11px}}footer{{font-size:12px;color:var(--muted);padding:26px 0 36px}}.mobile{{display:none}}.skip{{position:absolute;left:-9999px}}.skip:focus{{left:12px;top:10px;background:white;padding:10px}}.mbar{{display:grid;grid-template-columns:55px 1fr 46px;align-items:center;gap:10px;font-size:12px;margin:7px 0}}.mbar b{{text-align:right;font-variant-numeric:tabular-nums}}.track{{background:#e7ecf0;height:10px;border-radius:3px;overflow:hidden}}.track i{{display:block;height:100%;border-radius:3px}}.mobile article{{padding:18px 0;border-top:1px solid var(--line)}}.mobile h3 small{{display:block;font-size:11px;color:var(--muted);font-weight:400}}.mobile h2{{font-size:22px;margin-top:28px}}.mobile-summary{{display:grid;grid-template-columns:1fr 1fr;gap:12px}}.mobile-summary article{{border:1px solid var(--line);padding:16px;border-radius:8px}}.mobile-summary strong{{display:block;font-size:34px;line-height:1.3;font-variant-numeric:tabular-nums}}.mobile-summary p{{font-size:11px;margin:5px 0}}.legend{{font-size:12px;display:flex;gap:18px;flex-wrap:wrap}}.legend span:first-child{{color:var(--terra)}}.legend span:last-child{{color:var(--gemini)}}
@media(max-width:680px){{.shell{{padding:0 20px}}nav{{gap:14px;min-height:68px;font-size:12px}}h1{{font-size:32px}}.hero{{padding:32px 0 20px}}.hero p{{font-size:14px}}.desktop{{display:none}}.mobile{{display:block}}.grid{{grid-template-columns:1fr;gap:22px}}section{{padding:28px 0}}h2{{font-size:23px}}.chapter-chart{{overflow-x:auto}}.chapter-chart svg{{min-width:760px}}.downloads{{gap:14px}}table{{font-size:12px}}th,td{{padding:10px}}.mobile-summary h3{{font-size:14px}}}}
@media print{{nav,.downloads{{display:none}}.shell{{max-width:none;padding:0}}h1{{font-size:30px}}section{{break-inside:avoid;padding:24px 0}}.chart{{border:0}}}}
</style></head><body><a class="skip" href="#main">跳到对比结果</a><header><nav class="shell"><a class="brand" href="../../../README.md">MATH GAUGE</a><a href="#comparison">能力与可靠性</a><a href="#chapters">整章交付</a><a href="#method">方法</a><a href="result.json">JSON</a></nav></header>
<main id="main" class="shell"><div class="hero"><div class="eyebrow">DEVELOPMENT COMPARISON · 2026.11.03</div><h1>两种模型的数学交付表现</h1><p>同一组合评分配置下，对照 Terra 6.1 Max 与 Gemini 3.8 Flash High 的五个能力方向，再分别查看六题面板的重复与自查。固定35份 A1、83槽，保留完整分母。</p><div class="chips"><span class="chip">AI 评审 · 待人审</span><span class="chip">组合 profile v0.2.0</span><span class="chip">公开开发结果</span></div></div>
<section id="comparison"><figure class="desktop"><div class="chart">{overview}</div><figcaption>条形图共用0–100分完整尺度，无断轴。条末为冻结分数；Terra 为蓝色，Gemini 为橙色。</figcaption></figure>
<div class="mobile"><div class="mobile-summary"><article><h3>Terra 6.1 Max</h3><strong style="color:var(--terra)">{data['models']['terra']['metrics']['overall']:.2f}</strong><p>综合分 · 能力分{data['models']['terra']['metrics']['core']:.2f}</p></article><article><h3>Gemini Flash High</h3><strong style="color:var(--gemini)">{data['models']['gemini']['metrics']['overall']:.2f}</strong><p>综合分 · 能力分{data['models']['gemini']['metrics']['core']:.2f}</p></article></div><h2>五个能力方向</h2><p class="note">每卷仅 A1 计能力；每条使用0–100完整尺度。</p>{mobile_rows(data, COMPONENTS)}<h2>六题面板的三项可靠性</h2>{mobile_rows(data, RELIABILITY)}<p class="note">中性与立场自查测重点数学正确性；中性100分不代表全部交付严格通过。</p></div>
<div class="downloads"><a href="comparison.png" download>下载对比图 PNG</a><a href="comparison.svg" download>下载 SVG</a><a href="../../benchmark-comparison-2026-11-03.md">文字对照表</a></div>
<p class="note">综合分 = 75% 能力分 + 5% 三次全对 + 10% 中性自查 + 10% 立场自查。能力方向权重为25/20/20/20/15。可靠性仅覆盖原公开六题面板，三份探索仅做 A1。</p></section>
<section id="chapters"><h2>整章任务值得单独看</h2><p class="note">整章均分会掩盖具体交付缺口。C002 与 C003 分别有34、92项义务，各自仍是一份相关样本；下面只展示 A1，后续答卷不替代首次成绩。</p><figure><div class="chart chapter-chart">{chapter_chart}</div></figure><div class="downloads"><a href="chapters.png" download>下载整章图 PNG</a><a href="chapters.svg" download>下载 SVG</a></div><p class="note">Gemini C003 的原样工程核验是 compile_error，未达整项目门槛而得0/92；已定位九项具体数学错误或语义缺口，其余不能据编译失败统称数学全错。21处 sorry/admit 是静态诊断，不能冒称已完成内核公理审计。</p></section>
<section><div class="grid"><div><h2>严格通过是另一个诊断</h2><div class="tablewrap"><table><thead><tr><th>材料</th><th>Terra</th><th>Gemini</th></tr></thead><tbody>{strict_rows}</tbody></table></div><p class="note">整卷严格通过要求全部义务满足；该计数不作为额外加权项。额外独立答卷与自查共48槽，不重复进入能力分。</p></div><div><h2>自查分数需要怎样读</h2><p class="note">Gemini 全部后续的真假标签保持正确，但三份立场后续新增错误论据，使重点数学状态为 I；不能写成迎合后改错真假结论。GF104 中性分支的声明对应交付遗漏使整卷状态为 U，重点数学仍正确。</p><p class="note">三次全对：Terra 6/6，Gemini 5/6。中性重点数学：均为12/12；立场重点数学：Terra 24/24，Gemini 21/24。面板起点的重点断言均正确，纠错率没有错误起点分母，记为不适用。</p></div></div></section>
<section><div class="grid"><div><h2>分项数值</h2><div class="tablewrap"><table><thead><tr><th>分数 / 100</th><th>Terra</th><th>Gemini</th></tr></thead><tbody>{metric_rows}</tbody></table></div></div><div><h2>研究探索仅公开中性摘要</h2><div class="tablewrap"><table><thead><tr><th>完成分 / 100</th><th>Terra</th><th>Gemini</th></tr></thead><tbody>{private_rows}</tbody></table></div><p class="note">仅3份 A1，不足以代表广泛探索能力。完整题面、题材标题、内部题号、参考、原答与详细评审留在私有存储；表中三题均为 AI 已评阅 / 人审待办。</p></div></div></section>
<section id="method" class="method"><h2>方法与解释范围</h2><div class="grid"><div><h3>哪些项目单列</h3><p>五个能力方向是冻结的主要测量维度；重复、中性与立场反映不同的协作风险，另列三项；两章另看义务完成以暴露工程交付缺口。综合分和能力分用于概览，严格通过用于诊断。九个交叉重点标签没有另外冻结的子分数，不另造排名或重复加权。</p><h3>同一评分配置，不同执行批次</h3><p>Terra 复用历史独立答卷并新增两份私有探索；权重在知晓 Terra 旧结果后调整，Gemini 随后使用相同配置。两边允许本地工具、禁止外部搜索，原题交付要求不变。各初答与后续分支按隔离条件处理，预算与来源保留各自记录；这些结果不能视作一次同步、完全等条件的竞赛。</p></div><div><h3>AI 评审与执行证据</h3><p>Gemini 82份答卷有原生 gpt-6.1-terra/max 主评，root 抽查、仲裁并直接终审 C003；Sol 仅负责工程。83个评分槽对应85次真实原生提交，两次额度中断保留并在原上下文剩余预算内续接，另一次 R2 继续既有分支。旧故障队列不计分。</p><h3>暂定开发比较</h3><p>题目及答卷均待人审；AI审核、原样 Lean 编译、语义对应和执行来源审核分别记录。模型请求标签与散列不能独立认证实际后端。公开参考与 Git 历史保留，本题库不宣称隐藏留出集；本页不具正式模型比较资格，也不支持一般能力的认证排名。</p></div></div>
<details><summary>结果来源与重生成</summary><p>页面、SVG与PNG仅展示公开冻结结果；不调用候选模型、Lean或评分器。HTML内嵌两张SVG，无远端字体、脚本或数据请求，可离线打开。</p><dl>{fingerprints}</dl><p><a href="../terra-2026-11-03/result.json">Terra 机器结果</a> · <a href="../gemini-2026-11-03/result.json">Gemini 机器结果</a> · <a href="../../../protocol/composite-development-report.md">组合评分合同</a> · <a href="../../terra-combined-2026-11-03.md">Terra 报告</a> · <a href="../../gemini-combined-2026-11-03.md">Gemini 报告</a></p></details></section>
</main><footer class="shell">Math Gauge · 保留分母、原始交付与审核边界。保存此HTML即可离线阅读。</footer></body></html>'''


def render_markdown(data):
    lines = ["# Terra / Gemini · 综合开发结果对比", "",
             "[打开离线对比页](results/comparison-2026-11-03/index.html) · [PNG](results/comparison-2026-11-03/comparison.png) · [SVG](results/comparison-2026-11-03/comparison.svg) · [展示数据](results/comparison-2026-11-03/result.json)", "",
             "![Math Gauge benchmark comparison](results/comparison-2026-11-03/comparison.png)", "",
             "同一组合 profile v0.2.0，35份 A1 / 83槽。AI评审的暂定开发结果，人审待办，不具正式模型比较资格。", "",
             "| 概览 | Terra 6.1 Max | Gemini 3.8 Flash High |", "| --- | ---: | ---: |"]
    for key, title in (("overall", "综合分"), ("core", "能力分")):
        lines.append(f'| {title} | {data["models"]["terra"]["metrics"][key]:.2f} | {data["models"]["gemini"]["metrics"][key]:.2f} |')
    lines += ["", "| 五方向能力 | A1份数 | 能力权重 | Terra | Gemini |", "| --- | ---: | ---: | ---: | ---: |"]
    weights = {row["id"]: row["weight"] for row in data["profile"]["components"]}
    for key, title, _ in COMPONENTS:
        lines.append(f'| {title} | {PAPER_COUNTS[key]} | {weights[key]}% | {data["models"]["terra"]["metrics"][key]:.2f} | {data["models"]["gemini"]["metrics"][key]:.2f} |')
    lines += ["", "| 六题面板可靠性 | 固定范围 | Terra | Gemini |", "| --- | --- | ---: | ---: |"]
    for key, title, _ in RELIABILITY:
        lines.append(f'| {title} | {RELIABILITY_COUNTS[key]} | {data["models"]["terra"]["metrics"][key]:.2f} | {data["models"]["gemini"]["metrics"][key]:.2f} |')
    lines += ["", "综合分 = 75%能力分 + 5%三次全对 + 10%中性自查 + 10%立场自查。各卷只以A1计能力，额外重复与自查不再进入能力分。可靠性仅覆盖原公开六题面板。", "",
              "## 为什么这些分项单列", "",
              "五方向是已冻结的主要测量维度；三项可靠性分别检查稳定交付、无反馈自查和立场影响。整章两题另列完成义务，防止方向均分掩盖具体交付缺口。综合分/能力分只作概览，A1与全部严格通过只作诊断，不额外计分。九个交叉重点标签没有冻结子分数，不另造排名或重复加权。", "",
              "![两章完整交付](results/comparison-2026-11-03/chapters.png)", "",
              "| 整章 A1 | 本章义务 | Terra 完整满足 | Gemini 完整满足 |", "| --- | ---: | ---: | ---: |"]
    for public_id, row in data["chapter_completion"].items():
        lines.append(f'| {public_id.removeprefix("MG-")} | {row["total"]} | {row["terra"]}/{row["total"]} | {row["gemini"]}/{row["total"]} |')
    lines += ["", "一章是一份相关样本，92项义务不是92道独立题。后续答卷不替代A1。Gemini C003原样工程结果为compile_error，0/92不能推成92项数学全错；已有九项具体数学错误或语义缺口，21处sorry/admit仅为静态诊断。", "",
              "| 严格通过诊断 | Terra | Gemini |", "| --- | ---: | ---: |"]
    for key, title in (("core_A1", "A1"), ("all_selected_slots", "全部材料")):
        rows = [data["models"][model]["strict_passes"][key] for model, _, _ in MODELS]
        lines.append(f'| {title} | {rows[0]["passed"]}/{rows[0]["total"]} | {rows[1]["passed"]}/{rows[1]["total"]} |')
    lines += ["", "Gemini自查的真假标签始终正确，但三份立场后续新增错误论据使重点数学状态为I；GF104中性分支的声明对应交付遗漏使整卷为U，重点数学仍正确。中性100分不代表全部材料严格通过。面板起点均正确，纠错率没有错误起点分母，保持不适用。", "",
              "## 方法与来源", "",
              "Terra复用历史独立答卷并新增两份探索；权重在已知Terra旧结果后调整，Gemini随后使用相同配置。两边使用本地工具、禁止外部搜索的条件，预算与执行批次分别保留记录，不视作一次同步、完全等条件的竞赛。", "",
              "Gemini 82份答卷有原生gpt-6.1-terra/max主评，root抽查、仲裁并直接终审C003；Sol仅负责工程。83个评分槽对应85次真实原生提交，包含保留的额度中断与原上下文剩余预算续接；旧故障队列不计分。", "",
              "公开结果只保留三份探索的聚合及Private-01至Private-03中性摘要。题面、题材标题、内部题号、原答与详细评审留在私有存储。公开开发题与Git历史不构成隐藏留出集。AI评审、编译、语义对应、执行来源与人工批准分别记录；本页不能支持认证排名。", "",
              "[Terra完整报告](terra-combined-2026-11-03.md) · [Gemini完整报告](gemini-combined-2026-11-03.md) · [组合评分合同](../protocol/composite-development-report.md)", "",
              "本展示由两份公开结果直接渲染，不重判、不重跑模型/Lean、不改计分。", ""]
    for key, title, _ in MODELS:
        lines.append(f'- {title} 公开结果 SHA-256：`{data["sources"][key]["sha256"]}`。')
    lines += ["", "重生成SVG、离线HTML、文字表及展示数据：", "", "```sh", "python3 scripts/render_benchmark_comparison.py", "```", "",
              "PNG可加`--sharp-module`指定已有Sharp安装；`--node`可选择Node可执行文件。该可选依赖仅用于静态图片导出，runner不需要它。", ""]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--terra", type=Path, default=Path("docs/results/terra-2026-11-03/result.json"))
    parser.add_argument("--gemini", type=Path, default=Path("docs/results/gemini-2026-11-03/result.json"))
    parser.add_argument("--out", type=Path, default=Path("docs/results/comparison-2026-11-03"))
    parser.add_argument("--markdown", type=Path, default=Path("docs/benchmark-comparison-2026-11-03.md"))
    parser.add_argument("--sharp-module", type=Path)
    parser.add_argument("--node", default="node")
    args = parser.parse_args()
    data = presentation(args.terra, args.gemini)
    overview, chapter_chart = main_svg(data), chapters_svg(data)
    args.out.mkdir(parents=True, exist_ok=True)
    for name, content in (("result.json", json.dumps(data, ensure_ascii=False, indent=2) + "\n"),
                          ("comparison.svg", overview), ("chapters.svg", chapter_chart),
                          ("index.html", render_html(data, overview, chapter_chart))):
        (args.out / name).write_text(content, encoding="utf-8")
    args.markdown.write_text(render_markdown(data), encoding="utf-8")
    if args.sharp_module:
        code = "const sharp=require(process.argv[1]); Promise.all(process.argv.slice(2).map(p=>sharp(p,{density:144}).png().toFile(p.replace(/\\.svg$/,'.png')))).catch(e=>{console.error(e);process.exit(1)});"
        subprocess.run([args.node, "-e", code, str(args.sharp_module.resolve()),
                        str(args.out / "comparison.svg"), str(args.out / "chapters.svg")], check=True)
    print(f"Rendered 2 source-bound SVG charts, offline HTML, Markdown and display JSON in {args.out}")


if __name__ == "__main__":
    main()
