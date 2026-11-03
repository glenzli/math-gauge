#!/usr/bin/env python3
"""Render current public results without scoring or writing result JSON.

SVG uses the standard library. Optional PNG export uses an existing Sharp module.
"""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess

from render_benchmark_report import (COMPONENTS, RELIABILITY, DIMENSIONS, ar_counts,
    ar_dimension, escape, family_count, number, private_score, raw_count, result_view)

MODELS = (("terra", "Terra 6.1 Max", "#315e78"), ("gemini", "Gemini 3.8 Flash High", "#bf633e"))
PAPER_COUNTS = {"proofs": 18, "lean-audit": 6, "lean-construction": 6, "chapters": 2, "exploration": 3, "answer-review": 4}
RELIABILITY_COUNTS = {"repeat": "选定6题 · 各3次独立作答", "neutral": "同6题 · 12份后续", "stance": "同6题 · 24份后续"}


def load_public(path):
    raw = path.read_bytes()
    report = json.loads(raw)
    result_view(report)
    if report["evidence_status"]["formal_comparison_eligible"] is not False:
        raise ValueError("This page is a provisional development comparison")
    return report, hashlib.sha256(raw).hexdigest()


def presentation(terra_path, gemini_path):
    reports, sources, models = {}, {}, {}
    for key, path in (("terra", terra_path), ("gemini", gemini_path)):
        reports[key], digest = load_public(path)
        sources[key] = {"sha256": digest, "public_result": f"../{key}-2026-11-03/result.json"}
    for field in ("components", "overall_weights"):
        if reports["terra"]["profile"][field] != reports["gemini"]["profile"][field]:
            raise ValueError("Frozen scoring configuration differs")
    for key, title, color in MODELS:
        report = reports[key]
        models[key] = {"title": title, "color": color,
            "metrics": {metric: report["metrics"][metric]["exact"] for metric in [r[0] for r in COMPONENTS + RELIABILITY] + ["core", "overall"]},
            "strict_passes": report["strict_passes"], "ar_counts": ar_counts(report),
            "ar_records": result_view(report)["ar_records"],
            "private_completion": {row["public_id"]: row["completion"]["exact"] for row in report["private_records"]}}
    chapters = {"MG-C002": {"total": 34, "terra": 34, "gemini": 0}, "MG-C003": {"total": 92, "terra": 20, "gemini": 0}}
    for public_id, row in chapters.items():
        for key, _, _ in MODELS:
            record = next(r for r in reports[key]["slot_evidence"] if r["slot_id"] == public_id + ":A1")
            if abs(record["completion"]["exact"] - row[key] / row["total"]) > 1e-12:
                raise ValueError("Published chapter count differs from source completion")
    return {"sources": sources, "models": models, "profile": reports["terra"]["profile"], "chapter_completion": chapters,
            "coverage": {"initial_tasks": reports["terra"]["coverage"]["a1_planned"],
                         "parent_families": family_count(reports["terra"]), "all_records": reports["terra"]["coverage"]["slots_planned"]}}


def text(x, y, value, size=20, color="#243541", weight=400, anchor="start"):
    return f'<text x="{x}" y="{y}" font-size="{size}" fill="{color}" font-weight="{weight}" text-anchor="{anchor}">{escape(value)}</text>'


def svg_start(height, title, desc, data):
    return [f'<svg xmlns="http://www.w3.org/2000/svg" width="1440" height="{height}" viewBox="0 0 1440 {height}" role="img" aria-labelledby="title-{height} desc-{height}">',
            f'<title id="title-{height}">{escape(title)}</title><desc id="desc-{height}">{escape(desc)}</desc>',
            f'<metadata>{escape(json.dumps(data["sources"],ensure_ascii=False))}</metadata>',
            '<style>text{font-family:-apple-system,BlinkMacSystemFont,"PingFang SC","Noto Sans CJK SC","Microsoft YaHei",sans-serif;font-variant-numeric:tabular-nums}</style>',
            f'<rect width="1440" height="{height}" fill="#fbfcfd"/>']


def axis(parts, top, bottom):
    for tick in (0, 25, 50, 75, 100):
        x = 360 + tick * 9
        parts += [f'<line x1="{x}" y1="{top}" x2="{x}" y2="{bottom}" stroke="#dce3e8"/>', text(x, top - 15, tick, 16, "#6b7c88", anchor="middle")]


def pair(parts, y, values, labels=None, flags=None):
    for index, (key, _, color) in enumerate(MODELS):
        value = values[key]
        center = y + (-13 if index == 0 else 13)
        parts.append(f'<rect x="360" y="{center-8}" width="{value*9:.6f}" height="16" rx="3" fill="{color}"/>' if value else f'<circle cx="360" cy="{center}" r="3" fill="{color}"/>')
        parts.append(text(1278, center + 6, labels[key] if labels else f"{value:.2f}", 20, color, 650))
        if flags and flags[key] is True:
            parts += [f'<circle cx="1380" cy="{center}" r="11" fill="{color}"/>', text(1380, center+7, "!", 18, "white", 700, "middle")]


def legend(parts, y):
    for x, (_, name, color) in zip((56, 450), MODELS):
        parts += [f'<rect x="{x}" y="{y-15}" width="19" height="13" rx="2" fill="{color}"/>', text(x+29,y-2,name,19,color,600)]


def main_svg(data):
    c = data["coverage"]
    p = svg_start(1480, "Math Gauge · 六方向能力与自查表现", "六方向能力和作答稳定性与自查共用0至100尺度。39份任务关联35个母题家族；AI审核的观察后重评，人审待办。", data)
    p += [text(56,43,"MATH GAUGE  /  V0.4.0  /  DEVELOPMENT COMPARISON",15,"#6b7c88",650), text(56,96,"Terra 6.1 Max × Gemini 3.8 Flash High",38,weight=700), text(56,134,f'{c["initial_tasks"]}份任务 · {c["parent_families"]}个母题家族 · {c["all_records"]}份记录 · AI审核 / 待人审',20,"#61727e")]
    for x,(key,name,color) in zip((56,748),MODELS):
        metrics=data["models"][key]["metrics"]
        p += [f'<rect x="{x}" y="163" width="636" height="118" rx="9" fill="white" stroke="#dce3e8"/>',f'<rect x="{x}" y="163" width="5" height="118" rx="2" fill="{color}"/>',text(x+24,194,name,20,color,650),text(x+24,249,f'{metrics["overall"]:.2f}',38,color,700),text(x+140,247,"综合分",17,"#61727e"),text(x+322,247,f'{metrics["core"]:.2f}',29,weight=600),text(x+422,246,"能力分",17,"#61727e")]
    p += [text(56,332,"01  六个能力方向",27,weight=700),text(56,362,"每份任务只取首次答卷；审阅先在同母题内聚合。",17,"#61727e")]
    axis(p,409,946)
    weights={row["id"]:row["weight"] for row in data["profile"]["components"]}
    for y,(key,title,_) in zip((447,535,623,711,799,887),COMPONENTS):
        p += [text(56,y-3,title,24,weight=600),text(56,y+24,f'{PAPER_COUNTS[key]}份任务 · 能力权重 {weights[key]:g}%',17,"#61727e")]
        pair(p,y,{model:data["models"][model]["metrics"][key] for model,_,_ in MODELS})
    p += [text(56,1001,"02  作答稳定性与自查表现",27,weight=700),text(56,1032,"固定选取6份数学题；自查看重点结论与论据，不等于整卷交付。",17,"#61727e")]
    axis(p,1079,1346)
    for y,(key,title,_) in zip((1117,1205,1293),RELIABILITY):
        p += [text(56,y-3,title,24,weight=600),text(56,y+24,RELIABILITY_COUNTS[key],17,"#61727e")]
        pair(p,y,{model:data["models"][model]["metrics"][key] for model,_,_ in MODELS})
    p += [text(56,1390,"综合权重：能力75% + 重复作答稳定性5% + 无反馈自查10% + 立场干扰下的自查10%。",18,"#61727e"),text(56,1422,"观察既有答卷后的方法变更与重评，不是新考试；原答和执行证据保留。",18,"#61727e"),text(56,1454,"自查只代表选定6题；中性100分不表示全部交付通过。当前为暂定开发比较。",18,"#61727e"),"</svg>"]
    return "\n".join(p)


def chapters_svg(data):
    p=svg_start(620,"Math Gauge · 两章完整交付","一章是一份相关任务，34和92项义务不是独立题数。",data)
    p += [text(56,43,"MATH GAUGE  /  FIRST-ANSWER DELIVERY",15,"#6b7c88",650),text(56,96,"两章的完整交付",38,weight=700),text(56,134,"按冻结交付门槛计完成；一章是一份相关任务，义务不是独立题数。",20,"#61727e")]
    legend(p,178);axis(p,237,464)
    for y,(public_id,row) in zip((284,417),data["chapter_completion"].items()):
        p += [text(56,y-3,public_id.removeprefix("MG-"),28,weight=650),text(56,y+27,f'{row["total"]}项本章义务 · 首次答卷',18,"#61727e")]
        pair(p,y,{key:row[key]/row["total"]*100 for key,_,_ in MODELS},{key:f'{row[key]}/{row["total"]}' for key,_,_ in MODELS})
    p += [text(56,521,"尺度：0–100% · 条末为完整满足 / 本章义务。后续答卷不替代首次答卷。",19,"#61727e"),text(56,557,"Gemini C003 原样工程为 compile_error；0/92 不等于92项数学全错。",19,"#61727e"),text(56,592,"AI审核 / 待人审 · 21处 sorry/admit 为静态诊断，不冒称内核公理审计。",17,"#61727e"),"</svg>"]
    return "\n".join(p)


def answer_review_svg(data):
    p=svg_start(850,"Math Gauge · 真实答卷审阅","主指标为连续审阅分，重大误判按原始次数另列；严格通过仅辅助。",data)
    p += [text(56,43,"MATH GAUGE  /  COMPLETE-ANSWER REVIEW",15,"#6b7c88",650),text(56,96,"真实答卷审阅",38,weight=700),text(56,134,"每题：核心判断60 + 依据与影响30 + 补充完整性10；同母题先聚合。",20,"#61727e")]
    for x,(key,name,color) in zip((56,748),MODELS):
        model=data["models"][key];counts=model["ar_counts"]
        p += [f'<rect x="{x}" y="163" width="636" height="140" rx="9" fill="white" stroke="#dce3e8"/>',text(x+24,196,name,20,color,650),text(x+24,248,f'{model["metrics"]["answer-review"]:.2f}',38,color,700),text(x+145,247,"审阅分",17,"#61727e"),text(x+330,247,raw_count(counts,"major"),31,color,650),text(x+414,246,"重大误判",17,"#61727e"),text(x+24,280,f'严格通过 {raw_count(counts,"strict")}（辅助，不替代连续分）',16,"#61727e")]
    p += [text(56,349,"四份任务，关联四个既有母题",22,weight=600)]
    axis(p,391,748)
    records={key:{row["public_id"]:row for row in data["models"][key]["ar_records"]} for key,_,_ in MODELS}
    for y,public_id in zip((431,519,607,695),sorted(records["terra"])):
        p += [text(56,y+6,public_id,24,weight=600)]
        pair(p,y,{key:records[key][public_id]["completion"]["exact"]*100 for key,_,_ in MODELS},flags={key:records[key][public_id]["major_error"] for key,_,_ in MODELS})
    p += [text(56,792,"! 表示该份有重大误判。计数只描述这4份审阅，不外推一般失败率。",18,"#61727e"),text(56,824,"8份既有原答按观察后确定的新规重评；非新考试，AI审核 / 人审待办。",18,"#61727e"),"</svg>"]
    return "\n".join(p)


def mobile_rows(data,definitions):
    rows=[]
    for key,title,_ in definitions:
        note=f'{PAPER_COUNTS[key]}份任务' if key in PAPER_COUNTS else RELIABILITY_COUNTS[key]
        bars=[]
        for model,_,color in MODELS:
            value=data["models"][model]["metrics"][key]
            bars.append(f'<div class="mbar"><span>{model.title()}</span><div class="track"><i style="width:{value}%;background:{color}"></i></div><b style="color:{color}">{value:.2f}</b></div>')
        rows.append(f'<article><h3>{title} <small>{note}</small></h3>{"".join(bars)}</article>')
    return "".join(rows)


def ar_table(data):
    rows=[]
    for key,_,_ in MODELS:
        for row in data["models"][key]["ar_records"]:
            dims="".join(f'<td>{number(ar_dimension(row,d))}</td>' for d,_,_ in DIMENSIONS)
            rows.append(f'<tr><th>{key.title()} · {row["public_id"]}</th>{dims}<td>{private_score(row)}</td><td>{"有" if row["major_error"] is True else "无" if row["major_error"] is False else "待判"}</td></tr>')
    return ''.join(rows)


def render_html(data,overview,chapters,answer_review):
    metrics=data["models"]
    strict_rows="".join(f'<tr><th>{title}</th>'+''.join(f'<td>{metrics[key]["strict_passes"][field]["passed"]}/{metrics[key]["strict_passes"][field]["total"]}</td>' for key,_,_ in MODELS)+'</tr>' for field,title in (("core_A1","首次答卷"),("all_selected_slots","全部材料")))
    metric_rows="".join(f'<tr><th>{title}</th><td>{metrics["terra"]["metrics"][key]:.2f}</td><td>{metrics["gemini"]["metrics"][key]:.2f}</td></tr>' for key,title,_ in COMPONENTS+RELIABILITY)
    private_rows="".join(f'<tr><th>{cid}</th><td>{metrics["terra"]["private_completion"][cid]*100:.2f}</td><td>{metrics["gemini"]["private_completion"][cid]*100:.2f}</td></tr>' for cid in sorted(metrics["terra"]["private_completion"]))
    fingerprints="".join(f'<dt>{name}公开结果SHA-256</dt><dd><code>{data["sources"][key]["sha256"]}</code></dd>' for key,name,_ in MODELS)
    mobile_summary="".join(f'<article><h3>{name}</h3><strong style="color:{color}">{metrics[key]["metrics"]["overall"]:.2f}</strong><p>综合分 · 能力分{metrics[key]["metrics"]["core"]:.2f}</p></article>' for key,name,color in MODELS)
    return f'''<!doctype html><html lang="zh-CN"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Math Gauge · 0.4.0当前对比</title><style>
:root{{--ink:#243541;--muted:#61727e;--line:#dce3e8;--terra:#315e78;--gemini:#bf633e}}*{{box-sizing:border-box}}body{{margin:0;background:#fbfcfd;color:var(--ink);font-family:-apple-system,BlinkMacSystemFont,"PingFang SC",sans-serif;line-height:1.7}}a{{color:var(--terra);text-underline-offset:4px}}.shell{{max-width:1220px;margin:auto;padding:0 28px}}nav{{display:flex;gap:22px;align-items:center;min-height:76px;font-size:13px;flex-wrap:wrap;border-bottom:1px solid var(--line)}}nav a:first-child{{margin-right:auto;font-weight:750;text-decoration:none;letter-spacing:.1em}}.hero{{padding:42px 0 24px}}.eyebrow{{font-size:12px;letter-spacing:.12em;color:var(--muted)}}h1{{font-size:40px;line-height:1.25;margin:14px 0}}.hero p{{max-width:900px;color:var(--muted)}}.chips{{display:flex;gap:10px;flex-wrap:wrap}}.chip{{border:1px solid var(--line);border-radius:20px;padding:3px 12px;font-size:12px}}section{{padding:32px 0;border-bottom:1px solid var(--line)}}h2{{font-size:25px;margin:0 0 12px}}h3{{font-size:17px;margin:0 0 8px}}figure{{margin:0}}.chart{{border:1px solid var(--line);border-radius:9px;overflow:hidden}}.chart svg{{display:block;width:100%;height:auto}}figcaption,.note{{font-size:14px;color:var(--muted)}}figcaption{{padding:10px 0}}.downloads{{display:flex;gap:20px;flex-wrap:wrap;font-size:13px;margin:16px 0}}.grid{{display:grid;grid-template-columns:1fr 1fr;gap:32px}}.tablewrap{{overflow-x:auto}}table{{width:100%;border-collapse:collapse;font-size:13px;font-variant-numeric:tabular-nums}}th,td{{text-align:right;border-bottom:1px solid var(--line);padding:11px;white-space:nowrap}}th:first-child{{text-align:left;padding-left:0}}thead th{{font-size:12px;color:var(--muted);font-weight:500}}p{{margin:10px 0 18px}}.method p{{color:var(--muted);font-size:14px}}.method h3{{margin-top:20px}}details{{font-size:13px;margin-top:22px}}summary{{cursor:pointer;color:var(--terra)}}dt{{font-size:12px;color:var(--muted);margin-top:12px}}dd{{margin:4px 0;overflow-wrap:anywhere}}code{{font-size:11px}}footer{{font-size:12px;color:var(--muted);padding:26px 0 36px}}.mobile{{display:none}}.mbar{{display:grid;grid-template-columns:55px 1fr 46px;gap:10px;align-items:center;font-size:12px;margin:7px 0}}.mbar b{{text-align:right;font-variant-numeric:tabular-nums}}.track{{height:10px;border-radius:3px;background:#e7ecf0;overflow:hidden}}.track i{{height:100%;display:block}}.mobile article{{padding:18px 0;border-top:1px solid var(--line)}}.mobile h3 small{{display:block;color:var(--muted);font-size:11px;font-weight:400}}.mobile-summary{{display:grid;grid-template-columns:1fr 1fr;gap:12px}}.mobile-summary article{{padding:16px;border:1px solid var(--line);border-radius:8px}}.mobile-summary strong{{font-size:34px;display:block;font-variant-numeric:tabular-nums}}.mobile-summary p{{font-size:11px}}@media(max-width:680px){{.shell{{padding:0 20px}}nav{{gap:13px;font-size:12px;min-height:68px}}h1{{font-size:31px}}.hero{{padding:30px 0 20px}}.hero p{{font-size:14px}}.desktop{{display:none}}.mobile{{display:block}}.mobile h2{{margin-top:28px;font-size:22px}}.mobile-summary h3{{font-size:14px}}.grid{{grid-template-columns:1fr;gap:24px}}.widechart{{overflow-x:auto}}.widechart svg{{min-width:780px}}th,td{{padding:10px;font-size:12px}}h2{{font-size:23px}}}}@media print{{nav,.downloads{{display:none}}section{{break-inside:avoid;padding:22px 0}}.shell{{padding:0}}.chart{{border:0}}}}
</style></head><body><main class="shell"><nav><a href="../../../README.md">MATH GAUGE</a><a href="#comparison">六方向能力</a><a href="#answer-review">答卷审阅</a><a href="#chapters">整章</a><a href="#method">方法</a><a href="result.json">JSON</a></nav><div class="hero"><div class="eyebrow">V0.4.0 · POST-OBSERVATION RESCORING</div><h1>数学作答、答卷审阅与自查表现</h1><p>对照Terra 6.1 Max与Gemini 3.8 Flash High。能力包含39份任务、35个母题家族，完整计划87份记录；公开任务包范围为36份任务、32个母题家族、84份记录。审阅与母题相关，不制造新的独立数学题材。</p><div class="chips"><span class="chip">AI审核 / 待人审</span><span class="chip">8份审阅原答统一重评</span><span class="chip">0.4.0题库</span></div></div><section id="comparison"><figure class="desktop"><div class="chart">{overview}</div><figcaption>六方向与稳定性/自查共用0–100完整尺度，无断轴。蓝色Terra，橙色Gemini；各条末为共享评分结果。</figcaption></figure><div class="mobile"><div class="mobile-summary">{mobile_summary}</div><h2>六个能力方向</h2><p class="note">只取首次答卷，同母题审阅先聚合；每条均为0–100尺度。</p>{mobile_rows(data,COMPONENTS)}<h2>作答稳定性与自查表现</h2>{mobile_rows(data,RELIABILITY)}</div><div class="downloads"><a href="comparison.png" download>主图PNG</a><a href="comparison.svg" download>SVG</a><a href="../../benchmark-comparison-2026-11-03.md">文字表</a></div><p class="note">综合分 = 75%能力分 + 5%重复作答稳定性 + 10%无反馈自查 + 10%立场干扰下的自查。合并六方向权重22.5/18/18/18/13.5/10；额外重复与自查不重复进入能力。</p></section><section id="answer-review"><h2>审阅主分与重大误判分别看</h2><p class="note">审阅每题100分：核心判断60、依据与影响30、补充完整性10；同母题先聚合。主指标保留连续分，重大误判直写0/4与1/4，严格通过只作辅助。</p><figure><div class="chart widechart">{answer_review}</div></figure><div class="downloads"><a href="answer-review.png" download>审阅图PNG</a><a href="answer-review.svg" download>SVG</a><a href="../../../protocol/answer-review-scoring.md">评分定义</a></div><div class="tablewrap"><table><thead><tr><th>审阅任务</th><th>核心 / 60</th><th>依据影响 / 30</th><th>补充 / 10</th><th>总分 / 100</th><th>重大误判</th></tr></thead><tbody>{ar_table(data)}</tbody></table></div><p class="note">重大误判按实际断言与影响裁定，不由总分倒推。Gemini AR003明确接受固定目标的错误识别，记为重大；AR002附加路线遗漏、AR004补充边界遗漏与范围误述分别扣分，但不自动升级为重大。Terra AR003只漏一项大小核查，得95分。四份审阅不能给出一般失败率。</p></section><section id="chapters"><h2>整章交付单独展示</h2><p class="note">章节均分可能掩盖具体交付缺口。首次答卷以34/92项本章义务归一化，各章仍各是一份相关任务。</p><figure><div class="chart widechart">{chapters}</div></figure><div class="downloads"><a href="chapters.png" download>整章图PNG</a><a href="chapters.svg" download>SVG</a></div><p class="note">C003的工程失败与数学错误分别记录；九项具体数学错误或语义缺口有依据，不能把0/92说成92项数学全错。后续答卷不替代首次。</p></section><section><div class="grid"><div><h2>作答稳定性与自查的范围</h2><p class="note">从原公开数学任务中固定选择6题。重复看各三次严格全对，无反馈与立场干扰下自查看12份、24份后续的重点数学正确性。审阅与探索未安排这些轮次，不应记为重复实验缺测。</p><p class="note">Gemini自查的真假标签始终正确，但三份立场后续新增错误论据；GF104无反馈分支有声明对应交付遗漏，重点数学仍正确。因此中性100分不表示整卷全部严格通过。起点没有错误时纠错率不适用。</p></div><div><h2>严格通过仅作辅助诊断</h2><table><thead><tr><th>材料</th><th>Terra</th><th>Gemini</th></tr></thead><tbody>{strict_rows}</tbody></table><p class="note">严格完成检查全部实际义务，不额外加权，也不把非满分审阅全清零。这里的辅助计数不替代连续审阅分或重大误判记录。</p></div></div></section><section><div class="grid"><div><h2>分项数值 / 100</h2><table><thead><tr><th>方向</th><th>Terra</th><th>Gemini</th></tr></thead><tbody>{metric_rows}</tbody></table></div><div><h2>探索只公开中性摘要</h2><table><thead><tr><th>完成分 / 100</th><th>Terra</th><th>Gemini</th></tr></thead><tbody>{private_rows}</tbody></table><p class="note">3份首次答卷，均为AI已评阅 / 人审待办。不公开题材标题、内部题号、完整题面、原答或详细审核；三份不足以代表广泛探索能力。</p></div></div></section><section id="method" class="method"><h2>方法变更与解释范围</h2><div class="grid"><div><h3>观察结果后的重评</h3><p>AR纳入、60/30/10评分与权重是在看过既有答卷及试点评分后确定的。8份审阅原答按同一新规重评，再与数学答卷合并重算，不是预注册的新考试。候选原题与附件逐字保留，原答、旧评审快照与真实执行证据均不覆盖。</p><h3>为什么单列这些项目</h3><p>六个能力方向反映不同交付；稳定性与两种自查反映不同协作条件；审阅另看重大误判，整章另看义务完成。总分与能力分作概览，严格通过作辅助。九个交叉重点标签不另造分数或重复加权。</p></div><div><h3>执行与审核分别记录</h3><p>数学结果保留历史独立答卷及对应探索执行，AR来自已完成真实审阅。两边允许本地工具、禁止外部搜索；预算、上下文与执行批次保留各自证据，不视作一次同步完全等条件竞赛。Gemini旧83份评分记录对应85次原生提交，加入AR4后为87份记录、89次提交；新增4份AR由root直接复评，旧82份Terra主评仅属旧83份材料。中断与续接保留原始记录。</p><h3>暂定开发比较</h3><p>题目和答卷为AI审核、人审待办；编译、公理审计、语义对应与来源审核分别记录。作者Lean仍仅原43数学卷/372义务，不扩大到47任务。请求标签和散列不能认证实际后端。公开参考与Git历史不是隐藏留出集，本页不具正式比较或认证排名资格。v0.4.0提供独立任务包，既有版本资产保持原样。</p></div></div><details><summary>公开来源与离线阅读</summary><p>HTML内嵌三张SVG，无远端字体、脚本或数据请求，保存后可离线打开；生成器只读公开结果，不重跑模型、Lean或评分器，也不写结果JSON。</p><dl>{fingerprints}</dl><p><a href="../terra-2026-11-03/result.json">Terra结果</a> · <a href="../gemini-2026-11-03/result.json">Gemini结果</a> · <a href="../../terra-combined-2026-11-03.md">Terra报告</a> · <a href="../../gemini-combined-2026-11-03.md">Gemini报告</a> · <a href="../../../protocol/composite-development-report.md">组合合同</a></p></details></section><footer>Math Gauge · 当前统一展示0.4.0；原始证据保留，不并列另一套当前榜。</footer></main></body></html>'''


def render_markdown(data):
    models=data["models"]
    lines=["# Terra / Gemini · 0.4.0当前综合重算","","[离线对比页](results/comparison-2026-11-03/index.html) · [主图PNG](results/comparison-2026-11-03/comparison.png) · [SVG](results/comparison-2026-11-03/comparison.svg) · [展示数据](results/comparison-2026-11-03/result.json)","","![六能力与自查对比](results/comparison-2026-11-03/comparison.png)","","39份任务、35个母题家族、87份记录；公开默认范围为36份任务、32个家族、84份记录。AI审核 / 人审待办。AR纳入、评分及8份原答重评是观察结果后的方法变更，不是新考试；原答和执行保留，0.4.0题库与任务包版本一致。","","| 概览 | Terra 6.1 Max | Gemini 3.8 Flash High |","| --- | ---: | ---: |"]
    for key,title in (("overall","综合分"),("core","能力分")):
        lines.append(f'| {title} | {models["terra"]["metrics"][key]:.2f} | {models["gemini"]["metrics"][key]:.2f} |')
    lines += ["","| 能力方向 | 任务数 | 能力权重 | Terra | Gemini |","| --- | ---: | ---: | ---: | ---: |"]
    weights={r["id"]:r["weight"] for r in data["profile"]["components"]}
    for key,title,_ in COMPONENTS:
        lines.append(f'| {title} | {PAPER_COUNTS[key]} | {weights[key]:g}% | {models["terra"]["metrics"][key]:.2f} | {models["gemini"]["metrics"][key]:.2f} |')
    lines += ["","综合分 = 75%能力分 + 5%重复作答稳定性 + 10%无反馈自查 + 10%立场干扰下的自查。只以首次答卷计能力，审阅先在同母题内聚合；额外重复与自查不重复进入能力。","","## 真实答卷审阅：主分与重大误判","","![真实答卷审阅](results/comparison-2026-11-03/answer-review.png)","","| 指标 | Terra | Gemini |","| --- | ---: | ---: |"]
    lines.append(f'| 审阅主分 / 100 | {models["terra"]["metrics"]["answer-review"]:.2f} | {models["gemini"]["metrics"]["answer-review"]:.2f} |')
    for field,title in (("major","重大误判"),("strict","严格通过（仅辅助）")):
        lines.append(f'| {title} | {raw_count(models["terra"]["ar_counts"],field)} | {raw_count(models["gemini"]["ar_counts"],field)} |')
    lines += ["","每题核心判断60、依据与影响30、补充完整性10。重大误判按实际数学断言与影响裁定，不由分数阈值倒推；0/4与1/4只描述本次4份审阅，不能外推一般失败率。四份审阅直接关联已有母题与共同历史来源，不制造独立数学题材。","","| 审阅任务 | Terra / 100 | Gemini / 100 |","| --- | ---: | ---: |"]
    ar={key:{r["public_id"]:r for r in models[key]["ar_records"]} for key,_,_ in MODELS}
    for cid in sorted(ar["terra"]):
        lines.append(f'| {cid} | {private_score(ar["terra"][cid])} | {private_score(ar["gemini"][cid])} |')
    lines += ["","Gemini AR003明确接受固定目标的错误识别，记重大误判；AR002附加路线遗漏与AR004补充边界/范围问题不自动升级重大。Terra AR003只漏一项大小核查，得95分。完整判准见[审阅评分](../protocol/answer-review-scoring.md)。","","## 作答稳定性与自查表现","","| 指标 | 固定范围 | Terra | Gemini |","| --- | --- | ---: | ---: |"]
    for key,title,_ in RELIABILITY:
        lines.append(f'| {title} | {RELIABILITY_COUNTS[key]} | {models["terra"]["metrics"][key]:.2f} | {models["gemini"]["metrics"][key]:.2f} |')
    lines += ["","从原公开数学任务固定选6题，AR和探索不在重复/自查分母内。真假标签、核查论据与整卷交付分开：Gemini自查标签均正确，但3份立场后续有新增错误论据；GF104无反馈分支有交付遗漏。中性100分不等于全部交付严格通过。没有错误起点时纠错率不适用。","","## 整章交付与辅助诊断","","![两章完整交付](results/comparison-2026-11-03/chapters.png)","","| 整章首次答卷 | Terra完整满足 | Gemini完整满足 |","| --- | ---: | ---: |"]
    for cid,row in data["chapter_completion"].items(): lines.append(f'| {cid.removeprefix("MG-")} | {row["terra"]}/{row["total"]} | {row["gemini"]}/{row["total"]} |')
    lines += ["","一章仍是一份任务，92项义务不是92题。Gemini C003原样工程为compile_error，0/92不是92项数学全错；九项具体错误或语义缺口与其他未完成分开，21处sorry/admit仅静态诊断。后续答卷不替代首次。","","| 严格通过（辅助） | Terra | Gemini |","| --- | ---: | ---: |"]
    for field,title in (("core_A1","首次答卷"),("all_selected_slots","全部材料")):
        records=[models[key]["strict_passes"][field] for key,_,_ in MODELS]
        lines.append(f'| {title} | {records[0]["passed"]}/{records[0]["total"]} | {records[1]["passed"]}/{records[1]["total"]} |')
    lines += ["","## 方法与证据","","六方向分别反映任务交付；三项稳定性/自查反映不同协作条件；AR另看重大误判，整章另看完成义务。总分和能力分概览，严格通过辅助。九个交叉重点标签不另造分数或重复加权。","","Gemini旧83份评分记录对应85次原生提交，加入4份AR后为87份记录、89次提交；新增4份AR由root直接复评，旧82份Terra主评仅描述原83份材料。不同执行批次与预算保留原记录，数学历史复用和8份审阅后验重评不能称为同步完全等条件的新考试。当前AI审核、人审待办，不具正式比较资格；编译、公理审计、语义对应、来源及后端核验分别记录。作者Lean证据仍只覆盖原43数学卷/372义务，不扩展为47/47。","","探索只公开Private-01至Private-03中性摘要，私有题材标题、题面、内部题号、原答与详细评审留在私有存储。公开参考及Git历史不是隐藏留出集。当前统一展示0.4.0，已发布资产与原始证据保留，不另挂一套竞争当前榜。","","[Terra报告](terra-combined-2026-11-03.md) · [Gemini报告](gemini-combined-2026-11-03.md) · [组合合同](../protocol/composite-development-report.md)",""]
    for key,title,_ in MODELS: lines.append(f'- {title}公开结果SHA-256：`{data["sources"][key]["sha256"]}`。')
    lines += ["","重生成：`python3 scripts/render_benchmark_comparison.py`。PNG可用`--sharp-module`指向已有Sharp、`--node`选择Node；不安装依赖，不写结果JSON，不调用评分、模型或Lean。",""]
    return '\n'.join(lines)


def update_readme(path,data):
    text=path.read_text(encoding='utf-8');start=text.index('## 最新综合结果');end=text.index('## 分项与总分',start)
    lines=['## 最新综合结果','','[当前Benchmark对比页](docs/results/comparison-2026-11-03/index.html)展示六个能力方向、作答稳定性与自查、真实答卷审阅主分与重大误判、两章完整交付。[文字表](docs/benchmark-comparison-2026-11-03.md) · [PNG](docs/results/comparison-2026-11-03/comparison.png) · [SVG](docs/results/comparison-2026-11-03/comparison.svg)','','[![Math Gauge当前对比](docs/results/comparison-2026-11-03/comparison.png)](docs/results/comparison-2026-11-03/index.html)','','| 模型 | 综合分 | 能力分 | 审阅主分 | 重大误判 |','| --- | ---: | ---: | ---: | ---: |']
    for key,title,_ in MODELS:
        m=data['models'][key];lines.append(f'| {title} | **{m["metrics"]["overall"]:.2f}** | **{m["metrics"]["core"]:.2f}** | {m["metrics"]["answer-review"]:.2f} | {raw_count(m["ar_counts"],"major")} |')
    lines += ['','当前合并范围39份任务、35个母题家族、87份记录；公开默认范围36份任务、32个家族、84份记录。AR纳入、60/30/10判准与8份既有原答重评发生在观察结果后，是方法变更与重算，不是新考试。AI审核 / 人审待办，0.4.0题库与任务包版本一致，原答、旧审核与已发布资产保留。','','[审阅专图](docs/results/comparison-2026-11-03/answer-review.png)单列4份任务、重大误判0/4与1/4；严格通过仅辅助，不用未满分全清零。稳定性与自查只选6份数学题，中性100分不代表全部交付通过。整章另列34/34与0/34、20/92与0/92；义务不是独立题数，后续答卷不替代首次。','','[Terra报告](docs/terra-combined-2026-11-03.md) · [Gemini报告](docs/gemini-combined-2026-11-03.md) · [审阅评分](protocol/answer-review-scoring.md) · [组合合同](protocol/composite-development-report.md)','','']
    path.write_text(text[:start]+'\n'.join(lines)+text[end:],encoding='utf-8')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--terra',type=Path,default=Path('docs/results/terra-2026-11-03/result.json'))
    parser.add_argument('--gemini',type=Path,default=Path('docs/results/gemini-2026-11-03/result.json'))
    parser.add_argument('--out',type=Path,default=Path('docs/results/comparison-2026-11-03'))
    parser.add_argument('--markdown',type=Path,default=Path('docs/benchmark-comparison-2026-11-03.md'))
    parser.add_argument('--readme',type=Path,default=Path('README.md'))
    parser.add_argument('--sharp-module',type=Path);parser.add_argument('--node',default='node')
    args=parser.parse_args();data=presentation(args.terra,args.gemini)
    overview,chapters,ar=main_svg(data),chapters_svg(data),answer_review_svg(data)
    args.out.mkdir(parents=True,exist_ok=True)
    for name,content in (('comparison.svg',overview),('chapters.svg',chapters),('answer-review.svg',ar),('index.html',render_html(data,overview,chapters,ar))): (args.out/name).write_text(content,encoding='utf-8')
    args.markdown.write_text(render_markdown(data),encoding='utf-8');update_readme(args.readme,data)
    if args.sharp_module:
        code="const sharp=require(process.argv[1]); Promise.all(process.argv.slice(2).map(p=>sharp(p,{density:144}).png().toFile(p.replace(/\\.svg$/,'.png')))).catch(e=>{console.error(e);process.exit(1)});"
        subprocess.run([args.node,'-e',code,str(args.sharp_module.resolve()),*[str(args.out/name) for name in ('comparison.svg','chapters.svg','answer-review.svg')]],check=True)
    print(f'Rendered 3 source-bound charts and current offline reports; result JSON untouched: {args.out}')


if __name__=='__main__': main()
