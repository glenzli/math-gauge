#!/usr/bin/env python3
"""Render current public results without scoring or writing result JSON.

SVG uses the standard library. Optional PNG export uses an existing Sharp module.
"""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess

from render_benchmark_report import (RELIABILITY, DIMENSIONS, ar_counts,
    ar_dimension, count_label, coverage_note, escape, family_count, method_note,
    number, planned_count, private_score, profile_versions, raw_count,
    reliability_description, result_view, value, version_label, weight_note)

MODELS = (("terra", "Terra 6.1 Max", "#315e78"), ("gemini", "Gemini 3.8 Flash High", "#bf633e"))


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
    for field in ("components", "overall_weights", "repeat_attempt_labels", "self_check_rounds_per_arm"):
        if reports["terra"]["profile"].get(field) != reports["gemini"]["profile"].get(field):
            raise ValueError(f"Frozen scoring configuration differs: {field}")
    if profile_versions(reports["terra"]) != profile_versions(reports["gemini"]):
        raise ValueError("Frozen scoring versions differ")
    source = reports["terra"]
    view = result_view(source)
    components = view["components"]
    for key in [row[0] for row in components + list(RELIABILITY)]:
        if planned_count(source, key) != planned_count(reports["gemini"], key):
            raise ValueError(f"Frozen direction coverage differs: {key}")
    for field in ("a1_planned", "slots_planned"):
        if source["coverage"][field] != reports["gemini"]["coverage"][field]:
            raise ValueError(f"Frozen plan coverage differs: {field}")
    if family_count(source) != family_count(reports["gemini"]):
        raise ValueError("Frozen parent-family coverage differs")
    for key, title, color in MODELS:
        report = reports[key]
        models[key] = {"title": title, "color": color,
            "metrics": {metric: value(report["metrics"][metric]) for metric in [r[0] for r in components + list(RELIABILITY)] + ["core", "overall"]},
            "strict_passes": report["strict_passes"], "ar_counts": ar_counts(report),
            "ar_records": result_view(report)["ar_records"],
            "private_completion": {row["public_id"]: value(row["completion"]) for row in report.get("private_records", [])}}
    chapters = {}
    # These are the unchanged chapter obligation denominators, not model scores.
    for public_id, total in (("MG-C002", 34), ("MG-C003", 92)):
        row = {"total": total}
        for key, _, _ in MODELS:
            record = next((r for r in reports[key]["slot_evidence"] if r["slot_id"] == public_id + ":A1"), None)
            exact = value(record["completion"]) if record is not None else None
            row[key] = None if exact is None else round(exact * total)
            if exact is not None and abs(exact - row[key] / total) > 1e-12:
                raise ValueError("Frozen chapter fraction is not an obligation count")
        chapters[public_id] = row
    return {"sources": sources, "models": models, "profile": source["profile"], "chapter_completion": chapters,
            "version": version_label(source), "components": components,
            "component_counts": {key: planned_count(source, key) for key, _, _ in components},
            "reliability_counts": {key: reliability_description(source, key) for key, _, _ in RELIABILITY},
            "reliability_planned": {key: planned_count(source, key) for key, _, _ in RELIABILITY},
            "coverage_note": coverage_note(source), "method_note": method_note(source),
            "weight_note": weight_note(source),
            "private_planned": planned_count(source, "exploration") if "exploration" in models["terra"]["metrics"] else 0,
            "coverage": {"initial_tasks": source["coverage"]["a1_planned"],
                         "parent_families": family_count(source), "all_records": source["coverage"]["slots_planned"]}}


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
        if value is not None:
            parts.append(f'<rect x="360" y="{center-8}" width="{value*9:.6f}" height="16" rx="3" fill="{color}"/>' if value else f'<circle cx="360" cy="{center}" r="3" fill="{color}"/>')
        parts.append(text(1278, center + 6, labels[key] if labels else number(value), 20, color, 650))
        if flags and flags[key] is True:
            parts += [f'<circle cx="1380" cy="{center}" r="11" fill="{color}"/>', text(1380, center+7, "!", 18, "white", 700, "middle")]


def legend(parts, y):
    for x, (_, name, color) in zip((56, 450), MODELS):
        parts += [f'<rect x="{x}" y="{y-15}" width="19" height="13" rx="2" fill="{color}"/>', text(x+29,y-2,name,19,color,600)]


def main_svg(data):
    c = data["coverage"]
    p = svg_start(1480, "Math Gauge · 能力与自查表现", data["coverage_note"] + "AI审核的观察后选题重算，人审待办。", data)
    p += [text(56,43,f'MATH GAUGE  /  V{data["version"]}  /  DEVELOPMENT COMPARISON',15,"#6b7c88",650), text(56,96,"Terra 6.1 Max × Gemini 3.8 Flash High",38,weight=700), text(56,134,f'{c["initial_tasks"]}份任务 · {count_label(c["parent_families"])}个母题家族 · {c["all_records"]}份记录 · AI审核 / 待人审',20,"#61727e")]
    for x,(key,name,color) in zip((56,748),MODELS):
        metrics=data["models"][key]["metrics"]
        p += [f'<rect x="{x}" y="163" width="636" height="118" rx="9" fill="white" stroke="#dce3e8"/>',f'<rect x="{x}" y="163" width="5" height="118" rx="2" fill="{color}"/>',text(x+24,194,name,20,color,650),text(x+24,249,f'{number(metrics["overall"])}',38,color,700),text(x+140,247,"综合分",17,"#61727e"),text(x+322,247,f'{number(metrics["core"])}',29,weight=600),text(x+422,246,"能力分",17,"#61727e")]
    p += [text(56,332,f'01  {len(data["components"])}个能力方向',27,weight=700),text(56,362,"每份任务只取首次答卷；审阅先在同母题内聚合。",17,"#61727e")]
    axis(p,409,946)
    weights={row["id"]:row["weight"] for row in data["profile"]["components"]}
    for y,(key,title,_) in zip((447,535,623,711,799,887),data["components"]):
        p += [text(56,y-3,title,24,weight=600),text(56,y+24,f'{data["component_counts"][key]}份任务 · 能力权重 {weights[key]:g}%',17,"#61727e")]
        pair(p,y,{model:data["models"][model]["metrics"][key] for model,_,_ in MODELS})
    p += [text(56,1001,"02  作答稳定性与自查表现",27,weight=700),text(56,1032,"使用冻结计划的固定数学选题；自查看重点数学正确性、结论与论据，不等于整卷交付。",17,"#61727e")]
    axis(p,1079,1346)
    for y,(key,title,_) in zip((1117,1205,1293),RELIABILITY):
        note = data["reliability_counts"][key]
        if key in ("neutral", "stance"):
            note = f'{data["reliability_planned"][key]}份后续'
            rounds = data["profile"].get("self_check_rounds_per_arm")
            if rounds is not None:
                note += f" · 每分支{rounds}轮"
        p += [text(56,y-3,title,24,weight=600),text(56,y+24,note,17,"#61727e")]
        pair(p,y,{model:data["models"][model]["metrics"][key] for model,_,_ in MODELS})
    p += [text(56,1390,data["weight_note"].split("。",1)[0]+"。",18,"#61727e"),text(56,1422,"原生初答与旧答复用分别留证；观察后选题重算，已发布资产不变。",18,"#61727e"),text(56,1454,"自查只代表固定选题；中性100分不表示全部交付通过。当前为暂定开发比较。",18,"#61727e"),"</svg>"]
    return "\n".join(p)


def chapters_svg(data):
    p=svg_start(620,"Math Gauge · 两章完整交付","一章是一份相关任务，34和92项义务不是独立题数。",data)
    p += [text(56,43,"MATH GAUGE  /  FIRST-ANSWER DELIVERY",15,"#6b7c88",650),text(56,96,"两章的完整交付",38,weight=700),text(56,134,"按冻结交付门槛计完成；一章是一份相关任务，义务不是独立题数。",20,"#61727e")]
    legend(p,178);axis(p,237,464)
    for y,(public_id,row) in zip((284,417),data["chapter_completion"].items()):
        p += [text(56,y-3,public_id.removeprefix("MG-"),28,weight=650),text(56,y+27,f'{row["total"]}项本章义务 · 首次答卷',18,"#61727e")]
        pair(p,y,{key:None if row[key] is None else row[key]/row["total"]*100 for key,_,_ in MODELS},{key:"待完成" if row[key] is None else f'{row[key]}/{row["total"]}' for key,_,_ in MODELS})
    p += [text(56,521,"尺度：0–100% · 条末为完整满足 / 本章义务。后续答卷不替代首次答卷。",19,"#61727e"),text(56,557,"工程失败与数学错误分别记录，未完成义务不能全部解释为数学错误。",19,"#61727e"),text(56,592,"AI审核 / 待人审 · 静态诊断、编译与内核公理审计分别记录。",17,"#61727e"),"</svg>"]
    return "\n".join(p)


def answer_review_svg(data):
    records={key:{row["public_id"]:row for row in data["models"][key]["ar_records"]} for key,_,_ in MODELS}
    public_ids=sorted(set().union(*(set(rows) for rows in records.values())))
    height=498+88*len(public_ids)
    p=svg_start(height,"Math Gauge · 真实答卷审阅","主指标为连续审阅分，重大误判按原始次数另列；严格通过仅辅助。",data)
    p += [text(56,43,"MATH GAUGE  /  COMPLETE-ANSWER REVIEW",15,"#6b7c88",650),text(56,96,"真实答卷审阅",38,weight=700),text(56,134,"每题：核心判断60 + 依据与影响30 + 补充完整性10；同母题先聚合。",20,"#61727e")]
    for x,(key,name,color) in zip((56,748),MODELS):
        model=data["models"][key];counts=model["ar_counts"]
        p += [f'<rect x="{x}" y="163" width="636" height="140" rx="9" fill="white" stroke="#dce3e8"/>',text(x+24,196,name,20,color,650),text(x+24,248,f'{number(model["metrics"]["answer-review"])}',38,color,700),text(x+145,247,"审阅分",17,"#61727e"),text(x+330,247,raw_count(counts,"major"),31,color,650),text(x+414,246,"重大误判",17,"#61727e"),text(x+24,280,f'严格通过 {raw_count(counts,"strict")}（辅助，不替代连续分）',16,"#61727e")]
    p += [text(56,349,f'计划{data["component_counts"]["answer-review"]}份审阅单位，关联既有母题',22,weight=600)]
    axis(p,391,396+88*len(public_ids))
    for index,public_id in enumerate(public_ids):
        y=431+88*index
        p += [text(56,y+6,public_id,24,weight=600)]
        pair(p,y,{key:percent(value(records[key][public_id]["completion"])) if public_id in records[key] else None for key,_,_ in MODELS},flags={key:records[key].get(public_id,{}).get("major_error") for key,_,_ in MODELS})
    p += [text(56,440+88*len(public_ids),"! 表示该份有重大误判。计数只描述本次审阅，不外推一般失败率。",18,"#61727e"),text(56,472+88*len(public_ids),"既有原答按观察后确定的判准重评；AI审核 / 人审待办。",18,"#61727e"),"</svg>"]
    return "\n".join(p)


def percent(item):
    return None if item is None else item * 100


def mobile_rows(data,definitions):
    rows=[]
    for key,title,_ in definitions:
        note=f'{data["component_counts"][key]}份任务' if key in data["component_counts"] else data["reliability_counts"][key]
        bars=[]
        for model,_,color in MODELS:
            value=data["models"][model]["metrics"][key]
            bar = f'<i style="width:{value}%;background:{color}"></i>' if value is not None else ""
            bars.append(f'<div class="mbar"><span>{model.title()}</span><div class="track">{bar}</div><b style="color:{color}">{number(value)}</b></div>')
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
    metric_rows="".join(f'<tr><th>{title}</th><td>{number(metrics["terra"]["metrics"][key])}</td><td>{number(metrics["gemini"]["metrics"][key])}</td></tr>' for key,title,_ in data["components"]+list(RELIABILITY))
    private_rows="".join(f'<tr><th>{cid}</th><td>{number(percent(metrics["terra"]["private_completion"].get(cid)))}</td><td>{number(percent(metrics["gemini"]["private_completion"].get(cid)))}</td></tr>' for cid in sorted(set(metrics["terra"]["private_completion"]) | set(metrics["gemini"]["private_completion"])))
    fingerprints="".join(f'<dt>{name}公开结果SHA-256</dt><dd><code>{data["sources"][key]["sha256"]}</code></dd>' for key,name,_ in MODELS)
    mobile_summary="".join(f'<article><h3>{name}</h3><strong style="color:{color}">{number(metrics[key]["metrics"]["overall"])}</strong><p>综合分 · 能力分{number(metrics[key]["metrics"]["core"])}</p></article>' for key,name,color in MODELS)
    return f'''<!doctype html><html lang="zh-CN"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Math Gauge · {escape(data['version'])}当前对比</title><style>
:root{{--ink:#243541;--muted:#61727e;--line:#dce3e8;--terra:#315e78;--gemini:#bf633e}}*{{box-sizing:border-box}}body{{margin:0;background:#fbfcfd;color:var(--ink);font-family:-apple-system,BlinkMacSystemFont,"PingFang SC",sans-serif;line-height:1.7}}a{{color:var(--terra);text-underline-offset:4px}}.shell{{max-width:1220px;margin:auto;padding:0 28px}}nav{{display:flex;gap:22px;align-items:center;min-height:76px;font-size:13px;flex-wrap:wrap;border-bottom:1px solid var(--line)}}nav a:first-child{{margin-right:auto;font-weight:750;text-decoration:none;letter-spacing:.1em}}.hero{{padding:42px 0 24px}}.eyebrow{{font-size:12px;letter-spacing:.12em;color:var(--muted)}}h1{{font-size:40px;line-height:1.25;margin:14px 0}}.hero p{{max-width:900px;color:var(--muted)}}.chips{{display:flex;gap:10px;flex-wrap:wrap}}.chip{{border:1px solid var(--line);border-radius:20px;padding:3px 12px;font-size:12px}}section{{padding:32px 0;border-bottom:1px solid var(--line)}}h2{{font-size:25px;margin:0 0 12px}}h3{{font-size:17px;margin:0 0 8px}}figure{{margin:0}}.chart{{border:1px solid var(--line);border-radius:9px;overflow:hidden}}.chart svg{{display:block;width:100%;height:auto}}figcaption,.note{{font-size:14px;color:var(--muted)}}figcaption{{padding:10px 0}}.downloads{{display:flex;gap:20px;flex-wrap:wrap;font-size:13px;margin:16px 0}}.grid{{display:grid;grid-template-columns:1fr 1fr;gap:32px}}.tablewrap{{overflow-x:auto}}table{{width:100%;border-collapse:collapse;font-size:13px;font-variant-numeric:tabular-nums}}th,td{{text-align:right;border-bottom:1px solid var(--line);padding:11px;white-space:nowrap}}th:first-child{{text-align:left;padding-left:0}}thead th{{font-size:12px;color:var(--muted);font-weight:500}}p{{margin:10px 0 18px}}.method p{{color:var(--muted);font-size:14px}}.method h3{{margin-top:20px}}details{{font-size:13px;margin-top:22px}}summary{{cursor:pointer;color:var(--terra)}}dt{{font-size:12px;color:var(--muted);margin-top:12px}}dd{{margin:4px 0;overflow-wrap:anywhere}}code{{font-size:11px}}footer{{font-size:12px;color:var(--muted);padding:26px 0 36px}}.mobile{{display:none}}.mbar{{display:grid;grid-template-columns:55px 1fr 46px;gap:10px;align-items:center;font-size:12px;margin:7px 0}}.mbar b{{text-align:right;font-variant-numeric:tabular-nums}}.track{{height:10px;border-radius:3px;background:#e7ecf0;overflow:hidden}}.track i{{height:100%;display:block}}.mobile article{{padding:18px 0;border-top:1px solid var(--line)}}.mobile h3 small{{display:block;color:var(--muted);font-size:11px;font-weight:400}}.mobile-summary{{display:grid;grid-template-columns:1fr 1fr;gap:12px}}.mobile-summary article{{padding:16px;border:1px solid var(--line);border-radius:8px}}.mobile-summary strong{{font-size:34px;display:block;font-variant-numeric:tabular-nums}}.mobile-summary p{{font-size:11px}}@media(max-width:680px){{.shell{{padding:0 20px}}nav{{gap:13px;font-size:12px;min-height:68px}}h1{{font-size:31px}}.hero{{padding:30px 0 20px}}.hero p{{font-size:14px}}.desktop{{display:none}}.mobile{{display:block}}.mobile h2{{margin-top:28px;font-size:22px}}.mobile-summary h3{{font-size:14px}}.grid{{grid-template-columns:1fr;gap:24px}}.widechart{{overflow-x:auto}}.widechart svg{{min-width:780px}}th,td{{padding:10px;font-size:12px}}h2{{font-size:23px}}}}@media print{{nav,.downloads{{display:none}}section{{break-inside:avoid;padding:22px 0}}.shell{{padding:0}}.chart{{border:0}}}}
</style></head><body><main class="shell"><nav><a href="../../../README.md">MATH GAUGE</a><a href="#comparison">六方向能力</a><a href="#answer-review">答卷审阅</a><a href="#chapters">整章</a><a href="#method">方法</a><a href="result.json">JSON</a></nav><div class="hero"><div class="eyebrow">V{escape(data['version'])} · POST-OBSERVATION RESCORING</div><h1>数学作答、答卷审阅与自查表现</h1><p>对照Terra 6.1 Max与Gemini 3.8 Flash High。{escape(data["coverage_note"])}审阅与母题相关，不制造新的独立数学题材。</p><div class="chips"><span class="chip">AI审核 / 待人审</span><span class="chip">观察后选题重算</span><span class="chip">{escape(data["version"])}本地报告</span></div></div><section id="comparison"><figure class="desktop"><div class="chart">{overview}</div><figcaption>能力方向与稳定性/自查共用0–100完整尺度，无断轴。蓝色Terra，橙色Gemini；各条末为共享评分结果。</figcaption></figure><div class="mobile"><div class="mobile-summary">{mobile_summary}</div><h2>{len(data["components"])}个能力方向</h2><p class="note">只取首次答卷，同母题审阅先聚合；每条均为0–100尺度。</p>{mobile_rows(data,data["components"])}<h2>作答稳定性与自查表现</h2>{mobile_rows(data,RELIABILITY)}</div><div class="downloads"><a href="comparison.png" download>主图PNG</a><a href="comparison.svg" download>SVG</a><a href="../../benchmark-comparison-2026-11-03.md">文字表</a></div><p class="note">{escape(data["weight_note"])}额外重复与自查不重复进入能力。</p></section><section id="answer-review"><h2>审阅主分与重大误判分别看</h2><p class="note">审阅每题100分：核心判断60、依据与影响30、补充完整性10；同母题先聚合。主指标保留连续分，重大误判按冻结记录另列原始计数，严格通过只作辅助。</p><figure><div class="chart widechart">{answer_review}</div></figure><div class="downloads"><a href="answer-review.png" download>审阅图PNG</a><a href="answer-review.svg" download>SVG</a><a href="../../../protocol/answer-review-scoring.md">评分定义</a></div><div class="tablewrap"><table><thead><tr><th>审阅任务</th><th>核心 / 60</th><th>依据影响 / 30</th><th>补充 / 10</th><th>总分 / 100</th><th>重大误判</th></tr></thead><tbody>{ar_table(data)}</tbody></table></div><p class="note">重大误判按实际断言与影响裁定，不由总分倒推。具体判定来自冻结审核记录，小样本计数不能给出一般失败率。</p></section><section id="chapters"><h2>整章交付单独展示</h2><p class="note">章节均分可能掩盖具体交付缺口。首次答卷以34/92项本章义务归一化，各章仍各是一份相关任务。</p><figure><div class="chart widechart">{chapters}</div></figure><div class="downloads"><a href="chapters.png" download>整章图PNG</a><a href="chapters.svg" download>SVG</a></div><p class="note">工程失败、数学错误与其他未完成分别记录，不能把未完成义务全部解释为数学错误。后续答卷不替代首次。</p></section><section><div class="grid"><div><h2>作答稳定性与自查的范围</h2><p class="note">使用冻结计划的固定数学选题：{escape(data["reliability_counts"]["repeat"])}；{escape(data["reliability_counts"]["neutral"])}；{escape(data["reliability_counts"]["stance"])}。审阅与探索未安排这些轮次，不应记为重复实验缺测。</p><p class="note">真假标签、核查论据与完整交付分别记录。中性100分不表示整卷全部严格通过。起点没有错误时纠错率不适用。</p></div><div><h2>严格通过仅作辅助诊断</h2><table><thead><tr><th>材料</th><th>Terra</th><th>Gemini</th></tr></thead><tbody>{strict_rows}</tbody></table><p class="note">严格完成检查全部实际义务，不额外加权，也不把非满分审阅全清零。这里的辅助计数不替代连续审阅分或重大误判记录。</p></div></div></section><section><div class="grid"><div><h2>分项数值 / 100</h2><table><thead><tr><th>方向</th><th>Terra</th><th>Gemini</th></tr></thead><tbody>{metric_rows}</tbody></table></div><div><h2>探索只公开中性摘要</h2><table><thead><tr><th>完成分 / 100</th><th>Terra</th><th>Gemini</th></tr></thead><tbody>{private_rows}</tbody></table><p class="note">计划{data["private_planned"]}份首次答卷，AI审核 / 人审待办。不公开题材标题、内部题号、完整题面、原答或详细审核；少量任务不足以代表广泛探索能力。</p></div></div></section><section id="method" class="method"><h2>方法变更与解释范围</h2><div class="grid"><div><h3>观察结果后的重评</h3><p>{escape(data["method_note"])}候选实际消息、原答、旧评审快照与真实执行证据均保留。</p><h3>为什么单列这些项目</h3><p>各能力方向反映不同交付；稳定性与两种自查反映不同协作条件；审阅另看重大误判，整章另看义务完成。总分与能力分作概览，严格通过作辅助。九个交叉重点标签不另造分数或重复加权。</p></div><div><h3>执行与审核分别记录</h3><p>新原生初答、旧答复用与后验重评分别保留对应来源。两边允许本地工具、禁止外部搜索；预算、上下文与执行批次保留各自证据，不视作一次同步完全等条件竞赛。中断与续接保留原始记录。</p><h3>暂定开发比较</h3><p>题目和答卷为AI审核、人审待办；编译、公理审计、语义对应与来源审核分别记录。既有作者Lean证据不自动覆盖新增矩阵任务、加强题或审阅。请求标签和散列不能认证实际后端。公开参考与Git历史不是隐藏留出集，本页不具正式比较或认证排名资格。已发布v0.4.0资产保持不可变。</p></div></div><details><summary>公开来源与离线阅读</summary><p>HTML内嵌三张SVG，无远端字体、脚本或数据请求，保存后可离线打开；生成器只读公开结果，不重跑模型、Lean或评分器，也不写结果JSON。</p><dl>{fingerprints}</dl><p><a href="../terra-2026-11-03/result.json">Terra结果</a> · <a href="../gemini-2026-11-03/result.json">Gemini结果</a> · <a href="../../terra-combined-2026-11-03.md">Terra报告</a> · <a href="../../gemini-combined-2026-11-03.md">Gemini报告</a> · <a href="../../../protocol/composite-development-report.md">组合合同</a></p></details></section><footer>Math Gauge · 当前统一展示{escape(data['version'])}；原始证据和已发布v0.4.0资产保留，不并列另一套当前榜。</footer></main></body></html>'''


def render_markdown(data):
    models = data["models"]
    lines = [f"# Terra / Gemini · {data['version']}当前综合重算", "",
             "[离线对比页](results/comparison-2026-11-03/index.html) · [主图PNG](results/comparison-2026-11-03/comparison.png) · [SVG](results/comparison-2026-11-03/comparison.svg) · [展示数据](results/comparison-2026-11-03/result.json)", "",
             "![能力与自查对比](results/comparison-2026-11-03/comparison.png)", "",
             data["coverage_note"] + "AI审核 / 人审待办。" + data["method_note"], "",
             "| 概览 | Terra 6.1 Max | Gemini 3.8 Flash High |", "| --- | ---: | ---: |"]
    for key, title in (("overall", "综合分"), ("core", "能力分")):
        lines.append(f'| {title} | {number(models["terra"]["metrics"][key])} | {number(models["gemini"]["metrics"][key])} |')
    lines += ["", "| 能力方向 | 计划单位数 | 能力权重 | Terra | Gemini |", "| --- | ---: | ---: | ---: | ---: |"]
    weights = {row["id"]: row["weight"] for row in data["profile"]["components"]}
    for key, title, _ in data["components"]:
        lines.append(f'| {title} | {data["component_counts"][key]} | {weights[key]:g}% | {number(models["terra"]["metrics"][key])} | {number(models["gemini"]["metrics"][key])} |')
    lines += ["", data["weight_note"], "只以首次答卷计能力，审阅先在同母题内聚合；额外重复与自查不重复进入能力。", "",
              "## 真实答卷审阅：主分与重大误判", "",
              "![真实答卷审阅](results/comparison-2026-11-03/answer-review.png)", "",
              "| 指标 | Terra | Gemini |", "| --- | ---: | ---: |"]
    lines.append(f'| 审阅主分 / 100 | {number(models["terra"]["metrics"]["answer-review"])} | {number(models["gemini"]["metrics"]["answer-review"])} |')
    for field, title in (("major", "重大误判"), ("strict", "严格通过（仅辅助）")):
        lines.append(f'| {title} | {raw_count(models["terra"]["ar_counts"], field)} | {raw_count(models["gemini"]["ar_counts"], field)} |')
    lines += ["", "每题核心判断60、依据与影响30、补充完整性10。重大误判按实际数学断言与影响裁定，不由分数阈值倒推；小样本计数不能外推一般失败率。审阅关联已有母题与共同历史来源，不制造独立数学题材。", "",
              "| 审阅任务 | Terra / 100 | Gemini / 100 |", "| --- | ---: | ---: |"]
    ar = {key: {row["public_id"]: row for row in models[key]["ar_records"]} for key, _, _ in MODELS}
    for cid in sorted(set(ar["terra"]) | set(ar["gemini"])):
        scores = [private_score(ar[key][cid]) if cid in ar[key] else "待完成" for key, _, _ in MODELS]
        lines.append(f'| {cid} | {scores[0]} | {scores[1]} |')
    lines += ["", "完整判准见[审阅评分](../protocol/answer-review-scoring.md)。", "",
              "## 作答稳定性与自查表现", "", "| 指标 | 固定范围 | Terra | Gemini |", "| --- | --- | ---: | ---: |"]
    for key, title, _ in RELIABILITY:
        lines.append(f'| {title} | {data["reliability_counts"][key]} | {number(models["terra"]["metrics"][key])} | {number(models["gemini"]["metrics"][key])} |')
    lines += ["", "AR和探索不在重复/自查分母内。真假标签、核查论据与整卷交付分开；中性100分不等于全部交付严格通过。没有错误起点时纠错率不适用。", "",
              "## 整章交付与辅助诊断", "", "![两章完整交付](results/comparison-2026-11-03/chapters.png)", "",
              "| 整章首次答卷 | Terra完整满足 | Gemini完整满足 |", "| --- | ---: | ---: |"]
    for cid, row in data["chapter_completion"].items():
        counts = ["待完成" if row[key] is None else f'{row[key]}/{row["total"]}' for key, _, _ in MODELS]
        lines.append(f'| {cid.removeprefix("MG-")} | {counts[0]} | {counts[1]} |')
    lines += ["", "一章仍是一份任务，本章义务不是独立题数。工程失败、数学错误与其他未完成分别记录。后续答卷不替代首次。", "",
              "| 严格通过（辅助） | Terra | Gemini |", "| --- | ---: | ---: |"]
    for field, title in (("core_A1", "首次答卷"), ("all_selected_slots", "全部材料")):
        records = [models[key]["strict_passes"][field] for key, _, _ in MODELS]
        lines.append(f'| {title} | {records[0]["passed"]}/{records[0]["total"]} | {records[1]["passed"]}/{records[1]["total"]} |')
    lines += ["", "## 方法与证据", "", data["method_note"], "",
              "各能力方向分别反映任务交付；三项稳定性/自查反映不同协作条件；AR另看重大误判，整章另看完成义务。总分和能力分概览，严格通过辅助。交叉重点标签不另造分数或重复加权。", "",
              "新原生初答、旧答复用与后验重评分别保留来源。不同执行批次与预算保留原记录，不能称为同步完全等条件的一次新考试。当前AI审核、人审待办，不具正式比较资格；编译、公理审计、语义对应、来源及后端核验分别记录。既有作者Lean证据不自动覆盖新增矩阵任务、加强题或审阅。", "",
              f'探索计划{data["private_planned"]}份首次答卷，仅公开中性摘要，私有题材标题、题面、内部题号、原答与详细评审留在私有存储。公开参考及Git历史不是隐藏留出集。当前统一展示{data["version"]}，已发布v0.4.0资产与原始证据保留，不另挂一套竞争当前榜。', "",
              "[Terra报告](terra-combined-2026-11-03.md) · [Gemini报告](gemini-combined-2026-11-03.md) · [组合合同](../protocol/composite-development-report.md)", ""]
    for key, title, _ in MODELS:
        lines.append(f'- {title}公开结果SHA-256：`{data["sources"][key]["sha256"]}`。')
    lines += ["", "重生成：`python3 scripts/render_benchmark_comparison.py`。PNG可用`--sharp-module`指向已有Sharp、`--node`选择Node；不安装依赖，不写结果JSON，不调用评分、模型或Lean。", ""]
    return "\n".join(lines)


def update_readme(path, data):
    text = path.read_text(encoding="utf-8")
    start = text.index("## 最新综合结果")
    end = text.index("## 分项与总分", start)
    lines = ["## 最新综合结果", "",
             "[当前Benchmark对比页](docs/results/comparison-2026-11-03/index.html)展示能力方向、作答稳定性与自查、真实答卷审阅及整章交付。[文字表](docs/benchmark-comparison-2026-11-03.md) · [PNG](docs/results/comparison-2026-11-03/comparison.png) · [SVG](docs/results/comparison-2026-11-03/comparison.svg)", "",
             "[![Math Gauge当前对比](docs/results/comparison-2026-11-03/comparison.png)](docs/results/comparison-2026-11-03/index.html)", "",
             "| 模型 | 综合分 | 能力分 | 审阅主分 | 重大误判 |", "| --- | ---: | ---: | ---: | ---: |"]
    for key, title, _ in MODELS:
        model = data["models"][key]
        lines.append(f'| {title} | **{number(model["metrics"]["overall"])}** | **{number(model["metrics"]["core"])}** | {number(model["metrics"]["answer-review"])} | {raw_count(model["ar_counts"], "major")} |')
    lines += ["", data["coverage_note"] + f'当前本地报告版本{data["version"]}。' + data["method_note"], "",
              "[审阅专图](docs/results/comparison-2026-11-03/answer-review.png)单列连续审阅分与重大误判；严格通过仅辅助，不用未满分全清零。稳定性与自查只代表冻结计划的选题。整章义务不是独立题数，后续答卷不替代首次。", "",
              "[Terra报告](docs/terra-combined-2026-11-03.md) · [Gemini报告](docs/gemini-combined-2026-11-03.md) · [审阅评分](protocol/answer-review-scoring.md) · [组合合同](protocol/composite-development-report.md)", "", ""]
    path.write_text(text[:start] + "\n".join(lines) + text[end:], encoding="utf-8")


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
