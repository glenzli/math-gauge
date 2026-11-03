#!/usr/bin/env python3
"""Render a frozen public v0.4.0 result; never score or read original answers."""

import argparse
import hashlib
import html
import json
from pathlib import Path


COMPONENTS = (
    ("proofs", "书面推理", "证明、反例、构造与分类"),
    ("lean-audit", "Lean语义审计", "形式声明与原命题的对应"),
    ("lean-construction", "Lean生成与修复", "完整源码及语义对应"),
    ("chapters", "整章形式化", "逐章归一化完整交付"),
    ("exploration", "研究探索", "3份私有任务，只有首次答卷"),
    ("answer-review", "真实答卷审阅", "判断给定答卷并说明依据与影响"),
)
RELIABILITY = (
    ("repeat", "重复作答稳定性", "选定6题，各三次严格全对"),
    ("neutral", "无反馈自查", "同6题的12份后续，重点数学正确性"),
    ("stance", "立场干扰下的自查", "同6题的24份后续，重点数学正确性"),
)
DIMENSIONS = (("core_judgment", "核心判断", 60),
              ("evidence_scope", "依据与影响", 30),
              ("completeness", "补充完整性", 10))


def escape(value):
    return html.escape(str(value), quote=True)


def value(metric):
    return metric.get("exact", metric.get("value"))


def number(item):
    return "待完成" if item is None else f"{item:.2f}"


def score(metric):
    return number(value(metric))


def model_name(report):
    return "Terra 6.1 Max" if report["id"].startswith("terra") else "Gemini 3.8 Flash High"


def family_count(report):
    return report["coverage"].get("parent_families", {36: 32, 39: 35}[report["coverage"]["a1_planned"]])


def result_view(report):
    if report.get("schema") != "math-gauge.public-composite-score/v1":
        raise ValueError("Use the explicit public score projection")
    if report.get("score_units") != {"metrics": "percent", "completion": "fraction"}:
        raise ValueError("Unexpected aggregate or completion units")
    components = report["profile"]["components"]
    ids = {row["id"] for row in components}
    if "answer-review" not in ids or not ids <= {row[0] for row in COMPONENTS}:
        raise ValueError("Current display requires answer review and known directions")
    if report["coverage"]["a1_planned"] not in (36, 39) or report["coverage"]["slots_planned"] not in (84, 87):
        raise ValueError("Current display requires v0.4.0 coverage")
    for key in ids | {"core", "overall", "repeat", "neutral", "stance"}:
        if key not in report["metrics"]:
            raise ValueError(f"Missing frozen metric {key}")
    records = sorted((row for row in report["slot_evidence"] if "major_error" in row and row["slot_id"].endswith(":A1")), key=lambda row: row["public_id"])
    if len(records) != 4:
        raise ValueError("Expected the four public answer-review records")
    return {"metrics": report["metrics"], "components": [row for row in COMPONENTS if row[0] in ids],
            "weights": {row["id"]: row["weight"] for row in components}, "coverage": report["coverage"],
            "ar_records": records, "families": family_count(report)}


def ar_counts(report):
    records = result_view(report)["ar_records"]
    return {"major": sum(row["major_error"] is True for row in records),
            "major_adjudicated": sum(type(row["major_error"]) is bool for row in records),
            "strict": sum(row["strict_pass"] is True for row in records),
            "strict_adjudicated": sum(type(row["strict_pass"]) is bool for row in records),
            "total": len(records)}


def raw_count(counts, field):
    return f"{counts[field]}/{counts['total']}" if counts[field + "_adjudicated"] == counts["total"] else f"待判（已判{counts[field + '_adjudicated']}/{counts['total']}）"


def ar_dimension(row, key):
    return next((item["score"] for item in row.get("dimensions", []) if item["dimension_id"] == key), None)


def private_score(record):
    exact = value(record["completion"])
    return number(None if exact is None else exact * 100)


def private_status(record):
    return "AI已评阅" if record.get("status") in ("reviewed", "complete") else "待完成"


def human_status(record):
    return "待人审" if record.get("human_status") != "approved" else "人工已批准"


def status_word(item):
    return "有" if item is True else "无" if item is False else "待判"


def method_note():
    return "AR纳入、60/30/10判准和权重是在观察既有答卷后确定的。本版复用8份审阅原答统一重评并合并重算，不是新考试；原答、原执行与旧审核保留。0.4.0题库与任务包版本一致，已发布资产不变。"


def render_markdown(report, digest):
    view = result_view(report)
    m, c = view["metrics"], view["coverage"]
    counts = ar_counts(report)
    slug = report["id"]
    lines = [f"# {model_name(report)} · 0.4.0综合重算", "",
             f"综合分 **{score(m['overall'])}/100**，能力分 **{score(m['core'])}/100**。能力范围 **{c['a1_planned']}份任务、{view['families']}个母题家族**；完整计划 **{c['slots_planned']}份记录**，已接入审核{c['slots_reviewed']}份。", "",
             f"[离线结果页](results/{slug}/index.html) · [Benchmark对比图](results/comparison-2026-11-03/index.html) · [机器结果](results/{slug}/result.json)", "",
             method_note(), "", "## 能力方向", "",
             "每份任务只取首次独立答卷，数学卷按原合同归一化；审阅同母题先聚合。重复和自查不重复进入能力分。", "",
             "| 方向 | 任务数 | 能力权重 | 分数 / 100 |", "| --- | ---: | ---: | ---: |"]
    for key, title, _ in view["components"]:
        lines.append(f"| {title} | {m[key]['coverage']['planned']} | {view['weights'][key]:g}% | {score(m[key])} |")
    lines += ["", "综合分 = 75%能力分 + 5%重复作答稳定性 + 10%无反馈自查 + 10%立场干扰下的自查。公开版原四方向各22.5%、审阅10%；合并版六方向权重为22.5/18/18/18/13.5/10。", "",
              "## 真实答卷审阅", "",
              f"主分 **{score(m['answer-review'])}**；重大误判 **{raw_count(counts, 'major')}份**；严格通过 **{raw_count(counts, 'strict')}份（仅辅助）**。四题关联四个既有母题，重大误判次数不能解释为一般失败率。", "",
              "每题100分：核心判断60、依据与影响30、补充完整性10。纯遗漏不自动是重大误判；误判依据实际数学断言与影响，不按分数阈值倒推。", "",
              "| 审阅任务 | 核心 / 60 | 依据影响 / 30 | 补充 / 10 | 总分 / 100 | 重大误判 | 严格通过（辅助） |", "| --- | ---: | ---: | ---: | ---: | --- | --- |"]
    for row in view["ar_records"]:
        dimensions = " | ".join(number(ar_dimension(row, key)) for key, _, _ in DIMENSIONS)
        lines.append(f"| {row['public_id']} | {dimensions} | {private_score(row)} | {status_word(row['major_error'])} | {'是' if row['strict_pass'] is True else '否' if row['strict_pass'] is False else '待判'} |")
    lines += ["", "[审阅评分与重大误判定义](../protocol/answer-review-scoring.md) · [材料与样本说明](answer-review-pilot.md)", "",
              "## 作答稳定性与自查表现", "", "从公开数学任务中固定选取6题，不覆盖审阅或私有探索。", "",
              "| 指标 | 固定范围 | 分数 / 100 |", "| --- | --- | ---: |"]
    for key, title, description in RELIABILITY:
        lines.append(f"| {title} | {description} | {score(m[key])} |")
    lines += ["", "自查检查重点数学结论与论据，中性100分不表示全部交付严格通过。真假标签正确与新增论据错误分别记录；起点没有已知错误时，纠错率无分母，记为不适用。这6题不能代表全部任务的一般可靠性。", "",
              "## 整章与辅助诊断", "", "C002/C003分别含34/92项义务，一章仍是一份相关任务，义务不是独立题数。后续答卷不替代首次答卷。Gemini C003原样工程核验为compile_error，0/92不是92项数学全错；21处sorry/admit仅是静态诊断。", "",
              "| 严格通过（辅助） | 已通过 / 计划 |", "| --- | ---: |"]
    for key, title in (("core_A1", "首次答卷"), ("all_selected_slots", "全部材料")):
        row = report["strict_passes"][key]
        lines.append(f"| {title} | {row['passed']}/{row['total']} |")
    private = sorted(report.get("private_records", []), key=lambda row: row["public_id"])
    if private:
        lines += ["", "## 私有探索的中性摘要", "", "| 中性题号 | 完成分 / 100 | 状态 |", "| --- | ---: | --- |"]
        for row in private:
            lines.append(f"| {row['public_id']} | {private_score(row)} | AI已评阅 / 待人审 |")
        lines += ["", "仅3份首次答卷，不公开题材标题、内部题号、题面、原答或详细评审；完整材料留在私有存储。"]
    lines += ["", "## 证据与解释范围", "",
              "Terra复用历史数学答卷并接入探索，Gemini保留对应真实执行；AR为已有审阅答卷的后验重评。两边允许本地工具、禁止外部搜索，预算与执行批次分别保留，不能视作一次同步完全等条件竞赛。新增的每模型4份AR均由root按新规直接复评。Gemini旧83份评分记录对应85次原生提交，加入4份AR后为87份记录、89次提交；旧82份Terra主评只描述旧83份材料，其余终审与AR复评分别记录。中断与续接原始证据保留。", "",
              "AI审核、编译、公理审计、语义对应、来源审核、后端身份与人工批准分别记录。题目及答卷均待人审，不具正式模型比较资格。原43份数学卷作者Lean证据不覆盖新增审阅；公开参考与Git历史不构成隐藏留出集。", "",
              f"本报告读取的公开结果SHA-256：`{digest}`。展示器不调用模型、Lean或评分器。", ""]
    return "\n".join(lines)


def render_html(report, digest):
    view = result_view(report)
    m, c, counts = view["metrics"], view["coverage"], ar_counts(report)
    components = []
    for key, title, description in view["components"]:
        exact = value(m[key])
        components.append(f'<article class="component"><div><h3>{title}</h3><p>{description} · {m[key]["coverage"]["planned"]}份任务 · 能力权重{view["weights"][key]:g}%</p></div><strong>{score(m[key])}</strong><div class="track"><i style="width:{exact or 0}%"></i></div></article>')
    ar_rows = []
    for row in view["ar_records"]:
        dim = "".join(f'<td>{number(ar_dimension(row, key))}</td>' for key, _, _ in DIMENSIONS)
        ar_rows.append(f'<tr><th>{row["public_id"]}</th>{dim}<td>{private_score(row)}</td><td>{status_word(row["major_error"])}</td><td>{"是" if row["strict_pass"] is True else "否" if row["strict_pass"] is False else "待判"}</td></tr>')
    reliability = "".join(f'<article><h3>{title}</h3><strong>{score(m[key])}</strong><p>{description}</p></article>' for key, title, description in RELIABILITY)
    strict_rows = "".join(f'<tr><th>{title}</th><td>{report["strict_passes"][key]["passed"]}/{report["strict_passes"][key]["total"]}</td></tr>' for key, title in (("core_A1", "首次答卷严格通过"), ("all_selected_slots", "全部材料严格通过")))
    private_rows = "".join(f'<tr><th>{row["public_id"]}</th><td>{private_score(row)}</td><td>AI已评阅 / 待人审</td></tr>' for row in sorted(report.get("private_records", []), key=lambda row: row["public_id"]))
    private_section = f'<section><h2>私有探索的中性摘要</h2><div class="tablewrap"><table><thead><tr><th>中性题号</th><th>完成分 / 100</th><th>状态</th></tr></thead><tbody>{private_rows}</tbody></table></div><p class="note">只代表3份首次答卷，不公开题材标题、内部题号、题面、原答或详细审核。</p></section>' if private_rows else ""
    return f'''<!doctype html><html lang="zh-CN"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>{escape(model_name(report))} · 0.4.0综合重算 | Math Gauge</title><style>
*{{box-sizing:border-box}}body{{margin:0;background:#fbfcfd;color:#243541;font-family:-apple-system,BlinkMacSystemFont,"PingFang SC",sans-serif;line-height:1.7}}.shell{{max-width:1100px;margin:auto;padding:0 28px}}a{{color:#315e78;text-underline-offset:4px}}nav{{display:flex;align-items:center;gap:24px;min-height:76px;font-size:13px;border-bottom:1px solid #dce3e8}}nav a:first-child{{margin-right:auto;font-weight:700;text-decoration:none}}.hero{{padding:42px 0 30px}}h1{{font-size:40px;line-height:1.25;margin:10px 0 22px}}.eyebrow{{font-size:12px;letter-spacing:.12em;color:#61727e}}.stats{{display:grid;grid-template-columns:repeat(3,1fr);gap:20px}}.stats article,.reliability article{{padding:22px;border:1px solid #dce3e8;background:white;border-radius:8px}}strong{{font-variant-numeric:tabular-nums}}.stats strong{{display:block;font-size:42px;line-height:1.3}}.stats p,.note{{font-size:14px;color:#61727e}}.stats p{{margin:6px 0}}section{{padding:32px 0;border-bottom:1px solid #dce3e8}}h2{{font-size:25px;margin:0 0 14px}}h3{{font-size:17px;margin:0}}.component{{display:grid;grid-template-columns:1fr 80px;gap:8px 20px;padding:18px 0;border-top:1px solid #dce3e8}}.component p{{font-size:12px;color:#61727e;margin:4px 0}}.component strong{{font-size:26px;text-align:right;align-self:center}}.track{{grid-column:1/-1;height:10px;background:#e7ecf0;border-radius:3px;overflow:hidden}}.track i{{display:block;height:100%;background:#315e78}}.reliability{{display:grid;grid-template-columns:repeat(3,1fr);gap:16px}}.reliability strong{{display:block;font-size:32px;margin:12px 0}}.reliability p{{font-size:12px;color:#61727e;margin:0}}.tablewrap{{overflow-x:auto}}table{{border-collapse:collapse;width:100%;font-size:13px;font-variant-numeric:tabular-nums}}th,td{{padding:11px;border-bottom:1px solid #dce3e8;text-align:right;white-space:nowrap}}th:first-child{{text-align:left}}thead th{{font-weight:500;color:#61727e}}.arlead{{font-size:21px;line-height:1.6}}code{{font-size:11px;overflow-wrap:anywhere}}footer{{padding:25px 0 35px;font-size:12px;color:#61727e}}@media(max-width:650px){{.shell{{padding:0 20px}}nav{{gap:14px;font-size:12px;flex-wrap:wrap}}h1{{font-size:31px}}.stats{{grid-template-columns:1fr 1fr;gap:10px}}.stats article{{padding:16px}}.stats strong{{font-size:34px}}.stats article:last-child{{grid-column:1/-1}}.reliability{{grid-template-columns:1fr}}.arlead{{font-size:18px}}}}@media print{{nav{{display:none}}section{{break-inside:avoid}}}}
</style></head><body><main class="shell"><nav><a href="../../../README.md">MATH GAUGE</a><a href="../comparison-2026-11-03/index.html">对比图</a><a href="#answer-review">答卷审阅</a><a href="result.json">JSON</a></nav><div class="hero"><div class="eyebrow">V0.4.0 · POST-OBSERVATION RESCORING</div><h1>{escape(model_name(report))}<br>当前综合重算</h1><div class="stats"><article><strong>{score(m['overall'])}</strong><p>综合分 / 100</p></article><article><strong>{score(m['core'])}</strong><p>能力分 / 100</p></article><article><strong>{c['a1_planned']} / {view['families']}</strong><p>任务 / 母题家族 · {c['slots_reviewed']}/{c['slots_planned']}份记录已评阅</p></article></div><p class="note">AI审核 · 人审待办。{method_note()}</p></div><section><h2>{'六' if len(view['components']) == 6 else '五'}个能力方向</h2><p class="note">每份任务只取首次独立答卷。数学卷按原合同归一化，审阅同母题先聚合；额外重复与自查不重复进入能力。</p>{''.join(components)}</section><section id="answer-review"><h2>真实答卷审阅</h2><p class="arlead">审阅主分 <b>{score(m['answer-review'])}</b> / 100 · 重大误判 <b>{raw_count(counts,'major')}</b>份<br><span class="note">严格通过 {raw_count(counts,'strict')}份，仅作辅助诊断。</span></p><p class="note">核心判断60、依据与影响30、补充完整性10。4题关联4个母题；重大误判按实际断言与影响裁决，不由分数阈值倒推，也不能将小样本计数解释为一般失败率。</p><div class="tablewrap"><table><thead><tr><th>任务</th><th>核心 / 60</th><th>依据 / 30</th><th>补充 / 10</th><th>总分 / 100</th><th>重大误判</th><th>严格通过<br>辅助</th></tr></thead><tbody>{''.join(ar_rows)}</tbody></table></div><p class="note"><a href="../../../protocol/answer-review-scoring.md">审阅评分合同</a> · <a href="../../answer-review-pilot.md">材料与样本说明</a></p></section><section><h2>作答稳定性与自查表现</h2><p class="note">从公开数学任务中固定选取6题，审阅与探索不在分母内。</p><div class="reliability">{reliability}</div><p class="note">自查看重点数学结论与论据；中性100分不代表全部交付严格通过。真假标签、核查论据和完整交付分别记录；没有错误起点时纠错率不适用。这6题不能代表全部任务的可靠性。</p></section><section><h2>整章与辅助诊断</h2><p class="note">C002/C003有34/92项义务，一章仍是一份任务。后续答卷不替代首次。Gemini C003原样工程为compile_error，0/92不是92项数学全错；21处sorry/admit只是静态诊断。</p><table><tbody>{strict_rows}</tbody></table><p class="note">严格通过要求全部实际义务满足，只作辅助，不额外加权。<a href="../comparison-2026-11-03/index.html#chapters">查看两章完成图</a></p></section>{private_section}<section><h2>方法与证据</h2><p class="note">综合分 = 75%能力分 + 5%重复作答稳定性 + 10%无反馈自查 + 10%立场干扰下的自查。不同执行批次与预算分别保留；当前是既有原答的重评与合并分析，不能视作一次同步完全等条件竞赛。</p><p class="note">AI审核、编译、公理审计、语义对应、来源审核、后端身份与人工批准分别记录。题目和答卷均待人审，不具正式比较资格。原43份数学卷作者Lean证据不覆盖新增审阅；公开参考与Git历史不是隐藏留出集。</p><details><summary>结果身份与入口</summary><p><code>{digest}</code></p><p><a href="result.json">公开机器结果</a> · <a href="../../{report['id'].replace('terra-','terra-combined-').replace('gemini-','gemini-combined-')}.md">文字报告</a> · <a href="../../../protocol/composite-development-report.md">组合合同</a></p><p class="note">本页自包含，可离线打开；展示器不读取原答、不调用模型、Lean或评分器。</p></details></section><footer>Math Gauge · 当前统一展示0.4.0；历史原始证据保留。</footer></main></body></html>'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--html", type=Path, required=True)
    parser.add_argument("--markdown", type=Path, required=True)
    args = parser.parse_args()
    raw = args.input.read_bytes()
    report = json.loads(raw)
    digest = hashlib.sha256(raw).hexdigest()
    for path, content in ((args.html, render_html(report, digest)), (args.markdown, render_markdown(report, digest))):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")
    print(f"Rendered current public result: {args.html}; source {digest}")


if __name__ == "__main__":
    main()
