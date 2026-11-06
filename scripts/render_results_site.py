#!/usr/bin/env python3
"""Render the current, source-bound user-selected result records only."""
import argparse
import base64
import copy
import hashlib
import html
import json
import re
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from math_gauge.records import load_assessment_results, validate_record

MODEL_THEMES = {
    "terra-6.1-max": {"color": "#252525", "ink": "#252525", "tint": "#f1f2f3"},
    "deepseek-v4.1-flash-1017": {"color": "#4b6ed8", "ink": "#3655b2", "tint": "#f1f4fd"},
    "gemini-3.8-flash-high": {"color": "#68b77a", "ink": "#397a4a", "tint": "#f0f8f2"},
}
MODEL_PROVIDERS = {
    "terra-6.1-max": ("OpenAI", "openai.svg"),
    "deepseek-v4.1-flash-1017": ("DeepSeek", "deepseek.svg"),
    "gemini-3.8-flash-high": ("Google", "google.svg"),
}


def build_data(source_root=ROOT):
    root = Path(source_root).resolve()
    policy = json.loads((root / "protocol/scoring-policy.json").read_bytes())
    strict_policy = json.loads((root / "protocol/strict-scoring-policy.json").read_bytes())
    models, sources = [], []
    for model, label in (("terra-6.1-max", "Terra 6.1 Max"),
                         ("deepseek-v4.1-flash-1017", "DeepSeek v4.1 Flash 1017"),
                         ("gemini-3.8-flash-high", "Gemini 3.8 Flash High")):
        folder = root / "results/v0.6.0" / model / "20261105"
        validate_record(folder)
        record = json.loads((folder / "record.json").read_bytes())
        partial = load_assessment_results(folder, record)
        strict = load_assessment_results(folder, record, mode="strict")
        if partial is None or strict is None:
            raise ValueError("Current display requires both classified assessment modes")
        combined = partial["single_attempt"]
        provider, filename = MODEL_PROVIDERS[model]
        icon_path = root / "site/assets/logos" / filename
        icon_bytes = icon_path.read_bytes()
        models.append({"id": model, "label": label, "theme": dict(MODEL_THEMES[model]),
            "logo": {"label": provider, "data_url": "data:image/svg+xml;base64," + base64.b64encode(icon_bytes).decode("ascii"),
                     "sha256": hashlib.sha256(icon_bytes).hexdigest()},
            "combined": combined, "strict": strict, "trajectory": record["trajectory"],
            "lean_formalization_breakdown": combined["lean_formalization_breakdown"],
            "alignment_selfcheck": combined["alignment_selfcheck"],
            "source_record": str((folder / "record.json").relative_to(root)),
            "retry": {"combined": partial["nonlogical_retry_3"],
                      "note": ("GR021共3次、采用第3次；GR023共2次、采用第2次。原失败保留，重跑接纳依据为操作者声明，运行细节未独立认证。"
                               if record.get("retry_admission") else "无新增重跑，沿用原答；不据此认证全部历史底层调用均一次完成。")}})
        names = ["record.json", record["assessment_policy"]["path"], record["strict_scoring_policy"]["path"],
                 *(item["path"] for item in record["assessment_results"].values()),
                 *(item["path"] for item in record["strict_results"].values())]
        if record.get("retry_admission"):
            names += ["retry-admission.json", "retry-attempts.json", "nonlogical-retry-policy.json"]
        for name in names:
            path = folder / name
            sources.append({"path": str(path.relative_to(root)), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()})
        sources.append({"path": str(icon_path.relative_to(root)), "sha256": hashlib.sha256(icon_bytes).hexdigest()})
    return {"schema": "math-gauge.current-results-display/v4", "benchmark_version": "0.6.0",
            "scoring_method_version": "0.5.0", "strict_method_version": "0.2.0",
            "human_review": "pending", "formal_comparison_eligible": False,
            "models": models, "policy": policy, "strict_policy": strict_policy, "sources": sources,
            "capacity": {"total": 100, "active": 70, "under_construction": 30},
            "publication_scope": "combined", "score_modes": ["partial", "strict"],
            "attempt_conditions": ["single_attempt", "nonlogical_retry_3"]}


def overlaid_bars(models, score_mode="partial"):
    """Top the first-attempt bar with the actual retry gain; never select best-of."""
    groups, labels = [], []
    for model in models:
        name = html.escape(model["label"])
        bars, values, descriptions_for_model = [], [], []
        has_retry = model["retry"]["combined"].get("retry_summary", {}).get("slots_with_reruns", 0) > 0
        for series, result in (("single_attempt", model["combined"]),
                               ("nonlogical_retry_3", model["retry"]["combined"])):
            if score_mode == "strict":
                result = model["strict"][series]
            value = result["metrics"]["earned"]["exact"]
            text = "未决" if value is None else f"{value:.2f}"
            height = 0 if value is None else max(0, min(100, value))
            raw_value = "" if value is None else str(value)
            values.append(value)
            descriptions_for_model.append(text)
            if series == "single_attempt":
                bars.append(f'<div class="score-bar first-solid" aria-hidden="true" data-score-mode="{score_mode}" data-model="{html.escape(model["id"], quote=True)}" '
                            f'data-series="{series}" data-score="{raw_value}" style="height:{height:.8f}%" '
                            f'></div>')
        has_gain = has_retry and all(v is not None for v in values) and values[1] > values[0]
        if has_retry and all(v is not None for v in values) and values[0] != values[1]:
            first, retry = (max(0, min(100, value)) for value in values)
            if has_gain:
                kind, bottom, height = "retry-extension", first, retry - first
            else:
                # A zero-height endpoint preserves an equal/lower source total without inventing a gain.
                kind, bottom, height = "retry-end", retry, 0
            bars.append(f'<div class="score-bar {kind}" aria-hidden="true" data-score-mode="{score_mode}" data-model="{html.escape(model["id"], quote=True)}" '
                        f'data-series="nonlogical_retry_3" data-score="{values[1]}" '
                        f'data-start-score="{values[0]}" data-gain-score="{values[1] - values[0]}" '
                        f'style="bottom:{bottom:.8f}%;height:{height:.8f}%"></div>')
        theme = model["theme"]
        color, ink = html.escape(theme["color"], quote=True), html.escape(theme["ink"], quote=True)
        position = max([max(0, min(100, v)) for v in values if v is not None], default=0)
        headline = max((v for v in values if v is not None), default=None)
        text = "未决" if headline is None else f"{headline:.2f}"
        value_label = f'<span class="chart-value" aria-hidden="true" data-score-mode="{score_mode}" style="bottom:calc({position:.8f}% + 9px)">{text}</span>'
        changed = has_retry and all(v is not None for v in values) and values[0] != values[1]
        tooltip, focus = "", ""
        if changed:
            tooltip_id = "score-detail-" + score_mode + "-" + html.escape(model["id"], quote=True)
            focus = f' tabindex="0" aria-describedby="{tooltip_id}"'
            tooltip = (f'<div class="score-tooltip" role="tooltip" data-score-mode="{score_mode}" id="{tooltip_id}" '
                       f'style="bottom:calc({position:.8f}% + 30px)"><strong>{name}</strong>'
                       f'<dl><div><dt>首次</dt><dd>{descriptions_for_model[0]}</dd></div>'
                       f'<div><dt>重跑后</dt><dd>{descriptions_for_model[1]}</dd></div>'
                       f'<div><dt>增量</dt><dd>{values[1] - values[0]:+.2f}</dd></div></dl></div>')
        spoken = html.escape(model["label"] + "。首次" + descriptions_for_model[0]
                             + "，允许重跑后" + descriptions_for_model[1], quote=True)
        groups.append(f'<div class="bar-group{" has-extension" if has_gain else ""}" role="group" data-score-mode="{score_mode}" aria-label="{spoken}" '
                      f'data-model="{html.escape(model["id"], quote=True)}"{focus} '
                      f'style="--model-color:{color};--model-ink:{ink}">' + "".join(bars) + value_label + tooltip + '</div>')
        logo = model["logo"]
        labels.append(f'<div class="chart-model" style="--model-color:{color};--model-ink:{ink}">'
                      f'<img class="provider-logo" data-score-mode="{score_mode}" src="{html.escape(logo["data_url"], quote=True)}" '
                      f'alt="{html.escape(logo["label"], quote=True)}" width="24" height="24">{name}</div>')
    ticks = "".join(f'<span style="bottom:{value}%">{value}</span>' for value in range(0, 101, 20))
    grid = "".join(f'<i class="chart-gridline" aria-hidden="true" style="bottom:{value}%"></i>' for value in range(0, 101, 20))
    chart_name = "Strict 已获分" if score_mode == "strict" else "分项已获分"
    return (f'<div class="chart-frame" role="group" aria-label="公开＋私有{chart_name}，纵轴0至100">'
            f'<div class="chart-axis" aria-hidden="true">{ticks}</div><div class="chart-plot">'
            f'{grid}<i class="chart-capacity" style="bottom:70%"><span>当前可测上限 70</span></i><div class="chart-groups">' + "".join(groups) + '</div></div></div>'
            '<div class="chart-labels" aria-hidden="true">' + "".join(labels) + '</div>')


def render(data):
    # Only escaped data enters the standalone template; scores come from archives.
    payload = json.dumps(data, ensure_ascii=False).replace("<", "\\u003c").replace("&", "\\u0026")
    rows = []
    for index, model in enumerate(data["models"], 1):
        label = html.escape(model["label"])
        source = html.escape("../" + model["source_record"].replace("record.json", "README.md"), quote=True)
        single = model["combined"]["metrics"]["earned"]["exact"]
        retry = model["retry"]["combined"]["metrics"]["earned"]["exact"]
        display = lambda value: "—" if value is None else f"{value:.2f}"
        rows.append(f'<tr><td class="rank">{index}</td><td class="model-name">{label}</td>'
                    f'<td class="numeric score-cell single-score"><span class="score-number">{display(single)}</span></td>'
                    f'<td class="numeric score-cell retry-score"><span class="score-number">{display(retry)}</span></td>'
                    f'<td class="numeric">—</td><td class="numeric"><a href="{source}">查看 ↗</a></td></tr>')
    values = {"DATA": payload, "ROWS": "".join(rows), "CHART": overlaid_bars(data["models"]),
              "STRICT_CHART": overlaid_bars(data["models"], "strict")}
    template = (Path(__file__).parent / "templates/current-results.html").read_text(encoding="utf-8")
    return re.sub(r"@@MG_(DATA|ROWS|CHART|STRICT_CHART)@@", lambda match: values[match[1]], template)


def write_site(destination, *, source_root=ROOT):
    dest = Path(destination)
    data = build_data(source_root)
    dest.mkdir(parents=True, exist_ok=True)
    (dest / "index.html").write_text(render(data), encoding="utf-8")
    (dest / "data.json").write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n")
    (dest / "downloads").mkdir(exist_ok=True)
    for model in data["models"]:
        for scope in ["combined"]:
            (dest / "downloads" / (model["id"] + "-" + scope + ".json")).write_text(
                json.dumps(model[scope], ensure_ascii=False, indent=2) + "\n")
            (dest / "downloads" / (model["id"] + "-" + scope + "-retry.json")).write_text(
                json.dumps(model["retry"][scope], ensure_ascii=False, indent=2) + "\n")
            for condition, suffix in (("single_attempt", ""), ("nonlogical_retry_3", "-retry")):
                (dest / "downloads" / (model["id"] + "-combined-strict" + suffix + ".json")).write_text(
                    json.dumps(model["strict"][condition], ensure_ascii=False, indent=2) + "\n")
        # Retire only this renderer's known public-only exports; preserve unrelated files.
        for suffix in ("-public.json", "-public-retry.json"):
            path = dest / "downloads" / (model["id"] + suffix)
            if path.is_file():
                path.unlink()
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
