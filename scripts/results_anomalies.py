"""Homepage presentation of the independent operational observation."""
import html
import json
from datetime import datetime
from pathlib import Path
from zoneinfo import ZoneInfo

from math_gauge.execution_anomalies import validate_public


HEADINGS = {
    "timeout": "超时", "service_stream_connection": "断流／服务错误", "http_429": "429",
    "output_or_context_limit": "输出／上下文耗尽", "harness_environment": "运行器／环境", "other": "其他",
    "server_errors": "服务端错误", "context": "上下文", "runner": "运行器",
}
COVERAGE = {"complete": "完整留档批次", "partial": "部分记录", "unknown": "缺少运行记录",
            "qualitative_only": "仅有定性记录"}


def _harness(row):
    label = row["harness_label"]
    if label.startswith("Historical external executor"):
        label = "历史执行器（未核实）"
    return html.escape(label)


def _count(metric, *, total=False, show_known=False):
    value, exact = metric["known"], metric["exact"]
    text = str(exact) if exact is not None else str(value) if value or show_known else "—"
    state = "positive" if value else "zero" if exact is not None or show_known else "unknown"
    css = "anomaly-count " + state + (" anomaly-total" if total else "")
    return '<span class="' + css + '">' + text + '</span>'


def _coverage(row):
    if row["history_complete"] and row["anomalous_runs"]["exact"] is None:
        return "异常归因待核实"
    return COVERAGE[row["coverage"]]


def _model_notes(document, model_id, root):
    path = Path(root) / 'results/execution-anomalies' / ('v' + document['version']) / 'model-notes.json'
    if not path.is_file():
        return ''
    notes = json.loads(path.read_bytes())
    if (notes.get('schema') != 'math-gauge.operational-model-notes/v1'
            or notes.get('source_review_sha256') != document['source_review_sha256']):
        return ''
    note = notes.get('models', {}).get(model_id)
    if not note:
        return ''
    if (type(note['unresolved_runs']) is not int or note['unresolved_runs'] <= 0
            or any(type(event['runs']) is not int or event['runs'] <= 0 for event in note['events'])
            or sum(event['runs'] for event in note['events']) != note['unresolved_runs']):
        raise ValueError('Operational model-note event totals do not match its unresolved runs')
    blocks = []
    for language in ('zh', 'en'):
        events = ''.join('<li>' + html.escape(event[language]) + '</li>' for event in note['events'])
        blocks.append('<div class="prose" data-lang-content="' + language + '"'
                      + (' hidden' if language == 'en' else '') + '><h3>'
                      + html.escape(note['title'][language]) + '</h3><ul>' + events
                      + '</ul><p>' + html.escape(note['explanation'][language]) + '</p></div>')
    return ''.join(blocks)


def render_model_details(document, model_id, *, root=None):
    """Keep run-history quantities on the model page, separate from scores."""
    if document is None:
        return ""
    validate_public(document)
    rows = []
    for row in document["rows"]:
        if row["model_id"] != model_id:
            continue
        reviewed = str(row["reviewed_runs"]) if row["reviewed_runs"] else "—"
        rows.append('<tr><th scope="row">' + _harness(row) + '</th><td class="numeric">' + reviewed
                    + '</td><td class="numeric">' + _count(row["anomalous_runs"], show_known=bool(row["reviewed_runs"]))
                    + '</td><td>' + _coverage(row) + '</td></tr>')
    if not rows:
        return ""
    notes = _model_notes(document, model_id, root or Path(__file__).resolve().parents[1])
    return (
        '<section class="panel" id="execution-anomalies"><div class="panel-head"><h2>运行记录</h2></div>'
        '<div class="table-wrap"><table class="compact"><thead><tr><th>Harness</th>'
        '<th class="numeric">已核对运行</th><th class="numeric">异常运行</th><th>记录覆盖</th>'
        '</tr></thead><tbody>' + ''.join(rows) + '</tbody></table></div>'
        '<p class="panel-foot">已核对运行包含正式题目作答及重试；异常次数仅计模型、服务端或原生Harness自身的问题。</p>'
        '<p class="panel-foot">测试脚本、采集器、本地适配器和环境配置导致的中断不计入；记录不全或归因待确认时，仅列已核实次数。</p>'
        + notes +
        '<p class="panel-foot"><a data-context-link href="../../index.html#execution-anomalies">返回运行异常统计 →</a></p>'
        '</section>'
    )


def render_panel(document, *, models=()):
    if document is None:
        return ""
    validate_public(document)
    categories = document["categories"]
    labels = {model["id"]: model for model in models}
    rows = []
    ordered = sorted(document["rows"], key=lambda r: (
        r["anomalous_runs"]["known"] == 0 and r["anomalous_runs"]["exact"] is None and not r["reviewed_runs"],
        -r["anomalous_runs"]["known"], r["model_label"].casefold(), r["harness_label"], r["route"]))
    for row in ordered:
        model = labels.get(row["model_id"])
        label = html.escape(row["model_label"])
        if model is not None:
            label = '<a data-context-link href="models/' + html.escape(row["model_id"], quote=True) + '/index.html">' + label + '</a>'
        else:
            label = '<a data-context-link href="models/' + html.escape(row["model_id"], quote=True) + '/operations.html">' + label + '</a>'
        if row["anomalous_runs"]["exact"] is None:
            label += '<sup aria-describedby="anomaly-history-note">*</sup>'
        harness = _harness(row)
        cells = ''.join('<td class="numeric">' + _count(row["categories"][key]) + '</td>' for key in categories)
        rows.append('<tr><th scope="row" class="anomaly-model">' + label + '</th>'
                    '<td class="anomaly-harness">' + harness + '</td>'
                    '<td class="numeric">' + _count(row["anomalous_runs"], total=True, show_known=bool(row["reviewed_runs"]))
                    + '</td>' + cells + '</tr>')
    timestamp = datetime.fromisoformat(document["cutoff_utc"].replace("Z", "+00:00")).astimezone(ZoneInfo("Asia/Singapore"))
    return (
        '<section class="panel execution-anomalies" id="execution-anomalies" aria-labelledby="execution-anomalies-title">'
        '<div class="panel-head"><div><h2 id="execution-anomalies-title">运行异常记录</h2>'
        '<p class="panel-desc">只统计正式题目作答及重试；同一次运行可涉及多类异常，合计去重。</p></div>'
        '<span class="anomaly-cutoff">截至 ' + timestamp.strftime("%Y-%m-%d %H:%M") + ' SGT</span></div>'
        '<div class="anomalies-scroll" tabindex="0" role="region" aria-label="模型与Harness运行异常统计">'
        '<table class="anomalies-table"><thead><tr><th scope="col">模型</th><th scope="col">Harness</th>'
        '<th scope="col" class="numeric">异常运行</th>'
        + ''.join('<th scope="col" class="numeric">' + HEADINGS[key] + '</th>' for key in categories)
        + '</tr></thead><tbody>' + ''.join(rows) + '</tbody></table></div>'
        '<div class="anomaly-notes"><p>订阅额度耗尽、主动取消及正常续接本身不计异常；恢复后成功交卷的真实断流或429仍计入。</p>'
        '<p>测试脚本和环境配置导致的中断已排除；原生Harness自身的超时、回传与上下文故障照计。</p>'
        '<p id="anomaly-history-note">* 部分历史运行记录未能补全或异常归因未确认；表中仅列已核实次数。</p>'
        '<p>—表示记录不足，不能视作0。不同模型的运行次数、留档范围与环境不同，本表不作可用性排名，也不影响数学分数。</p>'
        '<div class="anomaly-links"><a href="../docs/execution-anomalies.md">统计口径与来源 ↗</a>'
        '<a href="downloads/execution-anomalies.json" download>下载异常统计</a></div></div></section>'
    )
