"""Homepage presentation of the independent operational observation."""
import html
import json
from datetime import datetime
from pathlib import Path
from zoneinfo import ZoneInfo

from math_gauge.execution_anomalies import validate_public
from scripts.results_attempt_history import validate_public as validate_attempt_history


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


def _languages(chinese, english, *, tag='p', css=''):
    return ''.join('<'+tag+(' class="'+css+'"' if css else '')
                   +' data-lang-content="'+language+'"'+(' hidden' if language == 'en' else '')
                   +'>'+text+'</'+tag+'>'
                   for language, text in (('zh', chinese), ('en', english)))


def render_attempt_summary(document, model_id=None, *, detail=False, labels=None):
    """Present source-bound attempt counts independently of anomaly judgments."""
    if document is None:
        return ''
    validate_attempt_history(document)
    models = document['models']
    selected = ([models[model_id]] if model_id in models else []) if model_id else list(models.values())
    blocks = []
    for model in selected:
        total = model['totals']
        metrics = ((total['lifecycle_records'], '尝试记录', 'Attempt records'),
                   (total['additional_lifecycles'], '额外尝试', 'Additional attempts'),
                   (total['additional_effective_attempts'], '有效重试', 'Effective retries'),
                   (total['system_exclusions'], '系统排除', 'System exclusions'))
        strip = ''.join('<div class="attempt-stat"><strong>'+str(value)+'</strong>'
                        +_languages(zh, en, tag='span')+'</div>' for value, zh, en in metrics)
        rows = []
        for key, zh, en in (('historical', '早期失败批次', 'Earlier failed batch'),
                            ('resumed', '续跑与自查', 'Resumed run and self-checks')):
            counts = model['segments'][key]
            rows.append('<tr><th scope="row">'+_languages(zh, en, tag='span')+'</th>'
                        +''.join('<td class="numeric">'+str(counts[field])+'</td>' for field in
                                 ('lifecycle_records', 'effective_attempts', 'system_exclusions', 'normal_finals'))
                        +'</tr>')
        rows.append('<tr><th scope="row">'+_languages('全部', 'Total', tag='span')+'</th>'
                    +''.join('<td class="numeric">'+str(total[field])+'</td>' for field in
                             ('lifecycle_records', 'effective_attempts', 'system_exclusions', 'normal_finals'))
                    +'</tr>')
        headings = (('范围', 'Scope'), ('尝试记录', 'Attempt records'), ('有效尝试', 'Effective attempts'),
                    ('系统排除', 'System exclusions'), ('正常交卷', 'Normal finals'))
        table = ('<div class="table-wrap"><table class="compact attempt-table"><thead><tr>'
                 +''.join('<th>'+_languages(zh, en, tag='span')+'</th>' for zh, en in headings)
                 +'</tr></thead><tbody>'+''.join(rows)+'</tbody></table></div>')
        phases = model['phases']
        description = _languages(
            '初答'+str(phases['A1']['lifecycle_records'])+'次；三轮自查'
            +str(phases['selfcheck']['lifecycle_records'])+'次。固定'
            +str(total['planned_slots'])+'个交付槽，额外尝试包含系统排除。',
            str(phases['A1']['lifecycle_records'])+' initial-answer attempts and '
            +str(phases['selfcheck']['lifecycle_records'])+' self-check attempts across '
            +str(total['planned_slots'])+' prescribed deliveries. Additional attempts include system exclusions.')
        disclosure = ('<details class="attempt-breakdown"><summary>'
                      +_languages('展开分批与交付统计', 'Batch and delivery breakdown', tag='span')
                      +'</summary>'+table+description+'</details>')
        note = _languages('尝试记录包含联网前中断，不等于API请求次数。异常归因与数学分数另行保留。',
                          'Attempt records include pre-request interruptions; they are not API-call counts. '
                          'Anomaly attribution and mathematical scores are recorded separately.', css='attempt-note')
        name = html.escape((labels or {}).get(model['model_id'], model['model_id']))
        blocks.append('<div class="attempt-summary" data-attempt-model="'
                      +html.escape(model.get('model_id', model_id or ''), quote=True)+'"><h3>'+name+' · '
                      +_languages('完整尝试与重试', 'Complete attempts and retries', tag='span')
                      +'</h3><div class="attempt-stats">'+strip+'</div>'+disclosure+note+'</div>')
    if not blocks:
        return ''
    download = ('../../../results/execution-attempts/v0.1.0/current.json' if detail
                else 'downloads/execution-attempts.json')
    docs = '../../../' if detail else '../'
    return (''.join(blocks)+'<p class="panel-foot"><a href="'+download+'" download>'
            +_languages('下载完整尝试摘要', 'Download complete attempt summary', tag='span')+'</a> · '
            '<a href="'+docs+'docs/execution-attempts.md">'
            +_languages('尝试与重试口径', 'Attempt and retry definitions', tag='span')+'</a></p>')


def render_model_details(document, model_id, *, root=None, attempt_reference=None, model_label=None):
    """Keep run-history quantities on the model page, separate from scores."""
    attempts = render_attempt_summary(attempt_reference, model_id, detail=True,
                                      labels={model_id: model_label or model_id})
    if document is None and not attempts:
        return ""
    if document is not None:
        validate_public(document)
    rows = []
    for row in document["rows"] if document else ():
        if row["model_id"] != model_id:
            continue
        reviewed = str(row["reviewed_runs"]) if row["reviewed_runs"] else "—"
        rows.append('<tr><th scope="row">' + _harness(row) + '</th><td class="numeric">' + reviewed
                    + '</td><td class="numeric">' + _count(row["anomalous_runs"], show_known=bool(row["reviewed_runs"]))
                    + '</td><td>' + _coverage(row) + '</td></tr>')
    if not rows and not attempts:
        return ""
    notes = _model_notes(document, model_id, root or Path(__file__).resolve().parents[1]) if document else ''
    cutoff = (datetime.fromisoformat(document['cutoff_utc'].replace('Z', '+00:00'))
              .astimezone(ZoneInfo('Asia/Singapore')).strftime('%Y-%m-%d %H:%M') if document else '')
    snapshot = ('<details class="historical-anomalies"><summary>'
                +_languages('历史异常样本 · 截至 '+cutoff+' SGT',
                            'Historical anomaly sample · as of '+cutoff+' SGT', tag='span')+'</summary>'
                '<div class="table-wrap"><table class="compact"><thead><tr><th>Harness</th>'
                '<th class="numeric">已核对运行</th><th class="numeric">异常运行</th><th>记录覆盖</th>'
                '</tr></thead><tbody>'+''.join(rows)+'</tbody></table></div>'
                +_languages('本表保留旧时间截点的异常样本，不代表上方完整尝试总数。',
                            'This sample retains the earlier cutoff; it does not represent the complete attempt count above.',
                            css='panel-foot')+'</details>' if rows and attempts else '')
    if not snapshot and rows:
        snapshot = ('<div class="table-wrap"><table class="compact"><thead><tr><th>Harness</th>'
                    '<th class="numeric">已核对运行</th><th class="numeric">异常运行</th><th>记录覆盖</th>'
                    '</tr></thead><tbody>'+''.join(rows)+'</tbody></table></div>')
    return (
        '<section class="panel" id="execution-anomalies"><div class="panel-head"><h2>'
        +('运行与重试记录' if attempts else '运行记录')+'</h2></div>'+attempts+snapshot+
        '<p class="panel-foot">已核对运行包含正式题目作答及重试；异常次数仅计模型、服务端或原生Harness自身的问题。</p>'
        '<p class="panel-foot">测试脚本、采集器、本地适配器和环境配置导致的中断不计入；记录不全或归因待确认时，仅列已核实次数。</p>'
        + notes +
        '<p class="panel-foot"><a data-context-link href="../../index.html#execution-anomalies">返回运行异常统计 →</a></p>'
        '</section>'
    )


def render_panel(document, *, models=(), attempt_reference=None):
    model_labels = {model['id']: model['label'] for model in models}
    attempts = render_attempt_summary(attempt_reference, labels=model_labels)
    if document is None and not attempts:
        return ""
    if document is None:
        return '<details class="panel execution-anomalies" id="execution-anomalies"><summary>运行与重试记录</summary>'+attempts+'</details>'
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
    overview = []
    for model_id, model in (attempt_reference or {}).get('models', {}).items():
        total = model['totals']
        name = html.escape(model_labels.get(model_id, model_id))
        overview.append(_languages(name+' · '+str(total['lifecycle_records'])+'次尝试 · '
                                   +str(total['additional_effective_attempts'])+'次有效重试',
                                   name+' · '+str(total['lifecycle_records'])+' attempts · '
                                   +str(total['additional_effective_attempts'])+' effective retries', tag='span'))
    return (
        '<details class="panel execution-anomalies" id="execution-anomalies" aria-labelledby="execution-anomalies-title">'
        '<summary class="panel-head"><strong id="execution-anomalies-title">运行与重试记录</strong>'
        '<span class="anomaly-cutoff">'+(''.join(overview) if attempts else '历史异常样本')
        +'</span></summary>'+attempts+
        '<div class="panel-head"><div><h3>历史异常样本</h3>'
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
        '<a href="downloads/execution-anomalies.json" download>下载异常统计</a></div></div></details>'
    )
