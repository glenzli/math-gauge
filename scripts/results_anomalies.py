"""Homepage presentation of the independent operational observation."""
import html
import json
from datetime import datetime
from pathlib import Path
from zoneinfo import ZoneInfo

from math_gauge.evidence_retention import read_json
from math_gauge.execution_anomalies import validate_public
from scripts.results_attempt_history import validate_public as validate_attempt_history
from scripts.results_rankings import model_display_key


HEADINGS = {
    "timeout": ("超时", "Timeout"), "service_stream_connection": ("断流／服务错误", "Stream / service errors"),
    "http_429": ("429", "429"), "output_or_context_limit": ("输出／上下文耗尽", "Output / context limit"),
    "harness_environment": ("运行器／环境", "Harness / environment"), "other": ("其他", "Other"),
    "server_errors": ("服务端错误", "Server errors"), "context": ("上下文", "Context"), "runner": ("运行器", "Harness"),
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
        '<p class="panel-foot"><a href="../../../docs/execution-anomalies.md">'
        +_languages('异常记录口径与来源 →', 'Anomaly definitions and sources →', tag='span')+'</a> · '
        '<a href="../../downloads/execution-anomalies.json" download>'
        +_languages('下载异常统计', 'Download anomaly summary', tag='span')+'</a></p>'
        '</section>'
    )


def _initial_attempt_counts(model, complete, root):
    """Take counts only from the applicable retained run scope."""
    if complete:
        counts = complete['totals']
        return tuple(counts[key] for key in ('lifecycle_records', 'effective_attempts',
            'additional_effective_attempts', 'system_exclusions')), ('任务尝试记录', 'Task-attempt records')

    path = model.get('source_record')
    if root is None or not path:
        return (None, None, None, None), ('参见历史异常样本', 'See historical anomaly sample')
    record = read_json(Path(root) / path)
    summary = record.get('execution_summary', {})
    requests = summary.get('physical_model_requests')
    system = summary.get('pure_system_exclusions')
    if type(requests) is int and type(system) is int and summary.get('physical_requests_include_selfcheck'):
        effective = requests - system
        retries = summary.get('native_model_attempt_retries')
        slots = summary.get('planned_initial_tasks', 0) + summary.get('prescribed_selfcheck_rounds', 0)
        delivered = summary.get('delivered_initial_tasks', 0) + summary.get('delivered_selfcheck_rounds', 0)
        if retries is None and slots == delivered and 0 < slots <= effective:
            retries = effective - slots
        return (requests, effective, retries, system), ('外层物理请求', 'Outer physical requests')

    if 'request_history_counts' in summary:
        counts = summary['request_history_counts']
        return (counts['retained_lifecycle_records'], counts.get('effective_attempts_after_source_bound_correction'),
                None, None), ('部分归因未结算', 'Some classifications remain unsettled')

    if 'physical_initial_preparations' in summary:
        return (summary['physical_initial_preparations'], None, None, summary.get('pure_system_initial_exclusions')), (
            '仅首答准备记录', 'Initial-answer preparations only')

    if summary.get('native_first_final_verified_within_deadline') and summary.get('effective_retry_attempts') == 0:
        return (summary.get('total_physical_invocations'), summary['scored_deliveries'], 0, None), (
            '已核对的候选交付', 'Verified candidate deliveries')

    return (None, None, None, None), ('尝试总数缺少统一记录', 'Complete attempt counts unavailable')


def _render_attempt_table(models, attempt_reference, resources, root):
    if attempt_reference is not None:
        validate_attempt_history(attempt_reference)
    complete = (attempt_reference or {}).get('models', {})
    by_id = {model['id']: model for model in models}
    base_phase = ('首答／自查', 'Initial answers / self-checks')
    rows = []

    def row(model_id, phase, phase_label, counts, note):
        cells = ''.join('<td class="numeric">'+('—' if count is None else str(count))+'</td>' for count in counts)
        return ('<tr data-run-phase="'+phase+'" data-run-model="'+html.escape(model_id, quote=True)+'">'
                '<th scope="row">'+html.escape(by_id.get(model_id, {}).get('label', model_id))+'</th><td>'
                +_languages(*phase_label, tag='span')+'</td>'+cells
                +'<td class="attempt-scope">'+_languages(*note, tag='span')+'</td></tr>')

    if root is not None or complete:
        for model in sorted(models, key=model_display_key):
            mid = model['id']
            counts, note = _initial_attempt_counts(model, complete.get(mid), root)
            rows.append(row(mid, 'initial', base_phase, counts, note))
        for mid in sorted(complete.keys() - by_id.keys()):
            counts, note = _initial_attempt_counts({}, complete[mid], root)
            rows.append(row(mid, 'initial', base_phase, counts, note))

    reasons = {'capacity': ('容量不足', 'Service at capacity'),
               'network': ('网络故障', 'Network failure'), 'system': ('系统故障', 'System failure')}
    for resource in sorted(resources, key=lambda item: model_display_key(by_id.get(item['id'], item))):
        revision = resource['revision']
        requests = revision.get('physical_requests')
        if requests is None:
            selected = revision['planned_calls']
            reused = revision['reused_calls']
            counts = (selected, selected, None, None)
            note = (f'已采纳调用，含 {reused} 次复用', f'Adopted calls, {reused} reused')
        else:
            effective = revision['effective_attempts']
            system = revision.get('system_exclusions', 0) if requests == effective else revision.get('system_exclusions')
            counts = (requests, effective, effective - revision['selected_tasks'], system)
            failures = revision.get('system_failure_reasons', {})
            note = ('、'.join(reasons[key][0] for key in failures),
                    ', '.join(reasons[key][1] for key in failures)) if failures else ('外层物理请求', 'Outer physical requests')
        rows.append(row(resource['id'], 'continuation', ('1.2.0 续答', '1.2.0 continuation'), counts, note))

    if not rows:
        return ''
    headings = (('模型', 'Model'), ('阶段', 'Phase'), ('留档次数', 'Recorded'), ('有效尝试', 'Effective attempts'),
                ('有效重试', 'Effective retries'), ('系统排除', 'System exclusions'), ('说明', 'Notes'))
    downloads = []
    if complete:
        downloads.append('<a href="downloads/execution-attempts.json" download>'
                         +_languages('完整尝试摘要', 'Complete attempt summary', tag='span')+'</a>')
    if resources:
        downloads.append('<a href="downloads/continuation-resources.json" download>'
                         +_languages('续答资源', 'Continuation resources', tag='span')+'</a>')
    downloads.append('<a href="../docs/execution-attempts.md">'
                     +_languages('统计口径 ↗', 'Counting method ↗', tag='span')+'</a>')
    return (
        '<section aria-label="Attempt counts" class="run-history-attempts">'
        '<div class="table-wrap" tabindex="0" role="region" aria-label="按模型和阶段统计的尝试">'
        '<table class="compact attempt-table run-history-table"><thead><tr>'
        +''.join('<th scope="col"'+(' class="numeric"' if 2 <= i <= 5 else '')+'>'
                 +_languages(zh, en, tag='span')+'</th>' for i, (zh, en) in enumerate(headings))
        +'</tr></thead><tbody>'+''.join(rows)+'</tbody></table></div>'
        +_languages('留档次数沿用各批原始单位。— 表示来源未确认。确认的系统故障进入重试记录，有效尝试用于成本和耗时统计。',
                    'Recorded counts retain the source units. A dash means the source does not confirm a count. '
                    'Confirmed system failures remain in retry history. Cost and time use effective attempts.',
                    css='attempt-note')
        +'<p class="anomaly-links">'+' · '.join(downloads)+'</p></section>')


def _render_historical_anomalies(document, models, source_edition):
    validate_public(document)
    categories = document["categories"]
    labels = {model["id"]: model for model in models}
    rows = []
    ordered = sorted(document["rows"], key=lambda row: (
        model_display_key(labels.get(row['model_id'], {'id': row['model_id'], 'label': row['model_label']})),
        row['harness_label'], row['route']))
    for row in ordered:
        model = labels.get(row["model_id"])
        label = html.escape(model["label"] if model else row["model_label"])
        route = 'models/' + row['model_id']
        fixed = ''
        if model:
            route += '/index.html'
            if source_edition:
                route += '?edition=' + source_edition
                fixed = ' data-fixed-edition="' + html.escape(source_edition, quote=True) + '"'
        else:
            route += '/operations.html'
        label = '<a'+fixed+' href="'+html.escape(route+'#execution-anomalies', quote=True)+'">'+label+'</a>'
        if row["anomalous_runs"]["exact"] is None:
            label += '<sup aria-describedby="anomaly-history-note">*</sup>'
        harness = _harness(row)
        cells = ''.join('<td class="numeric">' + _count(row["categories"][key]) + '</td>' for key in categories)
        rows.append('<tr><th scope="row" class="anomaly-model">' + label + '</th>'
                    '<td class="anomaly-harness">' + harness + '</td>'
                    '<td class="numeric">' + (str(row["reviewed_runs"]) if row["reviewed_runs"] else '—') + '</td>'
                    '<td class="numeric">' + _count(row["anomalous_runs"], total=True, show_known=bool(row["reviewed_runs"]))
                    + '</td>' + cells + '</tr>')
    timestamp = datetime.fromisoformat(document["cutoff_utc"].replace("Z", "+00:00")).astimezone(ZoneInfo("Asia/Singapore"))
    cutoff = timestamp.strftime("%Y-%m-%d %H:%M") + ' SGT'
    headings = [('模型', 'Model'), ('Harness', 'Harness'), ('已核对运行', 'Reviewed runs'), ('异常运行', 'Anomalous runs')]
    headings.extend(HEADINGS[key] for key in categories)
    return (
        '<details class="historical-anomalies run-history-snapshot"><summary>'
        +_languages('历史异常样本 · 截至 '+cutoff, 'Historical anomaly sample · as of '+cutoff, tag='span')
        +'</summary><div class="table-wrap" tabindex="0" role="region" aria-label="模型与Harness运行异常统计">'
        '<table class="compact attempt-table run-history-table anomalies-table"><thead><tr>'
        + ''.join('<th scope="col"'+(' class="numeric"' if i >= 2 else '')+'>'
                 +_languages(zh, en, tag='span')+'</th>' for i, (zh, en) in enumerate(headings))
        + '</tr></thead><tbody>' + ''.join(rows) + '</tbody></table></div>'
        '<p class="attempt-note" id="anomaly-history-note">'
        +_languages('* 表示记录不全或归因未定，数字为已核实次数。历史异常合计按运行去重，独立于上表的尝试次数。',
                    '* indicates incomplete records or unresolved attribution. Values show verified counts. '
                    'Historical totals count unique runs independently of the attempt counts above.', tag='span')
        +'</p><p class="anomaly-links"><a href="../docs/execution-anomalies.md">'
        +_languages('异常统计口径 ↗', 'Anomaly counting method ↗', tag='span')+'</a> · '
        '<a href="downloads/execution-anomalies.json" download>'
        +_languages('下载异常统计', 'Download anomaly summary', tag='span')+'</a></p></details>'
    )


def render_panel(document, *, models=(), attempt_reference=None, continuation_resources=(),
                 source_root=None, source_edition=None):
    attempts = _render_attempt_table(models, attempt_reference, continuation_resources, source_root)
    history = _render_historical_anomalies(document, models, source_edition) if document is not None else ''
    if not attempts and not history:
        return ''
    return ('<details class="panel subboard execution-anomalies" id="execution-anomalies"><summary><strong>'
            +_languages('运行与重试记录', 'Attempts and retries', tag='span')
            +'</strong></summary><div class="run-history-body">'+attempts+history+'</div></details>')
