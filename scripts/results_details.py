"""Public evidence pages. This module formats retained judgments, never scores them."""
import hashlib
import html
import json
import os
from pathlib import Path
import subprocess

from math_gauge.records import evidence_bytes, load_public_task_scores
from scripts.results_i18n import language_switch

HERE = Path(__file__).resolve().parent
CONDITIONS = ("single_attempt", "nonlogical_retry_3")
CATEGORY_TITLES = {'proofs': '书面论证', 'answer-review': '论证审阅', 'lean-audit': '语义审计',
                   'lean-formalization': '形式化', 'theorem-extension': '命题拓展', 'background-check': '背景核查', 'manuscript-completion': '数学想法手稿化'}


def embedded(value):
    return json.dumps(value, ensure_ascii=False).replace("<", "\\u003c").replace("&", "\\u0026")


def source_link(source, page, label):
    href = os.path.relpath(source, Path("site") / Path(page).parent)
    return f'<a href="{html.escape(href, quote=True)}">{html.escape(label)}</a>'


class EvidenceRenderer:
    """Batch local Markdown/MathML rendering; no browser runtime or network dependency."""
    def __init__(self):
        self.sources = []

    def add(self, text):
        token = f"@@EVIDENCE_{len(self.sources)}@@"
        self.sources.append(str(text))
        return token

    def finish(self, pages):
        result = subprocess.run(["node", str(HERE / "render_evidence.mjs")],
            input=json.dumps(self.sources), text=True, capture_output=True, check=True)
        rendered = json.loads(result.stdout)
        if len(rendered) != len(self.sources):
            raise ValueError("Evidence renderer dropped a source")
        import re
        return {path: re.sub(r"@@EVIDENCE_(\d+)@@", lambda m: rendered[int(m[1])], page)
                for path, page in pages.items()}


def controls(data):
    buttons = "".join('<button data-score-mode="'+m['id']+'" aria-label="'
        +html.escape(m['name']+' '+m['abbreviation'], quote=True)+'" aria-pressed="'
        +str(m['id']==data['default_score_mode']).lower()+'"><span class="mode-name">'
        +html.escape(m['name'])+'</span><span class="mode-code">'+html.escape(m['abbreviation'])+'</span></button>'
        for m in data['display_score_modes'])
    return '<div class="controls detail-controls"><div class="control-group"><span class="control-name">计分口径</span><div class="segmented" role="group" aria-label="计分口径">'+buttons+'</div></div></div>'



def shell(page, title, subtitle, body, data, script, *, back=None):
    prefix = os.path.relpath(".", Path(page).parent)
    def local(path):
        return html.escape(prefix + "/" + path, quote=True)
    crumbs = '<a data-context-link href="'+local('index.html')+'">排行榜</a>'
    if back:
        crumbs += ' <span>／</span> <a data-context-link href="'+local(back[0])+'">'+html.escape(back[1])+'</a>'
    return ('<!doctype html><html lang="zh-CN"><head><meta charset="utf-8">'
        '<meta name="viewport" content="width=device-width,initial-scale=1">'
        '<title>'+html.escape(title)+' · Math Gauge</title><link rel="stylesheet" href="'+local('assets/results.css')+'"></head><body>'
        '<header class="topbar"><nav class="nav" aria-label="主导航"><a class="brand" data-context-link href="'+local('index.html')+'"><span class="mark" aria-hidden="true">MG</span>Math Gauge</a>'
        '<div class="navlinks"><a data-context-link href="'+local('index.html')+'">排行榜</a><a data-nav-method data-context-link href="'+local('method.html')+'">方法与数据</a></div>'+language_switch()+'</nav></header>'
        '<main class="detail-main"><div class="breadcrumbs">'+crumbs+'</div><div class="intro"><div><div class="eyebrow">MATH GAUGE · v0.6.0</div><h1>'+html.escape(title)+'</h1><p class="subtitle">'+html.escape(subtitle)+'</p></div></div>'
        '<div class="statusline"><span class="status-dot"></span><span>AI 审核 · 人审待定</span><span class="divider"></span><span>观察后选题与复核，正式比较资格未确立</span></div>'
        '<section class="panel context-panel">'+controls(data)+'<p class="panel-foot context-label" aria-live="polite"></p></section><p class="original-language-note">原题与原答保留原始语言。</p>'+body+
        '<footer class="footer"><span>Math Gauge · 原答与原评审保留</span><a data-context-link href="'+local('method.html')+'">计分方法与证据边界</a></footer></main>'
        '<script type="application/json" id="data">'+embedded(data)+'</script><script src="'+local('assets/results-i18n.js')+'"></script><script src="'+local('assets/results-core.js')+'"></script><script src="'+local('assets/'+script)+'"></script></body></html>')


def compact_data(data, model=None):
    keys = ('schema', 'benchmark_version', 'score_mode_catalog', 'default_score_mode', 'score_modes',
            'attempt_conditions', 'display_score_modes', 'default_attempt_condition', 'policy', 'capacity', 'human_review', 'formal_comparison_eligible')
    value = {k: data[k] for k in keys}
    if model:
        value['model'] = model
    return value


def panel(title, body, note=None, *, id=None):
    return '<section class="panel"'+(' id="'+id+'"' if id else '')+'><div class="panel-head"><h2>'+html.escape(title)+'</h2></div>'+body+('<p class="panel-foot">'+html.escape(note)+'</p>' if note else '')+'</section>'


def descriptor(root, item, *, role):
    raw = evidence_bytes(root, item)
    return {'path': str((root / item['path']).relative_to(root.parents[3])),
            'sha256': hashlib.sha256(raw).hexdigest(), 'role': role, 'raw': raw}


def review_projection(value):
    if value.get('schema') == 'math-gauge.public-adjudication-projection/v1':
        return value.get('judgment')
    return value


def public_evidence(folder, record, cid, condition, task):
    """Resolve the actual selected public answer; a retry never inherits A1 text."""
    if record.get('record_kind') == 'paper_observation':
        row = next(r for r in record['public_deliveries'] if r['case_id'] == cid)
        claims = json.loads(evidence_bytes(folder, record['public_claim_review']))['conditions'][condition]
        claim = next(r for r in claims['cases'] if r['case_id'] == cid)
        sources = [descriptor(folder, row[key], role=role) for key, role in
                   (('response', 'answer'), ('review', 'source_review')) if row.get(key) is not None
                   and row[key]['sha256'] == task['response_sha256' if key == 'response' else 'review_sha256']]
        review = next((json.loads(s['raw']) for s in sources if s['role'] == 'source_review'), None)
        return {'sources': sources, 'review': review, 'claim': claim, 'notes': [],
                'selected_record': cid + ':A1', 'source_row': row}
    sources, notes, primary = [], [], None
    chosen = None
    if record.get('retry_admission') and condition == 'nonlogical_retry_3':
        admission = json.loads(evidence_bytes(folder, record['retry_admission']))
        ledger = json.loads(evidence_bytes(folder, admission['ledger']))
        chosen = next((s['selected_record_id'] for s in ledger['slots'] if s['slot_id']==cid+':A1'), None)
    legacy = next((s for s in record['records'] if s['id']==(chosen or cid+':A1')), None)
    row = legacy
    for name, field in (('theorem_extension_evidence', 'records'), ('background_check_evidence', 'records'),
                        ('written_replacement_evidence', 'slots')):
        if name in record:
            data = json.loads(evidence_bytes(folder, record[name]))
            candidate = next((s for s in data[field] if s['case_id']==cid), None)
            if candidate:
                row = candidate
    if row:
        answer = row.get('response')
        if answer:
            if answer['sha256'] != task['response_sha256']:
                raise ValueError(f"Selected answer differs from task score: {cid}/{condition}")
            sources.append(descriptor(folder, answer, role='answer'))
        if legacy and row is legacy:
            review_items = ([row['review']] if row.get('review') else [])
            review_items += [s for s in row.get('artifacts', []) if s['path'].endswith('.json')
                            and (s['path'].startswith('reviews/')
                                 or s['path'].endswith('/mathematical-review.json'))]
            if not review_items and chosen:
                # Retry reviews are independently bound in the public claim audit below.
                review_items = []
            if review_items:
                sources.append(descriptor(folder, review_items[0], role='review'))
                primary = review_projection(json.loads(sources[-1]['raw']))
        else:
            item = row.get('review') or row.get('source_review')
            if item:
                sources.append(descriptor(folder, item, role='review'))
                primary = review_projection(json.loads(sources[-1]['raw']))
                # Background R conversion binds the original, more detailed review.
                if primary.get('source_review_sha256'):
                    path = (folder / item['path']).parent / 'source-review.json'
                    raw = path.read_bytes()
                    if hashlib.sha256(raw).hexdigest() != primary['source_review_sha256']:
                        raise ValueError('Background detailed review does not match its retained conversion')
                    item = {'path': str(path.relative_to(folder)), 'bytes': len(raw), 'sha256': primary['source_review_sha256']}
                    sources.append(descriptor(folder, item, role='source_review'))
        if row.get('missing_response_reason'):
            notes.append(row['missing_response_reason'])
        if row is legacy:
            for item in row.get('artifacts', []):
                path = str((folder/item['path']).relative_to(folder.parents[3]))
                if not any(s['path']==path for s in sources):
                    sources.append(descriptor(folder,item,role='attachment'))
    audit = json.loads(evidence_bytes(folder, record['claim_review']))
    claim = next(s for s in audit['conditions'][condition]['cases'] if s['case_id']==cid)
    for item in claim['sources']:
        if item.get('archive') != 'public':
            raise ValueError('A public case attempted to reference private evidence')
        archive_prefix = folder.relative_to(folder.parents[3]).as_posix() + '/'
        if item['path'] in {s['path'].removeprefix(archive_prefix) for s in sources}:
            continue
        inferred_role = ('answer' if item['sha256'] == task['response_sha256'] else
                         'review' if item['path'].endswith('.json') else 'attachment')
        source = descriptor(folder, item, role=item.get('role', inferred_role))
        if item.get('case_pointer'):
            selected = json.loads(source['raw'])
            for key in item['case_pointer'].strip('/').split('/'):
                selected = selected[int(key)] if isinstance(selected,list) else selected[key.replace('~1','/').replace('~0','~')]
            source['selected'] = selected
        sources.append(source)
        if primary is None and source['role']=='review':
            primary = review_projection(source['selected'] if 'selected' in source
                                        else json.loads(source['raw']))
    if record.get('formalization_review') and not any(s['role']=='engineering_review' for s in sources):
        source = descriptor(folder, record['formalization_review'], role='engineering_review')
        engineering = next((r for r in json.loads(source['raw'])['cases'] if r['case_id']==cid), None)
        if engineering:
            if engineering['original_response_sha256'] != task['response_sha256']:
                raise ValueError(f'Engineering review differs from selected answer: {cid}/{condition}')
            source['selected'] = engineering
            sources.append(source)
            if primary is None:
                primary = engineering
    if task['response_sha256'] and not any(s['sha256']==task['response_sha256'] for s in sources):
        raise ValueError(f'Missing selected public answer for {cid}/{condition}')
    return {'sources': sources, 'review': primary, 'claim': claim, 'notes': notes,
            'selected_record': chosen or cid+':A1', 'source_row': row}


def review_markdown(review):
    """Readable projection of explicit review fields, without new judgments."""
    if not review:
        return '当前没有可展示的逐项评审；计分状态以正式档案为准。'
    lines = []
    for key, title in [('summary','评审摘要'), ('reason','判定理由'), ('strict_reason','SMC 理由'),
                       ('baseline_findings','原题核查'), ('research_findings','拓展核查'), ('issues','主要问题')]:
        value = review.get(key)
        if value:
            lines.extend(['### '+title, readable(value), ''])
    if 'B' in review or 'R' in review:
        lines.append('原题判定 B：'+str(review.get('B','—'))+'；拓展判定 R：'+str(review.get('R','—'))+'。')
    for key in ('background_R', 'baseline_B', 'research_R'):
        if key in review:
            lines.append(key+'：'+str(review[key]))
    diagnostic = review.get('group_diagnostic') or review
    rows = next((diagnostic[k] for k in ('criteria','stages','dimensions','obligations')
                 if isinstance(diagnostic.get(k), list)), [])
    for index, row in enumerate(rows, 1):
        key = next((row[k] for k in ('criterion_id','stage_id','dimension_id','id','obligation_id') if k in row), str(index))
        lines.append('### '+str(key))
        fields = [('points','分数'), ('max_points','满分'), ('score','评分'), ('decision','判定'),
                  ('status','状态'), ('complete','已核实完成'), ('reason','理由'), ('notes','审核说明'),
                  ('finding','核查结论'), ('counterexample','反例'), ('additional_gap','补充缺口')]
        for field, title in fields:
            if field in row:
                lines.append('**'+title+'：** '+readable(row[field])+'\n')
    return '\n\n'.join(lines) or '原评审未提供独立摘要。完整判断及证据见下方原评审文件。'


def readable(value):
    if value is None:
        return '未知'
    if isinstance(value, str):
        return value
    if isinstance(value, list):
        return '\n\n'.join(readable(v) for v in value)
    if isinstance(value, dict):
        return '\n\n'.join('**'+str(k)+'：** '+readable(v) for k,v in value.items())
    return json.dumps(value, ensure_ascii=False)


def render_case(page, data, model, entry, projection, evidence, markdown, root):
    cid = entry['case_id']
    details = compact_data(data, {'id':model['id'], 'label':model['label']})
    details['case'] = {'id': cid, 'title': entry['title'], 'category': entry['category'],
        'views': {mode: {c: next(r for r in projection['views'][mode][c]['tasks'] if r['case_id']==cid)
                         for c in CONDITIONS} for mode in projection['views']}}
    body = panel('本题成绩', '<div class="case-score" id="case-score"></div><p class="panel-foot" id="case-score-note"></p>',
        'MC/RMC 显示单题计分比例 /100，权重贡献在模型页汇总；SMC 显示整题判定。未测与交付失败分别保留。')
    task_path = Path(model['source_record']).parent/'inputs'/cid/'task.md'
    if not (root/task_path).is_file():
        task_path = Path(entry['paths']['task'])
    task = (root/task_path).read_text()
    body += '<details class="panel evidence-fold"><summary>题目与要求</summary><div class="prose">'+markdown.add(task)+'</div><p class="panel-foot">'+source_link(task_path,page,'原题文件 ↗')+'</p></details>'
    for condition, item in evidence.items():
        claim = item['claim']
        reasons = ''.join('<li>'+markdown.add(f['reason'])+'</li>' for f in claim['findings'])
        if not reasons:
            reasons = '<li>'+markdown.add(claim['scope_note'])+'</li>'
        current = '<div class="evidence-condition" data-evidence-condition="'+condition+'"'+(' hidden' if condition!=CONDITIONS[0] else '')+'>'
        current += panel('判定与主要理由', '<div class="prose"><ul class="findings">'+reasons+'</ul></div>')
        # Many Lean obligations belong in an expandable audit, while short proof criteria stay visible.
        selected_review = item['review']
        engineering = next((s.get('selected') for s in item['sources'] if s['role']=='engineering_review'), None)
        review_source = next((s for s in item['sources'] if s['role']=='source_review'), None)
        criterion_review = json.loads(review_source['raw']) if review_source else selected_review
        review_html = '<div class="prose review-criteria">'+markdown.add(review_markdown(criterion_review))+'</div>'
        if engineering:
            review_html += '<details class="evidence-fold nested"><summary>逐项工程与语义审核（'+str(len(engineering.get('obligations',[])))+'项）</summary><div class="prose">'+markdown.add(review_markdown(engineering))+'</div></details>'
        current += panel('逐项评审', review_html,
            '以下为原评审字段的阅读视图；当前口径的额外扣罚与 SMC 判定以本页成绩及上方理由为准。')
        answers = [s for s in item['sources'] if s['role'] in ('answer','response') and s['sha256']==details['case']['views']['partial'][condition]['response_sha256']]
        if answers:
            answer = answers[0]
            current += '<details class="panel evidence-fold original-answer"><summary>完整原答 · 含原自评与不确定性表述</summary><div class="prose">'+markdown.add(answer['raw'].decode('utf-8'))+'</div><p class="panel-foot">'+source_link(answer['path'],page,'原答文件 ↗')+'</p></details>'
        else:
            unknown = details['case']['views']['partial'][condition]['completion']['exact'] is None
            current += '<p class="empty-state">'+('本题尚未作答或评审未决，成绩保持未知。' if unknown else '本次没有保留可读的最终原答；已确认的交付失败或独立工程证据按正式记录计分。')+'</p>'
        links = ''.join('<li>'+source_link(s['path'],page,s['role']+' · '+Path(s['path']).name)+'<span class="hash">SHA256 '+s['sha256']+'</span></li>' for s in item['sources'])
        links += '<li>'+source_link(model['source_record'],page,'来源记录 ↗')+'</li>'
        current += '<details class="panel evidence-fold"><summary>来源、原评审与运行附件</summary><div class="prose"><p>采用记录：<code>'+html.escape(item['selected_record'])+'</code>。正文来自已保留的公开文件，原始字节与哈希不变。</p><ul class="source-list">'+links+'</ul></div></details></div>'
        body += current
    return shell(page,cid+' · '+entry['title'],model['label']+' · '+CATEGORY_TITLES.get(entry['category'],entry['category'])+' · 公开题证据',body,details,'case-results.js',back=('models/'+model['id']+'/index.html',model['label']))


def render_model(page, data, model, cases, record, folder, markdown):
    details = compact_data(data, model)
    details['cases'] = cases
    body = panel('当前成绩', '<div id="model-overview" class="metric-grid"></div>',
        '公开与私有合并，满分保持100；未测项目保持未知。')
    if model.get('record_kind') == 'native_harness':
        body = panel('Dot native harness', '<div class="prose"><p>'
            +html.escape(model['comparison_note'])+'</p><p>'
            +html.escape(model['harness']['detail'])+'</p><p>当前初答和三轮自查均保留原始交付；原批次与补充来源分别留证。'
            '独立AI评审，人工待审；原始初评与本次复核差异另行保存。</p></div>')+body
    if model.get('record_kind') == 'paper_observation':
        body = panel('答卷观察与证据范围', '<div class="prose"><p>'
            +html.escape(model['comparison_note'])+'</p><p>来源按原标签及所报推理档位保存，后端型号与运行遥测未核实。'
            '数学评审、操作者声明的交付失败与未知项分别留存；内容可靠率与目标达成率尚未补审。</p></div>')+body
    rates = model.get('content_rates')
    if rates:
        def percent(value):
            return '—' if value is None else f'{value:.2f}%'
        target = 'attainment' if rates['version'] == '0.2.0' else 'delivery'
        target_label = '目标达成率' if target == 'attainment' else '旧细项覆盖率'
        r, d = rates['metrics']['reliability'], rates['metrics'][target]
        rows = ''
        for child in data['policy']['subcategories']:
            category = rates['categories'][child['id']]
            delivered = category[target]['confirmed'] if category['coverage']['reviewed_tasks'] else None
            rows += '<tr><td>'+html.escape(child['title'])+'</td><td class="numeric">'
            rows += percent(category['reliability']['observed'])+'</td><td class="numeric">'
            rows += percent(delivered)+'</td></tr>'
        body += panel('内容可靠率与'+target_label, '<div class="prose"><p>已审内容可靠率 '
            +percent(r['observed'])+'；已确认'+target_label+' '+percent(d['confirmed'])+'。</p><p>完整题包可能范围：可靠率 '
            +percent(r['lower'])+'–'+percent(r['upper'])+'；'+target_label+' '+percent(d['lower'])+'–'
            +percent(d['upper'])+'。未测保持未知。</p></div><div class="table-wrap"><table class="compact rate-table">'
            '<thead><tr><th>子类</th><th class="numeric">已审内容可靠率</th><th class="numeric">已确认'+target_label+'</th>'
            '</tr></thead><tbody>'+rows+'</tbody></table></div><p class="panel-foot">'
            +source_link(Path(model['source_record']).parent/'content-rates.json', page, '补审汇总 JSON ↗')
            +' · <a data-context-link href="../../method.html#content-rate-method">计算方法 →</a></p>',
            '内容核查实际断言；目标按完整独立成果验收。不改变MC、RMC、SMC。AI审核／人审待定。')
    body += panel('分类贡献', '<div class="table-wrap"><table id="model-categories" class="compact"></table></div>',
        '每格为贡献分 / 该项满分。书面论证12个家族等权；相关变体在家族内聚合。')
    body += '<div class="equal-grid">'+panel('Lean · 自查计分', '<div class="table-wrap"><table id="model-selfcheck" class="compact"></table></div><p id="selfcheck-rule" class="panel-foot"></p><details class="selfcheck-comparison"><summary>比较三种计分口径</summary><div class="table-wrap"><table id="selfcheck-comparison" class="compact"></table></div></details>')
    rounds = ''
    for index in (1,2,3):
        row = (next(s for s in record['selfcheck_rounds'] if s['round']==index)
               if model.get('record_kind') in {'native_harness', 'paper_observation'} else
               next(s for s in record['records'] if s['id'] in
                    ('MG-C003:alignment:'+str(index), 'MG-C003:R'+str(index))))
        response = row.get('response')
        content = markdown.add(evidence_bytes(folder,response).decode()) if response else '原记录没有可读的最终原答，未补写。'
        link = source_link(Path(model['source_record']).parent/response['path'],page,'原答文件 ↗') if response else ''
        rounds += '<details class="evidence-fold nested"><summary>R'+str(index)+' · 完整原答</summary><div class="prose">'+content+'<p>'+link+'</p></div></details>'
    alignment_path = next((s['path'] for s in record.get('evidence',[]) if s['path'] in ('reviews/alignment.json','alignment-review.json')),None)
    if alignment_path:
        rounds += '<p class="panel-foot">'+source_link(Path(model['source_record']).parent/alignment_path,page,'完整三轮审核与诊断依据 ↗')+'</p>'
    body += panel('整章对齐 · 固定三轮', '<div class="table-wrap"><table id="model-trajectory" class="compact"></table></div><details class="evidence-fold nested"><summary>展开三轮原答与审核</summary>'+rounds+'</details>', '原答事实，不随口径改变。92项义务，采用最后规定轮次；不取最好一轮，不拼接各轮成果。')+'</div>'
    body += panel('公开题 · 逐题成绩与证据', '<div class="table-wrap"><table id="case-list" class="compact case-list"></table></div>',
        f"当前{data['policy']['scope']['public_tasks']}道公开题。私有{data['policy']['scope']['private_tasks']}题只进入上方合并贡献，"
        '不提供题号、原答或逐题评审。单题比例不可直接相加为总分。')
    body += '<details class="panel evidence-fold"><summary>形式化初答 · 逐题核实数</summary><div class="table-wrap"><table id="model-formalization" class="compact"></table></div><p class="panel-foot">编译与逐项语义审核同时成立才计完成。初答与后续自查分开计分。</p></details>'
    body += panel('可靠性审核', '<div id="model-penalties" class="metric-grid"></div><details class="nested evidence-fold"><summary>公开题的错误承诺与扣罚理由</summary><div id="model-findings" class="prose"></div></details>',
        '记录数不等于独立样本或扣罚次数；同根因去重。RMC 普通扣罚5%/10%/20%，通常每题最多20%，数学想法手稿化最多50%；已确立的核心错误放行使该题最高0分，SMC 不通过。')
    body += panel('Harness与工具', '<div class="prose"><p>'+html.escape(model['harness']['detail'])+'</p><p>允许本地工具与预置公共依赖，禁止联网检索及工具联网。</p><p>'+html.escape(model['harness']['tool_usage'])+'</p></div>')
    source = source_link(model['source_record'],page,'正式档案 ↗')
    body += '<details class="panel evidence-fold"><summary>运行条件、重跑与来源</summary><div class="prose"><p>'+html.escape(model['retry']['note'])+'</p><p>允许本地工具，禁止联网检索和工具联网。历史答卷的具体条件以原始记录为准；允许重跑采用第一次正常交付，不按数学得分择优。</p><p>'+source+'</p></div></details>'
    body += panel('下载当前口径', '<div class="downloads" id="downloads"></div><p class="panel-foot"><a data-context-link href="../../method.html">查看完整方法与数据说明 →</a></p>')
    return shell(page,model['label'],'模型详细评测 · 公开＋私有合并成绩',body,details,'model-results.js')


def build_detail_pages(data, root):
    root = Path(root)
    entries = json.loads((root/'cases/catalog.json').read_bytes())['entries']
    catalog = {e['case_id']:e for e in entries}
    pages, markdown = {}, EvidenceRenderer()
    for source_model in data['models']:
        model = dict(source_model, label=source_model.get('source_model_label', source_model['label']))
        folder = root / Path(model['source_record']).parent
        if model.get('record_kind') == 'paper_observation':
            record = json.loads((folder/'record.json').read_bytes())
            projection = json.loads(evidence_bytes(folder,record['public_task_scores']))
            claims = json.loads(evidence_bytes(folder,record['public_claim_review']))['conditions']
            model['public_claims'] = {c:claims[c]['cases'] for c in CONDITIONS}
            rows = {r['case_id']:r for r in record['public_deliveries']}
            if set(rows) != set(catalog) or set(projection['public_case_ids']) != set(catalog):
                raise ValueError('Paper public projection differs from the fixed public catalog')
            cases = []
            for cid in projection['public_case_ids']:
                row,entry = rows[cid],catalog[cid]
                evidence = {}
                for condition in CONDITIONS:
                    task = next(t for t in projection['views']['partial'][condition]['tasks'] if t['case_id']==cid)
                    evidence[condition] = public_evidence(folder, record, cid, condition, task)
                cases.append({'id':cid, 'title':entry['title'], 'category':entry['category'],
                    'category_title':CATEGORY_TITLES.get(entry['category'],entry['category']),
                    'views':{mode:{c:next(t for t in projection['views'][mode][c]['tasks'] if t['case_id']==cid)
                                   for c in CONDITIONS} for mode in projection['views']}})
                path = 'models/'+model['id']+'/cases/'+cid+'.html'
                pages[path] = render_case(path,data,model,entry,projection,evidence,markdown,root)
            path = 'models/'+model['id']+'/index.html'
            pages[path] = render_model(path,data,model,cases,record,folder,markdown)
            del model['public_claims']
            continue
        if model.get('record_kind') == 'native_harness':
            record = json.loads((folder/'native-observation.json').read_bytes())
            projection = json.loads(evidence_bytes(folder,record['public_task_scores']))
            if set(projection['public_case_ids']) != set(catalog):
                raise ValueError('Native public projection differs from the fixed public catalog')
            native_rows = {row['case_id']:row for row in record['public_deliveries']}
            claims = []
            for cid,row in native_rows.items():
                review = json.loads(evidence_bytes(folder,row['review']))
                claims.append({'case_id':cid,'scope_note':review['scope'],'findings':review['findings']})
            model['public_claims'] = {c:claims for c in CONDITIONS}
            cases = []
            for cid in projection['public_case_ids']:
                row,entry = native_rows[cid],catalog[cid]
                source_review = descriptor(folder,row['review'],role='source_review')
                answer = descriptor(folder,row['response'],role='answer')
                claim = next(c for c in claims if c['case_id']==cid)
                evidence = {c:{'claim':claim,'review':json.loads(source_review['raw']),
                    'selected_record':cid+':A1','sources':[answer,source_review]} for c in CONDITIONS}
                cases.append({'id':cid,'title':entry['title'],'category':entry['category'],
                    'category_title':CATEGORY_TITLES.get(entry['category'],entry['category']),
                    'views':{mode:{c:next(t for t in projection['views'][mode][c]['tasks'] if t['case_id']==cid)
                                   for c in CONDITIONS} for mode in projection['views']}})
                path = 'models/'+model['id']+'/cases/'+cid+'.html'
                pages[path] = render_case(path,data,model,entry,projection,evidence,markdown,root)
            path = 'models/'+model['id']+'/index.html'
            pages[path] = render_model(path,data,model,cases,record,folder,markdown)
            del model['public_claims']
            continue
        record = json.loads((folder/'record.json').read_bytes())
        projection = load_public_task_scores(folder, record)
        if projection is None:
            raise ValueError('Detail pages require source-bound public task scores')
        if set(projection['public_case_ids']) != set(catalog):
            raise ValueError('Site catalog differs from current scoring selection')
        cases = []
        audits = json.loads(evidence_bytes(folder,record['claim_review']))
        model['public_claims'] = {c: audits['conditions'][c]['cases'] for c in CONDITIONS}
        for cid in projection['public_case_ids']:
            entry = catalog[cid]
            evidence = {c: public_evidence(folder, record, cid, c,
                next(r for r in projection['views']['partial'][c]['tasks'] if r['case_id']==cid)) for c in CONDITIONS}
            cases.append({'id':cid,'title':entry['title'],'category':entry['category'],
                'category_title':CATEGORY_TITLES.get(entry['category'],entry['category']),
                'views': {mode:{c:next(r for r in projection['views'][mode][c]['tasks'] if r['case_id']==cid)
                               for c in CONDITIONS} for mode in projection['views']}})
            path = 'models/'+model['id']+'/cases/'+cid+'.html'
            pages[path] = render_case(path, data, model, entry, projection, evidence, markdown, root)
        path = 'models/'+model['id']+'/index.html'
        pages[path] = render_model(path, data, model, cases, record, folder, markdown)
        del model['public_claims']
    pages['method.html'] = shell('method.html','方法与数据','三个计分口径、固定分母与公开证据的阅读方式',
        '<div data-lang-content="zh">'+(HERE/'templates/method-content.html').read_text()+'</div>'
        '<div data-lang-content="en" hidden>'+(HERE/'templates/method-content.en.html').read_text()+'</div>',
        compact_data(data),'method-results.js')
    return markdown.finish(pages)
