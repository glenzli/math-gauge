"""Public evidence pages. This module formats retained judgments, never scores them."""
import hashlib
import html
import json
import os
from pathlib import Path
import subprocess
from urllib.parse import quote

from math_gauge.records import evidence_bytes, load_public_task_scores
from math_gauge.attempt_conditions import load_sources as load_attempt_sources
from math_gauge.evidence_retention import source_location, read_bytes as retained_bytes, is_file as retained_file
from scripts.results_i18n import language_switch
from scripts.results_harness import display_harness_labels
from scripts.results_presentation import project_payload

HERE = Path(__file__).resolve().parent
CONDITIONS = ("single_attempt", "nonlogical_retry_3")
CATEGORY_TITLES = {'proofs': '书面论证', 'answer-review': '论证审阅', 'lean-audit': '语义审计',
                   'lean-formalization': '形式化', 'theorem-extension': '命题拓展', 'background-check': '背景核查', 'manuscript-completion': '数学想法手稿化'}


def embedded(value):
    return json.dumps(display_harness_labels(project_payload(value)), ensure_ascii=False).replace("<", "\\u003c").replace("&", "\\u0026")


def source_link(source, page, label, *, root=None):
    root = Path(root or HERE.parent).resolve()
    source = Path(source)
    source = Path(os.path.abspath(source if source.is_absolute() else root / source))
    if not source.is_relative_to(root):
        raise ValueError("Public evidence link escapes its source repository")
    location = source_location(source)
    if Path(location['repository_root']).resolve() != root:
        raise ValueError("Public evidence link belongs to another repository")
    if location['revision'] is not None:
        href = ('https://github.com/glenzli/math-gauge/blob/' + location['revision']
                + '/' + quote(location['git_path'], safe='/'))
    else:
        href = quote(os.path.relpath(root / location['git_path'],
                                    root / "site" / Path(page).parent), safe='/')
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


def review_status(data, href):
    process = data['review_process']
    detail = '全审：'+process['primary_ai_reviewer']+'；抽审核对：'+' + '.join(process['cross_check_reviewers'])
    return ('<div class="statusline"><span class="status-dot" aria-hidden="true"></span>'
            '<span title="'+html.escape(detail, quote=True)+'">AI 审核 · 部分人工抽审</span>'
            '<a data-context-link href="'+html.escape(href, quote=True)+'">审核方式 →</a></div>')



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
        '<main class="detail-main"><div class="breadcrumbs">'+crumbs+'</div><div class="intro"><div><div class="eyebrow">MATH GAUGE · v1.0.0</div><h1>'+html.escape(title)+'</h1><p class="subtitle">'+html.escape(subtitle)+'</p></div></div>'
        +review_status(data, prefix+'/method.html#review-process')+
        '<section class="panel context-panel">'+controls(data)+'</section>'+body+
        '<footer class="footer"><span>Math Gauge</span><a data-context-link href="'+local('method.html')+'">方法与数据</a></footer></main>'
        '<script type="application/json" id="data">'+embedded(data)+'</script><script src="'+local('assets/results-i18n.js')+'"></script><script src="'+local('assets/results-core.js')+'"></script><script src="'+local('assets/'+script)+'"></script></body></html>')


def compact_data(data, model=None):
    keys = ('schema', 'benchmark_version', 'score_mode_catalog', 'default_score_mode', 'score_modes',
            'attempt_conditions', 'display_score_modes', 'default_attempt_condition', 'policy', 'capacity', 'human_review', 'review_process', 'formal_comparison_eligible')
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
    if value.get('schema') in {'math-gauge.public-adjudication-projection/v1',
                               'math-gauge.public-original-review-projection/v1'}:
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
    condition_sources = load_attempt_sources(folder, record, condition)
    chosen = None
    if record.get('retry_admission') and condition == 'nonlogical_retry_3':
        admission = json.loads(evidence_bytes(folder, record['retry_admission']))
        ledger = json.loads(evidence_bytes(folder, admission['ledger']))
        chosen = next((s['selected_record_id'] for s in ledger['slots'] if s['slot_id']==cid+':A1'), None)
    selected_records = condition_sources['records']['records'] if condition_sources else record['records']
    legacy = next((s for s in selected_records if s['id']==(chosen or cid+':A1')), None)
    if condition_sources and legacy and not legacy.get('review'):
        original = next((r for r in record['records'] if r['id'] == legacy['id']), None)
        if (original and original.get('review')
                and (original.get('response') or {}).get('sha256') == task['response_sha256']):
            projected = json.loads(evidence_bytes(folder, original['review']))
            if (projected.get('schema') == 'math-gauge.public-original-review-projection/v1'
                    and isinstance(projected.get('judgment', {}).get('binding'), dict)):
                judgment = projected['judgment']
                normalized_sha = judgment.get('review_sha256')
                # Component score adapters may have their own review hash. This
                # displays the original judgment selected for the same response.
                if (normalized_sha != original.get('evaluation', {}).get('review_sha256')
                        or normalized_sha != legacy.get('evaluation', {}).get('review_sha256')
                        or judgment.get('binding', {}).get('response_sha256') != task['response_sha256']):
                    raise ValueError('Original review projection belongs to another selected answer')
                legacy = dict(legacy, review=original['review'], artifacts=original.get('artifacts', []))
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
        if not answer and row.get('missing_response_reason'):
            notes.append(row['missing_response_reason'])
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
                    raw = retained_bytes(path)
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
        engineering_source = (condition_sources['bindings']['formalization_review']
                              if condition_sources else record['formalization_review'])
        source = descriptor(folder, engineering_source, role='engineering_review')
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
    for key, title in [('summary','评审摘要'), ('reason','判定理由'), ('finding','核查结论'), ('strict_reason','SMC 理由'),
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
    rows = next((diagnostic[k] for k in ('criteria','stages','dimensions','obligations','credit_units')
                 if isinstance(diagnostic.get(k), list)), [])
    for index, row in enumerate(rows, 1):
        key = next((row[k] for k in ('criterion_id','stage_id','dimension_id','id','obligation_id') if k in row), str(index))
        lines.append('### '+str(key))
        fields = [('points','分数'), ('max_points','满分'), ('earned','已获分'), ('maximum','满分'), ('score','评分'), ('decision','判定'),
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
        'MC/RMC为单题比例，SMC为整题判定；总分贡献见模型页。')
    task_path = Path(model['source_record']).parent/'inputs'/cid/'task.md'
    if not retained_file(root/task_path):
        task_path = Path(entry['paths']['task'])
    task = retained_bytes(root/task_path).decode('utf-8')
    body += '<details class="panel evidence-fold"><summary>题目与要求</summary><div class="prose">'+markdown.add(task)+'</div><p class="panel-foot">'+source_link(task_path,page,'原题文件 ↗',root=root)+'</p></details>'
    source_folder=root/Path(model['source_record']).parent
    source_record=json.loads((root/model['source_record']).read_bytes())
    submissions=(json.loads(evidence_bytes(source_folder,source_record['submission_evidence']))
                 if source_record.get('submission_evidence') else None)
    for condition, item in evidence.items():
        claim = item['claim']
        reasons = ''.join('<li>'+markdown.add(f['reason'])+'</li>' for f in claim['findings'])
        if not reasons:
            reasons = '<li>计分依据见下方逐项评审。</li>'
        current = '<div class="evidence-condition" data-evidence-condition="'+condition+'"'+(' hidden' if condition!=CONDITIONS[0] else '')+'>'
        if submissions:
            selected=next(row for row in submissions['conditions'][condition]['public_initials'] if row['case_id']==cid)
            selected = dict(selected, **item.get('submission_override', {}))
            if (model.get('review_completion') and condition == 'nonlogical_retry_3'
                    and cid in model['review_completion']['resolved_public_cases']):
                selected = dict(selected, pending_original_record_review=False)
            label={'active_final':'正常交卷；三种评分采用实际交付。',
                   'forced_content':'强收有内容；MC按已核实原成果计分，RMC与SMC为0。',
                   'blank':'原记录待复核，按已确认口径暂记0。' if selected['pending_original_record_review'] else '无可审核交付，计0。',
                   'not_run':'未测，保留未知。'}[selected['classification']]
            if item.get('recovered_original_reply'):
                label = '原后端答卷已恢复并接纳；三种评分采用该原答。原CLI ERROR保留。'
            if selected['pending_original_record_review']:
                label+=' 待补原记录复核。'
            current += panel('提交来源','<div class="prose"><p>'+html.escape(label)+'</p></div>')
        current += panel('判定与主要理由', '<div class="prose"><ul class="findings">'+reasons+'</ul></div>')
        # Many Lean obligations belong in an expandable audit, while short proof criteria stay visible.
        selected_review = item['review']
        engineering = next((s.get('selected') for s in item['sources'] if s['role']=='engineering_review'), None)
        review_source = next((s for s in item['sources'] if s['role']=='source_review'), None)
        criterion_review = json.loads(review_source['raw']) if review_source else selected_review
        review_html = '<div class="prose review-criteria">'+markdown.add(review_markdown(criterion_review))+'</div>'
        if engineering:
            review_html += '<details class="evidence-fold nested"><summary>逐项工程与语义审核（'+str(len(engineering.get('obligations',[])))+'项）</summary><div class="prose">'+markdown.add(review_markdown(engineering))+'</div></details>'
        review_title = ('补充逐项评审' if item.get('recovered_original_reply') else
                        '原始逐项评审' if submissions else '逐项评审')
        current += panel(review_title, review_html,
            ('原评保留原审核范围；当前采用的提交与成绩见上方及模型档案。' if submissions
             else '原始评审见下方来源文件。'))
        answers = [s for s in item['sources'] if s['role'] in ('answer','response') and s['sha256']==details['case']['views']['partial'][condition]['response_sha256']]
        if answers:
            answer = answers[0]
            current += '<details class="panel evidence-fold original-answer"><summary>完整原答</summary><div class="prose">'+markdown.add(answer['raw'].decode('utf-8'))+'</div><p class="panel-foot">'+source_link(answer['path'],page,'原答文件 ↗',root=root)+'</p></details>'
        else:
            unknown = details['case']['views']['partial'][condition]['completion']['exact'] is None
            current += '<p class="empty-state">'+('本题尚无评审结果。' if unknown else '本题的交付记录及计分依据见档案。')+'</p>'
        links = ''.join('<li>'+source_link(s['path'],page,s['role']+' · '+Path(s['path']).name,root=root)+'<span class="hash">SHA256 '+s['sha256']+'</span></li>' for s in item['sources'])
        links += '<li>'+source_link(model['source_record'],page,'来源记录 ↗',root=root)+'</li>'
        current += '<details class="panel evidence-fold"><summary>来源、原评审与运行附件</summary><div class="prose"><p>采用记录：<code>'+html.escape(item['selected_record'])+'</code></p><ul class="source-list">'+links+'</ul></div></details></div>'
        body += current
    return shell(page,cid+' · '+entry['title'],model['label']+' · '+CATEGORY_TITLES.get(entry['category'],entry['category'])+' · 公开题证据',body,details,'case-results.js',back=('models/'+model['id']+'/index.html',model['label']))


def render_model(page, data, model, cases, record, folder, markdown):
    root = folder.parents[3]
    details = compact_data(data, model)
    details['cases'] = cases
    body = panel('当前成绩', '<div id="model-overview" class="metric-grid"></div>')
    if model.get('harness_correction'):
        correction = model['harness_correction']
        body += panel('Harness故障更正',
            '<div class="prose"><p>HCH02采用因回传故障而恢复的原始后端答卷，按原判分规则补审。'
            '原始ERROR、旧成绩与审核均保留；没有补跑，也没有将执行错误改写为成功。</p></div>'
            '<p class="panel-foot">' + source_link(correction['manifest']['path'], page,
                '恢复来源与更正记录 ↗', root=root) + '</p>')
    if model.get('review_completion'):
        receipt = Path(model['source_record']).parent / 'review-completion.json'
        body += panel('来源审核完成', '<div class="prose"><p data-lang-content="zh">39道初答的原始答卷审核完成，三项缺档已复核。三轮自查因初答未交付而未执行，仍保留未知。</p>'
            '<p data-lang-content="en" hidden>All 39 initial-answer sources have been reviewed, including the three recovered records. The three self-check rounds were not run because the initial engineering delivery was absent; their scores remain unknown.</p></div>'
            '<p class="panel-foot">'+source_link(receipt,page,'补充复核记录 ↗',root=root)+'</p>')
    rates = model.get('content_rates')
    if rates:
        def percent(value):
            return '—' if value is None else f'{value:.2f}%'
        target = 'attainment' if rates['version'] == '0.2.0' else 'delivery'
        target_label = '目标达成率' if target == 'attainment' else '旧细项覆盖率'
        r, d = rates['metrics']['reliability'], rates['metrics'][target]
        ranges = []
        for label, value in [('内容可靠率', r), (target_label, d)]:
            if percent(value['lower']) != percent(value['upper']):
                ranges.append(label+' '+percent(value['lower'])+'–'+percent(value['upper']))
        interval = '<p>可能范围：'+'；'.join(ranges)+'</p>' if ranges else ''
        rows = ''
        for child in data['policy']['subcategories']:
            category = rates['categories'][child['id']]
            delivered = category[target]['confirmed'] if category['coverage']['reviewed_tasks'] else None
            rows += '<tr><td>'+html.escape(child['title'])+'</td><td class="numeric">'
            rows += percent(category['reliability']['observed'])+'</td><td class="numeric">'
            rows += percent(delivered)+'</td></tr>'
        rates_path = (model['harness_correction']['rates']['path'] if model.get('harness_correction')
                      else 'content-rates.json')
        body += panel('内容可靠率与'+target_label, '<div class="prose" data-ui-prose><p>已审内容可靠率 '
            +percent(r['observed'])+'；已确认'+target_label+' '+percent(d['confirmed'])+'。</p>'+interval+'</div><div class="table-wrap"><table class="compact rate-table">'
            '<thead><tr><th>子类</th><th class="numeric">已审内容可靠率</th><th class="numeric">已确认'+target_label+'</th>'
            '</tr></thead><tbody>'+rows+'</tbody></table></div><p class="panel-foot">'
            +source_link(Path(model['source_record']).parent/rates_path, page, '补审汇总 JSON ↗',root=root)
            +' · <a data-context-link href="../../method.html#content-rate-method">计算方法 →</a></p>')
    body += panel('分类贡献', '<div class="table-wrap"><table id="model-categories" class="compact"></table></div>',
        '贡献分 / 该项满分；相关变体在家族内聚合。')
    body += '<div class="equal-grid">'+panel('Lean · 自查计分', '<div class="table-wrap"><table id="model-selfcheck" class="compact"></table></div><p id="selfcheck-rule" class="panel-foot"></p><details class="selfcheck-comparison"><summary>比较三种计分口径</summary><div class="table-wrap"><table id="selfcheck-comparison" class="compact"></table></div></details>')
    rounds = ''
    for index in (1,2,3):
        row = (next(s for s in record['selfcheck_rounds'] if s['round']==index)
               if model.get('record_kind') in {'native_harness', 'paper_observation'} else
               next(s for s in record['records'] if s['id'] in
                    ('MG-C003:alignment:'+str(index), 'MG-C003:R'+str(index))))
        response = row.get('response')
        content = markdown.add(evidence_bytes(folder,response).decode()) if response else '未留存可读原答。'
        link = source_link(Path(model['source_record']).parent/response['path'],page,'原答文件 ↗',root=root) if response else ''
        rounds += '<details class="evidence-fold nested"><summary>R'+str(index)+' · 完整原答</summary><div class="prose">'+content+'<p>'+link+'</p></div></details>'
    alignment_path = next((s['path'] for s in record.get('evidence',[]) if s['path'] in ('reviews/alignment.json','alignment-review.json')),None)
    if alignment_path:
        rounds += '<p class="panel-foot">'+source_link(Path(model['source_record']).parent/alignment_path,page,'完整三轮审核与诊断依据 ↗',root=root)+'</p>'
    body += panel('整章对齐 · 固定三轮', '<div class="table-wrap"><table id="model-trajectory" class="compact"></table></div><details class="evidence-fold nested"><summary>展开三轮原答与审核</summary>'+rounds+'</details>', '92项义务，按最后规定轮次计分。')+'</div>'
    body += panel('公开题 · 逐题成绩与证据', '<div class="table-wrap"><table id="case-list" class="compact case-list"></table></div>',
        f"公开{data['policy']['scope']['public_tasks']}题；私有{data['policy']['scope']['private_tasks']}题计入合并成绩。")
    body += '<details class="panel evidence-fold"><summary>形式化初答 · 逐题核实数</summary><div class="table-wrap"><table id="model-formalization" class="compact"></table></div><p class="panel-foot">按初答封卷工程核对编译及语义对应。</p></details>'
    body += panel('可靠性审核', '<div id="model-penalties" class="metric-grid"></div><details class="nested evidence-fold"><summary>公开题的错误承诺与扣罚理由</summary><div id="model-findings" class="prose"></div></details>',
        '同根因扣罚去重；具体依据见逐题说明。')
    source = source_link(model['source_record'],page,'正式档案 ↗',root=root)
    harness_note = ('<p class="panel-foot">'+html.escape(model['harness']['note_marker']+' '+model['harness']['note_text'])+'</p>'
                    if model['harness'].get('note_text') else '')
    body += panel('Harness与工具', '<div class="prose"><p>'+html.escape(model['harness_display_name'])+'</p><p>'
        +html.escape(model['harness']['tool_usage'])+'</p></div>'+harness_note+'<details class="nested evidence-fold"><summary>运行版本与来源</summary>'
        '<div class="prose"><p>'+html.escape(model['harness']['detail'])+'</p><p>'+source+'</p></div></details>')
    if (model.get('record_kind') != 'paper_observation' and
            model['retry']['combined'].get('retry_summary', {}).get('slots_with_reruns')):
        first = []
        for mode in data['display_score_modes']:
            report = model['combined'] if mode['id'] == 'partial' else model[mode['id']]['single_attempt']
            value = report['metrics']['earned']['confirmed']
            first.append('—' if value is None else f'{value:.2f}')
        body += panel('重跑与来源备注', '<div class="prose"><p data-original>'
            +html.escape(model['retry']['note'])+'</p></div>'
            '<p class="panel-foot"><span>首答 MC / RMC / SMC：</span>'
            +'<span class="mono">'+' / '.join(first)+'</span> · '
            '<a data-context-link href="../../method.html">查看方法与来源 →</a></p>',
            id='retry-provenance')
    body += panel('下载当前口径', '<div class="downloads panel-downloads" id="downloads"></div><p class="panel-foot"><a data-context-link href="../../method.html">查看完整方法与数据说明 →</a></p>')
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
        correction = model.get('harness_correction')
        if correction:
            projection = json.loads(evidence_bytes(folder, correction['public_tasks']))
            corrected_claim = json.loads(evidence_bytes(folder, correction['claim_review']))['case']
            for condition in correction['affected_conditions']:
                model['public_claims'][condition] = [corrected_claim if row['case_id'] == 'HCH02' else row
                    for row in model['public_claims'][condition]]
        for cid in projection['public_case_ids']:
            entry = catalog[cid]
            evidence = {c: public_evidence(folder, record, cid, c,
                next(r for r in projection['views']['partial'][c]['tasks'] if r['case_id']==cid)) for c in CONDITIONS
                if not (correction and cid in correction['affected_cases'] and c in correction['affected_conditions'])}
            if correction and cid in correction['affected_cases']:
                for condition in correction['affected_conditions']:
                    review_source = descriptor(folder, correction['math_review'], role='source_review')
                    evidence[condition] = {
                        'sources': [descriptor(folder, correction['answer'], role='answer'), review_source,
                                    descriptor(folder, correction['claim_review'], role='claim_review')],
                        'review': json.loads(review_source['raw']), 'claim': corrected_claim,
                        'notes': ['因harness回传故障恢复的原答；原生ERROR与旧审核保留，按既有规则补审。'],
                        'submission_override': {'classification': 'active_final',
                                                'pending_original_record_review': False},
                        'recovered_original_reply': True,
                        'selected_record': cid + ':A1:recovered-original', 'source_row': {}}
            cases.append({'id':cid,'title':entry['title'],'category':entry['category'],
                'category_title':CATEGORY_TITLES.get(entry['category'],entry['category']),
                'views': {mode:{c:next(r for r in projection['views'][mode][c]['tasks'] if r['case_id']==cid)
                               for c in CONDITIONS} for mode in projection['views']}})
            path = 'models/'+model['id']+'/cases/'+cid+'.html'
            pages[path] = render_case(path, data, model, entry, projection, evidence, markdown, root)
        path = 'models/'+model['id']+'/index.html'
        pages[path] = render_model(path, data, model, cases, record, folder, markdown)
        del model['public_claims']
    pages['method.html'] = shell('method.html','方法与数据','评分、运行条件与审核方式',
        '<div data-lang-content="zh">'+(HERE/'templates/method-content.html').read_text()+'</div>'
        '<div data-lang-content="en" hidden>'+(HERE/'templates/method-content.en.html').read_text()+'</div>',
        compact_data(data),'method-results.js')
    return markdown.finish(pages)
