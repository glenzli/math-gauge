"""Read-only manuscript initiative observations within the research leaderboard."""
import hashlib
import html
import json
import math
import re
from pathlib import Path

from math_gauge.manuscript_surplus import ROOT_PATH, load_public, read_source, require


def load_observations(root, models):
    root = Path(root)
    path = root / ROOT_PATH / 'observations.json'
    if not path.is_file():
        return None
    index = json.loads(path.read_bytes())
    require(index.get('schema') == 'math-gauge.manuscript-observation-index/v1'
            and index.get('visibility') == 'public' and index.get('is_score') is False,
            'Invalid manuscript observation index')
    read_source(root, index['policy'])
    by_id, rows = {m['id']: m for m in models}, []
    for item in index['models']:
        raw = read_source(root, item['observation'])
        require(raw['model_id'] == item['model_id'] and raw['record_id'] == item['record_id'],
                'Observation identity differs from its index')
        model = by_id.get(item['model_id'])
        require(model is not None and Path(model['source_record']).parent.name == item['record_id'],
                'Observation is not bound to the selected main snapshot')
        result = load_public((root / item['observation']['path']).parent, root)
        require(result['source_record']['path'] == model['source_record'],
                'Observation source differs from the selected main result')
        rows.append({'id': model['id'], 'label': model['label'], 'logo': model['logo'], 'theme': model['theme'],
                     'observation': result, 'download': '../' + item['observation']['path']})
    require(len({r['id'] for r in rows}) == len(rows), 'Duplicate model in manuscript observations')
    return {'version': index['version'], 'kind': 'descriptive-observation', 'models': rows,
            'source': {'path': path.relative_to(root).as_posix(),
                       'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}}


def ordered_models(data):
    return sorted(data['models'], key=lambda r: (-r['observation']['counts']['confirmed_groups'],
                  r['observation']['counts']['total_groups'] is None, r['label']))


def quote_markup(value):
    # Preserve the displayed source text without trailing whitespace in generated HTML.
    return re.sub(r'[ \t]+(?=\r?$)', lambda match: ''.join(
        '&#32;' if c == ' ' else '&#9;' for c in match[0]), html.escape(value), flags=re.MULTILINE)


def public_evidence(data):
    parts = []
    for model in ordered_models(data):
        for case in model['observation']['public_cases']:
            passed = case['original_task']['strict_pass']
            completion = '未知' if passed is None else '通过' if passed else '未通过'
            body = ['<p>原任务SMC：' + completion + ' · <a data-context-link href="models/'
                    + html.escape(model['id'], quote=True) + '/cases/MG-MCP003.html">原任务详情 →</a></p>']
            if not case['candidates']:
                body.append('<p>暂无可审核原答。</p>')
            for candidate in case['candidates']:
                label = '核实计入' if candidate['observation_included'] else '未计入'
                body += ['<article class="initiative-evidence-item" data-original><h4>' + label + ' · '
                         + html.escape(candidate['title']) + '</h4><p>' + html.escape(candidate['observation_note']) + '</p>']
                for key, name in [('statement', '陈述'), ('scope_delta', '原任务之外的内容'),
                                  ('proof_review', '原数学核验'), ('nontrivial_step', '实质步骤')]:
                    body.append('<p><strong>' + name + '：</strong>' + html.escape(candidate[key]) + '</p>')
                for cite in candidate['citations']:
                    body.append('<details><summary>原答摘录</summary><p class="mono initiative-source">SHA256 '
                        + html.escape(cite['source_sha256']) + ' · bytes ' + str(cite['start_byte']) + '–'
                        + str(cite['end_byte']) + '</p><pre>' + quote_markup(cite['quote']) + '</pre></details>')
                body.append('</article>')
            body.append('<p><a href="' + html.escape(model['download'], quote=True) + '">观察记录 · JSON ↓</a></p>')
            parts.append('<details class="initiative-evidence" data-model-note="'
                + html.escape(model['id'], quote=True) + '"><summary>' + html.escape(model['label'])
                + ' · MG-MCP003</summary>' + ''.join(body) + '</details>')
    return ''.join(parts)


def count_chart(data, chart_renderer):
    """Use the leaderboard's layout with an observed-count axis, never a score."""
    maximum = max([1] + [m['observation']['counts']['confirmed_groups'] for m in data['models']])
    step = max(1, math.ceil(maximum / 6))
    axis_end = math.ceil(maximum / step) * step
    groups = []
    for model in ordered_models(data):
        counts, coverage = model['observation']['counts'], model['observation']['coverage']
        value, mid = counts['confirmed_groups'], html.escape(model['id'], quote=True)
        marker = '<sup aria-label="手稿题尚未测完">*</sup>' if counts['total_groups'] is None else ''
        color = html.escape(model['theme']['color'], quote=True)
        groups.append('<div class="initiative-bar-group" data-model-note="' + mid + '" style="--model-color:' + color + '">'
            '<div class="initiative-chart-model"><img alt="" src="' + html.escape(model['logo']['data_url'], quote=True) + '">'
            '<div><a data-context-link href="models/' + mid + '/index.html">' + html.escape(model['label'])
            + '</a><small><span>已审手稿</span> ' + str(coverage['reviewed']) + '/' + str(coverage['planned']) + '</small></div></div>'
            '<div class="initiative-metric-row"><div class="bar-track"><span class="initiative-bar" aria-hidden="true" style="width:'
            + f'{value / axis_end * 100:.8f}' + '%"></span></div><span class="initiative-value">' + str(value)
            + '<small data-lang-content="zh">组</small><small data-lang-content="en" hidden>'
            + ('group' if value == 1 else 'groups') + '</small>'
            + marker + '</span></div></div>')
    ticks = [{'position': value / axis_end * 100, 'label': str(value)} for value in range(0, axis_end + 1, step)]
    return chart_renderer(groups, 'initiative-chart-groups', '各模型已核实额外成果组数', ticks, 0)


def render_subboard(data, *, chart_renderer, controls=''):
    if not data:
        return ''
    rows = []
    for model in ordered_models(data):
        observation = model['observation']
        counts, coverage = observation['counts'], observation['coverage']
        marker = '<sup aria-label="手稿题尚未测完">*</sup>' if counts['total_groups'] is None else ''
        mid = html.escape(model['id'], quote=True)
        rows.append('<tr data-model-note="' + mid + '"><td><span class="initiative-model">'
            '<img alt="" src="' + html.escape(model['logo']['data_url'], quote=True) + '">'
            '<a data-context-link href="models/' + mid + '/index.html">' + html.escape(model['label'])
            + '</a></span></td><td class="initiative-count">' + str(counts['confirmed_groups']) + marker
            + '</td><td>' + str(coverage['reviewed']) + '/' + str(coverage['planned']) + '</td></tr>')
    return ('<details class="manuscript-observations view-board" data-board="initiative" id="research-initiative">'
        '<summary><span><strong>主动额外成果</strong><small>原任务未要求 · 手稿题观察</small></span>'
        '<span class="initiative-expand" aria-hidden="true">＋</span></summary>'
        '<div class="initiative-body"><div class="board-subhead"><span class="board-sort-static">按已核实组数排序</span><div class="board-toolbar">'+controls+'</div></div>'
        '<p class="board-empty" data-board-empty hidden>当前筛选下没有已测完的模型。</p>'
        '<p class="initiative-intro">统计模型主动交付、经核实的独立额外成果组。</p>'
        '<p class="initiative-caveat">组数描述主动扩展任务的行为。成果价值及扩展范围是否合适，取决于研究问题和用途。</p>'
        '<p class="initiative-meta">五道手稿题（公1／私4） · 首答A1</p>'
        '<figure class="initiative-figure" data-display-mode="groups"><figcaption>已核实额外成果组数</figcaption>'
        + count_chart(data, chart_renderer) + '</figure>'
        '<p class="initiative-foot">横轴为已核实成果组数。</p>'
        '<details class="initiative-coverage" data-display-mode="coverage"><summary>查看组数与审阅覆盖</summary><div class="table-wrap"><table class="compact initiative-table"><thead><tr><th>模型</th>'
        '<th>已核实额外成果组</th><th>已审手稿</th></tr></thead><tbody>' + ''.join(rows) + '</tbody></table></div></details>'
        '<p class="initiative-foot" id="initiative-pending-note">* 手稿题尚未测完，所列为已核实组数。</p>'
        '<p class="initiative-foot">同一独立成果去重为一组；必要证明、纠错及题目要求的拓展归入原题评分。</p>'
        '<p class="initiative-links"><a href="../protocol/manuscript-observations.md">观察规则 →</a>'
        '<a href="../docs/manuscript-observations.md">观察报告 →</a></p>'
        '<details class="initiative-public"><summary>公开题的成果依据</summary>'
        '<p class="initiative-meta">此处列公有手稿题的核验依据；图表组数为公私合计。</p>'
        + public_evidence(data) + '</details></div></details>')
