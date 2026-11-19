"""Shared UI shell for supplied axes and independently reviewed profiles."""
from html import escape


def render_panel(profile):
    """The selected edition payload supplies all values; no scores live in HTML."""
    if (not isinstance(profile, dict)
            or profile.get('schema') != 'math-gauge.mathematical-profile/v1'
            or profile.get('version') not in {'0.1.0', '0.2.0', '0.3.0'}
            or profile.get('benchmark_version') != '1.1.0'):
        return ''
    modern = profile['version'] != '0.1.0'
    description = '七个维度 · 同一35个数学家族 · 每轴0–100' if modern else '七个独立维度 · 每轴0–100'
    note = ('已结案的空白或无可核成果的失败计0；经核实的截止前内容可得部分分。区间与断线仅表示真正未运行或缺证据。'
            if modern else '逐轴比较；区间与断线表示证据缺口。')
    values = '数值与已结算范围' if modern else '数值与家族覆盖'
    coverage = ('各轴固定35个家族；已结算范围包括已确定的0分交付。未运行或缺证据保留区间，画像不随顶部计分口径切换。'
                if modern else '覆盖数按各轴统计，轴间不相加。')
    if profile['version'] == '0.3.0':
        coverage += '要求完成度按整题及完整三轮自查验收，必需目标不以部分成果抵补。'
    definitions = ''.join('<div class="mp-axis-definition"><dt>' + escape(axis['label']['zh'])
                          + '</dt><dd>' + escape(axis['description']['zh']) + '</dd></div>'
                          for axis in profile.get('axes', [])) if modern else ''
    return f'''<section class="panel mathematical-profile" id="mathematical-profile"
 data-assessment-only="1.1.0" aria-labelledby="mathematical-profile-title">
<div class="panel-head"><div><h2 id="mathematical-profile-title">数学画像</h2>
<p class="panel-desc" id="mathematical-profile-description">{description}</p></div>
<span class="mp-review-status" id="mathematical-profile-review">AI评审 · 人工审核待完成</span></div>
<div class="mp-body">
<div class="mp-toolbar"><div id="mathematical-profile-controls" class="mp-presets"></div>
<span id="mathematical-profile-count" class="mp-count" aria-live="polite"></span></div>
<details class="mp-model-picker"><summary id="mathematical-profile-picker-title">选择模型</summary>
<div id="mathematical-profile-choices" class="mp-choices"></div></details>
<details class="mp-values mp-meanings" id="mathematical-profile-meanings"{'' if modern else ' hidden'}>
<summary id="mathematical-profile-meanings-title">七轴含义与范围</summary>
<p class="mp-coverage-note" id="mathematical-profile-meanings-scope">七轴均纳入39道初答与3轮自查，固定为同一35个数学家族；相关变体与自查在家族内聚合。范围覆盖全卷，不限六道命题拓展题。</p>
<dl class="mp-axis-definitions" id="mathematical-profile-meanings-list">{definitions}</dl></details>
<div class="mp-layout"><figure class="mp-figure" aria-labelledby="mathematical-profile-title">
<div id="mathematical-profile-chart" class="mp-chart"></div>
<figcaption id="mathematical-profile-note">{note}</figcaption></figure>
<div class="mp-legend-wrap"><div id="mathematical-profile-legend" class="mp-legend"></div>
<p id="mathematical-profile-focus-note" class="mp-focus-note">悬停或聚焦模型可突出曲线；点击可固定。</p></div></div>
<p id="mathematical-profile-empty" class="mp-empty" hidden>选择模型开始对照。</p>
<details class="mp-values"><summary id="mathematical-profile-values-title">{values}</summary>
<p id="mathematical-profile-coverage-note" class="mp-coverage-note">{coverage}</p>
<div class="mp-table-wrap" tabindex="0"><table id="mathematical-profile-values" class="compact mp-table"></table></div></details>
</div></section>'''
