"""Shared UI shell for supplied axes and independently reviewed profiles."""
from html import escape


def render_panel(profile):
    """The selected edition payload supplies all values; no scores live in HTML."""
    if (not isinstance(profile, dict)
            or profile.get('schema') != 'math-gauge.mathematical-profile/v1'
            or profile.get('version') != '0.4.0'
            or profile.get('benchmark_version') != '1.1.0'):
        return ''
    description = '六轴独立评审 · 严格完成度取主榜SMC · 每轴0–100'
    note = '已结算空白计0；可核实的截止前内容按实际论证评估，未交卷仍影响SMC。区间与断线表示真正未知。'
    values = '数值与已结算范围'
    coverage = '六个独立评审轴各用35家族；严格完成度直接取规则选定答卷的正式SMC，沿用主榜权重与三轮自查规则。画像固定使用这组答卷，不随顶部显示口径切换。'
    definitions = ''.join('<div class="mp-axis-definition"><dt>' + escape(axis['label']['zh'])
                          + '</dt><dd>' + escape(axis['description']['zh']) + '</dd></div>'
                          for axis in profile.get('axes', []))
    return f'''<section class="panel mathematical-profile" id="mathematical-profile"
 aria-labelledby="mathematical-profile-title">
<div class="panel-head"><div><h2 id="mathematical-profile-title">数学画像</h2>
<p class="panel-desc" id="mathematical-profile-description">{description}</p></div>
<span class="mp-review-status" id="mathematical-profile-review">AI评审 · 人工审核待完成</span></div>
<div class="mp-body">
<div class="mp-toolbar">
<label id="mathematical-profile-continuation-control" class="mp-stage-switch" hidden>
<input id="mathematical-profile-continuation" type="checkbox" role="switch">
<span class="mp-switch-track" aria-hidden="true"></span><span id="mathematical-profile-continuation-label">含续答</span></label>
<div id="mathematical-profile-controls" class="mp-presets"></div>
<button id="mathematical-profile-picker" class="mp-preset mp-picker" type="button" aria-expanded="false"
 aria-controls="mathematical-profile-choices"><span id="mathematical-profile-picker-title">选择模型</span>
<span id="mathematical-profile-count" class="mp-count" aria-live="polite"></span></button>
</div>
<div id="mathematical-profile-choices" class="mp-choices" hidden></div>
<div class="mp-layout"><figure class="mp-figure" aria-labelledby="mathematical-profile-title">
<div id="mathematical-profile-chart" class="mp-chart"></div>
<figcaption id="mathematical-profile-note">{note}</figcaption></figure>
<div class="mp-legend-wrap"><div id="mathematical-profile-legend" class="mp-legend"></div>
<p id="mathematical-profile-focus-note" class="mp-focus-note">悬停或聚焦模型可突出曲线；点击可固定。</p></div></div>
<p id="mathematical-profile-empty" class="mp-empty" hidden>选择模型开始对照。</p>
<details class="mp-values" id="mathematical-profile-meanings">
<summary id="mathematical-profile-meanings-title">七轴含义与范围</summary>
<p class="mp-coverage-note" id="mathematical-profile-meanings-scope">六轴覆盖39道初答与3轮自查、固定35家族，不限六道命题拓展题。SMC使用正式主榜权重，整条自查占10%；论证高档要求原题核心成立，局部成果不能抵补核心缺口。</p>
<dl class="mp-axis-definitions" id="mathematical-profile-meanings-list">{definitions}</dl></details>
<details class="mp-values"><summary id="mathematical-profile-values-title">{values}</summary>
<p id="mathematical-profile-coverage-note" class="mp-coverage-note">{coverage}</p>
<div class="mp-table-wrap" tabindex="0"><table id="mathematical-profile-values" class="compact mp-table"></table></div></details>
</div></section>'''
