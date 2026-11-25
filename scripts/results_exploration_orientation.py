"""Standalone collapsed exploration-orientation shell and static download links."""
from math_gauge.exploration_orientation import attach_public, load_public, encoded, validate_component

def render_panel(component):
    if component is None:
        return ''
    if component.get('edition') != '1.3.0':
        raise ValueError('Exploration orientation is a current1.3only component')
    return '<details id="exploration-orientation" class="exploration-orientation" data-assessment-only="1.3.0">\n<summary><span data-eo="summary">探索取向 / 研究方式，不计总分</span></summary>\n<div class="eo-body">\n<p class="eo-context" data-eo="context">含受邀推进；只描述本次研究选择，不代表能力或稳定偏好。</p>\n<div class="eo-picker" role="group" aria-label="选择最多三个模型" data-eo="picker"></div>\n<p class="eo-empty" data-eo="empty" hidden>选择最多三个模型开始对照。</p>\n<div class="eo-comparison"><div class="eo-chart" data-eo="chart"></div><div class="eo-organizing" data-eo="values"></div></div>\n<div class="eo-legend" data-eo="legend"></div>\n<p class="eo-scale" data-eo="scale">0 本次未观察 · 1 偶发探针 · 2 局部路线 · 3 持续主线 · 4 中心策略。缺口不按0处理。</p>\n<details class="eo-support"><summary data-eo="support-title">跨题补证</summary><div data-eo="support"></div></details>\n<p class="eo-links"><a href="../protocol/exploration-orientation.md" data-eo="method-link">方法与边界</a><span aria-hidden="true"> · </span><a href="versions/1.3.0/downloads/exploration-orientation.json" data-eo="json-link">下载数据</a><span class="eo-review" data-eo="review">AI评审 · 人工审核待完成</span></p>\n</div></details>'

def download_files(component):
    if component is None:
        return {}
    validate_component(component)
    return {'versions/1.3.0/downloads/exploration-orientation.json': encoded(component).decode('utf-8')}
__all__ = ['attach_public', 'load_public', 'render_panel', 'download_files']
