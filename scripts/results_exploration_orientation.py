"""Supplementary source links for the mathematical-profile exploration child."""
from math_gauge.exploration_orientation import attach_public, load_public, encoded, validate_component


def render_panel(component):
    if component is None:
        return ''
    if component.get('edition') != '1.3.0':
        raise ValueError('Exploration orientation is a current1.3only component')
    # The shared profile controller adopts this hidden supplement only after
    # validating and registering the current-edition exploration project.
    return '''<div id="exploration-orientation" class="mp-project-supplement" hidden>
<details class="eo-support"><summary data-eo="support-title">跨题补证</summary>
<p data-eo="support-note">其他题仅作补证，不进入雷达。</p>
<div class="mp-table-wrap" tabindex="0" data-eo="support"></div></details>
<p class="eo-links"><a href="../protocol/exploration-orientation.md" data-eo="method-link">方法与边界</a><span aria-hidden="true"> · </span><a href="versions/1.3.0/downloads/exploration-orientation.json" data-eo="json-link">下载数据</a></p>
</div>'''


def download_files(component):
    if component is None:
        return {}
    validate_component(component)
    return {'versions/1.3.0/downloads/exploration-orientation.json': encoded(component).decode('utf-8')}


__all__ = ['attach_public', 'load_public', 'render_panel', 'download_files']
