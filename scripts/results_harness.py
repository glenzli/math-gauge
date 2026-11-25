"""Display harness labels and scope-specific notes without changing archives."""
import html
import re


_SUPERSCRIPTS = str.maketrans('0123456789', '⁰¹²³⁴⁵⁶⁷⁸⁹')
_DIGITS = str.maketrans('⁰¹²³⁴⁵⁶⁷⁸⁹', '0123456789')
_DSH_NOTE = ('使用DeepSeek Harness（DSH）时，多道题因推理过程过长、'
             '耗尽最大输出预算而未能交卷，因此改用Codex CLI执行。')


def scoped_harness_notes(models):
    """Number retained explanations within this page/edition, not the archive."""
    from scripts.results_i18n import MESSAGES

    names, catalog = {}, {}
    for model in models:
        harness = model.get('harness', {})
        name = harness.get('name', '')
        native = model.get('record_kind') == 'native_harness' or name == 'Dot native harness'
        names[model['id']] = ('Unknown' if native else
            re.sub(r'[⁰¹²³⁴⁵⁶⁷⁸⁹†]+$', '', model.get('harness_display_name') or name))
        if native:
            text, english, priority = 'Dot原生独立运行方式', 'Dot’s independent native harness', 0
        elif name.startswith('AGY CLI') or not harness.get('note_text'):
            continue
        else:
            text = harness['note_text']
            if 'DeepSeek Harness' in text and name == 'Codex CLI':
                text = _DSH_NOTE
            english = harness.get('note_text_en') or MESSAGES.get(text, text)
            marker = harness.get('note_marker', '').translate(_DIGITS)
            priority = int(marker) if marker.isdecimal() else 1000
        key = (text, english)
        row = catalog.setdefault(key, dict(priority=priority, text=dict(zh=text, en=english), model_ids=[]))
        row['priority'] = min(row['priority'], priority)
        row['model_ids'].append(model['id'])
    notes = []
    for index, (_, row) in enumerate(sorted(catalog.items(), key=lambda item: (item[1]['priority'], item[0])), 1):
        marker = str(index).translate(_SUPERSCRIPTS)
        notes.append(dict(marker=marker, text=row['text'], model_ids=sorted(row['model_ids'])))
        for identifier in row['model_ids']:
            names[identifier] += marker
    return names, notes


def render_harness_notes(notes):
    """Keep static output bilingual; the browser replaces it for the chosen edition."""
    return ''.join('<p class="panel-foot" data-harness-note="'+html.escape(note['marker'], quote=True)+'">'
                   +html.escape(note['marker'])+' <span data-lang-content="zh">'
                   +html.escape(note['text']['zh'])+'</span><span data-lang-content="en" hidden>'
                   +html.escape(note['text']['en'])+'</span></p>' for note in notes)


def display_harness_labels(value):
    if isinstance(value, list):
        return [display_harness_labels(item) for item in value]
    if isinstance(value, dict):
        return {key: (re.sub(r'\s*·\s*(?:tclaude|tcodex)\b(?:\s+v?\d[\w.-]*)?', '', item, flags=re.I)
                      if key == 'model_label' and isinstance(item, str)
                      else display_harness_labels(item)) for key, item in value.items()}
    return value
