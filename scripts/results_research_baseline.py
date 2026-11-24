"""Explicitly retain an adopted research baseline beside a newer base edition.

This publication owner selects existing bytes; it neither changes grades nor
permits an adopted source to follow a moving current-edition data file.
"""
import copy
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path, PurePosixPath
import stat

from math_gauge import independent_research_adoption as adoption


POLICY_PATH = Path('protocol/mathematical-taste/v1.3.0/baseline-selection.json')
SCHEMA = 'math-gauge.independent-research-baseline-selection/v1'
CURRENT_PATH = 'versions/1.2.0/data.json'


def _need(condition, message):
    if not condition:
        raise ValueError(message)


def _read(root, name):
    path = PurePosixPath(name)
    _need(isinstance(name, str) and str(path) == name and not path.is_absolute()
          and all(part not in ('', '.', '..') for part in path.parts), 'Unsafe retained baseline path')
    target = root
    for part in path.parts:
        target = target / part
        _need(not target.is_symlink(), 'Retained baseline paths cannot contain symlinks')
    try:
        mode = target.stat().st_mode
        _need(stat.S_ISREG(mode), 'Retained baseline source must be a regular file')
        return target.read_bytes()
    except OSError as error:
        raise ValueError('Missing or unreadable retained baseline source') from error


def _descriptor(root, value, expected_path):
    _need(isinstance(value, dict) and set(value) == {'path', 'bytes', 'sha256'}
          and value['path'] == expected_path and type(value['bytes']) is int and value['bytes'] >= 0,
          'Unexpected retained baseline descriptor')
    raw = _read(root, value['path'])
    _need(len(raw) == value['bytes'] and hashlib.sha256(raw).hexdigest() == value['sha256'],
          'Retained baseline source bytes differ from the explicit selection')
    return raw


def _models(data):
    _need(data.get('benchmark_version') == '1.2.0' and isinstance(data.get('models'), list),
          'Retained research baseline and current publication must both be 1.2')
    rows = {row['id']: row for row in data['models']}
    _need(len(rows) == len(data['models']), 'Duplicate model in baseline publication')
    return rows


@dataclass(frozen=True)
class BaselineSelection:
    raw: str
    data: dict
    current_raw: str
    retained: bool = False


def select_baseline(files, root, adopted):
    """Choose a reviewed explicit source, or preserve the original strict path.

    A missing selector never causes a search or fallback to a historical file.
    With a selector, every retained model must be identical in the newer edition.
    """
    root = Path(root).resolve()
    policy_path = root / POLICY_PATH
    if not policy_path.exists() and not policy_path.is_symlink():
        raw = files['data.json']
        return BaselineSelection(raw, json.loads(raw), raw)
    policy = json.loads(_read(root, POLICY_PATH.as_posix()))
    _need(set(policy) == {'schema', 'version', 'edition', 'selection', 'baseline', 'settled_index',
                         'current_base_publication', 'original_grade_bindings_modified',
                         'new_candidate_calls', 'new_mathematical_judgments'}
          and policy['schema'] == SCHEMA and policy['version'] == '0.1.0'
          and policy['edition'] == '1.3.0' and policy['selection'] == 'retained-original-adoption-baseline'
          and policy['original_grade_bindings_modified'] is False
          and type(policy['new_candidate_calls']) is int and policy['new_candidate_calls'] == 0
          and type(policy['new_mathematical_judgments']) is int and policy['new_mathematical_judgments'] == 0
          and policy['current_base_publication'] == dict(edition='1.2.0', data_path=CURRENT_PATH),
          'Invalid explicit research baseline selection')
    adoption.validate_public(adopted)
    binding = adopted['source_binding']
    baseline = policy['baseline']
    _need(isinstance(baseline, dict) and set(baseline) == {'edition', 'path', 'bytes', 'sha256'}
          and all(baseline[key] == binding[key] for key in ('edition', 'path', 'sha256')),
          'Explicit baseline selection differs from the original adoption binding')
    raw = _descriptor(root, {key: baseline[key] for key in ('path', 'bytes', 'sha256')}, binding['path'])
    selected_index = _descriptor(root, policy['settled_index'], adoption.PUBLIC_PATH)
    _need(json.loads(selected_index) == adopted, 'Explicit selection binds a different settled index')
    data = json.loads(raw)
    current_raw = files['data.json']
    if current_raw.encode('utf-8') == raw and CURRENT_PATH in files:
        current_raw = files[CURRENT_PATH]
    current = json.loads(current_raw)
    old_models, current_models = _models(data), _models(current)
    _need(old_models.keys() <= current_models.keys(), 'Current edition removed a retained research model')
    for identifier, model in old_models.items():
        _need(json.dumps(model, sort_keys=True) == json.dumps(current_models[identifier], sort_keys=True),
              'Current edition modified retained research model: ' + identifier)
    return BaselineSelection(raw.decode('utf-8'), data, current_raw, True)


def baseline_homepage(current_envelope, selected, root):
    """Project only the selected cohort, with its own timing sample and resources."""
    if not selected.retained:
        return copy.deepcopy(current_envelope)
    from scripts.results_presentation import project_payload
    from scripts.results_editions import chart_scenes
    from scripts.timing_reference import build_reference as build_time
    from scripts.cost_reference import build_reference as build_cost

    envelope = copy.deepcopy(current_envelope)
    data = project_payload(selected.data)
    logos = {model['id']: model['logo'] for model in current_envelope['data']['models']}
    for model in data['models']:
        logo = logos.get(model['id'])
        _need(logo is not None and logo['sha256'] == model['logo']['sha256'],
              'Shared publication logo differs from the retained source identity')
        model['logo'] = copy.deepcopy(logo)
    data['chart_scenes'] = chart_scenes(selected.data)
    envelope['data'] = data
    extra = envelope.get('supplemental', {})
    if extra.get('timing-reference-data') is not None or extra.get('cost-reference-data') is not None:
        timing = build_time(root, display_data=selected.data)
        costs = build_cost(root, display_data=selected.data, timing_reference=timing)
        for name, value, id_key in [('timing-reference-data', timing, 'id'),
                                    ('cost-reference-data', costs, 'model_id')]:
            if extra.get(name) is not None:
                if value is not None:
                    for model in value['models']:
                        model['logo'] = copy.deepcopy(logos[model[id_key]])
                        # Match the edition publisher's public companion shape;
                        # full revision resources retain their separate download.
                        model.pop('revision_resources', None)
                    for key in ('link_prefix', 'data_link'):
                        if key in extra[name]:
                            value[key] = extra[name][key]
                extra[name] = value
    return envelope


def retain_publication_sources(result, selected):
    """Keep the original source bytes and independently expose current 1.2 data."""
    if selected.retained:
        result[CURRENT_PATH] = selected.current_raw
        result['data.json'] = selected.raw
        catalog = json.loads(result['editions.json'])
        for edition in catalog['editions']:
            if edition['version'] == '1.2.0':
                edition['data'] = CURRENT_PATH
        result['editions.json'] = json.dumps(catalog, ensure_ascii=False, indent=2) + '\n'
