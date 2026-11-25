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
from math_gauge import independent_research_admitted_delivery as admitted
from math_gauge import legacy_taste_addition


POLICY_PATH = Path('protocol/mathematical-taste/v1.3.0/baseline-selection.json')
SCHEMA = 'math-gauge.independent-research-baseline-selection/v1'
CURRENT_PATH = 'versions/1.2.0/data.json'
ADDITIONS_PATH = POLICY_PATH.with_name('baseline-additions.json')
ADDITIONS_SCHEMA = 'math-gauge.independent-research-baseline-additions/v1'
PROFILE_FIELDS = ('mathematical_profile', 'mathematical_profile_baseline',
                  'mathematical_profile_revision', 'open_research', 'formalization_profile')


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


@dataclass(frozen=True)
class NativeAddition:
    identifier: str
    parent: dict
    raw: bytes
    data: dict
    index: dict
    index_raw: bytes
    index_ref: dict
    resource_ref: dict | None
    legacy_taste_ref: dict | None = None


def _same(left, right):
    return json.dumps(left, sort_keys=True) == json.dumps(right, sort_keys=True)


def _profile_rows(data, key):
    rows = data.get(key, {}).get('models', [])
    _need(len({row['id'] for row in rows}) == len(rows), 'Duplicate model profile in selected parent')
    return {row['id']: row for row in rows}


def select_additions(root, selected):
    """Validate an explicitly selected Carbon parent; never search or rebind old sources."""
    root = Path(root).resolve()
    path = root / ADDITIONS_PATH
    if not path.exists() and not path.is_symlink():
        return ()
    manifest = json.loads(_read(root, ADDITIONS_PATH.as_posix()))
    _need(selected.retained and set(manifest) == {'schema', 'version', 'edition', 'original_selection', 'additions',
                                               'new_candidate_calls', 'new_mathematical_judgments'}
          and manifest['schema'] == ADDITIONS_SCHEMA and manifest['version'] in ('0.1.0', '0.2.0')
          and manifest['edition'] == '1.3.0' and type(manifest['new_candidate_calls']) is int
          and manifest['new_candidate_calls'] == 0 and type(manifest['new_mathematical_judgments']) is int
          and manifest['new_mathematical_judgments'] == 0
          and isinstance(manifest['additions'], list) and len(manifest['additions']) == 1,
          'Invalid explicit baseline addition selection')
    _descriptor(root, manifest['original_selection'], POLICY_PATH.as_posix())
    old, current = _models(selected.data), _models(json.loads(selected.current_raw))
    additions, seen = [], set(old)
    for row in manifest['additions']:
        fields = {'id', 'baseline', 'native_index', 'resources'}
        if manifest['version'] == '0.2.0': fields.add('legacy_taste')
        _need(set(row) == fields
              and row['id'] == admitted.MODEL and row['id'] not in seen,
              'Duplicate, withdrawn or unselected added model')
        raw, data = admitted.baseline(root, row['baseline'])
        parents = _models(data)
        _need(row['id'] in parents and row['id'] in current and set(old) <= set(parents)
              and _same(parents[row['id']], current[row['id']]), 'Added model differs from its actual current 1.2 parent')
        for identifier, model in old.items():
            _need(_same(model, parents[identifier]), 'New parent modified a retained research model: ' + identifier)
        for key in ('policy', 'strict_policy', 'score_mode_catalog', 'attempt_conditions'):
            _need(_same(selected.data.get(key), data.get(key)), 'New parent changed a shared base policy')
        for key in PROFILE_FIELDS:
            before, after, published = (_profile_rows(v, key) for v in (selected.data, data, json.loads(selected.current_raw)))
            _need(all(_same(before.get(mid), after.get(mid)) for mid in old),
                  'New parent changed a retained profile input: ' + key)
            _need(_same(after.get(row['id']), published.get(row['id'])), 'Added profile differs from its actual parent: ' + key)
        index_raw = _descriptor(root, row['native_index'], admitted.PUBLIC_PATH.as_posix())
        index = admitted.validate_public(json.loads(index_raw), policies=admitted.external.policy_bindings(root),
            baseline_hash=row['baseline']['sha256'], model_ids=[row['id']])
        _need(index['schema'] == admitted.SCHEMA and index['source_binding']['baseline'] == row['baseline']
              and index['cohort'] == [row['id']], 'Addition index selected a different parent or cohort')
        if row['resources'] is not None:
            from scripts import results_independent_research_resources as resources
            resource_raw = _descriptor(root, row['resources'], admitted.PUBLIC_PATH.with_name('gemini-4-carbon-medium-resources.json').as_posix())
            resources.validate_native_public(json.loads(resource_raw), index, hashlib.sha256(index_raw).hexdigest())
        legacy_ref = row.get('legacy_taste')
        if legacy_ref is not None:
            legacy_raw = _descriptor(root, legacy_ref, legacy_taste_addition.PUBLIC_PATH.as_posix())
            _, taste_policy_sha = legacy_taste_addition.strict.load_policy(root / legacy_taste_addition.strict.POLICY_PATH)
            legacy_taste_addition.validate_public(json.loads(legacy_raw), parent=row['baseline'], policy_sha256=taste_policy_sha)
        additions.append(NativeAddition(row['id'], row['baseline'], raw, data, index, index_raw,
                                        row['native_index'], row['resources'], legacy_ref))
        seen.add(row['id'])
    return tuple(additions)


def display_baseline(selected, additions):
    """Publication view only; each grade branch keeps its original source bytes."""
    if not additions:
        return selected.data
    # select_additions proved all retained model and profile inputs identical.
    # The additional parent's aggregate metadata covers the new profile rows;
    # exact old adoption bindings remain on the independent projection branch.
    data = copy.deepcopy(additions[0].data)
    data['models'] = copy.deepcopy(selected.data['models'])
    for addition in additions:
        data['models'].append(copy.deepcopy(_models(addition.data)[addition.identifier]))
    return data


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


def baseline_homepage(current_envelope, selected, root, *, display_data=None):
    """Project only the selected cohort, with its own timing sample and resources."""
    if not selected.retained:
        return copy.deepcopy(current_envelope)
    from scripts.results_presentation import project_payload
    from scripts.results_editions import chart_scenes
    from scripts.timing_reference import build_reference as build_time
    from scripts.cost_reference import build_reference as build_cost

    envelope = copy.deepcopy(current_envelope)
    selected_data = selected.data if display_data is None else display_data
    data = project_payload(selected_data)
    logos = {model['id']: model['logo'] for model in current_envelope['data']['models']}
    for model in data['models']:
        logo = logos.get(model['id'])
        _need(logo is not None and logo['sha256'] == model['logo']['sha256'],
              'Shared publication logo differs from the retained source identity')
        model['logo'] = copy.deepcopy(logo)
    data['chart_scenes'] = chart_scenes(selected_data)
    envelope['data'] = data
    extra = envelope.get('supplemental', {})
    if extra.get('timing-reference-data') is not None or extra.get('cost-reference-data') is not None:
        timing = build_time(root, display_data=selected_data)
        costs = build_cost(root, display_data=selected_data, timing_reference=timing)
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
