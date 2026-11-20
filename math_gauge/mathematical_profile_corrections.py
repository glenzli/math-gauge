"""Append-only acceptance of three source-evidence consistency corrections."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path

from .evidence_retention import read_bytes, is_file
from .mathematical_profile import (
    _require, _text, _pointer, source_bytes, load_policy,
    _validate_proof_core, _validate_fidelity_core,
)

DIRECTORY = 'results/mathematical-profile-baseline-corrections/v0.1.0'
INDEX_PATH = DIRECTORY + '/index.json'
ADOPTION_PATH = DIRECTORY + '/adoption.json'
INDEX_EXTENSION_PATH = DIRECTORY + '/source-index-extension.json'
INDEX_SOURCE_PATH = 'results/mathematical-profiles/v0.4.0/index.json'
INDEX_ALIASES = {'public_base_index': 'public', 'private_base_index': 'private'}
MODELS = frozenset({'terra-6.1-max', 'sol-6.1-xhigh', 'terra-6.1-xhigh'})
CORRECTED_AXES = frozenset({'proof', 'fidelity', 'discernment'})


def _read(roots, ref):
    _require(ref.get('repository') in roots, 'Unknown baseline correction source repository')
    return source_bytes(roots[ref['repository']], ref)


def _verify_added_profile(roots, model_id, public_ref, private, policy, policy_sha256, contracts):
    """Reproduce an added profile through its existing source and scoring owners."""
    from .mathematical_profile import ProfileInputs, project_public
    from .scoring import score_mathematical_profile
    from .current_results import selected_current_record_paths
    from .current_assessment_admissions import selections
    from .editions import load_assessment_transition

    prefix = 'results/mathematical-profiles/v0.4.0/' + model_id + '/'
    _require(isinstance(private, dict)
             and set(private) == {'review', 'source-bindings', 'score', 'public_projection'}
             and public_ref == private['public_projection']
             and public_ref.get('path') == prefix + 'profile.json',
             'Added profile must bind its own exact public/private projection')
    loaded = {}
    for key, filename in (('review', 'review.json'), ('source-bindings', 'source-bindings.json'),
                          ('score', 'score.json')):
        _require(private[key].get('path') == prefix + filename,
                 'Added profile source belongs to another model')
        loaded[key] = json.loads(source_bytes(roots['private'], private[key]))
    public = json.loads(source_bytes(roots['public'], public_ref))
    review, materials = loaded['review'], loaded['source-bindings']
    _require(review.get('model_id') == materials.get('model_id') == model_id,
             'Added profile substituted another model review')
    source = materials['sources']['public_source_record']
    _require(selected_current_record_paths(roots['public']).get(model_id) == source.get('path'),
             'Added profile source record is not independently selected')
    initial = selections(roots['public']).get(model_id)
    expected = initial or load_assessment_transition(roots['public'])['calibrations'].get(model_id)
    binding = materials['sources']['initial_assessment' if initial else 'calibration']
    _require(expected is not None and all(binding.get(k) == expected[k]
                                         for k in ('path', 'bytes', 'sha256')),
             'Added profile changed its independently selected assessment')
    inputs = ProfileInputs(review, policy, contracts, materials,
                           roots=roots, policy_sha256=policy_sha256)
    score = score_mathematical_profile(inputs)
    projected = project_public(score, policy=policy, policy_sha256=policy_sha256,
        private_review_sha256=private['review']['sha256'],
        private_materials_sha256=private['source-bindings']['sha256'],
        source_record=source, source_calibration=materials['sources'].get('calibration'),
        source_initial_assessment=materials['sources'].get('initial_assessment'))
    _require(score == loaded['score'] and projected == public,
             'Added profile does not reproduce from its independent review')


def _source_indices(roots, adoption_raw, sources):
    """Resolve only the two frozen index aliases through explicit append metadata.

    Current files are always read against their exact descriptors. An extension
    cannot serve as a fallback for missing, damaged or changed existing entries.
    """
    path = Path(roots['private']) / INDEX_EXTENSION_PATH
    if not is_file(path):
        return {alias: json.loads(_read(roots, sources[alias])) for alias in INDEX_ALIASES}
    extension = json.loads(read_bytes(path))
    fixed = dict(schema='math-gauge.mathematical-profile-source-index-extension/v1',
        version='0.1.0', benchmark_version='1.2.0', source_profile_version='0.4.0',
        post_observation=True, original_bytes_rewritten=False, new_candidate_calls=0)
    _require(set(extension) == set(fixed) | {'original_adoption_sha256', 'original_sources',
                'retained_sources', 'current_sources', 'added_models'}
             and all(type(extension.get(k)) is type(v) and extension[k] == v for k, v in fixed.items())
             and extension['original_adoption_sha256'] == hashlib.sha256(adoption_raw).hexdigest(),
             'Invalid explicit baseline source-index extension')
    for field in ('original_sources', 'retained_sources', 'current_sources'):
        _require(isinstance(extension[field], dict) and set(extension[field]) == set(INDEX_ALIASES),
                 'Index extension may relocate only the two original index aliases')
    old, current = {}, {}
    for alias, repository in INDEX_ALIASES.items():
        original = sources[alias]
        retained, active = extension['retained_sources'][alias], extension['current_sources'][alias]
        _require(extension['original_sources'][alias] == original
                 and original.get('repository') == active.get('repository') == retained.get('repository') == repository
                 and original.get('path') == active.get('path') == INDEX_SOURCE_PATH
                 and retained.get('path') == DIRECTORY + '/source-indices/' + repository + '.json'
                 and all(retained.get(k) == original[k] for k in ('bytes', 'sha256')),
                 'Index extension lost its exact immutable adoption snapshot')
        # Verify the current file first; damage must never cause a cold fallback.
        current[repository] = json.loads(_read(roots, active))
        old[repository] = json.loads(_read(roots, retained))
        _require(isinstance(current[repository].get('models'), dict)
                 and isinstance(old[repository].get('models'), dict)
                 and {k:v for k,v in current[repository].items() if k != 'models'}
                    == {k:v for k,v in old[repository].items() if k != 'models'}
                 and all(current[repository]['models'].get(mid) == entry
                         for mid, entry in old[repository]['models'].items()),
                 'Profile index extension changed original metadata or model entries')
    added = extension['added_models']
    _require(isinstance(added, list) and added
             and all(isinstance(mid, str) and mid and '/' not in mid and '\\' not in mid
                     and mid not in {'.', '..'} for mid in added)
             and added == sorted(set(added))
             and set(old['public']['models']) == set(old['private']['models'])
             and set(current['public']['models']) - set(old['public']['models'])
                == set(current['private']['models']) - set(old['private']['models']) == set(added),
             'Profile index extension must declare exactly the paired added models')
    policy, digest = load_policy(roots['public'])
    _require(old['private']['contracts']['sha256'] == policy['private_contract_sha256'],
             'Profile index extension changed the original task contracts')
    contracts = json.loads(source_bytes(roots['private'], old['private']['contracts']))
    for mid in added:
        _verify_added_profile(roots, mid, current['public']['models'][mid],
                              current['private']['models'][mid], policy, digest, contracts)
    return {alias: old[repository] for alias, repository in INDEX_ALIASES.items()}


def _evidence(value, sources, roots):
    if isinstance(value, dict):
        if {'source_id', 'pointer', 'quote'} <= set(value):
            _require(value['source_id'] in sources and _text(value['quote']), 'Unbound baseline audit evidence')
            ref = sources[value['source_id']]
            raw = _read(roots, ref)
            if ref['path'].endswith('.json'):
                selected = _pointer(json.loads(raw), value['pointer'])
                text = selected if isinstance(selected, str) else json.dumps(selected, ensure_ascii=False)
            else:
                _require(value['pointer'] == '', 'Raw baseline audit evidence needs an empty pointer')
                text = raw.decode()
            _require(value['quote'] in text, 'Baseline correction evidence differs from its original bytes')
        for child in value.values():
            _evidence(child, sources, roots)
    elif isinstance(value, list):
        for child in value:
            _evidence(child, sources, roots)


class BaselineCorrectionInputs:
    def __init__(self, raw, *, roots):
        data = json.loads(raw)
        fixed = dict(schema='math-gauge.mathematical-profile-baseline-correction-adoption/v1',
            version='0.1.0', benchmark_version='1.2.0', source_profile_version='0.4.0',
            condition='nonlogical_retry_3', post_observation=True, reviewer_kind='ai',
            human_review='pending', formal_comparison_eligible=False, new_candidate_calls=0,
            main_scores_modified=False, original_bytes_rewritten=False)
        _require(all(type(data.get(k)) is type(v) and data[k] == v for k,v in fixed.items())
                 and _text(data.get('reviewer_id')), 'Unsupported baseline correction acceptance')
        sources = data['sources']
        indices = _source_indices(roots, raw, sources)
        loaded = {key: indices[key] if key in INDEX_ALIASES else json.loads(_read(roots, ref))
                  for key,ref in sources.items()}
        policy, digest = load_policy(roots['public'])
        _require(sources['base_policy']['sha256'] == digest
                 and sources['public_base_index']['path'] == 'results/mathematical-profiles/v0.4.0/index.json'
                 and sources['private_base_index']['path'] == 'results/mathematical-profiles/v0.4.0/index.json',
                 'Baseline correction must bind the unchanged 0.4.0 policy and indices')
        corrections = data['corrections']
        _require(len(corrections) == 3 and {r['model_id'] for r in corrections} == MODELS
                 and len({r['id'] for r in corrections}) == 1,
                 'Baseline correction acceptance is limited to the three reviewed models')
        private_index = loaded['private_base_index']
        contracts = json.loads(source_bytes(roots['private'], private_index['contracts']))
        _require(private_index['contracts']['sha256'] == policy['private_contract_sha256'],
                 'Baseline correction task weights differ from the original profile')
        for row in corrections:
            mid = row['model_id']
            _require(set(row['axes']) == CORRECTED_AXES,
                     'Baseline correction cannot expand its task or axes')
            original = loaded['base_review:' + mid]
            expected = private_index['models'][mid]['review']
            _require(all(sources['base_review:' + mid][k] == expected[k] for k in ('path','bytes','sha256'))
                     and original['model_id'] == mid, 'Baseline correction borrowed another original review')
            original_row = next(r for r in original['tasks'] if r['id'] == row['id'])
            audit = loaded['audit:' + mid]
            bindings = json.loads(source_bytes(roots['private'],private_index['models'][mid]['source-bindings']))
            answer_hashes = {ref['sha256'] for alias,ref in bindings['sources'].items()
                             if alias == 'answer:' + row['id'] or alias.startswith('manuscript:' + row['id'] + ':')}
            _require(audit['model_id'] == mid and audit['id'] == row['id']
                     and audit['reviewer_kind'] == 'ai' and audit['human_review'] == 'pending'
                     and audit['advisory_only'] is True
                     and audit['sources']['old_profile']['sha256'] == expected['sha256']
                     and audit['original_answer_sha256'] in answer_hashes
                     and audit['verdict']['old_profile_inconsistent_with_own_bound_evidence'] is True
                     and audit['whole_original_answer_read'] is True
                     and audit['adopted_sources_independently_checked'] is True
                     and audit['official_scores_or_archive_changed'] is False
                     and audit['new_candidate_calls'] == 0,
                     'Baseline correction needs its independent full-source consistency audit')
            for ref in audit['sources'].values():
                _read(roots, ref)
            _evidence(audit, audit['sources'], roots)
            for axis, judgment in row['axes'].items():
                _require(judgment.get('from') == original_row['axes'][axis]['grade'] == 4
                         and type(judgment.get('to')) is int and judgment['to'] == 2
                         and _text(judgment.get('reason')) and judgment.get('evidence'),
                         'Baseline correction must preserve the accepted exact4to2 change')
                if axis == 'proof':
                    _validate_proof_core(dict(grade=judgment['to'], core_status=judgment.get('core_status')))
                if axis == 'fidelity':
                    _validate_fidelity_core(dict(grade=judgment['to'], core_scope_failure=judgment.get('core_scope_failure')))
                _evidence(judgment['evidence'], sources, roots)
        self.rows, self.contracts, self.data = deepcopy(corrections), contracts, deepcopy(data)
        self.sha256 = hashlib.sha256(raw).hexdigest()

    def for_model(self, model_id):
        return [deepcopy(row) for row in self.rows if row['model_id'] == model_id]


def load_private(public_root, private_root):
    path = Path(private_root) / ADOPTION_PATH
    if not is_file(path):
        return None
    return BaselineCorrectionInputs(read_bytes(path), roots=dict(public=public_root, private=private_root))


def apply_public(root, profile):
    """A current-edition display projection; the archived1.1 profile stays intact."""
    if not is_file(Path(root) / INDEX_PATH):
        return None
    index = json.loads(read_bytes(Path(root) / INDEX_PATH))
    _require(index.get('schema') == 'math-gauge.mathematical-profile-baseline-correction-index/v1'
             and set(index['models']) == MODELS and index.get('benchmark_version') == '1.2.0',
             'Invalid public baseline correction selection')
    result = deepcopy(profile)
    result.update(schema='math-gauge.mathematical-profile-baseline/v1', version='0.1.0',
                  benchmark_version='1.2.0', source_profile_version='0.4.0',
                  source_corrections=dict(path=INDEX_PATH, bytes=len(read_bytes(Path(root)/INDEX_PATH)),
                      sha256=hashlib.sha256(read_bytes(Path(root)/INDEX_PATH)).hexdigest()))
    for model in result['models']:
        if model['id'] not in index['models']:
            continue
        report = json.loads(source_bytes(root, index['models'][model['id']]))
        expected_keys = {'schema','version','benchmark_version','model_id','metrics','axis_delta',
            'corrected_tasks','corrected_axes','private_adoption_sha256','source_base_profile',
            'reviewer_kind','human_review','post_observation','new_candidate_calls','main_scores_modified'}
        _require(set(report) == expected_keys and report['model_id'] == model['id']
                 and report['private_adoption_sha256'] == index['private_adoption_sha256']
                 and report['source_base_profile'] == model['source'],
                 'Public baseline correction lost its exact original profile binding')
        baseline = json.loads(source_bytes(root, model['source']))
        _require(all(report['metrics'][axis] == baseline['metrics'][axis]
                     for axis in set(baseline['metrics']) - CORRECTED_AXES),
                 'Baseline correction changed an unreviewed axis or official SMC')
        model['metrics'] = deepcopy(report['metrics'])
        model['baseline_correction'] = deepcopy(index['models'][model['id']])
    return result
