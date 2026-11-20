"""Edition adoption binds preserved answer identities without rewriting history."""
import hashlib
import json
from pathlib import Path
import re

from .catalog import relative_name
from .result_admissions import COUNTS, configured_admissions, verify_result_admissions


SOURCE_EDITION = '1.0.0'
ASSESSMENT_EDITION = '1.1.0'
ASSESSMENT_DIRECTORY = 'results/edition-reassessments/v1.1.0'
TRANSITION_PATH = ASSESSMENT_DIRECTORY + '/transition.json'
SOURCE_EDITION_PATH = ASSESSMENT_DIRECTORY + '/source-edition.json'
CALIBRATION_POLICY_PATH = 'protocol/theorem-extension-calibration.json'
NATIVE_MODEL = 'dot-underlying-model-20261108'
EDITION_FIELDS = {'version', 'status', 'source_state'}
TRANSITION_FIELDS = {'assessment_transition', 'source_task_version'}
INITIAL_ADMISSION_FIELD = 'current_assessment_admissions'


def _checked_descriptor(item, path=None):
    if (not isinstance(item, dict) or set(item) != {'path', 'bytes', 'sha256'}
            or type(item['bytes']) is not int or item['bytes'] < 0
            or not isinstance(item['sha256'], str) or not re.fullmatch(r'[0-9a-f]{64}', item['sha256'])
            or (path is not None and item['path'] != path)):
        raise ValueError('Assessment transition requires an exact source descriptor')
    relative_name(item['path'])
    return item


def _bound_bytes(root, item, path=None):
    from .records import evidence_bytes

    item = _checked_descriptor(item, path)
    try:
        return evidence_bytes(root, item)
    except ValueError as error:
        raise ValueError('Assessment transition source failed verification: ' + item['path']) from error


def _source_and_transition(root, edition):
    if edition is None:
        if root is None:
            raise ValueError('Assessment source requires a repository root or edition')
        edition = json.loads((Path(root) / 'benchmark.json').read_bytes())
    if not isinstance(edition, dict):
        raise ValueError('Invalid benchmark edition')
    if edition.get('version') == '1.2.0':
        if edition.get('neutral_revision_transition') is None:
            raise ValueError('Assessment transition is supported only for benchmark 1.1.0 unless its source-bound neutral revision transition is supplied')
        from .neutral_revision import source_assessment_edition
        edition = source_assessment_edition(root, edition)
    if edition.get('version') != ASSESSMENT_EDITION:
        if (TRANSITION_FIELDS | {INITIAL_ADMISSION_FIELD}).intersection(edition):
            raise ValueError('Assessment transition is supported only for benchmark 1.1.0')
        return edition, None
    if (root is None or edition.get('source_task_version') != SOURCE_EDITION
            or edition.get('status') != 'local-assessment-candidate'):
        raise ValueError('Benchmark 1.1.0 needs its local source assessment transition and repository root')

    transition = json.loads(_bound_bytes(root, edition.get('assessment_transition'), TRANSITION_PATH))
    fixed = dict(schema='math-gauge.assessment-transition/v1', version='0.1.0',
                 source_benchmark_version=SOURCE_EDITION, target_benchmark_version=ASSESSMENT_EDITION,
                 task_suite_version=SOURCE_EDITION, counts=COUNTS, post_observation=True,
                 new_candidate_calls=0, source_raw_bytes_rewritten=False, original_judgments_rewritten=False,
                 research_judgments_changed=True, human_review='pending', formal_comparison_eligible=False)
    if (not isinstance(transition, dict)
            or set(transition) != set(fixed) | {'source_edition', 'policy', 'calibrations'}
            or any(type(transition[k]) is not type(v) or transition[k] != v for k, v in fixed.items())):
        raise ValueError('Invalid named benchmark 1.0.0 to 1.1.0 assessment transition')

    source = json.loads(_bound_bytes(root, transition['source_edition'], SOURCE_EDITION_PATH))
    release = source.get('release') if isinstance(source, dict) else None
    if (not isinstance(source, dict) or source.get('schema') != 'math-gauge.benchmark-edition/v1'
            or source.get('version') != SOURCE_EDITION or source.get('status') != 'frozen-release'
            or not isinstance(source.get('result_compatibility'), dict)
            or not isinstance(release, dict) or release.get('version') != SOURCE_EDITION
            or release.get('status') != 'sealed'
            or TRANSITION_FIELDS.intersection(source)):
        raise ValueError('Assessment transition requires the sealed 1.0.0 source edition')
    current_contract = {k: v for k, v in edition.items() if k not in EDITION_FIELDS | TRANSITION_FIELDS | {INITIAL_ADMISSION_FIELD}}
    source_contract = {k: v for k, v in source.items() if k not in EDITION_FIELDS}
    if current_contract != source_contract:
        raise ValueError('Assessment transition changed the source selection, suite or scoring contract')

    selected = source.get('selected_result_models')
    records = source.get('selected_result_record_ids')
    calibrations = transition['calibrations']
    if (not isinstance(selected, list) or not selected
            or any(not isinstance(model, str) for model in selected)
            or not isinstance(records, dict) or len(selected) != len(records)
            or set(selected) != set(records) or NATIVE_MODEL in records
            or not isinstance(calibrations, dict) or set(calibrations) != set(records) | {NATIVE_MODEL}):
        raise ValueError('Assessment transition must bind every selected source model, including the native record')
    paths = [_checked_descriptor(item)['path'] for item in calibrations.values()]
    if (len(paths) != len(set(paths)) or {TRANSITION_PATH, SOURCE_EDITION_PATH}.intersection(paths)
            or any(not path.startswith(ASSESSMENT_DIRECTORY + '/') for path in paths)):
        raise ValueError('Assessment transition requires distinct calibration manifests in its edition archive')
    _bound_bytes(root, transition['policy'], CALIBRATION_POLICY_PATH)
    from .current_assessment_admissions import configured
    configured(root, edition, source)
    return source, transition


def source_edition(root, edition=None):
    """Resolve the unchanged source edition for selected records and material plans."""
    source, _ = _source_and_transition(root, edition)
    return source


def load_assessment_transition(root, edition=None):
    """Load the named assessment transition and verify its source and policy bindings."""
    _, transition = _source_and_transition(root, edition)
    return transition


def result_archive(edition, model=None, *, root=None):
    """Resolve an explicitly selected source edition, retaining legacy defaults.

    The named assessment-only edition resolves its retained results through
    the bound source snapshot. Execution editions keep their own archive.
    """
    edition = source_edition(root, edition)
    version = edition['version']
    if not isinstance(version, str) or not re.fullmatch(r'\d+\.\d+\.\d+', version):
        raise ValueError('Invalid benchmark version')
    sources = edition.get('selected_result_source_versions', {})
    if (not isinstance(sources, dict)
            or any(key not in edition.get('selected_result_models', []) or value != version
                   for key, value in sources.items())):
        raise ValueError('Invalid selected result source edition')
    admissions = configured_admissions(edition)
    adoption = edition.get('result_compatibility')
    if adoption is not None:
        source = adoption.get('source_benchmark_version')
        if (not isinstance(source, str) or not re.fullmatch(r'\d+\.\d+\.\d+', source)
                or adoption.get('archive_root') != 'results/v' + source
                or adoption.get('path') != f'releases/v{version}/compatibility.json'
                or adoption.get('new_candidate_calls') != 0
                or adoption.get('mathematical_judgments_changed') is not False):
            raise ValueError('Invalid edition compatibility boundary')
        if model in admissions:
            return admissions[model]['archive_root']
        if model not in sources:
            return adoption['archive_root']
    elif admissions:
        raise ValueError('Result admission requires an unchanged sealed compatibility manifest')
    return 'results/v' + version


def verify_compatibility(root):
    root = Path(root).resolve()
    edition = json.loads((root / 'benchmark.json').read_bytes())
    source, transition = _source_and_transition(root, edition)
    _verify_source_compatibility(root, source)
    if transition is not None:
        for item in transition['calibrations'].values():
            _bound_bytes(root, item)
    from .current_assessment_admissions import configured, load
    for model in configured(root, edition, source):
        load(root, model)
    return edition


def _verify_source_compatibility(root, edition):
    archive = result_archive(edition)
    adoption = edition.get('result_compatibility')
    if adoption is None:
        if configured_admissions(edition):
            raise ValueError('Result admission requires an unchanged sealed compatibility manifest')
        return
    manifest = json.loads((root / adoption['path']).read_bytes())
    if (manifest.get('schema') != 'math-gauge.edition-compatibility/v1'
            or manifest.get('benchmark_version') != edition['version']
            or manifest.get('source_benchmark_version') != adoption['source_benchmark_version']
            or manifest.get('archive_root') != archive
            or manifest.get('new_candidate_calls') != 0
            or manifest.get('mathematical_judgments_changed') is not False
            or manifest.get('counts') != COUNTS):
        raise ValueError('Edition adoption differs from its frozen contract')
    suites = manifest.get('source_suites')
    if suites is not None and (suites.get('public_current_sha256') != edition['public']['suite_sha256']
                              or suites.get('private_current_sha256') != edition['private']['suite_sha256']):
        raise ValueError('Edition adoption binds different current suites')
    bindings = manifest.get('source_bindings', [])
    paths = [row['path'] for row in bindings]
    if not paths or len(paths) != len(set(paths)):
        raise ValueError('Edition compatibility requires unique source bindings')
    for row in bindings:
        relative = Path(row['path'])
        path = root / relative
        if (relative.is_absolute() or '..' in relative.parts
                or any(p.is_symlink() for p in (path, *path.parents))
                or not path.is_file() or not path.resolve().is_relative_to(root)
                or hashlib.sha256(path.read_bytes()).hexdigest() != row['sha256']):
            raise ValueError('Edition compatibility source changed: ' + row['path'])
    fresh = edition.get('selected_result_source_versions', {})
    admissions = configured_admissions(edition)
    if set(admissions).intersection(r['model_id'] for r in manifest.get('selected_records', [])):
        raise ValueError('Admission cannot relocate a sealed legacy model')
    selected = {model: record_id for model, record_id in edition['selected_result_record_ids'].items()
                if model not in fresh and model not in admissions}
    selected[NATIVE_MODEL] = '20261108'
    adopted = manifest.get('selected_records', [])
    if {row['model_id']: row['record_id'] for row in adopted} != selected or len(adopted) != len(selected):
        raise ValueError('Edition compatibility must bind every selected record')
    bound = set(paths)
    for row in adopted:
        parent = f"{archive}/{row['model_id']}/{row['record_id']}/"
        if (row['record_path'] not in bound or not row['record_path'].startswith(parent)
                or len(row['score_paths']) != 6
                or any(p not in bound or not p.startswith(parent) for p in row['score_paths'])):
            raise ValueError('Edition compatibility must retain the original record and six views')
    for model in fresh:
        record_id = edition['selected_result_record_ids'].get(model)
        if (not re.fullmatch(r'[a-z0-9][a-z0-9._-]*', model)
                or not isinstance(record_id, str)
                or not re.fullmatch(r'[a-zA-Z0-9][a-zA-Z0-9._-]*', record_id)):
            raise ValueError('New edition record requires safe explicit identities')
        path = root / result_archive(edition, model) / model / record_id / 'record.json'
        if (not path.is_file() or not path.resolve().is_relative_to(root)
                or any(p.is_symlink() for p in (path, *path.parents))
                or json.loads(path.read_bytes()).get('benchmark_version') != fresh[model]):
            raise ValueError('New result record differs from its selected source edition')
    verify_result_admissions(root, edition, manifest)
