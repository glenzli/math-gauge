"""Edition adoption binds preserved answer identities without rewriting history."""
import hashlib
import json
from pathlib import Path
import re


def result_archive(edition):
    version = edition['version']
    adoption = edition.get('result_compatibility')
    if adoption is not None:
        source = adoption.get('source_benchmark_version')
        if (not isinstance(source, str) or not re.fullmatch(r'\d+\.\d+\.\d+', source)
                or adoption.get('archive_root') != 'results/v' + source
                or adoption.get('path') != f'releases/v{version}/compatibility.json'
                or adoption.get('new_candidate_calls') != 0
                or adoption.get('mathematical_judgments_changed') is not False):
            raise ValueError('Invalid edition compatibility boundary')
        return adoption['archive_root']
    if not re.fullmatch(r'\d+\.\d+\.\d+', version):
        raise ValueError('Invalid benchmark version')
    return 'results/v' + version


def verify_compatibility(root):
    root = Path(root).resolve()
    edition = json.loads((root / 'benchmark.json').read_bytes())
    archive = result_archive(edition)
    adoption = edition.get('result_compatibility')
    if adoption is None:
        return edition
    manifest = json.loads((root / adoption['path']).read_bytes())
    if (manifest.get('schema') != 'math-gauge.edition-compatibility/v1'
            or manifest.get('benchmark_version') != edition['version']
            or manifest.get('source_benchmark_version') != adoption['source_benchmark_version']
            or manifest.get('archive_root') != archive
            or manifest.get('new_candidate_calls') != 0
            or manifest.get('mathematical_judgments_changed') is not False
            or manifest.get('counts') != dict(public_a1=25, private_a1=14, combined_a1=39,
                                             mathematical_families=35, c003_rounds=3)):
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
    selected = dict(edition['selected_result_record_ids'])
    selected['dot-underlying-model-20261108'] = '20261108'
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
    return edition
