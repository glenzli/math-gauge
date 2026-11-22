#!/usr/bin/env python3
"""Prepare local neutral-revision packages; never calls a model or credentials."""

import argparse
import json
from pathlib import Path
import sys
import zipfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from math_gauge.editions import NATIVE_MODEL, load_assessment_transition
from math_gauge.neutral_revision import (current_model_ids, load_model_selection, load_transition,
    source_assessment_edition)
from math_gauge.revision_harness import export_revision_bundle, _descriptor, _json_bytes


def selected_models(public_root):
    transition = load_transition(public_root)
    if transition is not None:
        return sorted(current_model_ids(transition))
    source = source_assessment_edition(public_root)
    old = load_assessment_transition(public_root, source)
    return sorted(set(old['calibrations']) | set(source.get('current_assessment_admissions', {})))


def export_all(public_root, private_root, destination, *, models=None):
    """Export only rule-selected tasks and publish a counts-only local summary."""
    public_root, private_root = Path(public_root).resolve(), Path(private_root).resolve()
    destination = Path(destination).resolve()
    if destination.exists():
        raise ValueError('Output must be a new local directory')
    if destination.is_relative_to(public_root):
        raise ValueError('Combined public/private packages cannot enter the public repository')
    available = selected_models(public_root)
    chosen = available if models is None else list(models)
    if len(chosen) != len(set(chosen)):
        raise ValueError('Repeated model selection')
    if not set(chosen) <= set(available):
        raise ValueError('Model is outside the selected assessment edition')
    destination.mkdir(parents=True)
    evaluator = destination / 'evaluator'
    evaluator.mkdir()
    rows, pending = [], []
    for model in chosen:
        selection = load_model_selection(public_root, private_root, model)
        # Never include this evaluator source-path/grade index in the handoff zip.
        (evaluator / (model + '.json')).write_bytes(_json_bytes({key: value for key, value in selection.items()
            if key != 'reports'}))
        excluded = model == 'glm-5.3-max'
        package = destination / 'models' / model
        manifest = export_revision_bundle(selection, public_root, private_root, package, exclude=excluded)
        archive = destination / 'archives' / (model + '.zip')
        archive.parent.mkdir(parents=True, exist_ok=True)
        with zipfile.ZipFile(archive, 'x', compression=zipfile.ZIP_DEFLATED) as stream:
            for path in sorted(package.rglob('*')):
                if path.is_file():
                    stream.writestr(model + '/' + path.relative_to(package).as_posix(), path.read_bytes())
        counts = manifest['counts']
        channel = 'native_external' if model == NATIVE_MODEL else 'gpt_prepared_only' if model.startswith(
            ('sol-', 'terra-', 'astra-')) else 'external_handoff'
        status = 'excluded_partial' if excluded else 'reused_completed' if counts['completed_reused'] == len(
            manifest['tasks']) and bool(manifest['tasks']) else 'prepared_pending_execution'
        row = dict(model_id=model, status=status, channel=channel, counts=counts,
            bundle_sha256=manifest['bundle_sha256'], archive=_descriptor(archive.name, archive.read_bytes()),
            package_path=str(package), archive_path=str(archive),
            total_bytes=sum(path.stat().st_size for path in package.rglob('*') if path.is_file()),
            candidate_calls=0)
        rows.append(row)
        if channel == 'gpt_prepared_only' and status == 'prepared_pending_execution':
            pending.append(dict(model_id=model, package_path=str(package),
                ready_task_ids=[task['task_id'] for task in manifest['tasks'] if task['status'] == 'ready'],
                source_unavailable_task_ids=[task['task_id'] for task in manifest['tasks'] if task['status'] == 'source_unavailable'],
                case_ids=[task['case_id'] for task in manifest['tasks'] if task['status'] == 'ready'],
                status='prepared_only_do_not_start', candidate_calls=0))
    index = dict(schema='math-gauge.neutral-revision-package-index/v1', local_only=True,
        candidate_calls=0, packages=rows, gpt_pending_execution=pending)
    (destination / 'operator-index.json').write_bytes(_json_bytes(index))
    (destination / 'gpt-pending-execution.json').write_bytes(_json_bytes(pending))
    public = dict(schema='math-gauge.neutral-revision-package-summary/v1', local_only=True,
        candidate_calls=0, models=[{key: row[key] for key in
            ('model_id', 'status', 'channel', 'counts', 'bundle_sha256')} for row in rows])
    (destination / 'public-counts-summary.json').write_bytes(_json_bytes(public))
    return index


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--public-root', type=Path, default=ROOT)
    parser.add_argument('--private-root', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--model', action='append')
    args = parser.parse_args()
    try:
        result = export_all(args.public_root, args.private_root, args.out, models=args.model)
    except (ValueError, OSError, KeyError) as error:
        parser.error(str(error))
    print(json.dumps(dict(output=str(args.out.resolve()), models=len(result['packages']),
        ready=sum(row['counts']['ready'] for row in result['packages']),
        reused=sum(row['counts']['completed_reused'] for row in result['packages']),
        source_unavailable=sum(row['counts']['source_unavailable'] for row in result['packages']),
        excluded=sum(row['counts']['excluded_partial'] for row in result['packages']), candidate_calls=0), indent=2))


if __name__ == '__main__':
    main()
