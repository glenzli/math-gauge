#!/usr/bin/env python3
"""Bind an explicitly listed author project; never invent coverage or run a model."""
import argparse
from pathlib import Path
import verify


def prepare(case_root, modules, profile=verify.DEFAULT_PROFILE):
    case_root = Path(case_root).resolve()
    root = case_root / 'formal'
    case, frozen = verify.author_frozen_inputs(case_root)
    config = verify.profile_config(profile)
    rows = []
    for name in modules:
        verify.require(bool(verify.MODULE_RE.fullmatch(name)), 'Invalid explicit module')
        source = name.replace('.', '/') + '.lean'
        path = verify.safe_relative(root, source)
        rows.append({'module': name, 'source': source, 'sha256': verify.digest(path),
                     'imports': verify.source_imports(path.read_text())})
    manifest = {'schema': 'math-gauge.formal-case/v2', 'case_id': case['id'],
                'case_version': case['version'], 'lean_toolchain': config['toolchain'],
                'mathlib_revision': config['mathlib_revision'], 'frozen_inputs': frozen,
                'coverage': {'source': 'COVERAGE.md', 'sha256': verify.digest(verify.safe_relative(root, 'COVERAGE.md'))},
                'alignment': {'source': 'alignment.json', 'sha256': verify.digest(verify.safe_relative(root, 'alignment.json'))},
                'modules': rows}
    if profile != verify.DEFAULT_PROFILE:
        manifest.update(verification_profile=profile)
        manifest.update({field: config[field] for field in verify.PROFILE_REVISION_FIELDS if field in config})
    verify.validate_author_alignment(root, manifest, case)
    audit = root / 'CurrentAudit.lean'
    audit.write_text(verify.render_audit(modules, profile, all_case_declarations=True))
    manifest['audit'] = {'module': 'CurrentAudit', 'source': audit.name,
                         'sha256': verify.digest(audit),
                         'root_selection': 'All constants from every explicitly listed local module, including private declarations',
                         'allowed_axioms': sorted(verify.ALLOWED_AXIOMS)}
    destination = root / 'manifest.json'
    verify.save(destination, manifest)
    verify.validate_case(destination)
    return destination


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', type=Path, required=True)
    parser.add_argument('--module', action='append', required=True, help='Repeat in dependency order; no automatic source discovery')
    parser.add_argument('--profile', choices=verify.PROFILES, default=verify.DEFAULT_PROFILE)
    args = parser.parse_args()
    print(prepare(args.case, args.module, args.profile))


if __name__ == '__main__':
    main()
