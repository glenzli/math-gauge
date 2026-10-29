#!/usr/bin/env python3
"""Fresh per-case Lean compilation and complete MathGauge kernel-axiom audit.

Only explicit case sources, the selected Lean standard library and package
caches from --dependency-root enter LEAN_PATH. No sibling output, source-side
olean, ambient LEAN_PATH or dependency-project build directory is reused.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

LEAN_VERSION = '4.29.1'
TOOLCHAIN = 'leanprover/lean4:v4.29.1'
MATHLIB_REV = '5e932f97dd25535344f80f9dd8da3aab83df0fe6'
DEFAULT_PROFILE = 'lean-4.29.1'
TAUCETI_PROFILE = 'lean-4.36.0-rc1-tauceti'
# These are trust profiles, not manifest-supplied package policies. Keep the
# legacy profile and its audit bytes stable for existing compilation evidence.
PROFILES = {
    DEFAULT_PROFILE: {'lean_version': LEAN_VERSION, 'toolchain': TOOLCHAIN,
                      'mathlib_revision': MATHLIB_REV, 'audit_template': 'audit.lean.in'},
    TAUCETI_PROFILE: {
        'lean_version': '4.36.0-rc1', 'toolchain': 'leanprover/lean4:v4.36.0-rc1',
        'mathlib_revision': '2cabef97b63d3275776b8b060d802de6a6fa1055',
        'tauceti_revision': 'ab0153c648bc0f1364ea268fc806793beb01473a',
        'audit_template': 'audit-4.36.lean.in',
        'packages': {
            'mathlib': '2cabef97b63d3275776b8b060d802de6a6fa1055',
            'TauCeti': 'ab0153c648bc0f1364ea268fc806793beb01473a',
            'plausible': 'c2d7840c65673533e15b499f25beecdc6227f7d8',
            'LeanSearchClient': '9d39f9bb0c30aa2f6200808805ff16e6ce950890',
            'importGraph': 'b3cc36c295aa5e3e3c0197b09a6556298e710447',
            'proofwidgets': '17137fad38a2cc782ff00b323a13c3a991d085ab',
            'aesop': '29c64c56cc38211d39b306db2df11701e3d3de11',
            'Qq': '6d26f8bb4b2bb78f929ad160feac508866821316',
            'batteries': '30691c775364967184547c94468bf6b5f25400fb',
            'Cli': '34d2efffcb6dc8d5f3537cf6a7f88bfaa999ec49',
        },
    },
}
ALLOWED_AXIOMS = frozenset(('propext', 'Classical.choice', 'Quot.sound'))
MODULE_RE = re.compile(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\Z')
HERE = Path(__file__).resolve().parent

class VerificationError(Exception):
    pass

def now():
    return datetime.now(timezone.utc).isoformat()

def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def load(path):
    return json.loads(Path(path).read_text(encoding='utf-8'))

def save(path, value):
    Path(path).write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')

def require(condition, message):
    if not condition:
        raise VerificationError(message)

def command(argv, cwd=None, env=None, timeout=120):
    result = subprocess.run(list(map(str, argv)), cwd=cwd, env=env, text=True,
                            capture_output=True, timeout=timeout)
    require(result.returncode == 0, f'Command failed ({result.returncode}): {argv[0]}: {result.stderr.strip()}')
    return result.stdout.strip()

def safe_relative(root, name):
    require(isinstance(name, str), 'Manifest path must be text')
    p = Path(name)
    require(not p.is_absolute() and '..' not in p.parts and str(p) == name, 'Unsafe manifest path: ' + name)
    full = (root / p).resolve()
    require(full.is_relative_to(root.resolve()) and full.is_file(), 'Missing or escaping source: ' + name)
    require(not (root / p).is_symlink(), 'Source symlinks are not accepted: ' + name)
    return full

def clean_lean(text):
    """Remove nested comments and string contents while preserving line breaks."""
    out = []; i = 0; depth = 0; string = False
    while i < len(text):
        pair = text[i:i+2]; ch = text[i]
        if depth:
            if pair == '/-': depth += 1; out.extend('  '); i += 2
            elif pair == '-/': depth -= 1; out.extend('  '); i += 2
            else: out.append('\n' if ch == '\n' else ' '); i += 1
        elif string:
            if ch == '\\' and i + 1 < len(text): out.extend('  '); i += 2
            elif ch == '"': string = False; out.append(' '); i += 1
            else: out.append('\n' if ch == '\n' else ' '); i += 1
        elif pair == '/-': depth = 1; out.extend('  '); i += 2
        elif pair == '--':
            end = text.find('\n', i)
            if end < 0: out.extend(' ' * (len(text)-i)); break
            out.extend(' ' * (end-i)); i = end
        elif ch == '"': string = True; out.append(' '); i += 1
        else: out.append(ch); i += 1
    return ''.join(out)

def source_imports(text):
    imports = []
    for match in re.finditer(r'^\s*(?:public\s+)?import\s+([^\n]+)', clean_lean(text), re.M):
        for name in match.group(1).split():
            require(bool(MODULE_RE.fullmatch(name)), 'Unsupported import syntax: ' + name)
            require(not re.match(r'(?:OET|FormalOET|OperatorEvolutionTheory)(?:\.|$)', name), 'Project-bound import forbidden: ' + name)
            imports.append(name)
    return imports

def profile_config(profile=DEFAULT_PROFILE):
    require(isinstance(profile, str) and profile in PROFILES, 'Unknown verification profile: ' + str(profile))
    return PROFILES[profile]

def manifest_profile(manifest):
    profile = manifest.get('verification_profile', DEFAULT_PROFILE)
    config = profile_config(profile)
    require(manifest.get('lean_toolchain') == config['toolchain'], 'Manifest toolchain is not pinned for profile ' + profile)
    require(manifest.get('mathlib_revision') == config['mathlib_revision'], 'Manifest Mathlib revision is not pinned for profile ' + profile)
    if 'tauceti_revision' in config:
        require(manifest.get('tauceti_revision') == config['tauceti_revision'], 'Manifest TauCeti revision is not pinned for profile ' + profile)
    else:
        require('tauceti_revision' not in manifest, 'TauCeti revision requires its fixed verification profile')
    return profile

def render_audit(modules, profile=DEFAULT_PROFILE):
    template = (HERE / profile_config(profile)['audit_template']).read_text(encoding='utf-8')
    require(template.count('{{IMPORTS}}') == template.count('{{MODULES}}') == 1, 'Invalid audit template')
    return template.replace('{{IMPORTS}}', '\n'.join('import ' + name for name in modules)).replace(
        '{{MODULES}}', '#[' + ', '.join(json.dumps(name) for name in modules) + ']')

def inspect_dependencies(dependency_root, lean_choice=None, profile=DEFAULT_PROFILE):
    config = profile_config(profile)
    root = Path(dependency_root).resolve()
    require(root.is_dir(), 'Dependency root does not exist')
    lock = root / 'lake-manifest.json'
    require(lock.is_file(), 'Dependency root has no lake-manifest.json')
    data = load(lock)
    packages = data.get('packages', [])
    require(isinstance(packages, list) and all(isinstance(p, dict) for p in packages), 'Invalid dependency package list')
    names = [p.get('name') for p in packages]
    require(all(isinstance(n, str) and MODULE_RE.fullmatch(n) and '.' not in n for n in names), 'Invalid package name')
    require(len(names) == len(set(names)), 'Duplicate dependency package name')
    mathlib = next((p for p in packages if p.get('name') == 'mathlib'), None)
    require(mathlib is not None and mathlib.get('rev') == config['mathlib_revision'], 'Dependency Mathlib revision is not the pinned revision')
    if 'packages' in config:
        require({p['name']: p.get('rev') for p in packages} == config['packages'], 'Dependency packages differ from the fixed profile whitelist')
        toolchain = root / 'lean-toolchain'
        require(toolchain.is_file() and toolchain.read_text(encoding='utf-8').strip() == config['toolchain'], 'Dependency root toolchain differs from the fixed profile')
    choice = str(lean_choice or shutil.which('lean') or '')
    require(bool(choice), 'Lean executable is unavailable; supply --lean')
    version = command([choice, '--version'], cwd=root)
    require(bool(re.search(r'\bversion ' + re.escape(config['lean_version']) + r'(?:,|\s|\))', version)), 'Expected Lean ' + config['lean_version'] + ': ' + version)
    prefix = Path(command([choice, '--print-prefix'], cwd=root)).resolve()
    lean = prefix / 'bin' / ('lean.exe' if os.name == 'nt' else 'lean')
    require(lean.is_file(), 'Resolved Lean installation is missing its executable')
    require(command([lean, '--version'], cwd=root) == version, 'Resolved Lean installation identity changed')
    package_dir = Path(data.get('packagesDir', '.lake/packages'))
    require(not package_dir.is_absolute() and '..' not in package_dir.parts, 'Unsafe packagesDir')
    if 'packages' in config:
        require(str(package_dir) == '.lake/packages', 'Fixed profile requires .lake/packages')
    paths = []; records = []; tracked_state = None
    for package in packages:
        name = package.get('name', '')
        require(bool(MODULE_RE.fullmatch(name)) and '.' not in name, 'Invalid package name')
        package_root = root / package_dir / name
        build = package_root / '.lake/build/lib/lean'
        require(package_root.is_dir(), 'Missing dependency checkout: ' + name)
        if name in ('mathlib', 'TauCeti'): require(build.is_dir(), 'Missing compiled dependency: ' + name)
        if 'packages' in config:
            actual_root = Path(command(['git', '--no-optional-locks', '-C', package_root, 'rev-parse', '--show-toplevel'])).resolve()
            require(actual_root == package_root.resolve(), 'Dependency is not its own pinned checkout: ' + name)
        head = command(['git', '--no-optional-locks', '-C', package_root, 'rev-parse', 'HEAD'])
        require(head == package.get('rev'), 'Dependency checkout differs from lockfile: ' + name)
        state = None
        if name == 'mathlib' or 'packages' in config:
            dirty = command(['git', '--no-optional-locks', '-C', package_root,
                             'status', '--porcelain', '--untracked-files=no'])
            diff = command(['git', '--no-optional-locks', '-C', package_root, 'diff', '--binary', 'HEAD'])
            state = {'clean': not dirty, 'status_porcelain': dirty, 'diff_sha256': hashlib.sha256(diff.encode('utf-8')).hexdigest(), 'diff_bytes': len(diff.encode('utf-8'))}
            if name == 'mathlib': tracked_state = state
            require(not dirty, name + ' tracked sources are modified; not clean pinned evidence: ' + json.dumps(state))
        if build.is_dir(): paths.append(build.resolve())
        records.append({'name': name, 'revision': head, 'build_library': str(build.resolve()), 'compiled_library_present': build.is_dir()})
        if 'packages' in config: records[-1]['tracked_state'] = state
    standard = prefix / 'lib/lean'
    require((standard / 'Lean/Util/CollectAxioms.olean').is_file(), 'Lean kernel audit dependency is missing')
    paths.append(standard)
    result = {'root': str(root), 'lockfile_sha256': digest(lock), 'mathlib_revision': config['mathlib_revision'],
            'lean': str(lean), 'lean_version': version, 'lean_sha256': digest(lean),
            'packages': records, 'mathlib_tracked_state': tracked_state, 'search_paths': list(map(str, paths)),
            'dependency_project_build_excluded': True, 'ambient_lean_path_excluded': True}
    # Preserve the legacy receipt shape for coverage-only evidence rebinding.
    if profile != DEFAULT_PROFILE:
        result.update(verification_profile=profile, tauceti_revision=config['tauceti_revision'])
    return result

def validate_case(manifest_path):
    manifest_path = Path(manifest_path).resolve(); root = manifest_path.parent
    manifest = load(manifest_path)
    require(manifest.get('schema') == 'math-gauge.formal-case/v1', 'Invalid formal manifest schema')
    cid = manifest.get('case_id', '')
    require(bool(re.fullmatch(r'MG-[RPF]\d{3}|MG-TEST-[A-Za-z0-9-]+', cid)), 'Invalid case id')
    profile = manifest_profile(manifest)
    frozen = manifest.get('frozen_inputs', {})
    require(set(frozen) == {'task.md', 'reference.md', 'rubric.json'}, 'Manifest must bind all three frozen case inputs')
    for filename, expected in frozen.items():
        path = safe_relative(root.parent, filename)
        require(digest(path) == expected, 'Frozen case input SHA256 mismatch: ' + filename)
    coverage = manifest.get('coverage', {})
    require(coverage.get('source') == 'COVERAGE.md', 'Manifest must bind COVERAGE.md')
    require(digest(safe_relative(root, 'COVERAGE.md')) == coverage.get('sha256'), 'Coverage SHA256 mismatch')
    modules = manifest.get('modules', [])
    require(isinstance(modules, list) and bool(modules), 'Explicit ordered modules are required')
    names = [row.get('module') for row in modules]
    require(all(isinstance(n, str) and MODULE_RE.fullmatch(n) for n in names), 'Invalid module identifier')
    require(len(names) == len(set(names)), 'Duplicate module in manifest')
    seen = set(); sources = []; all_external = set()
    for row in modules:
        name = row['module']; filename = row.get('source')
        require(filename == name.replace('.', '/') + '.lean', 'Module/source path mismatch: ' + name)
        path = safe_relative(root, filename)
        require(digest(path) == row.get('sha256'), 'Source SHA256 mismatch: ' + filename)
        text = path.read_text(encoding='utf-8')
        require(not re.search(r'\b(?:sorry|admit)\b', clean_lean(text)), 'Unproved placeholder in ' + filename)
        imports = source_imports(text)
        require(imports == row.get('imports'), 'Manifest imports differ from source: ' + filename)
        local = [x for x in imports if x in names]
        require(set(local).issubset(seen), 'Local import is missing or occurs later in module order: ' + filename)
        all_external.update(x for x in imports if x not in names)
        sources.append({'module': name, 'source': filename, 'sha256': row['sha256'], 'imports': imports, 'path': path})
        seen.add(name)
    audit = manifest.get('audit', {})
    require(audit.get('module') == 'CurrentAudit' and audit.get('source') == 'CurrentAudit.lean', 'Invalid current audit entry')
    path = safe_relative(root, audit['source'])
    expected_audit = render_audit(names, profile).encode('utf-8')
    require(path.read_bytes() == expected_audit and digest(path) == audit.get('sha256'), 'Current audit must exactly match shared generator and ordered case modules')
    all_external.update(('Lean.Util.CollectAxioms', 'Lean.PrivateName', 'Lean.Elab.Command'))
    return manifest, root, sources, path, all_external

def resolve_imports(imports, dependency):
    records = []
    for name in sorted(imports):
        relative = Path(*name.split('.')).with_suffix('.olean')
        matches = [Path(base) / relative for base in dependency['search_paths'] if (Path(base) / relative).is_file()]
        require(bool(matches), 'Missing compiled external import: ' + name)
        require(len(matches) == 1, 'Ambiguous compiled external import: ' + name)
        records.append({'module': name, 'olean': str(matches[0]), 'sha256': digest(matches[0])})
    return records

def verify_case(manifest_path, dependency, output):
    manifest, original, sources, audit_source, imports = validate_case(manifest_path)
    profile = manifest_profile(manifest)
    require(dependency.get('verification_profile', DEFAULT_PROFILE) == profile,
            'Manifest and dependency verification profiles differ')
    require(dependency['mathlib_revision'] == profile_config(profile)['mathlib_revision'],
            'Dependency Mathlib revision differs from the manifest profile')
    if profile == TAUCETI_PROFILE:
        require(dependency.get('tauceti_revision') == profile_config(profile)['tauceti_revision'],
                'Dependency TauCeti revision differs from the manifest profile')
    cid = manifest['case_id']; output = Path(output) / cid
    output.mkdir(exist_ok=False)
    staged = output / 'sources'; build = output / 'oleans'; logs = output / 'logs'
    for path in (staged, build, logs): path.mkdir()
    report = {'schema': 'math-gauge.formal-verification/v1', 'case_id': cid, 'started_utc': now(),
              'status': 'running', 'manifest_sha256': digest(manifest_path),
              'dependency': dependency, 'frozen_inputs': manifest['frozen_inputs'], 'coverage': manifest['coverage'], 'modules': [], 'audit': None,
              'fresh_output': True, 'source_side_oleans_reused': False,
              'sibling_case_outputs_used': False, 'mathematical_or_human_review': None}
    save(output / 'report.json', report)
    try:
        report['direct_external_imports'] = resolve_imports(imports, dependency)
        for row in sources:
            dest = staged / row['source']; dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(row['path'], dest)
        shutil.copyfile(audit_source, staged / audit_source.name)
        env = os.environ.copy()
        env['LEAN_PATH'] = os.pathsep.join([str(build), *dependency['search_paths']])
        env.pop('LEAN_SRC_PATH', None)
        report['lean_path'] = env['LEAN_PATH']
        work = sources + [{'module': 'CurrentAudit', 'source': 'CurrentAudit.lean',
                           'sha256': digest(audit_source), 'path': audit_source}]
        for row in work:
            name = row['module']; source = staged / row['source']
            target = build / Path(*name.split('.')).with_suffix('.olean'); target.parent.mkdir(parents=True, exist_ok=True)
            argv = [dependency['lean'], '--root=' + str(staged), '-o', str(target), str(source)]
            started = time.monotonic()
            result = subprocess.run(argv, cwd=staged, env=env, capture_output=True, text=True, timeout=600)
            log = logs / (name.replace('.', '_') + '.log'); log.write_text(result.stdout + result.stderr, encoding='utf-8')
            item = {'module': name, 'source_sha256': row['sha256'], 'exit_code': result.returncode,
                    'elapsed_seconds': round(time.monotonic()-started, 3), 'argv': argv,
                    'log': str(log.relative_to(output)), 'log_sha256': digest(log)}
            if target.exists(): item['olean_sha256'] = digest(target)
            require(digest(row['path']) == row['sha256'] == digest(source), 'Source changed during verification: ' + name)
            if name == 'CurrentAudit':
                text = log.read_text(encoding='utf-8')
                declarations = [json.loads(x) for x in re.findall(r'MATH_GAUGE_DECL (\{[^\r\n]*\})', text)]
                summaries = [json.loads(x) for x in re.findall(r'MATH_GAUGE_AUDIT_SUMMARY (\{[^\r\n]*\})', text)]
                report['audit'] = {'command': item, 'declarations': declarations,
                                   'summary': summaries[0] if len(summaries) == 1 else None,
                                   'all_mathgauge_constants_including_private': True,
                                   'dependency_traversal': ('Complete union of every root via Lean.CollectAxioms with a shared visited set'
                                       if profile == DEFAULT_PROFILE else 'Union of public Lean.collectAxioms results for every audited root'),
                                   'allowed_axioms': sorted(ALLOWED_AXIOMS)}
                save(output / 'declarations.json', declarations)
                require(result.returncode == 0, 'Kernel audit failed; see ' + str(log))
                require(len(summaries) == 1 and summaries[0].get('passed') is True, 'Current audit summary missing or failed')
                require(len(declarations) > 0 and len(declarations) == summaries[0]['declaration_count'], 'Audit root inventory is incomplete')
                require(len({x['name'] for x in declarations}) == len(declarations), 'Duplicate audit root')
                require(not (set(summaries[0]['axiom_union']) - ALLOWED_AXIOMS), 'Forbidden axiom in dynamic audit')
                require(all(x['module'] in [r['module'] for r in sources] for x in declarations), 'Foreign module in audit inventory')
            else:
                report['modules'].append(item)
                require(result.returncode == 0, 'Compilation failed: ' + name + '; see ' + str(log))
            save(output / 'report.json', report)
            print(cid + ' ' + name + ': passed', flush=True)
        for row in sources:
            require(digest(row['path']) == row['sha256'], 'Source changed after compilation: ' + row['module'])
        validate_case(manifest_path)
        require(digest(manifest_path) == report['manifest_sha256'], 'Manifest changed during verification')
        report['status'] = 'passed'
    except (OSError, VerificationError, subprocess.SubprocessError, ValueError) as error:
        report['status'] = 'failed'; report['error'] = str(error)
    report['finished_utc'] = now(); save(output / 'report.json', report)
    return report

def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, action='append', required=True,
                        help='Case manifest; may be repeated for independent case outputs')
    parser.add_argument('--dependency-root', type=Path, required=True,
                        help='Existing pinned Lake dependency project; its own library is excluded')
    parser.add_argument('--lean', type=Path, help='Optional Lean binary or elan shim')
    parser.add_argument('--out', type=Path, required=True, help='New output root; must not exist')
    args = parser.parse_args(argv)
    out = args.out.resolve()
    if out.exists(): parser.error('--out must be a fresh, nonexistent directory')
    out.mkdir(parents=True)
    report = {'started_utc': now(), 'status': 'running', 'case_reports': [], 'all_outputs_fresh': True}
    save(out / 'report.json', report)
    try:
        validated = [validate_case(p) for p in args.manifest]
        ids = [m[0]['case_id'] for m in validated]
        require(len(ids) == len(set(ids)), 'Repeated case id')
        profiles = {manifest_profile(m[0]) for m in validated}
        require(len(profiles) == 1, 'Cannot mix verification profiles in one invocation')
        dependency = inspect_dependencies(args.dependency_root, args.lean, profiles.pop())
        for manifest in args.manifest:
            case = verify_case(manifest, dependency, out)
            report['case_reports'].append({'case_id': case['case_id'], 'status': case['status'],
                                           'report': case['case_id'] + '/report.json'})
            require(case['status'] == 'passed', 'Case verification failed: ' + case['case_id'])
        report['status'] = 'passed'
    except (OSError, VerificationError, subprocess.SubprocessError, ValueError, StopIteration) as error:
        report['status'] = 'failed'; report['error'] = str(error)
        print(str(error), file=sys.stderr)
    report['finished_utc'] = now(); save(out / 'report.json', report)
    return 0 if report['status'] == 'passed' else 1

if __name__ == '__main__':
    raise SystemExit(main())
