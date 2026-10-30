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
MOTIVIC_PROFILE = 'lean-4.34.1-motivic'
PROFILE_REVISION_FIELDS = ('tauceti_revision', 'motivic_revision', 'aglib_revision')
REVISION_LABELS = {'tauceti_revision': 'TauCeti', 'motivic_revision': 'Motivic', 'aglib_revision': 'Aglib'}
# These are trust profiles, not manifest-supplied package policies. Keep the
# legacy profile and its audit bytes stable for existing compilation evidence.
PROFILES = {
    MOTIVIC_PROFILE: {'lean_version': '4.34.1',
     'toolchain': 'leanprover/lean4:v4.34.1',
     'mathlib_revision': 'd13f23b723b8a846827a245b89c10fc7d3f11612',
     'motivic_revision': 'a6805c4a87cdfd7717dd7a94039246a167f15380',
     'aglib_revision': '2c34f185fa859e862661f939cd216b07bcccfb26',
     'audit_template': 'audit-4.34.lean.in',
     'packages': {'mathlib': 'd13f23b723b8a846827a245b89c10fc7d3f11612',
                  'plausible': '118aa17ee84656b8bd727fef7c458ee8c833385c',
                  'LeanSearchClient': 'ddf04cf3949fa556442341e87d47f9f6e6074707',
                  'importGraph': 'e928b72544873815af278d38681b31c0293588e3',
                  'proofwidgets': '106ff4fafc74ef4ac99d81dbf3ab399118f497a5',
                  'aesop': '355695d523e41d0554926416cba2a2b3544fbbc9',
                  'Qq': '6a489d9af5d0c47e5b259e2e8bcdfc1811b5a259',
                  'batteries': 'f2effa3d803fda822b1f97b806c47cf2adfbcbc2',
                  'Cli': 'e92c9f15fdfacc8536f31cfb3b7ad26c3c8cd204',
                  'Aglib': '2c34f185fa859e862661f939cd216b07bcccfb26',
                  'Motivic': 'a6805c4a87cdfd7717dd7a94039246a167f15380'},
     'lockfile_sha256': '2f9cab228ffc375abbe1a4783c1e3908aef990b4c1e97626e8cf3f0476f31253',
     'bind_external_source_closure': True},
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
    for match in re.finditer(r'^\s*(?:(?:public|meta)\s+)*import\s+(?:all\s+)?([^\n]+)', clean_lean(text), re.M):
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
    for field in PROFILE_REVISION_FIELDS:
        label = REVISION_LABELS[field]
        if field in config:
            require(manifest.get(field) == config[field],
                    'Manifest ' + label + ' revision is not pinned for profile ' + profile)
        else:
            require(field not in manifest, label + ' revision requires its fixed verification profile')
    return profile

def render_audit(modules, profile=DEFAULT_PROFILE, *, all_case_declarations=False):
    template = (HERE / profile_config(profile)['audit_template']).read_text(encoding='utf-8')
    if all_case_declarations:
        # Author projects may contain frozen background namespaces as well as
        # MathGauge. Audit every declaration owned by the explicit local closure.
        old = '(privateToUserName entry.1).toString.startsWith "MathGauge."'
        require(template.count(old) == 1, 'Audit template root selector changed')
        template = template.replace(old, '''let origin := match env.getModuleIdxFor? entry.1 with
      | some index => env.header.moduleNames[index]!.toString
      | none => env.mainModule.toString
    expectedModules.contains origin''')
        template = template.replace('every loaded MathGauge constant',
                                    'every constant owned by the explicit case modules')
        template = template.replace('no MathGauge constants were loaded',
                                    'no case-owned constants were loaded')
    require(template.count('{{IMPORTS}}') == template.count('{{MODULES}}') == 1, 'Invalid audit template')
    return template.replace('{{IMPORTS}}', '\n'.join('import ' + name for name in modules)).replace(
        '{{MODULES}}', '#[' + ', '.join(json.dumps(name) for name in modules) + ']')

def inspect_dependencies(dependency_root, lean_choice=None, profile=DEFAULT_PROFILE):
    config = profile_config(profile)
    root = Path(dependency_root).resolve()
    require(root.is_dir(), 'Dependency root does not exist')
    lock = root / 'lake-manifest.json'
    require(lock.is_file(), 'Dependency root has no lake-manifest.json')
    if 'lockfile_sha256' in config:
        require(digest(lock) == config['lockfile_sha256'], 'Dependency lockfile bytes differ from the fixed profile')
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
        if name in ('mathlib', 'TauCeti') or (profile == MOTIVIC_PROFILE and name in ('Motivic', 'Aglib')):
            require(build.is_dir(), 'Missing compiled dependency: ' + name)
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
        result.update(verification_profile=profile)
        result.update({field: config[field] for field in PROFILE_REVISION_FIELDS if field in config})
    return result

def author_input_base(case_root, case):
    """Resolve the explicit path convention without guessing from file existence."""
    convention = case.get('path_base', 'suite')
    require(convention in {'suite', 'case'}, 'Invalid author case path_base')
    return case_root if convention == 'case' else case_root.parent

def author_frozen_inputs(case_root):
    """The current case is the authority for the complete new-paper projection."""
    case_root = Path(case_root).resolve()
    case_path = safe_relative(case_root, 'case.json')
    case = load(case_path)
    require(case.get('schema') == 'math-gauge.case/v1', 'Invalid author case schema')
    base = author_input_base(case_root, case)
    names = {'case.json'}
    source_names = [case.get(k) for k in ('task', 'reference', 'rubric', 'group_contract')]
    source_names += [row.get('source') for row in case.get('solver_files', [])]
    for source in source_names:
        path = safe_relative(base, source)
        require(path.is_relative_to(case_root), 'Author input must belong to the exact case')
        names.add(path.relative_to(case_root).as_posix())
    return case, {name: digest(safe_relative(case_root, name)) for name in sorted(names)}

def validate_author_alignment(root, manifest, case):
    binding = manifest.get('alignment', {})
    require(binding.get('source') == 'alignment.json', 'Author manifest must bind alignment.json')
    path = safe_relative(root, 'alignment.json')
    require(digest(path) == binding.get('sha256'), 'Author alignment SHA256 mismatch')
    alignment = load(path)
    require(alignment.get('schema') == 'math-gauge.author-alignment/v1', 'Invalid author alignment schema')
    require(alignment.get('case_id') == case['id'] and alignment.get('case_version') == case['version'],
            'Author alignment identity differs from the current case')
    contract = load(safe_relative(author_input_base(root.parent, case), case['group_contract']))
    require(contract['id'] == case['id'] and contract['version'] == case['version'],
            'Author case and stage contract identities differ')
    stage_ids = {row['id'] for row in contract['stages']}
    items = alignment.get('items', [])
    require(isinstance(items, list) and all(isinstance(row, dict) for row in items), 'Invalid author alignment items')
    ids = [row.get('id') for row in items]
    require(len(ids) == len(set(ids)) and set(ids) == stage_ids,
            'Author alignment must cover every stage exactly once')
    modules = {row['module'] for row in manifest['modules']}
    for row in items:
        status = row.get('status')
        require(status in {'complete', 'partial', 'pending'}, 'Invalid author alignment status')
        for key in ('assumptions', 'quantifiers', 'domains', 'conclusions', 'representation'):
            value = row.get(key)
            require((isinstance(value, str) and bool(value.strip())) or
                    (isinstance(value, list) and bool(value) and
                     all(isinstance(x, str) and x.strip() for x in value)),
                    'Missing author semantic description: ' + row['id'] + '/' + key)
        dependencies = row.get('dependencies')
        require(isinstance(dependencies, list) and len(dependencies) == len(set(dependencies))
                and set(dependencies) <= stage_ids and row['id'] not in dependencies,
                'Invalid author stage dependencies')
        gaps = row.get('gaps')
        require(isinstance(gaps, list) and all(isinstance(g, str) and g.strip() for g in gaps),
                'Author alignment must explicitly list gaps')
        declarations = row.get('declarations')
        require(isinstance(declarations, list), 'Invalid author declaration list')
        for declaration in declarations:
            require(isinstance(declaration, dict) and declaration.get('module') in modules
                    and isinstance(declaration.get('name'), str) and declaration['name'].strip(),
                    'Author declaration must belong to an explicit local module')
        require(status != 'complete' or (bool(declarations) and not gaps),
                'Complete author stage needs declarations and no known gaps')
        require(status == 'complete' or bool(gaps), 'Incomplete author stage needs an explicit gap')
    # This is an evidence-structure check. A human or independent AI must still
    # inspect the actual definitions, theorem types and proofs for equivalence.
    return alignment

def validate_case(manifest_path):
    manifest_path = Path(manifest_path).resolve(); root = manifest_path.parent
    manifest = load(manifest_path)
    schema = manifest.get('schema')
    require(schema in {'math-gauge.formal-case/v1', 'math-gauge.formal-case/v2'}, 'Invalid formal manifest schema')
    cid = manifest.get('case_id', '')
    require(bool(re.fullmatch(r'MG-(?:[RPF]|G[RPF]|C)\d{3}|MG-TEST-[A-Za-z0-9-]+', cid)), 'Invalid case id')
    new_paper = bool(re.fullmatch(r'MG-(?:G[RPF]|C)\d{3}', cid))
    require(not new_paper or schema == 'math-gauge.formal-case/v2', 'New papers require the v2 author contract')
    profile = manifest_profile(manifest)
    frozen = manifest.get('frozen_inputs', {})
    if schema == 'math-gauge.formal-case/v2':
        case, expected_inputs = author_frozen_inputs(root.parent)
        require(case['id'] == cid and case['version'] == manifest.get('case_version'), 'Author manifest case identity mismatch')
        require(frozen == expected_inputs, 'Author manifest must bind the complete case, contract and candidate input bytes')
    else:
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
    expected_audit = render_audit(names, profile, all_case_declarations=schema == 'math-gauge.formal-case/v2').encode('utf-8')
    require(path.read_bytes() == expected_audit and digest(path) == audit.get('sha256'), 'Current audit must exactly match shared generator and ordered case modules')
    all_external.update(('Lean.Util.CollectAxioms', 'Lean.PrivateName', 'Lean.Elab.Command'))
    if schema == 'math-gauge.formal-case/v2':
        validate_author_alignment(root, manifest, case)
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

def bind_external_source_closure(imports, dependency):
    """Bind each reachable external source and all compiled module parts to fixed Git trees."""
    roots = []
    for package in dependency['packages']:
        build = Path(package['build_library']).resolve()
        source_root = build.parents[3]
        head = command(['git', '--no-optional-locks', '-C', source_root, 'rev-parse', 'HEAD'])
        require(head == package['revision'], 'External package changed during verification: ' + package['name'])
        tree = {}
        listing = command(['git', '--no-optional-locks', '-C', source_root,
                           'ls-tree', '-r', 'HEAD'])
        for line in listing.splitlines():
            metadata, path = line.split('\t', 1)
            mode, kind, blob = metadata.split()
            if kind == 'blob' and path.endswith('.lean'):
                tree[path] = (mode, blob)
        roots.append((package, build, source_root, tree))
    standard = Path(dependency['lean']).resolve().parent.parent / 'lib/lean'
    todo = list(imports)
    seen = set()
    rows = []
    while todo:
        name = todo.pop()
        if name in seen:
            continue
        seen.add(name)
        require(bool(MODULE_RE.fullmatch(name)), 'Invalid external module: ' + name)
        relative = Path(*name.split('.'))
        found = resolve_imports([name], dependency)[0]
        compiled = Path(found['olean']).resolve()
        owners = [root for root in roots if compiled.is_relative_to(root[1])]
        if not owners:
            require(compiled.is_relative_to(standard), 'Unowned external module: ' + name)
            rows.append(dict(found, package='lean-standard-library'))
            continue
        require(len(owners) == 1, 'Ambiguous external package: ' + name)
        package, build, source_root, tree = owners[0]
        source_name = relative.as_posix() + '.lean'
        require(source_name in tree and tree[source_name][0] in ('100644', '100755'),
                'External source is not tracked in its fixed tree: ' + name)
        source = source_root / source_name
        require(source.is_file() and not source.is_symlink(), 'Missing or linked external source: ' + name)
        data = source.read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        require(blob == tree[source_name][1], 'External source differs from its fixed Git tree: ' + name)
        direct_imports = source_imports(data.decode('utf-8'))
        parts = {}
        for suffix in ('.olean', '.olean.server', '.olean.private', '.ir', '.ir.sig'):
            part = build / (relative.as_posix() + suffix)
            if part.is_file():
                parts[suffix] = digest(part)
        rows.append(dict(found, package=package['name'], revision=package['revision'],
                         source=str(source), source_git_blob=blob,
                         source_sha256=hashlib.sha256(data).hexdigest(), imports=direct_imports,
                         compiled_parts=parts))
        todo.extend(direct_imports)
    rows.sort(key=lambda row: row['module'])
    encoded = json.dumps(rows, sort_keys=True, separators=(',', ':')).encode('utf-8')
    return {'module_count': len(rows), 'sha256': hashlib.sha256(encoded).hexdigest(), 'modules': rows}

def verify_case(manifest_path, dependency, output):
    manifest, original, sources, audit_source, imports = validate_case(manifest_path)
    profile = manifest_profile(manifest)
    require(dependency.get('verification_profile', DEFAULT_PROFILE) == profile,
            'Manifest and dependency verification profiles differ')
    require(dependency['mathlib_revision'] == profile_config(profile)['mathlib_revision'],
            'Dependency Mathlib revision differs from the manifest profile')
    for field in PROFILE_REVISION_FIELDS:
        if field in profile_config(profile):
            require(dependency.get(field) == profile_config(profile)[field],
                    'Dependency ' + REVISION_LABELS[field] + ' revision differs from the manifest profile')
    cid = manifest['case_id']; output = Path(output) / cid
    output.mkdir(exist_ok=False)
    staged = output / 'sources'; build = output / 'oleans'; logs = output / 'logs'
    for path in (staged, build, logs): path.mkdir()
    report = {'schema': 'math-gauge.formal-verification/v1', 'case_id': cid, 'started_utc': now(),
              'status': 'running', 'manifest_sha256': digest(manifest_path),
              'dependency': dependency, 'frozen_inputs': manifest['frozen_inputs'], 'coverage': manifest['coverage'], 'modules': [], 'audit': None,
              'fresh_output': True, 'source_side_oleans_reused': False,
              'sibling_case_outputs_used': False, 'mathematical_or_human_review': None}
    if manifest['schema'] == 'math-gauge.formal-case/v2':
        report.update(alignment=manifest['alignment'],
                      semantic_alignment_inferred=False,
                      local_declaration_audit_scope='all-explicit-case-modules')
    save(output / 'report.json', report)
    try:
        report['direct_external_imports'] = resolve_imports(imports, dependency)
        if profile_config(profile).get('bind_external_source_closure'):
            report['external_source_closure'] = bind_external_source_closure(imports, dependency)
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
                if manifest['schema'] == 'math-gauge.formal-case/v2':
                    actual = {(d['module'], d['name']) for d in declarations}
                    actual.update((d['module'], d['user_name']) for d in declarations)
                    alignment = load(original / 'alignment.json')
                    for row in alignment['items']:
                        for declaration in row['declarations']:
                            require((declaration['module'], declaration['name']) in actual,
                                    'Author alignment declaration missing from kernel inventory: ' + declaration['name'])
                    report['author_coverage'] = {
                        'items': len(alignment['items']),
                        'claimed_complete': sum(x['status'] == 'complete' for x in alignment['items']),
                        'declaration_inventory_verified': True,
                        'semantic_correctness_automatically_established': False}
            else:
                report['modules'].append(item)
                require(result.returncode == 0, 'Compilation failed: ' + name + '; see ' + str(log))
            save(output / 'report.json', report)
            print(cid + ' ' + name + ': passed', flush=True)
        for row in sources:
            require(digest(row['path']) == row['sha256'], 'Source changed after compilation: ' + row['module'])
        if profile_config(profile).get('bind_external_source_closure'):
            require(bind_external_source_closure(imports, dependency) == report['external_source_closure'],
                    'External source or compiled closure changed during verification')
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
