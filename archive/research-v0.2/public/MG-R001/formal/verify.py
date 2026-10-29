#!/usr/bin/env python3
"""Check these exact sources, optionally reusing a pinned dependency cache."""
import argparse, hashlib, json, os, re, subprocess
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('--dependency-project', type=Path)
args = parser.parse_args()
root = Path(__file__).resolve().parent
project = (args.dependency_project or root).resolve()
work = root / '.verification'
build = work / 'oleans'
logs = work / 'logs'
build.mkdir(parents=True, exist_ok=True)
logs.mkdir(parents=True, exist_ok=True)

def lake(*parts):
    return subprocess.check_output(['lake', 'env', *parts], cwd=project, text=True).strip()

lean = lake('which', 'lean')
version = subprocess.check_output([lean, '--version'], text=True).strip()
if 'version 4.29.1' not in version:
    raise SystemExit('Expected Lean 4.29.1: ' + version)
manifest = json.loads((project / 'lake-manifest.json').read_text())
mathlib = next(p for p in manifest['packages'] if p['name'] == 'mathlib')
expected_rev = '5e932f97dd25535344f80f9dd8da3aab83df0fe6'
if mathlib.get('rev') != expected_rev:
    raise SystemExit('Unexpected mathlib revision: ' + str(mathlib.get('rev')))
env = os.environ.copy()
env['LEAN_PATH'] = str(build) + os.pathsep + lake('printenv', 'LEAN_PATH')
modules = ['Core', 'Partial', 'Bounds', 'Spectral', 'Weighted', 'Counterexample',
           'Obstructions', 'Limits', 'Extra', 'Routes', 'Reference', 'Audit']
results = []
for module in modules:
    source = root / (module + '.lean')
    if re.search(r'\b(?:sorry|admit|axiom)\b', source.read_text()):
        raise SystemExit('Placeholder or extra axiom in ' + module)
    result = subprocess.run([lean, '--root=' + str(root), '-o',
        str(build / (module + '.olean')), str(source)], cwd=root, env=env,
        text=True, capture_output=True)
    log = result.stdout + result.stderr
    (logs / (module + '.log')).write_text(log)
    results.append({'module': module, 'exit_code': result.returncode,
        'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest()})
    print(module + ': ' + ('PASS' if result.returncode == 0 else 'FAIL'), flush=True)
    if result.returncode:
        raise SystemExit(log)
audit = (logs / 'Audit.log').read_text()
declarations = json.loads((root / 'declarations.json').read_text())
entries = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", audit)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
axiom_free = re.findall(r"'([^']+)' does not depend on any axioms", audit)
if {name for name, _ in entries} | set(axiom_free) != {d['name'] for d in declarations}:
    raise SystemExit('Axiom audit does not cover the declaration inventory')
for name, axioms in entries:
    if set(axioms.replace('\n', '').replace(' ', '').split(',')) - allowed:
        raise SystemExit('Unexpected axiom in ' + name)
report = {'status': 'passed', 'lean': version, 'mathlib_revision': expected_rev,
          'modules': results, 'audited_theorems': len(entries) + len(axiom_free),
          'axiom_union': sorted(allowed), 'placeholders': 0,
          'note': 'All modules rebuilt from these sources; dependency oleans reused.'}
(work / 'report.json').write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
print('Audited ' + str(len(entries) + len(axiom_free)) + ' theorems; no extra axioms.', flush=True)
