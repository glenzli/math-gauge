#!/usr/bin/env python3
"""Exercise this draft's real Suite projection; no model invocation or grading."""
import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
from math_gauge.catalog import Suite


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, help='Write a new report while preserving earlier evidence')
    args = parser.parse_args()
    base = Path(__file__).resolve().parents[1]
    suite = Suite.load(base)
    assert len(suite.cases) == 12
    assert all(c['status'] == 'draft' and c['review']['human'] == 'pending'
               for c in suite.cases.values())
    assert all(c['track'] == 'alignment' and c.get('candidate_instruction') == ''
               for c in suite.cases.values())
    kinds = Counter(c['task_kind'] for c in suite.cases.values())
    assert kinds == Counter(audit=6, generate=3, repair=3), kinds
    hidden = {p for c in suite.cases.values()
              for p in [c['reference'], c['rubric'], *c.get('evaluator_files', [])]}
    families = Counter(c['family_id'] for c in suite.cases.values())
    assert len(families) == 6 and set(families.values()) == {2}, families
    labels = Counter(json.loads((base/c['rubric']).read_text())['expected']
                     for c in suite.cases.values() if c['task_kind'] == 'audit')
    assert labels == Counter(aligned=3, misaligned=3), labels
    projections = []
    with tempfile.TemporaryDirectory(prefix='math-gauge-alignment-projection-') as tmp:
        for case in suite.select():
            cid = case['id']
            dest = Path(tmp)/cid
            request = suite.prepare(case, dest)
            assert (dest/'prompt.md').read_bytes() == (base/case['task']).read_bytes()
            expected = {'prompt.md', 'request.json', *(f['target'] for f in case['solver_files'])}
            assert {p.name for p in dest.iterdir()} == expected
            assert set(request) == {'schema', 'case_id', 'case_version', 'track', 'instruction', 'task', 'files'}
            assert not hidden.intersection(f['source'] for f in case['solver_files'])
            for f in case['solver_files']:
                assert digest(base/f['source']) == digest(dest/f['target'])
            assert not case['lean_checks'], 'Author fixed-file checks are separate from candidate grading'
            projections.append({'case_id':cid, 'task_kind':case['task_kind'],
                                'family_id':case['family_id'],
                                'exported_files':{name:digest(dest/name) for name in sorted(expected)},
                                'task_bytes_preserved':True, 'hidden_material_exported':False})
    snapshot = json.loads((base/'validation/initial-default-and-runner.json').read_text())
    changed = [name for name,h in snapshot['sha256'].items()
               if not (ROOT/name).is_file() or digest(ROOT/name) != h]
    report = {'schema':'math-gauge.alignment-projection-check/v1', 'status':'passed',
              'suite_sha256':suite.sha256, 'task_kind_counts':dict(kinds),
              'audit_labels':dict(labels), 'family_counts':dict(families),
              'projections':projections,
              'preexisting_default_or_runner_changes':changed,
              'baseline_note':'Changes by concurrent tasks, if any, require attribution; this check does not overwrite them.',
              'model_run':False, 'semantic_alignment_inferred':False}
    output = args.out or base/'validation/projection.json'
    if args.out and output.exists():
        raise FileExistsError('New report must not overwrite earlier evidence: ' + str(output))
    output.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({'status':report['status'],'cases':len(projections),
                      'task_kinds':dict(kinds),'families':len(families),
                      'baseline_changed_files':len(changed)},ensure_ascii=False))


if __name__ == '__main__':
    main()
