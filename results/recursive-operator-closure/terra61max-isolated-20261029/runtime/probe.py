from pathlib import Path
import json,sys
root=Path('/private/tmp/math-gauge-isolated-20261029')
tests=[]
positive=root/'input/task.md'
tests.append({'kind':'allowed','target':'input/task.md','passed':positive.read_bytes().startswith('# '.encode())})
for label,path in [
 ('reference','/Users/g4i/lab/math-gauge/drafts/recursive-operator-closure/author-review.md'),
 ('reference-lean','/private/tmp/math-gauge-reference-20261029/Core.lean'),
 ('memory','/Users/g4i/.codex/memories/MEMORY.md'),
 ('oet-project','/Users/g4i/lab/oet-dev'),
 ('old-results','/Users/g4i/lab/math-gauge/results/terra61max-calibration')]:
 try:
  p=Path(path)
  if label in {'oet-project','old-results'}: list(p.iterdir())
  else:p.read_bytes()
  tests.append({'kind':'denied','target':label,'passed':False})
 except PermissionError:
  tests.append({'kind':'denied','target':label,'passed':True,'errno':1})
 except OSError as e:
  tests.append({'kind':'denied','target':label,'passed':False,'error_type':type(e).__name__})
report={'status':'passed' if all(t['passed'] for t in tests) else 'failed','tests':tests}
(root/'runtime/isolation-probe.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
if report['status']!='passed':sys.exit(2)
