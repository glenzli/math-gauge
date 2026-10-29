#!/usr/bin/env python3
"""Recheck this frozen author batch using the shared verifier; no model or Lean invocation.
Use --write only when intentionally rebuilding this batch ledger after new review.
This checks evidence identity, not mathematical correctness.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,sys,re,subprocess
root=Path(__file__).resolve().parents[2];sys.path.insert(0,str(root/'scripts/formal'));import verify
out=root/'results/author-lean-20261030';reviews=out/'semantic-reviews'
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def rd(p):return json.loads(p.read_text())
def rel(p):return p.relative_to(root).as_posix()
def independent(c):
 cid=c.name;p=reviews/(cid+'.json')
 if cid in ['MG-GR103','MG-GR106']:
  p=reviews/'GR103-GR106.json';group=rd(p);d=next(x for x in group['cases'] if x['case_id']==cid);reviewer=group['reviewer'];hashes=d['reviewed_sha256']
 elif cid=='MG-GR101':
  p=reviews/(cid+'.md');s=p.read_text();assert 'Final semantic result: all six stages aligned; no open' in s
  tail=s.split('Revised identities:')[1];hashes=dict(re.findall(r'- ([^:\n]+): ([0-9a-f]{64})',tail));reviewer='author-lean-chapters';d={'status':'passed','items':[{'id':f'S{i}','status':'passed'} for i in range(1,7)]}
 else:
  d=rd(p);reviewer=d['reviewer'];hashes=next(d[k] for k in ['files','source_hashes','artifacts','reviewed_sha256'] if k in d)
 for name,expected in hashes.items():
  target=root/name if name.startswith(('drafts/','cases/')) else c/name
  assert target.is_file() and h(target)==expected,(cid,'review stale',name)
 status=d.get('status',d.get('verdict'))
 assert status in ['passed','pass','passed-no-open-findings','partial'],(cid,status)
 items=d.get('items',d.get('stage_reviews',[]))
 return {'path':rel(p),'sha256':h(p),'reviewer':reviewer,'status':status,'bound_files_rechecked':len(hashes),'stage_ids':[x['id'] for x in items]}
rows=[]
for suite in ['progressive-groups-20261030','chapter-exams-20261030']:
 for c in sorted((root/'drafts'/suite).glob('MG-*')):
  if not (c/'case.json').is_file():continue
  p=c/'formal/manifest.json';m,f,*_=verify.validate_case(p);r=rd(f/'verification-report.json');a=rd(f/'alignment.json');ds=rd(f/'declarations.json')
  assert r['manifest_sha256']==h(p) and r['status']=='passed',(c.name,'report')
  assert r['frozen_inputs']==m['frozen_inputs'] and r['alignment']==m['alignment'] and r['coverage']==m['coverage']
  assert r['fresh_output'] and not r['source_side_oleans_reused'] and not r['sibling_case_outputs_used']
  assert r['audit']['summary']['passed'] and not r['audit']['summary']['unexpected_axioms']
  assert set(r['audit']['summary']['axiom_union'])<=verify.ALLOWED_AXIOMS
  assert ds==r['audit']['declarations'] and len(ds)==r['audit']['summary']['declaration_count']
  assert len(r['modules'])==len(m['modules'])
  for b,t in zip(m['modules']+[m['audit']],r['modules']+[r['audit']['command']]):
   assert b['module']==t['module'] and b['sha256']==t['source_sha256'] and t['exit_code']==0
   assert h(f/t['log'])==t['log_sha256'],(c.name,'log',t['module'])
  names={(v['module'],v['name']) for v in ds}
  for item in a['items']:
   for dec in item['declarations']:assert (dec['module'],dec['name']) in names
  for name,expected in m['frozen_inputs'].items():
   data=subprocess.check_output(['git','show','6a6338f133ee312d8905ea9066f92dda14543e51:'+rel(c/name)],cwd=root)
   assert hashlib.sha256(data).hexdigest()==expected,(c.name,'frozen changed',name)
  ir=independent(c)
  assert set(ir['stage_ids'])=={x['id'] for x in a['items']},(c.name,'independent stage coverage')
  complete=[x['id'] for x in a['items'] if x['status']=='complete']
  partial=[{'id':x['id'],'gaps':x['gaps']} for x in a['items'] if x['status']!='complete']
  assert not partial or ir['status']=='partial',(c.name,'partial mislabeled')
  rows.append({'id':c.name,'case_version':m['case_version'],'case_path':rel(c),'formal_status':'complete' if not partial else 'partial','items':len(a['items']),'complete_items':complete,'incomplete_items':partial,'modules':len(m['modules']),'declarations':len(ds),'manifest_sha256':h(p),'alignment_sha256':h(f/'alignment.json'),'verification_report_sha256':h(f/'verification-report.json'),'declarations_sha256':h(f/'declarations.json'),'compile_status':'passed','compile_started_utc':r['started_utc'],'compile_finished_utc':r['finished_utc'],'verification_profile':verify.manifest_profile(m),'independent_semantic_review':ir,'human_review':'pending'})
assert len(rows)==43
result={'schema':'math-gauge.author-evidence-ledger/v1','checked_at_utc':datetime.now(timezone.utc).isoformat(),'baseline_commit':'6a6338f133ee312d8905ea9066f92dda14543e51','scope':'43 new papers only; compiler and independent semantic review are separate evidence','candidate_model_calls':0,'human_approved':0,'counts':{'papers':len(rows),'fully_formalized_papers':sum(x['formal_status']=='complete' for x in rows),'items':sum(x['items'] for x in rows),'complete_items':sum(len(x['complete_items']) for x in rows),'modules':sum(x['modules'] for x in rows),'declarations_with_per_case_repetition':sum(x['declarations'] for x in rows)},'checks':['Every v2 manifest validates current complete frozen inputs, modules, audit and alignment','Every fresh report matches the current manifest and each compiled module hash','Every saved compiler/audit log and declaration inventory matches its report','Only propext, Classical.choice and Quot.sound occur in the collected axiom closure','Every mapped declaration exists in the compiled local-module inventory','Each independent review file hash and every recorded reviewed-source hash matches current bytes','Every candidate/evaluator frozen input in manifests is byte-identical to the baseline commit','Incomplete obligations remain explicitly incomplete and do not count as full paper completion'],'cases':rows}
if '--write' in sys.argv:
 (out/'ledger.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
else:
 saved=rd(out/'ledger.json');saved.pop('checked_at_utc');current=dict(result);current.pop('checked_at_utc')
 assert saved==current, 'Saved ledger differs from rechecked evidence'
print(json.dumps({'status':'passed','counts':result['counts'],'candidate_model_calls':0,'fresh_compilation_repeated':False}))
