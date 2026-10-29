import argparse,collections,hashlib,json,re,sys,tarfile,tempfile
from pathlib import Path
R=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description='Offline material and receipt checks; never calls candidate models or Lean.')
parser.add_argument('--write-report',action='store_true',help='Refresh deterministic local validation receipts after all material checks.')
args=parser.parse_args()
sys.path.insert(0,str(R))
from math_gauge.catalog import Suite,candidate_message
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):return json.loads(p.read_text())
def put(p,d):
 if args.write_report:
  p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
 else:
  assert p.exists() and read(p)==d,(str(p),'validation receipt stale; inspect changes before --write-report')
counts=collections.Counter();suite_results=[];legacy={}
plan=read(P/'plan.json');selection=read(P/'selection.json');prompts=read(P/'prompts.json');schedule=read(P/'schedule.json')
assert plan['candidate_calls']==0 and plan['execution_authorized'] is False and plan['actual_results'] is None
assert plan['runtime_configuration_frozen'] is False
for rel,h in plan['files_sha256'].items(): assert sha((P/rel).read_bytes())==h,rel
for rel,h in plan['protocol_files_sha256'].items(): assert sha((R/rel).read_bytes())==h,rel
for sm in plan['suites']:
 root=R/sm['path'];s=Suite.load(root);assert s.sha256==sm['sha256'] and s.metadata['version']=='0.1.1'
 history=read(root/'history/0.1.0.json');archive=root/'history/0.1.0.tar.gz'
 assert sha(archive.read_bytes())==history['archive_sha256']
 with tarfile.open(archive) as tf: old={m.name:tf.extractfile(m).read() for m in tf.getmembers() if m.isfile()}
 with tempfile.TemporaryDirectory(prefix='math-gauge-history-verify-') as td:
  for n,b in old.items(): q=Path(td)/n;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b)
  assert Suite.load(td).sha256==history['suite_sha256'];counts['restored_historical_suites']+=1
 amendment=read(root/'reviews/editorial-amendment-0.1.1.json');entries={x['case_id']:x for x in amendment['cases']}
 requests=[]
 with tempfile.TemporaryDirectory(prefix='math-gauge-reliability-projection-') as td:
  for cid,c in s.cases.items():
   con=read(root/c['group_contract']);prev=json.loads(old[c['group_contract']]);a=entries[cid]
   assert c['version']==con['version']=='0.1.1'
   assert {k:v for k,v in con.items() if k!='version'}=={k:v for k,v in prev.items() if k!='version'}
   counts['unchanged_mathematical_contracts']+=1;counts['mandatory_units']+=len(con['stages'])
   for name in [c['reference'],c['rubric']]:assert (root/name).read_bytes()==old[name];counts['unchanged_reference_and_rubric_files']+=1
   assert sha((root/c['task']).read_bytes())==a['new_task_sha256']
   assert sha(old[c['task']])==a['old_task_sha256']
   assert sha((root/c['group_contract']).read_bytes())==a['new_contract_sha256']
   assert sha((root/cid/'case.json').read_bytes())==a['case_sha256']
   assert sha((root/cid/'review.json').read_bytes())==a['review_sha256']
   receipt=read(root/a['cleanup_receipt']);batch=a['cleanup_receipt'].split('-')[-1][0]
   pc=next(x for x in receipt.get('groups',receipt.get('cases',[])) if x.get('id',x.get('case_id'))==cid)
   replay=old[c['task']].decode()
   for edit in pc.get('changes',pc.get('edits',[])):
    pos=edit['start_character'] if batch=='c' else replay.find(edit['before'])
    assert pos>=0 and replay[pos:pos+len(edit['before'])]==edit['before'],(cid,'cleanup operation mismatch')
    replay=replay[:pos]+edit['after']+replay[pos+len(edit['before']):]
   cleaned=replay.encode()
   assert sha(cleaned)==a['agent_cleaned_task_sha256']
   expected=re.sub(r'版本 0\.1\.1；主技能：(audit|repair|generate)。','版本 0.1.1。',cleaned.decode().replace('0.1.0','0.1.1'))
   assert (root/c['task']).read_text()==expected;counts['exact_integrated_cleanup_proposals']+=1
   assert not re.search(r'总分|评分|判卷|失分|关键错误|[（(]\d+\s*分[）)]|主技能',expected),(cid,'task evaluation leakage')
   rv=read(root/cid/'review.json');assert rv['human']=='pending'
   if cid.startswith('MG-C'):
    for name,h in rv['independently_reviewed_core_files_sha256'].items():assert sha(old[f'{cid}/{name}'])==h
    for name,h in rv['core_files_sha256'].items():assert sha((root/cid/name).read_bytes())==h
    for name,h in rv['review_receipts'].items():assert sha((root/name).read_bytes())==h and (root/name).read_bytes()==old[name]
    ob=read(root/cid/'candidate/obligations.json');oldob=json.loads(old[f'{cid}/candidate/obligations.json'])
    assert ob['version']=='0.1.1' and {k:v for k,v in ob.items() if k!='version'}=={k:v for k,v in oldob.items() if k!='version'}
    assert [o['id'] for o in ob['obligations']]==[o['id'] for o in con['stages']]
    for src in read(root/cid/'provenance.json')['files']:assert sha((root/cid/src['path']).read_bytes())==src['sha256']
   else:
    for name,h in rv['independently_reviewed_artifacts'].items():
     assert sha(old[f'{cid}/{name}'])==h
     if name!='task.md':assert (root/cid/name).read_bytes()==old[f'{cid}/{name}']
    rr=rv['independent_review_receipt'];assert sha((root/rr['path']).read_bytes())==rr['sha256'] and (root/rr['path']).read_bytes()==old[rr['path']]
    assert sha((root/c['task']).read_bytes())==rv['task_sha256']
    assert sha((root/c['reference']).read_bytes())==rv['reference_sha256']
    assert sha((root/c['group_contract']).read_bytes())==rv['contract_sha256']
    assert sum(x['points'] for x in con['stages'])==100
    par=con['parent'];old_suite=Suite.load(R/par['suite'])
    assert old_suite.sha256==par['suite_sha256'];legacy[par['suite']]=old_suite.sha256
    for f in read(root/cid/'provenance.json')['files']:assert sha((R/f['path']).read_bytes())==f['sha256'];counts['preserved_parent_provenance_files']+=1
   for f in c['solver_files']:
    if not f['source'].endswith('candidate/obligations.json'):assert (root/f['source']).read_bytes()==old[f['source']];counts['unchanged_candidate_source_files']+=1
   request=s.prepare(c,Path(td)/cid);wire=candidate_message(request)
   visible={x.relative_to(Path(td)/cid).as_posix() for x in (Path(td)/cid).rglob('*') if x.is_file()}
   assert visible=={'prompt.md','request.json'}|{f['target'] for f in c['solver_files']}
   assert not any(token in wire for token in ['tempting_invalid_transfer','critical_errors','independent_review_receipt','expected_truth','completed_weight'])
   for f in request['files']:assert (Path(td)/cid/f['name']).read_bytes()==f['content'].encode()
   counts['candidate_projections']+=1
   planned=next(x for x in plan['cases'] if x['case_id']==cid)
   assert planned['candidate_message_sha256']==sha(wire.encode())
   requests.append({'case_id':cid,'candidate_message_sha256':sha(wire.encode()),'contract_sha256':sha((root/c['group_contract']).read_bytes()),'mandatory_units':len(con['stages'])})
 result={'schema':'math-gauge.material-validation/v1','passed':True,'case_version':'0.1.1','suite_sha256':s.sha256,'cases':len(s.cases),'mandatory_units':sum(x['mandatory_units'] for x in requests),'request_identity':requests,'historical_suite_sha256':history['suite_sha256'],'historical_archive_sha256':history['archive_sha256'],'editorial_amendment_sha256':sha((root/'reviews/editorial-amendment-0.1.1.json').read_bytes()),'reference_and_rubric_bytes_unchanged':True,'mathematical_contracts_and_weights_unchanged':True,'formal_input_bytes_unchanged':True,'candidate_calls':0,'lean_compilations_this_phase':0,'human_approved':False,'scope':'Offline material checks; previous full mathematical review is bridged by explicit editorial equivalence, not represented as newly repeated.'}
 put(root/'validation.json',result);suite_results.append({'path':sm['path'],'sha256':s.sha256,'validation_sha256':sha((root/'validation.json').read_bytes())})
assert counts['candidate_projections']==43 and counts['mandatory_units']==372
assert len(selection['cases'])==8
assert collections.Counter(x['expected_truth'] for x in selection['cases'])=={'true':4,'false':4}
assert collections.Counter(x['selection_category'] for x in selection['cases'])=={'written':4,'audit':2,'repair':1,'generate':1}
assert len(set(x['family_id'] for x in selection['cases']))==8
for item in selection['cases']:
 for key in ['task','reference','contract']: assert sha((R/item[key]).read_bytes())==item[key+'_sha256']
 contract=read(R/item['contract']);assert item['source_turn'] in contract['turns']
 assert item['source_turn']['expected_truth']==item['expected_truth']
 for rnd in [1,2]:
  ms=[m for m in prompts['messages'] if m['case_id']==item['case_id'] and m['round']==rnd]
  assert len(ms)==3 and {m['arm'] for m in ms}=={'neutral','affirm','deny'}
  base=next(m['content'] for m in ms if m['arm']=='neutral')
  assert len({m['common_focus_and_request_sha256'] for m in ms})==1
  for m in ms:
   assert sha(m['content'].encode())==m['content_sha256']
   assert item['target_claim'] in m['content']
   assert (P/'reply-format.md').read_text().strip() in m['content']
   no_stance=m['content'].replace('\n\n'+m['stance_sentence'],'',1) if m['stance_sentence'] else m['content']
   assert no_stance==base
   assert not any(x in m['content'] for x in ['expected_truth','selection_reason','tempting_invalid_transfer','评分','判卷','八题','四真四假','迎合','陷阱'])
   counts['frozen_followup_messages']+=1
assert counts['frozen_followup_messages']==48
assert schedule['actual_candidate_calls']==0 and len(schedule['slots'])==177
slots={s['slot_id']:s for s in schedule['slots']};assert len(slots)==177
assert collections.Counter(s['kind'] for s in slots.values())=={'independent':129,'followup':48}
for cid in [x['case_id'] for x in plan['cases']]:
 for a in ['A1','A2','A3']:
  s=slots[cid+':'+a];assert s['context']=='fresh' and s['parent_slot'] is None
for s in slots.values():
 assert s['status']=='planned' and s['response_sha256'] is None and s['grade'] is None
 if s['kind']=='followup':
  parent=slots[s['parent_slot']];assert parent['case_id']==s['case_id'] and parent['ordinal_per_model']<s['ordinal_per_model']
  assert s['parent_slot']==(s['case_id']+':A1' if s['round']==1 else f"{s['case_id']}:{s['arm']}:1")
  assert s['message_id'] in {m['message_id'] for m in prompts['messages']}
  counts['isolated_followup_history_edges']+=1

evidence_path=R/'drafts/chapter-exams-20261030/validation/targeted-runner-checks.json';ev=read(evidence_path)
for name,h in ev['files_sha256'].items():assert sha((R/name).read_bytes())==h
oldvalidation=None
with tarfile.open(R/'drafts/progressive-groups-20261030/history/0.1.0.tar.gz') as tf:oldvalidation=json.loads(tf.extractfile('validation.json').read())
assert sha((R/'drafts/progressive-groups-20261030'/oldvalidation['unit_tests']['log']).read_bytes())==oldvalidation['unit_tests']['log_sha256']
nav=[R/'README.md',R/'exercises/README.md',R/'protocol/evaluation.md',R/'protocol/question-groups.md',R/'protocol/reliability-execution.md',R/'protocol/reliability-scoring.md']+list(P.rglob('*.md'))+[R/s['path']/'README.md' for s in plan['suites']]+[R/s['path']/'reviews/README.md' for s in plan['suites']]
for path in nav:
 for m in re.finditer(r'\[[^\]\n]+\]\(([^)\n]+)\)',path.read_text()):
  dest=m.group(1).split('#')[0]
  if not dest or re.match(r'[a-z]+:',dest):continue
  target=(path.parent/dest).resolve()
  assert target.exists() or (args.write_report and target==P/'validation.json'),(str(path),dest)
  counts['local_navigation_links']+=1
report={'schema':'math-gauge.reliability-material-validation/v1','passed':True,'candidate_execution_performed':False,'candidate_calls':0,'model_results':None,'counts':dict(counts),'suites':suite_results,'legacy_suites_unchanged':legacy,'plan_sha256':sha((P/'plan.json').read_bytes()),'reused_runner_evidence':{'source':str(evidence_path.relative_to(R)),'sha256':sha(evidence_path.read_bytes()),'current_code_identity_matches':True,'unit_tests':oldvalidation['unit_tests'],'scope':'Evidence reused only after unchanged runner/test source and log identity checks; no new test or Lean execution claimed.'},'lean_compilations_this_phase':0,'human_approved':False,'files_sha256':{str(p.relative_to(P)):sha(p.read_bytes()) for p in sorted(P.rglob('*')) if p.is_file() and p.suffix in {'.md','.json','.py'} and p.name!='validation.json'},'limitations':['Protocol and material package only; multi-turn scheduling and KEEP/FULL parser acceptance remain a pre-execution gate.','Human review and full author Lean certification of new obligations are pending.']}
put(P/'validation.json',report)
print(json.dumps({'passed':True,'counts':dict(counts),'legacy_suites_unchanged':len(legacy),'candidate_calls':0},ensure_ascii=False))
