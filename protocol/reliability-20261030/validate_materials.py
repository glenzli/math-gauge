import argparse,collections,copy,hashlib,json,re,sys,tarfile,tempfile
from pathlib import Path
R=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
sys.path.insert(0,str(R))
from math_gauge.catalog import Suite,candidate_message,relative_name,safe_file
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):return json.loads(p.read_text())
def archive_files(path):
 """Read exact regular-file bytes without extracting untrusted paths."""
 files={}
 with tarfile.open(path) as tf:
  for member in tf:
   if member.isdir():continue
   relative_name(member.name)
   assert member.isfile() and member.name not in files,'Invalid or duplicate archive member'
   files[member.name]=tf.extractfile(member).read()
 return files

def replay_text_edits(text,edits):
 for edit in edits:
  assert text.count(edit['before'])==1,'Ambiguous or missing strict task edit'
  text=text.replace(edit['before'],edit['after'],1)
 return text

def replay_contract_edits(contract,edits):
 result=copy.deepcopy(contract)
 paths=[tuple(edit['path']) for edit in edits]
 assert len(paths)==2 and set(paths)=={('version',),('stages',5,'assumptions',1)},'Unexpected strict contract edit'
 assert result['stages'][5]['id']=='S6'
 for edit in edits:
  target=result
  for key in edit['path'][:-1]:target=target[key]
  key=edit['path'][-1]
  assert target[key]==edit['before'],'Strict contract edit does not match its base'
  target[key]=edit['after']
 return result

def strict_baseline(root):
 """Restore the reviewed 0.1.1 base, then verify the one declared 0.1.2 edit."""
 receipt_path=root/'reviews/strict-amendment-0.1.2.json'
 if not receipt_path.exists():return {},{}
 receipt=read(receipt_path)
 assert receipt['schema']=='math-gauge.strict-mathematical-amendment/v1'
 assert receipt['previous_suite_version']=='0.1.1' and receipt['suite_version']=='0.1.2'
 assert receipt['suite_version_only_edit'] is True and receipt['candidate_calls']==0 and receipt['human_approved'] is False
 assert len(receipt['cases'])==1 and receipt['cases'][0]['case_id']=='MG-GR001'
 archive=safe_file(root,receipt['previous_files_archive']);manifest=read(safe_file(root,receipt['previous_archive_manifest']))
 assert sha(archive.read_bytes())==receipt['previous_files_archive_sha256']==manifest['archive_sha256']
 assert receipt['previous_git_commit']==manifest['git_commit']
 files=archive_files(archive)
 expected={'MG-GR001/'+name for name in ['task.md','case.json','contract.json','review.json']}|{'suite.json'}
 assert set(files)==set(manifest['files_sha256'])==expected,'Targeted archive must contain exactly the declared base files'
 for name,h in manifest['files_sha256'].items():assert sha(files[name])==h,(name,'historical hash mismatch')
 old_suite=json.loads(files['suite.json']);new_suite=read(root/'suite.json')
 assert new_suite==dict(old_suite,version=receipt['suite_version']),'Unrecorded suite change'
 item=receipt['cases'][0];cid=item['case_id']
 assert item['previous_version']=='0.1.1' and item['version']=='0.1.2'
 assert item['fresh_ai_review'] is True and item['independent_review_repeated'] is False
 assert item['human']=='pending' and item['new_lean_compilation'] is False and item['candidate_calls']==0
 assert set(item['old_files_sha256'])==set(item['new_files_sha256'])==expected-{'suite.json'}
 for name,h in item['old_files_sha256'].items():assert sha(files[name])==h
 for name,h in item['new_files_sha256'].items():assert sha(safe_file(root,name).read_bytes())==h,(name,'current strict hash mismatch')
 for name,h in item['unchanged_files_sha256'].items():assert sha(safe_file(root,cid+'/'+name).read_bytes())==h
 assert len(item['task_edits'])==2
 assert item['task_edits'][0]=={'before':'版本 0.1.1。','after':'版本 0.1.2。'}
 expected_task=replay_text_edits(files[cid+'/task.md'].decode(),item['task_edits'])
 assert (root/cid/'task.md').read_bytes()==expected_task.encode(),'Unrecorded strict task change'
 old_contract=json.loads(files[cid+'/contract.json']);new_contract=read(root/cid/'contract.json')
 assert replay_contract_edits(old_contract,item['contract_edits'])==new_contract,'Unrecorded strict contract change'
 assert [s['id'] for s in old_contract['stages']]==[s['id'] for s in new_contract['stages']]==item['stage_ids']
 old_case=json.loads(files[cid+'/case.json']);new_case=read(root/cid/'case.json')
 for key in set(old_case)|set(new_case):
  if key not in {'version','review','evaluator_files'}:assert old_case.get(key)==new_case.get(key),(key,'Unrecorded case change')
 assert new_case['version']==item['version'] and new_case['review']['human']=='pending'
 assert {k:v for k,v in old_case['review'].items() if k!='mathematical'}=={k:v for k,v in new_case['review'].items() if k!='mathematical'}
 assert new_case['evaluator_files']==old_case['evaluator_files']+[str(receipt_path.relative_to(root)),receipt['previous_archive_manifest'],receipt['previous_files_archive']]
 old_review=json.loads(files[cid+'/review.json']);new_review=read(root/cid/'review.json')
 permitted={'task_sha256','contract_sha256','integration_check','strict_amendment'}
 assert {k:v for k,v in old_review.items() if k not in permitted}=={k:v for k,v in new_review.items() if k not in permitted},'Unrecorded review change'
 assert new_review['task_sha256']==item['new_files_sha256'][cid+'/task.md'] and new_review['contract_sha256']==item['new_files_sha256'][cid+'/contract.json']
 assert new_review['integration_check']['historical_integration_check']==old_review['integration_check']
 assert new_review['integration_check']['mathematical_fields_unchanged_from_0_1_0'] is False
 assert new_review['strict_amendment']['receipt']==str(receipt_path.relative_to(root))
 assert new_review['strict_amendment']['human']=='pending'
 return files,{cid:{'receipt':str(receipt_path.relative_to(root)),'receipt_sha256':sha(receipt_path.read_bytes()),'previous_archive_sha256':sha(archive.read_bytes()),'previous_version':item['previous_version'],'version':item['version']}}

def validate_runner_evidence(repo):
 path=repo/'results/strict-review-20261030/engineering/current-evidence.json';evidence=read(path)
 assert evidence['candidate_model_requests']==0 and evidence['actual_isolated_lean_projects']==1
 required={'math_gauge/execution.py','math_gauge/review.py','math_gauge/catalog.py','tests/test_question_groups.py','tests/test_runner.py'}
 assert required<=set(evidence['current_source_files_sha256'])
 for name,h in evidence['current_source_files_sha256'].items():assert sha(safe_file(repo,name).read_bytes())==h,(name,'Current engineering source drift')
 for name,h in evidence['artifact_files_sha256'].items():assert sha(safe_file(repo,name).read_bytes())==h,(name,'Engineering evidence drift')
 previous=evidence['historical_runner'];old=read(safe_file(repo,previous['receipt']))
 assert sha((repo/previous['receipt']).read_bytes())==previous['receipt_sha256']
 frozen=archive_files(safe_file(repo,previous['source_archive']))
 assert sha((repo/previous['source_archive']).read_bytes())==previous['source_archive_sha256']
 assert set(frozen)==set(old['files_sha256'])
 for name,h in old['files_sha256'].items():assert sha(frozen[name])==h,(name,'Historical runner identity mismatch')
 assert any(evidence['current_source_files_sha256'][name]!=h for name,h in old['files_sha256'].items()),'Historical runner must not be presented as current'
 focused=evidence['focused_tests'];log=safe_file(repo,focused['log']).read_bytes()
 assert sha(log)==focused['log_sha256'] and focused['exit_code']==0
 assert f"Ran {focused['tests']} tests" in log.decode() and 'OK (skipped=1)' in log.decode()
 fixture=evidence['isolated_fixture'];report=read(safe_file(repo,fixture['report']))
 assert report['status']=='passed' and report['source_repaired'] is False
 assert report['engine_identity']['execution']==evidence['current_source_files_sha256']['math_gauge/execution.py']
 assert report['group_contract_sha256'] and len(report['modules'])==3
 assert report['audit']['summary']['passed'] is True
 assert not set(report['audit']['summary']['axiom_union'])-{'propext','Classical.choice','Quot.sound'}
 current_review=read(safe_file(repo,fixture['current_review']))
 assert current_review['passed'] is True and current_review['lean_recompiled'] is False and current_review['stage_passes']==5
 assert current_review['current_review_sha256']==evidence['current_source_files_sha256']['math_gauge/review.py']
 return {'historical':{'source':previous['receipt'],'sha256':previous['receipt_sha256'],'historical_source_archive':previous['source_archive'],'current_code_identity_matches':False},'current':{'source':str(path.relative_to(repo)),'sha256':sha(path.read_bytes()),'current_code_identity_matches':True,'focused_tests':focused,'actual_isolated_lean_projects':1,'scope':'Current engineering source and exact targeted evidence only; final full-workspace acceptance remains external to this material validator.'}}

def validate_packet_revalidation(repo,plan,selection,receipt):
 prior_plan=read(safe_file(repo,receipt['archived_reviewed_files']['protocol/reliability-20261030/plan.json']))
 prior_selection=read(safe_file(repo,receipt['archived_reviewed_files']['protocol/reliability-20261030/selection.json']))
 expected=copy.deepcopy(prior_plan)
 assert len(plan['suites'])==len(expected['suites'])
 for old,current in zip(expected['suites'],plan['suites']):
  assert old['path']==current['path']
  old.update(version=current['version'],sha256=current['sha256'])
 assert len(plan['cases'])==len(expected['cases'])
 for old,current in zip(expected['cases'],plan['cases']):
  assert old['case_id']==current['case_id']
  old['suite_sha256']=current['suite_sha256']
  if old['case_id']=='MG-GR001':
   for key in ['case_version','candidate_message_sha256','task_sha256','contract_sha256']:old[key]=current[key]
 expected['files_sha256']['selection.json']=sha(json.dumps(selection,ensure_ascii=False,indent=2).encode()+b'\n')
 assert expected==plan,'Unrecorded plan change beyond the explicit material identity refresh'
 expected_selection=dict(prior_selection,source_suite_sha256=selection['source_suite_sha256'])
 assert expected_selection==selection,'The eight selected cases, claims or selection rules changed'
 assert selection['source_suite_sha256']==next(x['sha256'] for x in plan['suites'] if x['path']=='drafts/progressive-groups-20261030')
 assert receipt['candidate_model_calls']==0 and receipt['new_independent_packet_review'] is False
def validate_materials(repo_root=R,write_report=False):
 R=Path(repo_root).resolve();P=R/'protocol/reliability-20261030'
 def put(path,data):
  if write_report:
   path.parent.mkdir(parents=True,exist_ok=True);path.write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n')
  else:
   assert path.exists() and read(path)==data,(str(path),'validation receipt stale; inspect changes before --write-report')
 counts=collections.Counter();suite_results=[];legacy={}
 plan=read(P/'plan.json');selection=read(P/'selection.json');prompts=read(P/'prompts.json');schedule=read(P/'schedule.json')
 assert plan['candidate_calls']==0 and plan['execution_authorized'] is False and plan['actual_results'] is None
 assert plan['runtime_configuration_frozen'] is False
 for rel,h in plan['files_sha256'].items(): assert sha((P/rel).read_bytes())==h,rel
 for rel,h in plan['protocol_files_sha256'].items(): assert sha((R/rel).read_bytes())==h,rel
 for sm in plan['suites']:
  root=R/sm['path'];s=Suite.load(root);assert s.sha256==sm['sha256'] and s.metadata['version']==sm['version']
  strict_files,strict_cases=strict_baseline(root);counts['strict_scope_amendments']+=len(strict_cases)
  def baseline_bytes(name):return strict_files[name] if name in strict_files else safe_file(root,name).read_bytes()
  history=read(root/'history/0.1.0.json');archive=root/'history/0.1.0.tar.gz'
  assert sha(archive.read_bytes())==history['archive_sha256']
  old=archive_files(archive)
  with tempfile.TemporaryDirectory(prefix='math-gauge-history-verify-') as td:
   for n,b in old.items(): q=Path(td)/n;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b)
   assert Suite.load(td).sha256==history['suite_sha256'];counts['restored_historical_suites']+=1
  amendment=read(root/'reviews/editorial-amendment-0.1.1.json');entries={x['case_id']:x for x in amendment['cases']}
  requests=[]
  with tempfile.TemporaryDirectory(prefix='math-gauge-reliability-projection-') as td:
   for cid,c in s.cases.items():
    base_case=json.loads(baseline_bytes(cid+'/case.json'));con=json.loads(baseline_bytes(c['group_contract']));prev=json.loads(old[c['group_contract']]);a=entries[cid]
    assert base_case['version']==con['version']==amendment['new_suite_version']
    assert c['version']==read(root/c['group_contract'])['version']==strict_cases.get(cid,{}).get('version',amendment['new_suite_version'])
    assert {k:v for k,v in con.items() if k!='version'}=={k:v for k,v in prev.items() if k!='version'}
    counts['editorial_baseline_unchanged_mathematical_contracts']+=1;counts['mandatory_units']+=len(con['stages'])
    counts['current_unchanged_mathematical_contracts']+=cid not in strict_cases
    for name in [c['reference'],c['rubric']]:assert (root/name).read_bytes()==old[name];counts['unchanged_reference_and_rubric_files']+=1
    assert sha(baseline_bytes(c['task']))==a['new_task_sha256']
    assert sha(old[c['task']])==a['old_task_sha256']
    assert sha(baseline_bytes(c['group_contract']))==a['new_contract_sha256']
    assert sha(baseline_bytes(cid+'/case.json'))==a['case_sha256']
    assert sha(baseline_bytes(cid+'/review.json'))==a['review_sha256']
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
    assert baseline_bytes(c['task']).decode()==expected;counts['exact_integrated_cleanup_proposals']+=1
    assert not re.search(r'总分|评分|判卷|失分|关键错误|[（(]\d+\s*分[）)]|主技能',(root/c['task']).read_text()),(cid,'current task evaluation leakage')
    assert not re.search(r'总分|评分|判卷|失分|关键错误|[（(]\d+\s*分[）)]|主技能',expected),(cid,'task evaluation leakage')
    rv=json.loads(baseline_bytes(cid+'/review.json'));assert rv['human']=='pending' and read(root/cid/'review.json')['human']=='pending'
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
      if name!='task.md':assert baseline_bytes(cid+'/'+name)==old[f'{cid}/{name}']
     rr=rv['independent_review_receipt'];assert sha((root/rr['path']).read_bytes())==rr['sha256'] and (root/rr['path']).read_bytes()==old[rr['path']]
     assert sha(baseline_bytes(c['task']))==rv['task_sha256']
     assert sha((root/c['reference']).read_bytes())==rv['reference_sha256']
     assert sha(baseline_bytes(c['group_contract']))==rv['contract_sha256']
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
    assert planned['case_version']==c['version'] and planned['suite_sha256']==s.sha256
    assert planned['task_sha256']==sha((root/c['task']).read_bytes()) and planned['contract_sha256']==sha((root/c['group_contract']).read_bytes())
    requests.append({'case_id':cid,'candidate_message_sha256':sha(wire.encode()),'contract_sha256':sha((root/c['group_contract']).read_bytes()),'mandatory_units':len(con['stages'])})
  result={'schema':'math-gauge.material-validation/v1','passed':True,'suite_version':s.metadata['version'],'case_versions':dict(collections.Counter(c['version'] for c in s.cases.values())),'suite_sha256':s.sha256,'cases':len(s.cases),'mandatory_units':sum(x['mandatory_units'] for x in requests),'request_identity':requests,'historical_suite_sha256':history['suite_sha256'],'historical_archive_sha256':history['archive_sha256'],'editorial_amendment_sha256':sha((root/'reviews/editorial-amendment-0.1.1.json').read_bytes()),'reference_and_rubric_bytes_unchanged':True,'editorial_baseline_mathematical_contracts_and_weights_unchanged':True,'current_mathematical_contracts_unchanged':not strict_cases,'stage_weights_unchanged':True,'strict_amendments':strict_cases,'formal_input_bytes_unchanged':True,'candidate_calls':0,'lean_compilations_this_phase':0,'human_approved':False,'scope':'Offline material checks first verify the archived editorial base, then replay the one explicit strict amendment. Earlier independent review, fresh scope correction, engineering evidence and human approval remain separate.'}
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

 runner_evidence=validate_runner_evidence(R)
 revalidation=read(P/'reviews/strict-revalidation-20261030.json')
 assert revalidation['current_plan_sha256']==sha((P/'plan.json').read_bytes())
 assert revalidation['current_selection_sha256']==sha((P/'selection.json').read_bytes())
 prior_review=read(P/'reviews/packet-review-c.json')
 assert sha((P/'reviews/packet-review-c.json').read_bytes())==revalidation['prior_packet_review_sha256']
 for name,h in prior_review['files_sha256'].items():
  archived=revalidation['archived_reviewed_files'].get(name,name)
  assert sha(safe_file(R,archived).read_bytes())==h,(name,'Original packet review identity changed')
 assert prior_review['files_sha256']['protocol/reliability-20261030/plan.json']==revalidation['previous_plan_sha256']
 validate_packet_revalidation(R,plan,selection,revalidation)
 oldvalidation=None
 with tarfile.open(R/'drafts/progressive-groups-20261030/history/0.1.0.tar.gz') as tf:oldvalidation=json.loads(tf.extractfile('validation.json').read())
 assert sha((R/'drafts/progressive-groups-20261030'/oldvalidation['unit_tests']['log']).read_bytes())==oldvalidation['unit_tests']['log_sha256']
 nav=[R/'README.md',R/'exercises/README.md',R/'protocol/evaluation.md',R/'protocol/question-groups.md',R/'protocol/reliability-execution.md',R/'protocol/reliability-scoring.md']+list(P.rglob('*.md'))+[R/s['path']/'README.md' for s in plan['suites']]+[R/s['path']/'reviews/README.md' for s in plan['suites']]
 for path in nav:
  for m in re.finditer(r'\[[^\]\n]+\]\(([^)\n]+)\)',path.read_text()):
   dest=m.group(1).split('#')[0]
   if not dest or re.match(r'[a-z]+:',dest):continue
   target=(path.parent/dest).resolve()
   assert target.exists() or (write_report and target==P/'validation.json'),(str(path),dest)
   counts['local_navigation_links']+=1
 report={'schema':'math-gauge.reliability-material-validation/v1','passed':True,'candidate_execution_performed':False,'candidate_calls':0,'model_results':None,'counts':dict(counts),'suites':suite_results,'legacy_suites_unchanged':legacy,'plan_sha256':sha((P/'plan.json').read_bytes()),'runner_evidence':runner_evidence,'historical_unit_tests':oldvalidation['unit_tests'],'strict_revalidation_sha256':sha((P/'reviews/strict-revalidation-20261030.json').read_bytes()),'lean_compilations_this_phase':0,'human_approved':False,'files_sha256':{str(p.relative_to(P)):sha(p.read_bytes()) for p in sorted(P.rglob('*')) if p.is_file() and p.suffix in {'.md','.json','.py'} and p.name!='validation.json'},'limitations':['Protocol and material package only; multi-turn scheduling and KEEP/FULL parser acceptance remain a pre-execution gate.','Human review and full author Lean certification of new obligations are pending.']}
 put(P/'validation.json',report)
 return {'passed':True,'counts':dict(counts),'legacy_suites_unchanged':len(legacy),'candidate_calls':0}

def main(argv=None):
 parser=argparse.ArgumentParser(description='Offline material and receipt checks; never calls candidate models or Lean.')
 parser.add_argument('--write-report',action='store_true',help='Refresh deterministic local validation receipts after all material checks.')
 args=parser.parse_args(argv)
 print(json.dumps(validate_materials(write_report=args.write_report),ensure_ascii=False))

if __name__=='__main__':main()
