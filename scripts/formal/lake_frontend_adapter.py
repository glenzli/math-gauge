#!/usr/bin/env python3
"""Diagnose one original Lake configuration with the pinned official plugin; no scripts run."""
import argparse,copy,hashlib,json,os,re,shutil,sys,tempfile,uuid
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--repository',required=True);p.add_argument('--source-report',required=True);p.add_argument('--out',required=True);p.add_argument('--timeout',type=int,default=120);a=p.parse_args()
sys.dont_write_bytecode=True;sys.path.insert(0,str(Path(a.repository).resolve()))
from math_gauge.catalog import read_json,write_json,digest_bytes
from math_gauge.execution import (_candidate_engine,_candidate_sources,_candidate_imports,_candidate_policy,_candidate_process,now)
original_path=Path(a.source_report).resolve();old=read_json(original_path);out=Path(a.out).resolve();out.mkdir(parents=True,exist_ok=False)
assert old['status']=='compile_error' and old['source_repaired'] is False
engine,engine_path=_candidate_engine();template=engine_path.with_name('audit-candidate.lean.in');dependency=old['dependency'];lean=Path(dependency['lean']).resolve();plugin=lean.parent.parent/'lib/lean/libLake_shared.dylib'
assert digest_bytes(lean.read_bytes())==dependency['lean_sha256']=='b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997'
assert digest_bytes(plugin.read_bytes())=='16f6fcceb7a3bc463c727d88f322c1de74e74286231d1aa3e607d086ac868e13'
request=read_json(original_path.parent/'request.json');raw=(original_path.parent/'response.md').read_bytes();assert digest_bytes(raw)==old['response_sha256']
submitted={name:(original_path.parent/'submitted'/name).read_text() for name in old['files_sha256']}
inputs={name:(original_path.parent/'inputs'/name).read_text() for name in old['input_files_sha256']}
assert {k:digest_bytes(v.encode()) for k,v in submitted.items()}==old['files_sha256'] and {k:digest_bytes(v.encode()) for k,v in inputs.items()}==old['input_files_sha256']
sources,external=_candidate_sources(submitted,inputs,lambda text:_candidate_imports(text,engine['clean_lean']));names=[n[:-5].replace('/','.') for n,_ in sources]
assert names==[m['module'] for m in old['modules']] and names[-1]=='lakefile'
manifest=read_json(original_path.parent/'manifest.json');assert manifest['ordered_sources']==[{'name':n,'sha256':digest_bytes(t.encode()),'origin':'submitted' if n in submitted else 'frozen-input'} for n,t in sources]
assert digest_bytes((original_path.parent/'manifest.json').read_bytes())==old['manifest_sha256']
for name in ['response.md','request.json','manifest.json']:shutil.copy2(original_path.parent/name,out/name)
for kind in ['submitted','inputs']:shutil.copytree(original_path.parent/kind,out/kind)
(out/'original-failed-report.json').write_bytes(original_path.read_bytes());(out/'logs').mkdir();(out/'oleans').mkdir()
report={'schema':'math-gauge.named-frontend-diagnostic/v1','status':'pending','started_at':now(),'source_report':str(original_path),'source_report_sha256':digest_bytes(original_path.read_bytes()),'source_response_sha256':old['response_sha256'],'source_repaired':False,'candidate_calls':0,'script_executions':0,'semantic_alignment_inferred':False,'base_engine_identity':old['engine_identity'],'adapter':{'name':'lean4.29.1-macos-arm64-lake-plugin/v1','source_sha256':digest_bytes(Path(__file__).read_bytes()),'source_path':str(Path(__file__).resolve()),'plugin_path':str(plugin),'plugin_sha256':digest_bytes(plugin.read_bytes())},'modules':[],'original_failure_retained':True}
try:
 with tempfile.TemporaryDirectory(prefix='math-gauge-lake-frontend-') as t:
  temp=Path(t).resolve();stage,build,scratch=[temp/n for n in ['sources','build','scratch']]
  for path in [stage,build,scratch]:path.mkdir()
  for name,text in sources:
   f=stage/name;f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(text.encode())
  audit_name='GaugeCandidateAudit_'+uuid.uuid4().hex
  audit=template.read_text().replace('{{IMPORTS}}','\n'.join('import '+n for n in names)).replace('{{MODULES}}','#['+', '.join(json.dumps(n) for n in names)+']')
  (stage/(audit_name+'.lean')).write_text(audit);(out/'audit.lean').write_text(audit)
  policy=_candidate_policy(stage,build,scratch,dependency);policy_path=temp/'compiler.sb';policy_path.write_text(policy);(out/'compiler.sb').write_text(policy)
  env={'PATH':'/usr/bin:/bin','TMPDIR':str(scratch),'LEAN_PATH':os.pathsep.join([str(build),*dependency['search_paths']])};prefix=['/usr/bin/sandbox-exec','-f',str(policy_path)]
  positive=stage/'isolation-probe.txt';positive.write_text('candidate-isolation-probe\n')
  probes=[]
  for name,path,allowed in [('source-read',positive,True),('response-read',original_path.parent/'response.md',False),('evaluator-read',engine_path,False)]:
   rc,stdout,stderr,timed=_candidate_process(prefix+['/bin/cat',str(path)],stage,env,10)
   passed=(rc==0 and stdout=='candidate-isolation-probe\n') if allowed else rc!=0 and any(v in stderr for v in ['Operation not permitted','Permission denied'])
   probes.append({'name':name,'expected':'allowed' if allowed else 'denied','passed':passed and not timed,'exit_code':rc,'stderr':stderr,'timeout':timed})
  report['isolation']={'policy_sha256':digest_bytes(policy.encode()),'network':'denied','process_fork':'denied','probes':probes}
  assert all(v['passed'] for v in probes),'Compiler boundary failed before candidate code'
  report['environment']={'stage':str(stage),'build':str(build),'scratch':str(scratch),'LEAN_PATH':env['LEAN_PATH']}
  for name,text in sources[:-1]:
   module=name[:-5].replace('/','.');entry=next(m for m in old['modules'] if m['module']==module);olean=original_path.parent/'oleans'/name[:-5];olean=olean.with_suffix('.olean')
   assert entry['exit_code']==0 and entry['timeout'] is False and entry['source_sha256']==digest_bytes(text.encode()) and digest_bytes(olean.read_bytes())==entry['olean_sha256']
   assert digest_bytes(Path(entry['log']).read_bytes())==entry['log_sha256']
   target=build/name[:-5];target=target.with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(olean,target)
   saved=out/'oleans'/name[:-5];saved=saved.with_suffix('.olean');saved.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(olean,saved)
   log=out/'logs'/(module.replace('.','_')+'.log');shutil.copy2(entry['log'],log);new=copy.deepcopy(entry);new.update(log=str(log),reused_original_compilation=True);report['modules'].append(new)
  for module,text in [('lakefile',dict(sources)['lakefile.lean']),(audit_name,audit)]:
   source=stage/(module+'.lean');target=build/(module+'.olean');argv=prefix+[str(lean),'--plugin='+str(plugin),'--root='+str(stage),'-o',str(target),str(source)]
   rc,stdout,stderr,timed=_candidate_process(argv,stage,env,a.timeout);log=out/'logs'/(module+'.log');log.write_text(stdout+stderr)
   entry={'module':module,'source_sha256':digest_bytes(text.encode()),'exit_code':rc,'timeout':timed,'argv':argv,'log':str(log),'log_sha256':digest_bytes(log.read_bytes()),'reused_original_compilation':False};report['modules'].append(entry)
   if rc or timed:raise RuntimeError('Adapted module failed: '+module)
   saved=out/'oleans'/(module+'.olean');shutil.copy2(target,saved);entry['olean_sha256']=digest_bytes(saved.read_bytes())
   if module==audit_name:
    summaries=[json.loads(s) for s in re.findall(r'CANDIDATE_AUDIT_SUMMARY (\{[^\r\n]*\})',stdout+stderr)];decls=[json.loads(s) for s in re.findall(r'CANDIDATE_DECL (\{[^\r\n]*\})',stdout+stderr)]
    assert len(summaries)==1 and summaries[0]['passed'] and decls and len(decls)==summaries[0]['declaration_count'] and not set(summaries[0]['axiom_union'])-engine['ALLOWED_AXIOMS']
    report['audit']={'summary':summaries[0],'declarations':decls}
  assert all((stage/name).read_bytes()==text.encode() for name,text in sources),'Candidate source bytes changed'
  report['status']='passed'
except Exception as error:report.update(status='infrastructure_or_frontend_error',error={'type':type(error).__name__,'message':str(error)})
report['finished_at']=now();write_json(out/'frontend-diagnostic.json',report);print(json.dumps({'status':report['status'],'modules':[(m['module'],m['exit_code']) for m in report['modules']],'error':report.get('error'),'candidate_calls':0,'script_executions':0}));sys.exit(0 if report['status']=='passed' else 1)
