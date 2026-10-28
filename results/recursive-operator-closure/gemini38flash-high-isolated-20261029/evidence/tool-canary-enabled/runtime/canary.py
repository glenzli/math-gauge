from pathlib import Path
import os,subprocess,json,datetime
b=Path('/private/tmp/math-gauge-agy-tools-enabled-control-20261029')
e={k:v for k,v in os.environ.items() if k in ['HOME','USER','LOGNAME','SHELL','PATH','LANG','LC_ALL','LC_CTYPE','TERM']}
e['TMPDIR']=str(b/'runtime/tmp');e['AGY_CLI_DISABLE_AUTO_UPDATE']='1'
cmd=['/usr/bin/sandbox-exec','-f',str(b/'runtime/outer.sb'),'/opt/homebrew/bin/agy','--gemini_dir',str(b/'state'),'--app_data_dir','antigravity-cli','--new-project','--agent','text-only','--model','gemini-3.8-flash-high','--effort','high','--output-format','stream-json','--print-timeout','3m','--log-file',str(b/'output/agy.log'),'-p','Use search_web to look up the current UTC date.']
(b/'runtime/command.json').write_text(json.dumps({'argv':cmd,'environment_keys':sorted(e)},indent=2)+'\n')
with (b/'output/events.ndjson').open('wb') as out,(b/'output/stderr.txt').open('wb') as err:
 p=subprocess.run(cmd,cwd=b/'work',env=e,stdout=out,stderr=err,timeout=240)
evs=[]
for line in (b/'output/events.ndjson').read_bytes().splitlines():
 try:evs.append(json.loads(line))
 except Exception:pass
inits=[x.get('init',{}) for x in evs if x.get('event')=='init']
tools=[x.get('step_update',{}) for x in evs if x.get('step_update',{}).get('step_type')=='tool']
results=[x.get('result',{}) for x in evs if x.get('event')=='result']
summary={'exit_code':p.returncode,'init':inits,'tool_steps':[{k:v for k,v in x.items() if k in ['step_index','tool_name','state']} for x in tools],'result_metadata':[{k:v for k,v in x.items() if k!='response'} for x in results],'passed':p.returncode==0 and len(inits)==1 and not any(x not in ['finish'] for x in inits[0].get('tools',[])) and not any(x.get('tool_name')!='finish' for x in tools)}
(b/'output/summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,ensure_ascii=False),flush=True)
