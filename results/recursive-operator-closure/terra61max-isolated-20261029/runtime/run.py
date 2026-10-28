from pathlib import Path
import hashlib, json, subprocess, time, datetime
root=Path(__file__).resolve().parent.parent
settings=json.loads((root/'runtime/settings.json').read_text())
def toml(x):
 if isinstance(x,dict):return '{'+', '.join(json.dumps(k)+' = '+toml(v) for k,v in x.items())+'}'
 return json.dumps(x)
args=['/usr/bin/sandbox-exec','-f',str(root/'runtime/outer.sb'),'/Applications/ChatGPT.app/Contents/Resources/codex-cli/CodexCLI.app/Contents/MacOS/codex','exec',
 '--ignore-user-config','--ignore-rules','--strict-config','--ephemeral','--skip-git-repo-check','--json',
 '-m','gpt-6.1-terra','-C',str(root/'input'),'-o',str(root/'output/response.md')]
for k,v in settings.items():args+=['-c',k+'='+toml(v)]
args+=['-']
prompt=(root/'input/task.md').read_bytes()
assert hashlib.sha256(prompt).hexdigest()=='779bf275a6184fb848a12f3d72089a21d4704513512e10323aa48d4ee462cecd'
probe=json.loads((root/'runtime/isolation-probe.json').read_text());assert probe['status']=='passed'
report={'requested_model':'gpt-6.1-terra','reasoning_effort':'max','fresh_session':True,'ephemeral':True,
 'prompt_sha256':hashlib.sha256(prompt).hexdigest(),'prompt_bytes':len(prompt),'candidate_files':['task.md'],
 'extra_instruction':None,'started_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'command':args,'cwd':str(root/'input'),'settings':settings,'isolation_probe':'isolation-probe.json'}
(root/'runtime/run-manifest.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
start=time.monotonic()
with (root/'output/events.jsonl').open('wb') as out,(root/'output/stderr.log').open('wb') as err:
 proc=subprocess.Popen(args,cwd=root/'input',stdin=subprocess.PIPE,stdout=out,stderr=err)
 try:
  proc.communicate(prompt,timeout=1500)
 except subprocess.TimeoutExpired:
  proc.terminate();proc.communicate(timeout=15);report['timeout']=True
report.update(exit_code=proc.returncode,elapsed_seconds=round(time.monotonic()-start,2),finished_at=datetime.datetime.now(datetime.timezone.utc).isoformat())
p=root/'output/response.md'
if p.exists():report['response_sha256']=hashlib.sha256(p.read_bytes()).hexdigest();report['response_bytes']=p.stat().st_size
(root/'runtime/run-manifest.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ['exit_code','elapsed_seconds','response_bytes'] if k in report}),flush=True)
if proc.returncode:print((root/'output/stderr.log').read_text()[-6000:]);raise SystemExit(proc.returncode)
