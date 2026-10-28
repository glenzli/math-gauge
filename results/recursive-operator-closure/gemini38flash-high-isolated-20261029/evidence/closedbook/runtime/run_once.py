from pathlib import Path
import os,subprocess,json,datetime,time,threading,ctypes,hashlib,sys,signal
b=Path('/private/tmp/math-gauge-gemini38flash-closedbook-20261029')
o=b/'output'
assert not (o/'run-metadata.json').exists(), 'Refusing to rerun formal attempt'
e={k:v for k,v in os.environ.items() if k in ['HOME','USER','LOGNAME','SHELL','PATH','LANG','LC_ALL','LC_CTYPE','HTTPS_PROXY','HTTP_PROXY','ALL_PROXY','NO_PROXY','https_proxy','http_proxy','all_proxy','no_proxy','SSL_CERT_FILE','SSL_CERT_DIR','TERM']}
e['TMPDIR']=str(b/'runtime/tmp')
e['AGY_CLI_DISABLE_AUTO_UPDATE']='1'
cmd=['/usr/bin/sandbox-exec','-f',str(b/'runtime/outer.sb'),'/opt/homebrew/bin/agy','--gemini_dir',str(b/'state'),'--app_data_dir','antigravity-cli','--new-project','--agent','text-only','--input-format','stream-json','--output-format','stream-json','--model','gemini-3.8-flash-high','--effort','high','--disable-slash-commands','--sandbox','--print-timeout','20m','--log-file',str(o/'agy.log')]
start=datetime.datetime.now(datetime.timezone.utc)
meta={'argv':cmd,'cwd':str(b/'work'),'environment_keys':sorted(e),'directory_overrides':{k:e[k] for k in ['TMPDIR','AGY_CLI_DISABLE_AUTO_UPDATE']},'start_utc':start.isoformat(),'input_sha256':hashlib.sha256((b/'input/task.md').read_bytes()).hexdigest(),'request_events':0,'formal_attempt':1,'status':'starting'}
(o/'run-metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
p=subprocess.Popen(cmd,cwd=b/'work',env=e,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
meta['pid']=p.pid
errors=[]
events=[]
def out_reader():
 with (o/'events.ndjson').open('wb') as f,(o/'event-observations.ndjson').open('w') as obs:
  for line in iter(p.stdout.readline,b''):
   f.write(line);f.flush()
   try:
    ev=json.loads(line)
    events.append(ev)
    record={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'event':ev.get('event')}
    if ev.get('event')=='init':record['init']=ev.get('init')
    if ev.get('event')=='step_update':record['step']={k:v for k,v in ev.get('step_update',{}).items() if k in ['step_index','state','step_type','tool_name','duration_seconds','usage']}
    if ev.get('event')=='result':
     res=ev.get('result',{})
     (o/'result-event.json').write_bytes(line)
     (o/'response.md').write_bytes(res.get('response','').encode('utf-8'))
     record['result']={k:v for k,v in res.items() if k not in ['response']}
    obs.write(json.dumps(record,ensure_ascii=False)+'\n');obs.flush()
   except Exception as ex:errors.append(type(ex).__name__+': '+str(ex))
def err_reader():
 with (o/'stderr.txt').open('wb') as f:
  for chunk in iter(lambda:p.stderr.read(8192),b''):
   f.write(chunk);f.flush()
t1=threading.Thread(target=out_reader);t2=threading.Thread(target=err_reader);t1.start();t2.start()
time.sleep(1.5)
try:
 assert p.poll() is None, 'CLI exited before request'
 lib=ctypes.CDLL('/usr/lib/libsandbox.dylib',use_errno=True)
 check_flags=1|ctypes.c_uint.in_dll(lib,'SANDBOX_CHECK_NO_REPORT').value
 lib.sandbox_check.restype=ctypes.c_int
 lib.sandbox_check.argtypes=[ctypes.c_int,ctypes.c_char_p,ctypes.c_int]
 paths=json.loads((b/'runtime/probe-paths.json').read_text())
 checks=[]
 for label,path,expected in [('task',paths['allow'],0)]+[(x['label'],x['path'],1) for x in paths['deny']]:
  ctypes.set_errno(0)
  result=lib.sandbox_check(p.pid,b'file-read-data',check_flags,ctypes.c_char_p(path.encode()))
  checks.append({'pid':p.pid,'operation':'file-read-data','label':label,'path':path,'result':result,'errno':ctypes.get_errno(),'expected_allow':expected==0})
 (o/'actual-process-sandbox-check.json').write_text(json.dumps(checks,indent=2)+'\n')
 assert checks[0]['result']==0 and all(x['result']>0 for x in checks[1:]), 'Actual CLI sandbox_check did not confirm filesystem restrictions'
 meta['status']='request_sent'
 meta['request_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
 meta['request_events']=1
 (o/'run-metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
 p.stdin.write((b/'runtime/request.ndjson').read_bytes());p.stdin.flush();p.stdin.close()
 print(json.dumps({'status':'request_sent','pid':p.pid,'sandbox_check_positive':1,'sandbox_check_negative':len(checks)-1,'input_sha256':meta['input_sha256']}),flush=True)
except Exception as ex:
 errors.append(type(ex).__name__+': '+str(ex))
 meta['status']='startup_failed_before_request'
 try:p.stdin.close()
 except Exception:pass
 if p.poll() is None:os.killpg(p.pid,signal.SIGTERM)
code=p.wait();t1.join();t2.join()
end=datetime.datetime.now(datetime.timezone.utc)
meta.update(exit_code=code,end_utc=end.isoformat(),wall_seconds=(end-start).total_seconds(),parse_errors=errors,event_count=len(events),result_count=sum(x.get('event')=='result' for x in events),tool_steps=[{k:v for k,v in x.get('step_update',{}).items() if k in ['step_index','state','step_type','tool_name']} for x in events if x.get('step_update',{}).get('step_type')=='tool'])
results=[x.get('result',{}) for x in events if x.get('event')=='result']
if results:
 last=results[-1]
 meta['result_metadata']={k:v for k,v in last.items() if k!='response'}
 meta['status']='completed' if code==0 and last.get('status')=='SUCCESS' else 'failed_after_request'
(o/'run-metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps({k:v for k,v in meta.items() if k in ['status','pid','exit_code','wall_seconds','request_events','event_count','result_count','tool_steps','result_metadata','parse_errors']},ensure_ascii=False),flush=True)
