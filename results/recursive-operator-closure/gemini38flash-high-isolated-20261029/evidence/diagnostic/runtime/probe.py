from pathlib import Path
import json,hashlib,os,sys,socket,errno
b=Path('/private/tmp/math-gauge-gemini38flash-20261029')
m=json.loads((b/'runtime/probe-paths.json').read_text())
r={'pid':os.getpid(),'cwd':os.getcwd(),'allow':{},'deny':[]}
p=Path(m['allow'])
r['allow']={'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
for item in m['deny']:
 item=dict(item)
 try:
  with open(item['path'],'rb') as f:f.read(1)
  item.update(outcome='UNEXPECTED_ALLOWED')
 except OSError as e:item.update(outcome='DENIED' if e.errno in [errno.EPERM,errno.EACCES] else 'OTHER_ERROR',errno=e.errno,error=str(e))
 r['deny'].append(item)
print(json.dumps(r,indent=2))
assert r['allow']['sha256']=='779bf275a6184fb848a12f3d72089a21d4704513512e10323aa48d4ee462cecd'
assert all(x['outcome']=='DENIED' and x['exists_outside_sandbox'] for x in r['deny']),r
