"""Non-inference supplement preparation with explicit inherited capability controls.

inspect/proxy/inventory run only when invoked by the operator after the first
archive. This module never calls execute_session or launches a model canary.
"""
import argparse
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

import r005_supplement as s
from common import helper
from replay_comparison import verified_archive


def original(archive):
    archive=Path(archive).resolve();manifest,names=verified_archive(archive)
    if s.digest(archive/"runtime/freeze.json")!=s.ORIGINAL_FREEZE:
        raise ValueError("Not the frozen original comparison")
    return archive,manifest,names


def inspect(root,archive,agy_source):
    root=Path(root).resolve();archive,manifest,_=original(archive)
    if (root/"config").exists() or not root.is_relative_to(Path('/private/tmp')):
        raise ValueError("Use a new dedicated temporary root")
    old_root=Path(manifest['source_root'])
    if root==old_root or root.is_relative_to(old_root):raise ValueError("Do not reuse original state")
    for model in s.MODELS:
        config=s.load(archive/'config'/(model+'.json'))
        old_identity=s.load(archive/Path(config['cli_identity']).relative_to(old_root))
        binary=Path(agy_source) if model=='gemini' else Path(old_identity['resolved_binary'])
        if s.digest(binary)!=old_identity['sha256']:raise ValueError("CLI bytes differ from original")
        if model=='gemini':
            pinned=root/'identity/gemini-pinned/agy';pinned.parent.mkdir(parents=True,exist_ok=True)
            with pinned.open('xb') as stream:stream.write(binary.read_bytes())
            pinned.chmod(0o555);binary=pinned
        identity_path=root/'identity'/model/'identity.json'
        helper.inspect_cli(config['client'],str(binary),identity_path.parent)
        identity=s.load(identity_path)
        if any(identity[k]!=old_identity[k] for k in ('client','sha256','version')):
            raise ValueError("Fresh CLI identity mismatch")
        config['cli_identity']=str(identity_path)
        for item in config['read_exceptions']:
            if item['path']==old_identity['resolved_binary']:item['path']=str(binary)
        # proxy evidence is refreshed before qualification; do not inherit stale evidence.
        if config.get('proxy_exception'):config['proxy_exception']['evidence']=[]
        s.save(root/'config'/(model+'.json'),config,exclusive=True)
    cache=Path.home()/'.codex/models_cache.json';data=s.load(cache)
    row=next(x for x in data['models'] if x.get('slug')==s.MODELS['terra'][0])
    if s.MODELS['terra'][1] not in [x['effort'] for x in row['supported_reasoning_levels']]:
        raise ValueError("Original Terra effort absent from current inventory")
    s.save(root/'preflight/terra-model-inventory.json',{'utc':s.now(),'source':str(cache),'sha256':s.digest(cache),
        'fetched_at':data.get('fetched_at'),'client_version':data.get('client_version'),
        'model':{k:row.get(k) for k in ('slug','supported_reasoning_levels','context_window','visibility')},
        'request_count':0,'credential_content_read':False},exclusive=True)


def run_read_command(command):
    result=subprocess.run(command,capture_output=True,text=True,timeout=25)
    return {'command':command,'exit_code':result.returncode,'stdout':result.stdout,'stderr':result.stderr}


def proxy(root):
    root=Path(root).resolve();out=root/'preflight/proxy-verification'
    system=run_read_command(['/usr/sbin/scutil','--proxy'])
    if system['exit_code'] or any(re.search(r'\b'+key+r'\s*:\s*'+value+r'\b',system['stdout']) is None
            for key,value in [('HTTPSEnable','1'),('HTTPSPort','7897'),('HTTPSProxy',r'127\.0\.0\.1')]):
        raise ValueError('Existing exact system proxy is not active')
    sockets=run_read_command(['/usr/sbin/netstat','-anv','-p','tcp'])
    lines=[line for line in sockets['stdout'].splitlines() if '127.0.0.1.7897' in line and 'LISTEN' in line]
    if sockets['exit_code'] or not lines:raise ValueError('No exact proxy listener evidence')
    sockets['stdout']='\n'.join(lines)
    match=re.search(r'(\S+):(\d+)\s',lines[0])
    if not match:raise ValueError('Cannot identify proxy listener PID')
    processes=run_read_command(['/bin/ps','-p',match.group(2),'-o','pid=,ppid=,comm='])
    if processes['exit_code'] or not processes['stdout'].strip():raise ValueError('Listener process disappeared')
    https=run_read_command(['/usr/bin/curl','--proxy','http://127.0.0.1:7897','--output','/dev/null',
        '--silent','--show-error','--max-time','15','--write-out','%{http_code} %{remote_ip} %{remote_port} %{ssl_verify_result}','https://chatgpt.com/'])
    fields=https['stdout'].strip().split()
    if https['exit_code'] or len(fields)!=4 or fields[0]=='000' or fields[1:]!=['127.0.0.1','7897','0']:
        raise ValueError('HTTPS/TLS reachability via exact proxy failed')
    for name,value in [('system-proxy.json',system),('sockets.json',sockets),('processes.json',processes),('https.json',https)]:
        s.save(out/name,value,exclusive=True)
    path=root/'config/terra.json';config=s.load(path)
    config['proxy_exception']={'endpoint':'127.0.0.1:7897','authorization':'Inherited explicit root authorization; freshly reverified exact endpoint',
        'evidence':[s.bound(out/name) for name in ('system-proxy.json','sockets.json','processes.json','https.json')]}
    s.save(path,config)


def inventory(root):
    root=Path(root).resolve();session=root/'preflight/gemini-inventory-fresh'
    prompt=root/'preflight/inventory-unused-prompt.md'
    prompt.parent.mkdir(parents=True,exist_ok=True)
    with prompt.open('x') as stream:stream.write('Unused by non-inference models inventory.\n')
    config=s.load(root/'config/gemini.json')
    s.prepare_session(config,prompt,session);s.open_probe(session);s.network_probe(session)
    try:
        helper.auth_links(session)
        report=helper.inventory_agy(session)
    finally:helper.auth_links(session,remove=True)
    source=session/'runtime/preflight/stdout.txt'
    available=[line.split()[0] for line in source.read_text().splitlines() if line.strip()]
    if config['model'] not in available:raise ValueError('Original Gemini model/effort unavailable; no substitution')
    row={'utc':s.now(),'source':str(source),'source_sha256':s.digest(source),'available_models':available,
         'selected_model':config['model'],'selected_effort':config['effort'],'cli_identity':config['cli_identity'],
         'cli_identity_sha256':s.digest(config['cli_identity']),'directory_overrides_verified':report['directory_overrides_verified'],
         'request_count':0,'credential_content_read':False,'policy':'Keep original comparison model/effort even if inventory has added another level'}
    s.save(session/'runtime/inventory-summary.json',row,exclusive=True)
    s.save(root/'preflight/gemini-model-inventory.json',row,exclusive=True)


def qualify(root,archive):
    root=Path(root).resolve();archive,manifest,names=original(archive);old_root=Path(manifest['source_root'])
    controls=[];bindings=[]
    def archived(relative):
        matches=[name for name in (str(relative),'preflight-evidence/'+str(relative)) if name in names]
        if len(matches)!=1:raise ValueError('Ambiguous or missing original control evidence: '+str(relative))
        return archive/matches[0]
    for model in s.MODELS:
        config=s.same_config(root,archive,old_root,model)
        current_identity=s.load(config['cli_identity'])
        for mode in ('disabled','enabled'):
            verdict_path=archived(Path('preflight')/(model+'-'+mode+'-verdict.json'))
            verdict=s.load(verdict_path)
            execution_path=archived(Path(verdict['execution_path']).relative_to(old_root));execution=s.load(execution_path)
            identity=s.load(execution_path.parent/'cli-identity.json')
            if (verdict.get('passed') is not True or s.digest(execution_path)!=verdict['execution_sha256']
                    or execution.get('status')!='completed' or execution.get('request_count')!=1
                    or any(identity[k]!=current_identity[k] for k in ('client','sha256','version'))
                    or execution.get('requested_model')!=config['model'] or execution.get('requested_effort')!=config['effort']):
                raise ValueError('Original capability control does not match new configuration')
            searched=any(x['name'] in ('search_web','web_search') for x in execution.get('tool_events',[]))
            if searched!=(mode=='enabled'):raise ValueError('Capability tool evidence mismatch')
            prefix=str(execution_path.parent.parent.relative_to(archive))+'/'
            selected=[name for name in names if name.startswith(prefix)]
            files=[s.bound(archive/name) for name in sorted(selected)]+[s.bound(verdict_path)]
            controls.append({'model':model,'mode':mode,'verdict':s.bound(verdict_path),'files':files})
            bindings.extend(files)
        for path in (root/'config'/(model+'.json'),Path(config['cli_identity']),root/'preflight'/(model+'-model-inventory.json')):
            bindings.append(s.bound(path))
    if s.load(root/'preflight/gemini-model-inventory.json').get('request_count')!=0:
        raise ValueError('Inventory must be non-inference')
    reuse={'schema':'math-gauge.capability-control-reuse/v1','source_archive_manifest':s.bound(archive/'manifest.json'),
        'controls':controls,'new_non_math_requests':0,'new_mathematical_requests':0,
        'basis':'Exact CLI bytes/version, model/effort and unchanged isolated runner; fresh identity/inventory/proxy; fresh session probes at prepare'}
    path=root/'preflight/control-reuse.json';s.save(path,reuse,exclusive=True)
    bindings.extend([s.bound(path),s.bound(archive/'manifest.json')])
    for item in s.load(root/'config/terra.json').get('proxy_exception',{}).get('evidence',[]):bindings.append(item)
    unique={x['path']:x for x in bindings}
    s.save(root/'preflight/qualification.json',{'utc':s.now(),'passed':True,'mathematical_requests':0,'non_math_requests':0,
        'inherited_control_requests':len(controls),'controls':'explicitly inherited; not newly executed',
        'fresh_probes':'non-inference inventory checked; each mathematical session probed during prepare',
        'bindings':list(unique.values()),'credential_content_read':False},exclusive=True)


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('action',choices=['inspect','proxy','inventory','qualify'])
    p.add_argument('--root',type=Path,required=True);p.add_argument('--archive',type=Path);p.add_argument('--agy-source',type=Path)
    args=p.parse_args()
    if args.action in ('inspect','qualify') and not args.archive:p.error('archive required')
    if args.action=='inspect':
        if not args.agy_source:p.error('explicit original fixed AGY binary source required')
        inspect(args.root,args.archive,args.agy_source)
    elif args.action=='proxy':proxy(args.root)
    elif args.action=='inventory':inventory(args.root)
    else:qualify(args.root,args.archive)
    print(json.dumps({'action':args.action,'model_requests':0,'credential_content_read':False}))


if __name__=='__main__':main()
