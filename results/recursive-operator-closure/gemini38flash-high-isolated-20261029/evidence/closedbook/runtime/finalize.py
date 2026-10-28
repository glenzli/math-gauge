from pathlib import Path
import json,hashlib,datetime,os,re,tarfile,subprocess
b=Path('/private/tmp/math-gauge-gemini38flash-closedbook-20261029')
diag=Path('/private/tmp/math-gauge-gemini38flash-20261029')
neg=Path('/private/tmp/math-gauge-agy-tools-preflight-20261029')
pos=Path('/private/tmp/math-gauge-agy-tools-enabled-control-20261029')
m=json.loads((b/'output/run-metadata.json').read_text())
assert m['status']=='completed',m['status']
assert m['request_events']==1 and m['result_count']==1
assert not any(x.get('tool_name') not in ['finish','manage_task'] for x in m['tool_steps']),m['tool_steps']
cli=Path('/opt/homebrew/bin/agy')
initial=json.loads((b/'runtime/provenance.json').read_text())
final_hash=hashlib.sha256(cli.read_bytes()).hexdigest()
assert final_hash==initial['cli_sha256'],'CLI identity changed'
request=json.loads((b/'runtime/request.ndjson').read_text())
assert request['message']['content'].encode()==(b/'input/task.md').read_bytes()
assert hashlib.sha256((b/'input/task.md').read_bytes()).hexdigest()==initial['input_sha256']
checks=json.loads((b/'output/actual-process-sandbox-check.json').read_text())
probe=json.loads((b/'runtime/probe-result.json').read_text())
assert len(probe['deny'])==12 and all(x.get('outcome')=='DENIED' for x in probe['deny'])
assert checks[0]['result']==0 and all(x['result']>0 for x in checks[1:])
meta=dict(m)
meta['classification']='formal closed-book comparison'
meta['tool_configuration']='custom primary agent text-only, configured tools=[finish], empty Markdown body; platform task bookkeeping retained'
(b/'output/run-metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
removed=[]
for rel in ['jetski-standalone-oauth-token','antigravity-cli/antigravity-oauth-token']:
 p=b/'state'/rel
 if p.is_symlink():p.unlink();removed.append(rel)
(b/'runtime/credential-link-cleanup.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'removed_only_links':removed,'original_credentials_modified':False},indent=2)+'\n')
p=b/'output/events.ndjson';q=b/'output/stdout.ndjson'
if not q.exists():os.link(p,q)
r=m['result_metadata']
readme='''# Gemini 3.8 Flash High: formal closed-book comparison

Antigravity CLI 1.4.9 ran one new conversation in a fresh temporary data directory. Model: `gemini-3.8-flash-high`; effort: `high`. No upgrade was performed by the isolation agent.

The first and only user message was the unchanged task. Input SHA-256: `779bf275a6184fb848a12f3d72089a21d4704513512e10323aa48d4ee462cecd`. No hints, answers, scoring, history, Lean source or follow-up feedback were submitted.

A documented custom primary agent selected with `--agent text-only` configured `tools: [finish]`, a local response-ending tool. The platform also retained its built-in task bookkeeping capability; any manage_task steps are listed in run-metadata.json. No external retrieval tools were used. Its Markdown body was empty. The exact file is `runtime/agent.md`. A separate paired capability test requested web search: the finish-only configuration made search unavailable, while adding search_web produced a completed search. This test did not use the math problem. The CLI init.tools array is the global registry in this version and does not reflect the custom primary-agent allowlist; raw init is retained without alteration.

The operating-system policy in `runtime/outer.sb` denied all user-home data except the exact OAuth/installation files and CLI binaries needed for startup; it also denied other temporary directories, including the prior diagnostic answer and both canary contexts. User-home writes and outbound localhost connections were denied. The language server ran in the newly isolated agy PID, not an existing service. `output/process-evidence.json` captures executable names and sockets without process-argument tokens.

The actual file-open probe read the copied task successfully and returned EPERM for 12 forbidden paths. The actual agy process was separately checked against the same 1 positive and 12 negative paths. See `runtime/probe-result.json` and `output/actual-process-sandbox-check.json`.

Raw stdout is `output/events.ndjson`, also linked as `output/stdout.ndjson`. Raw stderr is `output/stderr.txt`. `output/response.md` is exactly the final result.response UTF-8 text, with no added text or newline. `output/result-event.json` is the exact original result-event line. Raw files are read-only and hashed in `runtime/raw-file-manifest.json`.

The earlier run is preserved separately as a tool-mismatch diagnostic. The decision to fix the search-tool gap and run this comparison was recorded before that diagnostic emitted its final answer. No mathematical output was reviewed by the CLI/isolation agent or used to change the problem, prompts or sample selection. See `runtime/attempt-ledger.json` and the diagnostic `runtime/tool-mismatch-decision.json`.

Do not archive state/; it is private runtime storage. Only credential symlinks were used, and all links were removed after the completed run. The deliverable archive uses a file whitelist and contains no state directory or credential links.
'''
readme+=f"\nConversation: `{r['conversation_id']}`. Reported model duration: {r['duration_seconds']} seconds. Host wall time: {m['wall_seconds']:.3f} seconds. Usage: `{json.dumps(r['usage'],separators=(',',':'))}`. Observed external tool steps: 0.\n"
(b/'README.md').write_text(readme)
verification={'completed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'cli_version':initial['cli_version'],'cli_sha256':final_hash,'model':'gemini-3.8-flash-high','effort':'high','agent_file_sha256':hashlib.sha256((b/'runtime/agent.md').read_bytes()).hexdigest(),'agent_body_empty':(b/'runtime/agent.md').read_text().split('---',2)[2].strip()=='','only_user_content_exact':True,'user_request_count':m['request_events'],'positive_probe_sha256':probe['allow']['sha256'],'negative_actual_open_probe_count':len(probe['deny']),'negative_actual_pid_check_count':len(checks)-1,'all_actual_file_probes_passed':True,'all_actual_pid_checks_passed':True,'observed_tool_steps':m['tool_steps'],'observed_external_tool_steps':0,'platform_bookkeeping_tool_steps':[x for x in m['tool_steps'] if x.get('tool_name')=='manage_task'],'capability_ab_test_passed':json.loads((neg/'output/comparison-verdict.json').read_text())['passed'],'no_math_answer_review_by_isolation_agent':True,'global_settings_modified':False,'upgrade_performed_by_isolation_agent':False}
(b/'runtime/verification-summary.json').write_text(json.dumps(verification,indent=2)+'\n')
ledger=json.loads((b/'runtime/attempt-ledger.json').read_text())
ledger['math_requests'][1]['comparison_eligible']=True
(b/'runtime/attempt-ledger.json').write_text(json.dumps(ledger,indent=2)+'\n')
for root in [b,diag,neg,pos]:
 files=[]
 for rel in ['input/task.md','runtime/request.ndjson','runtime/outer.sb','runtime/agent.md','output/events.ndjson','output/stdout.ndjson','output/stderr.txt','output/result-event.json','output/response.md','output/agy.log']:
  p=root/rel
  if p.is_file() and not p.is_symlink():files.append({'path':rel,'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
 (root/'runtime/raw-file-manifest.json').write_text(json.dumps(files,indent=2)+'\n')
 for rel in ['output/events.ndjson','output/stdout.ndjson','output/stderr.txt','output/result-event.json','output/response.md','output/agy.log']:
  p=root/rel
  if p.is_file():p.chmod(0o444)
 patterns=[rb'(?i)(?:access_token|refresh_token|id_token|authorization|csrf_token|host_bridge_token)\s*[:=]\s*["\']?[A-Za-z0-9._-]{12,}']
 scans=[]
 for rel in ['output/events.ndjson','output/stderr.txt','output/agy.log']:
  p=root/rel
  if p.exists():scans.append({'path':rel,'credential_pattern_hits':sum(len(re.findall(x,p.read_bytes())) for x in patterns)})
 assert not any(x['credential_pattern_hits'] for x in scans),str(root)
 (root/'runtime/output-credential-pattern-scan.json').write_text(json.dumps(scans,indent=2)+'\n')
archive=Path('/private/tmp/math-gauge-gemini38flash-evidence-20261029.tar.gz')
manifest=[]
with tarfile.open(archive,'w:gz',dereference=False) as tar:
 for label,root in [('closedbook',b),('diagnostic',diag),('tool-canary-disabled',neg),('tool-canary-enabled',pos)]:
  files=[]
  if (root/'README.md').is_file():files.append(root/'README.md')
  for directory in ['input','runtime','output','preflight','startup01']:
   d=root/directory
   if not d.is_dir():continue
   for p in sorted(d.iterdir()):
    if p.is_file() and not p.is_symlink() and p.suffix in ['.md','.py','.sb','.json','.ndjson','.txt','.stdout','.stderr','.log']:files.append(p)
  for p in files:
   relative=p.relative_to(root)
   archive_path=str(Path(label)/relative)
   tar.add(p,arcname=archive_path,recursive=False)
   manifest.append({'path':archive_path,'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
delivery={'archive':str(archive),'archive_bytes':archive.stat().st_size,'archive_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'files':manifest,'closedbook_response':str(b/'output/response.md'),'closedbook_result_metadata':r,'diagnostic_response':str(diag/'output/response.md'),'no_state_or_credential_links_in_archive':True}
(b/'runtime/delivery-manifest.json').write_text(json.dumps(delivery,indent=2)+'\n')
print(json.dumps({k:v for k,v in delivery.items() if k!='files'},ensure_ascii=False,indent=2))
