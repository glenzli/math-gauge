from pathlib import Path
import os,subprocess,json,datetime,sys
b=Path('/private/tmp/math-gauge-gemini38flash-20261029')
e={k:v for k,v in os.environ.items() if k in ['HOME','USER','LOGNAME','SHELL','PATH','LANG','LC_ALL','LC_CTYPE','HTTPS_PROXY','HTTP_PROXY','ALL_PROXY','NO_PROXY','https_proxy','http_proxy','all_proxy','no_proxy','SSL_CERT_FILE','SSL_CERT_DIR','TERM']}
e['TMPDIR']=str(b/'runtime/tmp')
e['AGY_CLI_DISABLE_AUTO_UPDATE']='1'
cmd=['/usr/bin/sandbox-exec','-f',str(b/'runtime/outer.sb'),'/opt/homebrew/bin/agy','--gemini_dir',str(b/'state'),'--app_data_dir','antigravity-cli','--log-file',str(b/'preflight/attempt04-models.log'),'models']
(b/'preflight/attempt04-models-command.json').write_text(json.dumps({'argv':cmd,'environment_keys':sorted(e),'directory_overrides':{k:e[k] for k in ['TMPDIR','AGY_CLI_DISABLE_AUTO_UPDATE']}},indent=2)+'\n')
with (b/'preflight/attempt04-models.stdout').open('wb') as out,(b/'preflight/attempt04-models.stderr').open('wb') as err:
 p=subprocess.run(cmd,cwd=b/'work',env=e,stdout=out,stderr=err,timeout=120)
print(json.dumps({'exit_code':p.returncode,'new_state_file_count':len(list((b/'state').rglob('*')))}))
print((b/'preflight/attempt04-models.stderr').read_text()[:3000])
print((b/'preflight/attempt04-models.stdout').read_text()[:4000])
