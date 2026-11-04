"""One named, pinned Lake frontend adapter; base compiler evidence stays distinct."""
import os
from pathlib import Path
from .catalog import read_json,safe_file,digest_bytes
from .execution import _candidate_policy

SCHEMA='math-gauge.lake-frontend-adapter/v1'
NAME='lean4.29.1-macos-arm64-lake-plugin/v1'
LEAN_SHA256='b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997'
PLUGIN_SHA256='16f6fcceb7a3bc463c727d88f322c1de74e74286231d1aa3e607d086ac868e13'

def _require(value,message):
    if not value:raise ValueError('Lake frontend adapter: '+message)

def validate_frontend_adapter(directory,receipt):
    """Check explicit adapter lineage, trusted plugin and exact compile argv; no process."""
    directory=Path(directory).resolve();value=receipt.get('frontend_adapter')
    plugin_argv=any(str(arg).startswith(('--plugin','--load-dynlib','--setup'))
                    for module in receipt.get('modules',[]) for arg in module.get('argv',[]))
    if value is None:
        _require(not plugin_argv,'plugin compilation requires its named adapter receipt')
        return
    _require(isinstance(value,dict) and value.get('schema')==SCHEMA and value.get('name')==NAME,
             'unknown adapter schema or name')
    source=Path(__file__).resolve().parents[1]/'scripts/formal/lake_frontend_adapter.py'
    _require(value.get('source_sha256')==digest_bytes(source.read_bytes()),'adapter source identity changed')
    dependency=receipt['dependency'];lean=Path(dependency['lean']).resolve()
    plugin=lean.parent.parent/'lib/lean/libLake_shared.dylib'
    _require(dependency.get('lean_sha256')==LEAN_SHA256 and digest_bytes(lean.read_bytes())==LEAN_SHA256
             and value.get('plugin_path')==str(plugin) and value.get('plugin_sha256')==PLUGIN_SHA256
             and digest_bytes(plugin.read_bytes())==PLUGIN_SHA256,'official toolchain or Lake plugin identity changed')
    descriptor=value.get('original_failed_report',{});old_path=safe_file(directory,descriptor.get('path',''))
    _require(digest_bytes(old_path.read_bytes())==descriptor.get('sha256'),'original failed report changed')
    old=read_json(old_path)
    _require(old.get('schema')=='math-gauge.candidate-lean/v1' and old.get('status')=='compile_error'
             and old.get('source_repaired') is False,'original frontend failure is unavailable')
    for key in ('case_id','response_sha256','request_sha256','candidate_message_sha256','group_contract_sha256',
                'files_sha256','input_files_sha256','source_spans','manifest_sha256','artifact_sha256',
                'engine_identity','engine_sha256','alignment_manifest_sha256','dependency'):
        _require(old.get(key)==receipt.get(key),'original source, artifact or base engine differs: '+key)
    modules=receipt['modules'];before=old.get('modules',[])
    _require(len(before)>=2 and len(modules)==len(before)+1 and before[-1].get('module')=='lakefile'
             and before[-1].get('exit_code')!=0 and before[-1].get('timeout') is False,
             'expected one original Lake configuration failure')
    _require(value.get('reused_module_names')==[m['module'] for m in before[:-1]],'reused module inventory changed')
    for previous,current in zip(before[:-1],modules[:-2]):
        _require(previous.get('exit_code')==0 and previous.get('timeout') is False
                 and current.get('reused_original_compilation') is True
                 and not any(str(arg).startswith(('--plugin','--load-dynlib','--setup')) for arg in previous.get('argv',[]))
                 and all(previous.get(k)==current.get(k) for k in ('module','source_sha256','exit_code','timeout','argv','log_sha256','olean_sha256')),
                 'original successful module was changed or recompiled')
    failure=value.get('original_failure_log',{});failure_path=safe_file(directory,failure.get('path',''))
    failure_raw=failure_path.read_bytes()
    _require(digest_bytes(failure_raw)==failure.get('sha256')==before[-1].get('log_sha256')
             and b'elaboration function for `Lake.DSL.' in failure_raw and b'has not been implemented' in failure_raw,'original Lake elaborator failure log changed')
    environment=value.get('environment',{});stage=Path(environment.get('stage',''));build=Path(environment.get('build',''));scratch=Path(environment.get('scratch',''))
    _require(all(path.is_absolute() for path in (stage,build,scratch)) and len({stage,build,scratch})==3
             and all(not x.is_relative_to(y) and not y.is_relative_to(x) for x,y in ((stage,build),(stage,scratch),(build,scratch))),
             'compiler directories must be disjoint absolute paths')
    _require(environment.get('LEAN_PATH')==os.pathsep.join([str(build),*dependency['search_paths']]),'compiler import paths changed')
    policy=safe_file(directory,'compiler.sb').read_bytes()
    _require(policy==_candidate_policy(stage,build,scratch,dependency).encode(),'strict compiler policy changed')
    policy_argument=value.get('policy_argument')
    _require(isinstance(policy_argument,str) and Path(policy_argument).is_absolute(),'actual sandbox policy argument missing')
    _require(modules[-2].get('module')=='lakefile' and modules[-2].get('source_sha256')==before[-1].get('source_sha256'),
             'configuration source changed')
    for module in modules[-2:]:
        name=module['module'];expected=['/usr/bin/sandbox-exec','-f',policy_argument,str(lean),'--plugin='+str(plugin),
            '--root='+str(stage),'-o',str(build/(name+'.olean')),str(stage/(name+'.lean'))]
        _require(module.get('argv')==expected and module.get('reused_original_compilation') is False,
                 'adapted compiler argv differs from the official isolated frontend')
    diagnostic=value.get('diagnostic_receipt',{});diagnostic_path=safe_file(directory,diagnostic.get('path',''))
    _require(digest_bytes(diagnostic_path.read_bytes())==diagnostic.get('sha256'),'diagnostic receipt changed')
    trace=read_json(diagnostic_path)
    _require(trace.get('schema')=='math-gauge.named-frontend-diagnostic/v1' and trace.get('status')=='passed'
             and trace.get('source_report_sha256')==descriptor['sha256']
             and trace.get('source_response_sha256')==receipt.get('response_sha256')
             and trace.get('base_engine_identity')==receipt.get('engine_identity')
             and trace.get('environment')==environment and trace.get('isolation')==receipt.get('isolation')
             and trace.get('audit')==receipt.get('audit') and trace.get('source_repaired') is False
             and trace.get('candidate_calls')==0 and trace.get('script_executions')==0,
             'diagnostic source, audit or execution identity changed')
    _require(trace.get('adapter',{}).get('name')==NAME
             and trace['adapter'].get('source_sha256')==value['source_sha256']
             and trace['adapter'].get('plugin_path')==str(plugin)
             and trace['adapter'].get('plugin_sha256')==PLUGIN_SHA256,'diagnostic adapter identity changed')
    checked=('module','source_sha256','exit_code','timeout','argv','log_sha256','olean_sha256','reused_original_compilation')
    _require(len(trace.get('modules',[]))==len(modules) and all(
             all(a.get(k)==b.get(k) for k in checked) for a,b in zip(trace['modules'],modules)),
             'diagnostic module trace changed')
    _require(value.get('script_executions')==0 and value.get('candidate_calls')==0
             and value.get('source_bytes_changed') is False and value.get('base_engine_files_unchanged') is True,
             'adapter must preserve source and base engine attribution without running scripts or models')
