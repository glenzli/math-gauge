from pathlib import Path
from collections import Counter
import hashlib,json,sys
R=Path('/Users/g4i/lab/math-gauge');sys.path.insert(0,str(R));from math_gauge.catalog import Suite,candidate_message
sys.path.insert(0,str(R/'scripts/formal'));import verify
C=R/'cases/public/MG-R005';F=C/'formal';S=Path('/private/tmp/math-gauge-r005-adoption-20261030')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def J(p):return json.loads(Path(p).read_text())
def W(p,x):Path(p).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
b=J(S/'baseline.json');s=Suite.load(C.parent);c=s.cases['MG-R005'];v=J(C/'review.json');m=J(F/'manifest.json');r=J(F/'verification-report.json');f=J(F/'current-formal.json')
assert s.metadata['version']=='0.4.1' and c['version']==v['version']==m['case_version']==f['case_version']=='0.3.1'
assert c['status']=='draft' and c['review']['human']==v['human']==f['human_review']=='pending'
assert c['solver_files']==[] and c['candidate_instruction']=='' and c['lean_checks']==[]
request=s.prepare(c,S/'candidate-projection');message=candidate_message(request)
assert message==(C/'task.md').read_text() and set(p.name for p in (S/'candidate-projection').iterdir())=={'prompt.md','request.json'}
assert 'result' not in v['current_calibration'] and 'new_model_runs' not in v and v['current_calibration']['record_owner']=='separate-results'
assert v['historical_calibration']['calibration']==J(C/'history/v0.3.0/review.json')['current_calibration']
for field,name in [('candidate_task_sha256','task.md'),('reference_sha256','reference.md'),('rubric_sha256','rubric.json'),('author_design_sha256','design.json')]:assert v[field]==H(C/name)
for rel,h in J(C/'reviews/v0.3.1-preparation.json')['source_files'].items():assert H(C/rel)==h
assert H(C/'reviews/v0.3.1-semantic.json')==H(R/'results/full-comparison-20261030/reviews/r005-v031-material.json')
for p,h in J(C/'history/v0.3.0/snapshot.json')['files_sha256'].items():assert H(C/'history/v0.3.0'/p)==h
historical_case_files=0
for p,h in b['case_files_sha256'].items():
 if p.startswith('MG-R005/'):
  assert H(C/'history/v0.3.0'/p.removeprefix('MG-R005/'))==h;historical_case_files+=1
 else:assert H(C.parent/p)==h,p
for cid,h in b['candidate_messages_sha256'].items():
 if cid!='MG-R005':assert hashlib.sha256(candidate_message(s.request(s.cases[cid])).encode()).hexdigest()==h,cid
for p,h in b['gates'].items():assert H(R/p)==h
verify.validate_case(F/'manifest.json')
assert r['status']==f['status']=='passed' and r['fresh_output'] and not r['source_side_oleans_reused'] and not r['sibling_case_outputs_used']
assert f['source_manifest_sha256']==f['compiled_manifest_sha256']==r['manifest_sha256']==H(F/'manifest.json')
assert f['verification_report_sha256']==H(F/'verification-report.json')==v['formalization']['verification_report_sha256']
assert f['declaration_inventory_sha256']==H(F/'declarations.json')
assert f['current_audit_log_sha256']==H(F/'axiom-audit.log')==H(F/'logs/CurrentAudit.log')
assert f['current_audit_sha256']==H(F/'CurrentAudit.lean')
assert v['formalization']['current_evidence_sha256']==H(F/'current-formal.json')
assert not f['coverage_binding_reused_without_recompilation'] and 'evidence_reuse_receipt' not in f and not (F/'evidence-reuse.json').exists()
assert len(r['modules'])==5 and all(x['exit_code']==0 and H(F/x['log'])==x['log_sha256'] for x in r['modules'])
assert r['audit']['command']['exit_code']==0
assert r['audit']['summary']['declaration_count']==f['dynamic_declaration_count']==119
assert dict(Counter(x['kind'] for x in J(F/'declarations.json')))==f['dynamic_declaration_kinds']
assert r['audit']['summary']['unexpected_axioms']==[]
assert r['dependency']['mathlib_tracked_state']['clean']
assert r['dependency']['dependency_project_build_excluded'] and r['dependency']['ambient_lean_path_excluded']
assert H(F/'verification-report.json')==H(S/'fresh-five-module/MG-R005/report.json')
assert all(str(C.parent/p) for p in c['evaluator_files'])
all_local={str(p.relative_to(C)) for p in C.rglob('*') if p.is_file()}
assert all_local=={'case.json','task.md','reference.md','rubric.json'}|{p.removeprefix('MG-R005/') for p in c['evaluator_files']}
report={'schema':'math-gauge.case-adoption-metadata-check/v1','case_id':'MG-R005','case_version':'0.3.1','suite_version':'0.4.1','suite_sha256':s.sha256,'status':'passed','five_prepared_files_exact':True,'other_19_case_files_unchanged':True,'other_19_candidate_messages_unchanged':True,'previous_case_files_preserved_byte_identically':historical_case_files,'original_archive_and_offline_gate_bytes_unchanged':True,'candidate_projection_task_only':True,'candidate_message_sha256':hashlib.sha256(message.encode()).hexdigest(),'candidate_request_json_sha256':H(S/'candidate-projection/request.json'),'request_json_encoding':'math_gauge.catalog.write_json: ensure_ascii=False, indent=2, terminal newline','all_evaluator_files_hidden':True,'evaluator_file_count':len(c['evaluator_files']),'current_model_scores_or_mutable_counts_embedded':False,'human_approved':0,'source_manifest_equals_compiled_manifest':True,'source_module_count':5,'dynamic_declaration_count':119,'dynamic_declaration_kinds':f['dynamic_declaration_kinds'],'axiom_union':f['axiom_union'],'scoped_verifier_static_validation':'passed','current_files_sha256':{str(p.relative_to(C)):H(p) for p in sorted(C.rglob('*')) if p.is_file() and 'history' not in p.relative_to(C).parts},'suite_json_sha256':H(C.parent/'suite.json'),'public_readme_sha256':H(C.parent/'README.md')}
W(S/'metadata-checks.json',report)
print(json.dumps({k:v for k,v in report.items() if k!='current_files_sha256'},ensure_ascii=False,indent=2))
