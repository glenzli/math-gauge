"""Offline synthetic diagnostics only; no model requests or Lean compilation."""
import copy
import json
import shutil
import sys
from pathlib import Path

ROOT = Path('/Users/g4i/lab/math-gauge')
OUT = Path('/private/tmp/math-gauge-strict-20261030/engineering')
sys.path.insert(0, str(ROOT))
from math_gauge.catalog import Suite, digest_bytes, read_json, write_json
from math_gauge.execution import run
from math_gauge.review import apply_reviews, report, templates

work = OUT / 'contract-probes'
work.mkdir(exist_ok=True)
suite_path = work / 'suite'
suite_path.mkdir(exist_ok=True)
legacy = ROOT / 'archive/legacy-v0/public'
meta = read_json(legacy / 'suite.json')
meta['cases'] = ['MG-D001/case.json']
write_json(suite_path / 'suite.json', meta)
shutil.copyfile(legacy / 'sources.json', suite_path / 'sources.json')
shutil.copytree(legacy / 'MG-D001', suite_path / 'MG-D001', dirs_exist_ok=True)
shutil.copytree(legacy / 'common', suite_path / 'common', dirs_exist_ok=True)
case_path = suite_path / 'MG-D001/case.json'
case = read_json(case_path)
case['group_contract'] = 'MG-D001/contract.json'
write_json(case_path, case)
contract = {
    'schema': 'math-gauge.group-contract/v1', 'id': 'MG-D001',
    'kind': 'progressive', 'stages': [
        {'id': 'S' + str(i), 'kind': 'prove', 'depends_on': [],
         'assumptions': ['synthetic fixture only'], 'expected': 'true',
         'required_evidence': ['synthetic fixture proof'],
         'critical_errors': ['synthetic fixture error'], 'points': 20,
         'lean_required': True} for i in range(1, 6)
    ],
    'turns': [{'stage_id': 'S5', 'earlier_stage_ids': ['S1'],
               'changed_assumptions': 'synthetic fixture change', 'expected_truth': 'true',
               'mechanism': 'synthetic fixture', 'tempting_invalid_transfer': 'synthetic fixture',
               'correct_boundary': 'synthetic fixture'}]
}
response = '```lean filename=Other.lean\ntheorem answer : True := True.intro\n```\n'
responses = work / 'responses.json'
write_json(responses, {'MG-D001': response})

def make_run(name, frozen):
    write_json(suite_path / case['group_contract'], frozen)
    path = work / name
    run(Suite.load(suite_path), path, ['MG-D001'], replay=responses)
    return path

weak = make_run('weak-contract', contract)
strong_contract = copy.deepcopy(contract)
strong_contract['required_output_files'] = ['Main.lean']
strong = make_run('strong-contract', strong_contract)
weak_record = read_json(weak / 'MG-D001/record.json')
strong_record = read_json(strong / 'MG-D001/record.json')
assert weak_record['request_sha256'] == strong_record['request_sha256']
assert weak_record['response_sha256'] == strong_record['response_sha256']
assert weak_record['group_contract_sha256'] != strong_record['group_contract_sha256']

# This mimics the relevant fields of a weak-contract compilation receipt. It is
# explicitly a fixture and is never represented as actual compiler evidence.
receipt = {
    'schema': 'math-gauge.candidate-lean/v1', 'case_id': 'MG-D001',
    'response_sha256': weak_record['response_sha256'],
    'request_sha256': weak_record['request_sha256'],
    'status': 'passed', 'source_repaired': False, 'fixture_only': True,
    'fixture_compilation_performed': False,
    'files_sha256': {'Other.lean': digest_bytes(b'theorem answer : True := True.intro\n')},
    'audit': {'declarations': [{'module': 'Other', 'name': 'answer'}]},
}
receipt_path = strong / 'weak-contract-receipt-fixture.json'
write_json(receipt_path, receipt)
entry = templates(strong)[0]
entry.update(reviewer='Engineering synthetic fixture', reviewer_kind='fixture',
             decision='pass', assumption_fidelity='clean', proof_validity='valid',
             scope_accuracy='correct', notes='Synthetic validator test only; no mathematical claim.',
             candidate_lean_report=receipt_path.name,
             candidate_lean_report_sha256=digest_bytes(receipt_path.read_bytes()))
for stage in entry['stages']:
    stage.update(decision='pass', assumption_fidelity='clean', proof_validity='valid',
                 scope_accuracy='correct', failure_category='none', lean_status='passed',
                 declarations=[{'file': 'Other.lean', 'name': 'answer'}],
                 notes='Synthetic validator test only; no mathematical claim.')
apply_reviews(strong, [entry])
result, _ = report(strong)
accepted_stages = result['group_diagnostics']['MG-D001']['stage_passes']
assert accepted_stages == 5

# A review report currently checks response/contract bytes but not the frozen
# request bytes. The paired comparison path has a separate input-hash check.
request_path = strong / 'MG-D001/solver/request.json'
request = read_json(request_path)
request['task'] = 'Changed after execution; synthetic fixture only.'
write_json(request_path, request)
changed_request_hash = digest_bytes(json.dumps(request, ensure_ascii=False, sort_keys=True).encode())
assert changed_request_hash != strong_record['request_sha256']
result, _ = report(strong)
assert result['group_diagnostics']['MG-D001']['stage_passes'] == 5

diagnostics = {
    'schema': 'math-gauge.strict-contract-probes/v1',
    'candidate_model_requests': 0, 'lean_compilations': 0,
    'fixture_only': True,
    'cross_contract_receipt': {
        'weak_contract_sha256': weak_record['group_contract_sha256'],
        'strong_contract_sha256': strong_record['group_contract_sha256'],
        'request_response_hashes_identical': True,
        'required_output_files_in_strong_contract': ['Main.lean'],
        'receipt_files': ['Other.lean'],
        'accepted_stage_passes': accepted_stages,
        'limitation': 'Synthetic receipt validates the acceptance path; no Lean compilation was performed. The runtime-generated receipt has no group_contract_sha256 field, so a genuine receipt also lacks this binding.'
    },
    'changed_request_report': {
        'record_request_sha256': strong_record['request_sha256'],
        'actual_changed_request_sha256': changed_request_hash,
        'report_accepted': True,
        'limitation': 'The paired compare_models path independently rejects changed request hashes; this diagnostic concerns inspect_run/templates/apply_reviews/report only.'
    }
}
write_json(OUT / 'contract-probes.json', diagnostics)
print(json.dumps(diagnostics, ensure_ascii=False, indent=2))
