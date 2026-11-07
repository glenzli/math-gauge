"""Source-bound background-audit evidence. All point arithmetic lives in scoring.py."""
import re

COMPONENT = 'background-check'
PUBLIC_CASE_IDS = ('MG-BC001', 'MG-BC002')
CRITERIA = ('gap-diagnosis', 'model-specific-certificate', 'complete-correction')

def validate_policy(policy):
    required = {'schema':'math-gauge.background-check-policy/v1','version':'0.1.0',
        'benchmark_version':'0.6.0','initial_attempt_labels':['A1'],
        'public_case_ids':list(PUBLIC_CASE_IDS),'private_cases':2,'families':4,
        'component_weight':10,'family_aggregation':'equal','level_maximum':3,
        'false_actual_endorsement_level':0,'downstream_calculation_is_research_credit':False,
        'followups_replace_initial':False,'local_tools_allowed':True,'search_allowed':False,
        'tool_network_access':False,'post_observation':True,'human_review':'pending',
        'formal_comparison_eligible':False}
    if not isinstance(policy,dict) or any(policy.get(k)!=v for k,v in required.items()):
        raise ValueError('Unsupported background-check policy')
    return policy

def validate_inputs(data,policy):
    validate_policy(policy)
    if (not isinstance(data,dict) or data.get('schema')!='math-gauge.background-check-inputs/v1'
        or data.get('benchmark_version')!='0.6.0' or data.get('attempt_labels')!=['A1']
        or data.get('policy')!=policy or data.get('human_review')!='pending'
        or data.get('formal_comparison_eligible') is not False):
        raise ValueError('Invalid background-check evidence identity')
    cases=data.get('case_index',[]);index={c.get('case_id'):c for c in cases}
    if (len(index)!=4 or len(cases)!=4 or len({c.get('family_id') for c in cases})!=4
        or {c['case_id'] for c in cases if c.get('source_visibility')=='public'}!=set(PUBLIC_CASE_IDS)
        or sum(c.get('source_visibility')=='private' for c in cases)!=2):
        raise ValueError('Background-check evidence changed its fixed public/private families')
    for cid,c in index.items():
        if (not isinstance(cid,str) or not re.fullmatch(r'[A-Za-z0-9_-]+',cid)
            or c.get('family_id')!=cid or c.get('component')!=COMPONENT
            or c.get('contract_kind')!='written_proof' or c.get('task_kind')!='written'
            or c.get('total_weight')!=3 or c.get('criteria')!=[
                {'criterion_id':i,'points':1} for i in CRITERIA]
            or any(not re.fullmatch(r'[0-9a-f]{64}',c.get(k,'')) for k in ('task_sha256','contract_sha256'))):
            raise ValueError('Invalid background-check mathematical contract')
    rows=data.get('slots',[])
    if len(rows)!=4 or {r.get('case_id') for r in rows}!=set(index):
        raise ValueError('Background-check evidence must retain every fixed slot')
    for row in rows:
        if row.get('slot_id')!=row['case_id']+':A1' or row.get('attempt_label')!='A1':
            raise ValueError('Background checks use independent A1 only')
        status=row.get('status')
        if status=='not_run':
            if any(row.get(k) is not None for k in ('background_R','complete','false_endorsement','response','review')):
                raise ValueError('Unrun background checks stay unknown')
        elif status=='delivery_failed':
            if row.get('background_R')!=0 or row.get('complete') is not False or row.get('response') is not None or not isinstance(row.get('execution'),dict):
                raise ValueError('Invalid background delivery failure')
        elif status=='response_received_execution_unverified':
            level=row.get('background_R')
            if (type(level) is not int or level not in range(4) or type(row.get('complete')) is not bool
                or type(row.get('false_endorsement')) is not bool
                or row['false_endorsement'] and level!=0 or row['complete'] and level!=3
                or any(not isinstance(row.get(k),dict) for k in ('response','review'))):
                raise ValueError('Background diagnosis, completeness or false endorsement conflict')
        else:
            raise ValueError('Unknown background-check answer status')
    return data
