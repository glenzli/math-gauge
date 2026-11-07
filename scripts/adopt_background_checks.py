#!/usr/bin/env python3
"""Adopt the four user-selected background audits and retained exact answers. No model calls."""
import argparse,copy,json,shutil,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from scripts.adopt_theorem_extensions import load,write,digest,copy_exact
from scripts.current_assessment import configure_current
from math_gauge.catalog import Suite,candidate_message,assessment_weights
from math_gauge.records import descriptor
from math_gauge.background_check import validate_policy,CRITERIA

MODELS={'terra-6.1-max':'terra','gemini-3.8-flash-high':'gemini'}

def adopt(private_root):
    config=load(private_root/'protocol/background-check-adoption.json')
    cases_config=[(c['source_alias'],c['case_id'],c['visibility'],c['title']) for c in config['cases']]
    source=private_root/config['candidate_root']
    plan=load(source/'protocol/test-plan.json');originals={c['id']:c for c in plan['cases']}
    policy={'schema':'math-gauge.background-check-policy/v1','version':'0.1.0','benchmark_version':'0.6.0',
        'initial_attempt_labels':['A1'],'public_case_ids':['MG-BC001','MG-BC002'],'private_cases':2,'families':4,
        'component_weight':10,'family_aggregation':'equal','level_maximum':3,'false_actual_endorsement_level':0,
        'downstream_calculation_is_research_credit':False,'followups_replace_initial':False,
        'local_tools_allowed':True,'search_allowed':False,'tool_network_access':False,
        'post_observation':True,'human_review':'pending','formal_comparison_eligible':False,
        'levels':{'0':'未纠正实际背景，或仍作出错误的实际承诺；安全但未诊断也可为0，另报S状态。',
            '1':'准确定位缺失条件或非法推广，但缺乏本模型的有效证据。',
            '2':'有正确模型特定机制与实质反证贡献，所需证据仍有明确缺口。',
            '3':'完成本模型背景纠错及支持该纠错的完整有效证据。'},
        'strict_rule':'R3 and every substantive task requirement verified complete; original loose source thresholds do not imply Strict.',
        'partial_rule':'Each family contributes R/3 of its equal share. Correct downstream calculations are separately reported, not background research credit.',
        'classification_basis':'The mathematical work requested, not whether a particular model recognizes the issue. B01 remains background checking, with construction completeness separately recorded.',
        'selection':'Explicit user-selected four cases after exploratory answers; not an unseen holdout or synchronized formal comparison.',
        'false_actual_endorsement_definition':'最终仍接受题面针对的错误背景或部署认证；原答其他数学错误另列并影响证据级别和Strict，不与目标错误混为一谈。',
        'ordinal_scale_notice':'观察后的有序证据级别，不声称已校准为等距能力尺度。'}
    validate_policy(policy);write(ROOT/'protocol/background-check-policy.json',policy)
    for alias,cid,visibility,title in cases_config:
        old=originals[alias];root=ROOT if visibility=='public' else private_root
        folder=root/'cases/background-check'/cid;folder.mkdir(parents=True,exist_ok=True)
        copy_exact(source/old['input'],folder/'task.md')
        copy_exact(source/old['reference'],folder/'reference.md')
        copy_exact(source/old['rubric'],folder/'source-rubric.md')
        criteria=[{'id':ident,'title':title_,'points':1,'required_evidence':[detail,
                    '按原样对象、域、量词和结论审核；认可完整替代证据。'],
                'critical_errors':['把正确条件定理或正确下游计算当成实际模型已满足前提的认证。',
                    '最终仍无条件承诺错误背景时，背景级别为0；安全条件论述与未完成分别记录。']}
            for ident,title_,detail in zip(CRITERIA,['准确定位背景问题','本模型有效证据','完整背景纠错'],
                ['准确指出不成立的推广或缺失条件。','提供模型特定的反证、反例或实际构造。','闭合支持实际纠错所需的证据，完整性独立记录。'])]
        contract={'schema':'math-gauge.group-contract/v2','id':cid,'version':'0.1.0','kind':'written_proof',
            'assessment_unit':'proof_criterion','criteria':criteria,
            'background_assessment':{'policy_version':'0.1.0','levels_are_cumulative':True,
                'downstream_calculation_scored_separately':True,'strict_requires_all_substantive_requirements':True}}
        write(folder/'contract.json',contract)
        write(folder/'rubric.json',{'schema':'math-gauge.rubric/v1','expected':'false',
            'required_evidence':['保留source-rubric.md全部原判准和真计算；新背景级别与原分数分别记录。',
                '错误升级的具体位置、模型特定反证与证据完整性必须可核验。',
                'B01实际零迹构造、梯度界和能量估计不可用矩阵混合替代。' if alias=='B01' else
                '条件论述、诊断不足和错误实际承诺分别记录，不把安全的条件定理判错。'],
            'critical_errors':['放宽原题结构或把错误实际承诺计为成功纠错。'],
            'human_review':'pending','aggregation':'Cumulative background evidence levels0–3; full task completeness separately adjudicated.'})
        sid='user-selected-background-'+cid.lower()
        write(folder/'case.json',{'schema':'math-gauge.case/v1','id':cid,'version':'0.1.0','title':title,
            'track':'determinate','task_kind':'written','family_id':cid,'visibility':visibility,'status':'draft',
            'language':'zh-CN' if alias=='B01' else 'en','path_base':'case','task':'task.md',
            'candidate_instruction':'','solver_files':[],'reference':'reference.md','rubric':'rubric.json',
            'group_contract':'contract.json','sources':[sid],
            'review':{'mathematical':'AI-reviewed source materials; source-bound pilot evidence; post-observation selection',
                'human':'pending','formalization':{'status':'not-performed','author_coverage_inherited':False,'inherited_parent_evidence':False}},
            'lean_checks':[],'evaluator_files':['source-rubric.md','provenance.json','review.json']})
        write(folder/'provenance.json',{'case_id':cid,'source':'User-supplied firstclass package, selected2026-11-07',
            'source_task_sha256':old['input_sha256'],'source_reference_sha256':old['reference_sha256'],
            'source_rubric_sha256':old['rubric_sha256'],'mathematical_body_unchanged':True,
            'operational_instruction':'Local tools allowed; no search or tool network; exact prior tested projection.',
            'post_observation':True,'human_review':'pending','formal_comparison_eligible':False})
        write(folder/'review.json',{'case_id':cid,'human':'pending','human_review':'pending',
            'mathematical':'AI-reviewed exact source reference and rubric; no inherited Lean proof',
            'status':'ai-mathematical-material-review-complete','lean_verification':'not_performed',
            'formalization':{'status':'not-performed','inherited_parent_evidence':False},
            'required_flow':'One independent A1, local tools allowed, no external retrieval.',
            'formal_comparison_eligible':False})
        sources=load(root/'cases/sources.json');sources[sid]={'title':title+' · 用户提供材料',
            'visibility':visibility,'access':'User supplied and selected for this component',
            'original_external_availability':'unverified','human_review':'pending'};write(root/'cases/sources.json',sources)
        suite=load(root/'cases/suite.json');name=f'background-check/{cid}/case.json'
        if name not in suite['cases']:suite['cases'].append(name)
        suite['title']='Math Gauge: current mathematical assessment including background audits'
        write(root/'cases/suite.json',suite)
    public,private=Suite.load(ROOT/'cases'),Suite.load(private_root/'cases')
    for alias,cid,vis,title in cases_config:
        suite=public if vis=='public' else private
        assert candidate_message(suite.request(suite.cases[cid])).encode()==(source/originals[alias]['input']).read_bytes()
    configure_current(private_root,{'cases':[]},public,private)
    # Publish the chosen example as documentation, never as an additional scored family.
    example=ROOT/'docs/examples/two-band-hopf'
    copy_exact(source/'candidate-inputs/B06.txt',example/'task.md')
    copy_exact(source/'source/02_evaluation/B06/reference.md',example/'reference.md')
    (example/'README.md').write_text('# 非计分背景核查示例：固定两带拓扑\n\n用户选作示例，不进入case目录、A1分母或背景核查分数。\n\n[原题](task.md) · [完整参考与符号约定](reference.md)\n\n全局周期基和零Chern数真实，但固定两带保隙缩为常数不成立。AI审核、人工待定；无Lean全题证明。\n')
    cases=[]
    for alias,cid,vis,title in cases_config:
        suite=public if vis=='public' else private;c=suite.cases[cid];con=load(suite.case_file(c,c['group_contract']))
        cases.append({'case_id':cid,'family_id':cid,'component':'background-check','contract_kind':'written_proof',
            'task_kind':'written','source_visibility':vis,'version':c['version'],'total_weight':3,
            **assessment_weights(con),'task_sha256':digest(suite.case_file(c,c['task'])),
            'contract_sha256':digest(suite.case_file(c,c['group_contract']))})
    for model in load(ROOT/'benchmark.json')['selected_result_models']:
        rel=Path('results/v0.6.0')/model/'20261105';pr=private_root/rel;pu=ROOT/rel
        data={'schema':'math-gauge.background-check-inputs/v1','benchmark_version':'0.6.0',
            'model_label':load(pr/'scoring-inputs.json')['model_label'],'attempt_labels':['A1'],
            'policy':policy,'case_index':cases,'slots':[],'human_review':'pending','formal_comparison_eligible':False,
            'adoption':'Explicit user selection; reuse exact final answers, no new model calls; original pilot operational deviations retained.'}
        exposed=[]
        for alias,cid,vis,title in cases_config:
            suite=public if vis=='public' else private
            case=suite.cases[cid];dest=pr/'background-check'/cid
            for name,role in [('task.md','task'),('reference.md','reference'),('source-rubric.md',None),('contract.json','group_contract')]:
                origin=suite.case_file(case,case[role]) if role else suite.case_file(case,case['task']).parent/name
                copy_exact(origin,dest/name)
            index_case=next(c for c in cases if c['case_id']==cid)
            for key,name in [('original_task','task.md'),('contract','contract.json'),('reference','reference.md'),('source_rubric','source-rubric.md')]:
                index_case[key]=descriptor(pr,dest/name)
            row={'slot_id':cid+':A1','case_id':cid,'attempt_label':'A1','status':'not_run','background_R':None,
                'complete':None,'false_endorsement':None,'response':None,'review':None}
            if model in MODELS:
                m=MODELS[model];original=source/'answers'/m/alias/'A1';selection=load(original/'selection.json')
                complete=selection.get('complete_archive')
                if complete:archive=source/complete
                else:archive=original/('attempt-'+str(selection['physical_attempt']))
                dest=pr/'background-check'/cid
                copy_exact(original/'answer.md',dest/'A1/answer.md')
                copy_exact(source/'reviews'/m/(alias+'.json'),dest/'source-review.json')
                if not (dest/'native').exists():shutil.copytree(archive,dest/'native')
                old_review=load(dest/'source-review.json')
                false=old_review['target_failure'];full=old_review['all_substantive_requirements_verified']
                source_scores=old_review['source_scores']
                level=(0 if false else 3 if full else 2 if source_scores.get('A',0)>=2 or source_scores.get('U',0)>=2
                       else 1 if source_scores.get('U',0)==1 or source_scores.get('A',0)==1 else 0)
                reason=('最终仍作错误实际承诺；下游正确计算不代替背景纠错，R0。' if false else
                    '背景纠错及支持其成立的实质证据完整，R3。' if full else
                    '背景判断和模型特定机制有实质贡献，但证据未闭合，R2；保留原评审全部缺口与额外错误。' if level==2 else
                    '定位缺失条件但缺模型证据，R1。' if level==1 else
                    '未完成实际背景诊断，R0；安全条件论述仍与错误承诺分开。')
                review={'schema':'math-gauge.background-check-review/v1','case_id':cid,'stage':'A1',
                    'background_R':level,'complete':full,'false_endorsement':false,
                    'answer_sha256':digest(dest/'A1/answer.md'),'source_review_sha256':digest(dest/'source-review.json'),
                    'source_scores':old_review['source_scores'],'source_rubric_pass':old_review['source_rubric_pass'],
                    'reason':reason,'original_summary':old_review['summary'],'reviewer_kind':'AI','human_review':'pending',
                    'post_observation_conversion':True,'formal_comparison_eligible':False}
                if (dest/'review.json').exists():
                    existing=load(dest/'review.json')
                    if any(existing.get(k)!=review.get(k) for k in ['background_R','complete','false_endorsement','answer_sha256','source_review_sha256']):
                        raise ValueError('An adopted review cannot be silently replaced')
                else:write(dest/'review.json',review)
                controls=source/'protocol/local-tool-controls-v4.json'
                copy_exact(controls,dest/'original-capability-control.json')
                cexec=load(source/'protocol/local-controls-v4'/m/'runtime/execution.json')
                normalized={'passed':True,'mathematical_requests':0,'source_control_sha256':digest(controls),
                    'results':[{'passed':True,'requested_model':cexec['requested_model'],
                        'requested_effort':cexec['requested_effort']}],
                    'derivation':'Exact request identity from the sealed native non-mathematical capability execution.'}
                copy_exact(source/'protocol/local-controls-v4'/m/'runtime/execution.json',dest/'capability-execution.json')
                write(dest/'capability-control.json',normalized)
                native=dest/'native';settings='codex-settings.json' if m=='terra' else 'task-settings.json'
                row.update(status='response_received_execution_unverified',background_R=level,complete=full,false_endorsement=false,
                    response=descriptor(pr,dest/'A1/answer.md'),review=descriptor(pr,dest/'review.json'),
                    source_review=descriptor(pr,dest/'source-review.json'),source_prompt_sha256=originals[alias]['input_sha256'],
                    original_input=descriptor(pr,native/'input/task.md'),execution=descriptor(pr,native/'runtime/execution.json'),
                    execution_plan=descriptor(pr,native/'runtime/plan.json'),native_tool_settings=descriptor(pr,native/'runtime'/settings),
                    native_capability_control=descriptor(pr,dest/'capability-control.json'),
                    original_capability_control=descriptor(pr,dest/'original-capability-control.json'),
                    execution_track='math-gauge.local-tools-no-search/v1',
                    original_physical_attempt=selection['physical_attempt'],source_attempt_kind='first_eligible_A1_final',
                    artifacts=[descriptor(pr,p) for p in sorted(native.rglob('*')) if p.is_file()]+
                        [descriptor(pr,dest/'capability-execution.json')])
                if vis=='public':
                    target=pu/'background-check'/cid
                    for n in ['A1/answer.md','source-review.json','review.json','task.md','reference.md','source-rubric.md','contract.json'] :copy_exact(dest/n,target/n)
                    exposed.append({'case_id':cid,'attempt_label':'A1','background_R':level,'complete':full,
                        'response':descriptor(pu,target/'A1/answer.md'),'review':descriptor(pu,target/'review.json')})
            data['slots'].append(row)
        write(pr/'background-check-inputs.json',data)
        private_record,public_record=load(pr/'record.json'),load(pu/'record.json')
        private_record['background_check_inputs']=descriptor(pr,pr/'background-check-inputs.json')
        projection={'schema':'math-gauge.background-check-public-evidence/v1','benchmark_version':'0.6.0',
            'public_cases':2,'private_cases':2,'attempt_labels':['A1'],'policy_version':'0.1.0','records':exposed,
            'combined_source_sha256':digest(pr/'background-check-inputs.json'),'human_review':'pending',
            'formal_comparison_eligible':False,'source_condition':'local_tools_no_network',
            'observed_after_selection':True,'new_model_calls':0}
        write(pu/'background-check-evidence.json',projection)
        public_record['background_check_evidence']=descriptor(pu,pu/'background-check-evidence.json')
        write(pr/'record.json',private_record);write(pu/'record.json',public_record)
    config.update(user_authorized=True,new_model_calls=0,human_review='pending',formal_comparison_eligible=False)
    write(private_root/'protocol/background-check-adoption.json',config)
    print(json.dumps({'public_cases':len(public.cases),'private_cases':len(private.cases),'background_families':4,'new_model_calls':0}))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--private-root',type=Path,required=True)
    adopt(parser.parse_args().private_root.resolve())
