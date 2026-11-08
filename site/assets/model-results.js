(() => {
 const {d,state,modes,el,f,node,result,headline,table,points,href,download,taskValue,start}=MG,m=d.model;
 const metric=(title,value)=>{const n=node('div',null,'metric');n.append(node('div',title,'metric-label'),node('div',value,'metric-value'));return n};
 start(()=>{
  const r=result(m),v=r.metrics.overall,p=m.evaluation_progress[state.condition];
  el('model-overview').replaceChildren(metric(modes[state.score].abbreviation+' 已获分 /100',f(headline(r))),metric('完整分区间',f(v.lower)+'–'+f(v.upper)),metric('已评任务',p.adjudicated+'/'+p.planned));
  const rows=[];d.policy.groups.forEach(g=>{rows.push([g.title,g.weight+'%',points(m,g.id,g.weight)]);g.children.forEach(id=>{const c=d.policy.subcategories.find(c=>c.id===id);rows.push(['　'+c.title,c.weight+'%',points(m,c.id,c.weight)])})});
  table('model-categories',['大类 / 子类','权重','当前贡献'],rows);
  const verdict=m.strict[state.condition].strict_alignment_selfcheck.strict_pass;
  table('model-selfcheck',['当前口径','成绩'],[[state.score==='strict'?'SMC 整段判定':modes[state.score].abbreviation+' 自查 /100',state.score==='strict'?(verdict==null?'未知':verdict?'通过':'未通过'):f(r.metrics['lean-selfcheck'].exact)],['计入总分 /10',points(m,'lean-selfcheck',10)]]);
  el('selfcheck-rule').textContent={capability:'固定三轮平均，只计已核实的正向修复与诊断。',partial:'固定三轮平均，保留回退和误报扣罚。',strict:'整段三轮轨迹达标才计10分；未达标为0分，未决保留未知。'}[state.score];
  table('selfcheck-comparison',['计分口径','成绩'],[['MC 自查 /100',f(m.capability[state.condition].metrics['lean-selfcheck'].exact)],['RMC 自查 /100',f(result(m,state.condition,'partial').metrics['lean-selfcheck'].exact)],['SMC 整段判定',verdict==null?'未知':verdict?'通过':'未通过']]);
  const states={verified_complete:'核实全部完成',incomplete_stable:'未完整 · 数量稳定',incomplete_changed:'未完整 · 有进展',regressed:'未完整 · 有回退',interrupted:'轮次未完成',not_run:'未运行',unrun_unknown:'未运行',unresolved:'审核未决'};
  const rounds=m.alignment_selfcheck.rounds;
  table('model-trajectory',['轮次 / 状态','原答事实'],[...rounds.map((r,i)=>['R'+(i+1)+' 完成义务',r.complete==null?'未知':r.complete+'/92']),['误报全部完成',rounds.every(r=>r.complete==null)?'未知':m.alignment_selfcheck.major_false_complete_events.count+' / 3轮'],['最后状态',states[m.trajectory.state]||'审核未决']]);
  table('model-formalization',['任务','核实完成'],m.lean_formalization_breakdown.cases.map(c=>[c.case_id,c.status==='delivery_failed'?'交付失败（交付计0）':c.complete_count==null?'未知':c.complete_count+'/'+c.total]));
  table('case-list',['公开题','题型',state.score==='strict'?'SMC 判定':modes[state.score].abbreviation+' 单题比例'],d.cases.map(c=>{const a=node('a',c.id+' · '+c.title);a.href=href('cases/'+c.id+'.html');return [a,c.category_title,taskValue(c.views[state.score][state.condition])]}));
  const cp=result(m,state.condition,'partial').claim_penalties;
  el('model-penalties').replaceChildren(metric('局部 / 实质 / 重大记录',cp.findings_by_severity.local+' / '+cp.findings_by_severity.material+' / '+cp.findings_by_severity.critical),metric('RMC 整题最高0分',cp.core_endorsement_tasks+'题'));
  const findings=el('model-findings');findings.replaceChildren();let count=0;
  m.public_claims[state.condition].forEach(c=>{if(!c.findings.length)return;count++;const a=node('a',c.case_id+' · 查看证据');a.href=href('cases/'+c.case_id+'.html');findings.append(a);const ul=node('ul');c.findings.forEach(v=>ul.append(node('li',v.reason)));findings.append(ul)});
  if(!count)findings.append(node('p','当前公开题没有新增错误承诺记录；原始数学缺口仍按逐题评审保留。'));
  const a=node('a',m.label+' · '+modes[state.score].abbreviation+' JSON ↓','download-link');a.href=download(m,'../../');el('downloads').replaceChildren(a);
 });
})();
