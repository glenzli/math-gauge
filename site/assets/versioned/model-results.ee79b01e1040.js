(() => {
 const {d,state,modes,el,f,node,result,headline,table,points,href,download,taskValue,start}=MG,m=d.model;
 const metric=(title,value)=>{const n=node('div',null,'metric');n.append(node('div',title,'metric-label'),node('div',value,'metric-value'));return n};
 document.querySelectorAll('[data-first-attempt-scores]').forEach(n=>n.textContent=['capability','partial','strict'].map(mode=>f(headline(result(m,'single_attempt',mode)))).join(' / '));
 start(()=>{
  const r=result(m),v=r.metrics.overall,p=m.evaluation_progress[state.condition];
  const overview=[metric(modes[state.score].abbreviation+' 已获分 /100',f(headline(r)))];
  if(v.exact==null||f(v.lower)!==f(v.upper))overview.push(metric('完整分区间',f(v.lower)+'–'+f(v.upper)));
  const submission=r.submission_summary;
  if(submission)overview.push(metric('主动／强收／题数',submission.active_final+' / '+submission.forced_content+' / '+submission.planned));
  else if(m.answer_delivery?.delivered!=null)overview.push(metric('已交卷',m.answer_delivery.delivered+'/'+m.answer_delivery.planned));
  overview.push(metric('已评任务',p.adjudicated+'/'+p.planned));
  if(submission?.pending_original_record_review)overview.push(metric('待补原记录复核',submission.pending_original_record_review+'项 · 暂记0'));
  el('model-overview').style.setProperty('--model-count',String(overview.length));el('model-overview').replaceChildren(...overview);
  const researchDelivery=m.independent_research_delivery;
  let researchNote=el('independent-research-delivery');
  if(researchNote)researchNote.remove();
  if(researchDelivery?.schema==='math-gauge.independent-research-delivery-method/v1'&&
     researchDelivery.round_dispatches===3&&researchDelivery.normal_rounds+researchDelivery.forced_rounds===3&&
     researchDelivery.delivery_kinds?.filter(kind=>kind==='normal-final').length===researchDelivery.normal_rounds&&
     researchDelivery.delivery_kinds?.filter(kind=>kind==='forced-content').length===researchDelivery.forced_rounds&&
     researchDelivery.method?.selection==='post-observation-user-selected-cutoff'){
   researchNote=node('section',null,'panel');researchNote.id='independent-research-delivery';
   const title=node('h2'),titleZh=node('span','独立研究 · 实际交卷方式'),titleEn=node('span','Independent research · Actual delivery method');
   titleZh.dataset.langContent='zh';titleEn.dataset.langContent='en';titleEn.hidden=true;title.append(titleZh,titleEn);
   const zh=node('p',`三轮中${researchDelivery.normal_rounds}轮正常交卷、${researchDelivery.forced_rounds}轮按实际截止稿强制收卷；评审使用这三稿及明确交付附件。首轮原限45分钟，追加15分钟；六段有效作答累计约95.79分钟。费用参考按已记录用量统计，少量中断用量可能未计入，以*标注；原始未知用量保留。采用范围仅限本条轨迹，原生状态与历史成绩保留。`);
   zh.dataset.langContent='zh';
   const en=node('p',`This trajectory has ${researchDelivery.normal_rounds} normal finals and ${researchDelivery.forced_rounds} forced cutoff submissions, assessed on the actual manuscripts and explicit attachments. R1 had its original 45-minute limit plus 15 authorized minutes; the six effective answer segments total about 95.79 minutes. The cost reference uses recorded usage and carries * for a small amount of interrupted usage that may be uncounted; original unknown usage is preserved. This admission is limited to this trajectory; native states and historical scores are preserved.`);
   en.dataset.langContent='en';en.hidden=true;
   researchNote.append(title,zh,en);el('model-overview').closest('.panel').after(researchNote);
  }
  const rows=[];d.policy.groups.forEach(g=>{rows.push([g.title,g.weight+'%',points(m,g.id,g.weight)]);g.children.forEach(id=>{const c=d.policy.subcategories.find(c=>c.id===id);rows.push(['　'+c.title,c.weight+'%',points(m,c.id,c.weight)])})});
  table('model-categories',['大类 / 子类','权重','当前贡献'],rows);
  const verdict=m.strict[state.condition].strict_alignment_selfcheck.strict_pass;
  table('model-selfcheck',['当前口径','成绩'],[[state.score==='strict'?'SMC 整段判定':modes[state.score].abbreviation+' 自查 /100',state.score==='strict'?(verdict==null?'未知':verdict?'通过':'未通过'):f(r.metrics['lean-selfcheck'].exact)],['计入总分 /10',points(m,'lean-selfcheck',10)]]);
  el('selfcheck-rule').textContent={capability:'固定三轮平均，只计已核实的正向修复与诊断。',partial:'固定三轮平均，保留回退和误报扣罚。',strict:'整段三轮轨迹达标才计10分；未达标为0分，未决保留未知。'}[state.score];
  table('selfcheck-comparison',['计分口径','成绩'],[['MC 自查 /100',f(m.capability[state.condition].metrics['lean-selfcheck'].exact)],['RMC 自查 /100',f(result(m,state.condition,'partial').metrics['lean-selfcheck'].exact)],['SMC 整段判定',verdict==null?'未知':verdict?'通过':'未通过']]);
  const states={verified_complete:'核实全部完成',incomplete_stable:'未完整 · 数量稳定',incomplete_changed:'未完整 · 有进展',regressed:'未完整 · 有回退',interrupted:'轮次未完成',not_run:'未运行',unrun_unknown:'未运行',unresolved:'审核未决'};
  const trajectory=r.alignment_selfcheck||m.alignment_selfcheck,rounds=trajectory.rounds;
  const roundFact=r=>r.submission_classification==='blank'?'未交付本轮答卷 · 计0':r.submission_classification==='forced_content'&&state.score!=='capability'?'未正常交卷 · 计0':r.complete==null?'未知':r.complete+'/92'+(r.submission_classification==='forced_content'?' · 强收工程':'');
  table('model-trajectory',['轮次 / 状态','原答事实'],[...rounds.map((r,i)=>['R'+(i+1)+' 完成义务',roundFact(r)]),['误报全部完成',rounds.every(r=>r.complete==null||r.delivery_verified===false)?'未核实':trajectory.major_false_complete_events.count+' / 3轮']]);
  const engineering=r.lean_formalization_breakdown||m.lean_formalization_breakdown;
  table('model-formalization',['任务','核实完成'],engineering.cases.map(c=>[c.case_id,c.complete_count==null?(c.status==='delivery_failed'?'未正常交卷':'未知'):c.complete_count+'/'+c.total+(c.submission_classification==='forced_content'?' · 强收工程':'' )]));
  table('case-list',['公开题','题型',state.score==='strict'&&!m.neutral_revision?'SMC 判定':modes[state.score].abbreviation+' 单题比例'],d.cases.map(c=>{const a=node('a',c.id+' · '+c.title);a.href=href('cases/'+c.id+'.html');return [a,c.category_title,taskValue(c.views[state.score][state.condition])]}));
  const cp=result(m,state.condition,'partial').claim_penalties;
  el('model-penalties').replaceChildren(metric('局部 / 实质 / 重大记录',cp.findings_by_severity.local+' / '+cp.findings_by_severity.material+' / '+cp.findings_by_severity.critical),metric('RMC 整题最高0分',cp.core_endorsement_tasks+'题'));
  const findings=el('model-findings');findings.replaceChildren();let count=0;
  m.public_claims[state.condition].forEach(c=>{if(!c.findings.length)return;count++;const a=node('a',c.case_id+' · 查看证据');a.href=href('cases/'+c.case_id+'.html');findings.append(a);const ul=node('ul');c.findings.forEach(v=>ul.append(node('li',v.reason)));findings.append(ul)});
  if(!count)findings.append(node('p','当前公开题无额外错误承诺扣罚。'));
  const a=node('a',m.label+' · '+modes[state.score].abbreviation+' JSON ↓','download-link');a.href=download(m,'../../');el('downloads').replaceChildren(a);
 });
})();
