/* Version and publication notes consume saved values, never mathematical weights. */
(() => {
 'use strict';
 const {d,state,node,result,f}=MG,main=document.querySelector('main');if(!main)return;
 const isRevision=d.benchmark_version==='1.2.0',english=()=>state.lang==='en';
 const text=(zh,en)=>english()?en:zh;
 const section=(id,title)=>{let panel=document.getElementById(id);if(!panel){panel=node('section',null,'panel edition-notes-panel');panel.id=id;panel.setAttribute('data-original','');const board=document.getElementById('leaderboard');let anchor=board||main.querySelector('.context-panel')||main.querySelector('section');if(id==='revision-score-change'&&board)anchor=board.nextElementSibling;if(id==='partial-tests')anchor=main.querySelector('.footer');main.insertBefore(panel,anchor)}panel.replaceChildren(node('h2',title));return panel};
 function oldLink(label,mid,edition='1.1.0'){
  const page=window.MGEdition?.page||'index.html',depth=page.split('/').length-1;
  const url=new URL('../'.repeat(depth)+(mid?'models/'+encodeURIComponent(mid)+'/index.html':'index.html'),location.href);
  url.searchParams.set('edition',edition);url.searchParams.set('lang',state.lang);url.searchParams.set('score','partial');
  const link=node('a',label);link.href=url.href;link.setAttribute('data-fixed-edition',edition);return link;
 }
 const signed=value=>{if(value==null)return '—';const rounded=value.toFixed(2);return Number(rounded)===0?'0.00':(value>0?'+':'')+rounded;};
 const fullRate=value=>{
  if(!value||!value.selected)return '—';
  const rate=value.full_rate,count=value.full_count,percent=v=>(v*100).toFixed(1).replace(/\.0$/,'')+'%';
  if(!rate||!count||rate.lower==null||rate.upper==null)return '—';
  const label=rate.exact==null?percent(rate.lower)+'–'+percent(rate.upper):percent(rate.exact);
  return label+' ('+(count.exact==null?count.lower+'–'+count.upper:count.exact)+'/'+value.selected+')';
 };
 function table(panel,headers,rows){const wrap=node('div',null,'table-wrap'),table=node('table',null,'compact'),head=table.createTHead().insertRow(),body=table.createTBody();headers.forEach(title=>head.append(node('th',title)));rows.forEach(values=>{const row=body.insertRow();values.forEach(value=>{const cell=row.insertCell();typeof value==='string'?cell.textContent=value:cell.append(value)})});wrap.append(table);panel.append(wrap)}
 function revisionDetails(panel){
  const pending=d.pending_models,details=node('details',null,'guide-details');
  details.append(node('summary',pending?text('首答诊断与待续答模型（'+pending.length+'）','First-answer diagnostics and pending models ('+pending.length+')'):text('首答诊断与评审详情','First-answer diagnostics and review details')));
  if(d.models&&pending)details.append(node('p',text('本版已有'+d.models.length+'个模型完成；其余'+pending.length+'个待续答，不继承新成绩。','This edition has '+d.models.length+' completed models; '+pending.length+' remain pending and do not inherit new scores.')));
  details.append(node('p',text('两率、额外研究观察与原错误明细仍是首答诊断；数学画像可独立切换首答和含续答。','Content rates, extra-research observations and original error details remain first-answer diagnostics; mathematical profiles have a separate first-answer / with-continuation selector.')));
  const reviewers=d.model?.neutral_revision?.reviewer_ids;
  if(reviewers?.length)details.append(node('p',text('续答审核者（公开原评记录）：','Continuation reviewers (public source reviews): ')+reviewers.join(' · ')));
  details.append(oldLink(text('查看1.1首答成绩与诊断 →','View 1.1 first-answer results and diagnostics →')));
  if(pending){const list=node('ul',null,'neutral-pending-list');pending.forEach(model=>{const li=node('li');li.append(oldLink(model.label+' · 1.1',model.id));list.append(li)});details.append(list)}
  panel.append(details);
  return details;
 }
 function assessmentGuide(){
  const shell=document.querySelector('[data-assessment-guide]');if(!shell)return false;
  const expanded=shell.querySelector('.guide-details')?.open,guide=node('div',null,'assessment-guide-body');Object.assign(guide.dataset,shell.dataset);
  const summary=node('summary'),brief=node('span',null,'guide-summary-text');
  brief.append(node('strong',text('评测指南','Assessment guide')),
   node('span',text(shell.dataset.tasks+'题 · 书面35／Lean35／研究30 · 满分'+shell.dataset.total,shell.dataset.tasks+' tasks · Written35 / Lean35 / Research30 · '+shell.dataset.total+' points')),
   node('small',text('展开查看题型、计算方法、作答流程与三种指标','Expand for task categories, scoring, process and the three measures')));
  summary.append(brief);shell.replaceChildren(summary,guide);shell.setAttribute('aria-label',text('评测指南','Assessment guide'));
  const head=node('div',null,'guide-head'),title=node('h3',text('题库范围','Task scope')),catalog=node('a',text('题目目录 ↗','Task catalog ↗'));
  catalog.href='../cases/README.md';head.append(title,catalog);guide.append(head);
  guide.append(node('p',text(guide.dataset.tasks+'项首答（公开'+guide.dataset.public+'／私有'+guide.dataset.private+'） · '+guide.dataset.families+'个数学家族 · 总分'+guide.dataset.total,
   guide.dataset.tasks+' initial tasks ('+guide.dataset.public+' public / '+guide.dataset.private+' private) · '+guide.dataset.families+' mathematical families · '+guide.dataset.total+' total points'),'guide-scope'));
  const names={written:text('书面证明','Written proofs'),lean:'Lean',research:text('数学研究','Mathematical research'),
   'written-argument':text('书面论证','Written arguments'),'argument-review':text('论证审阅','Argument review'),'lean-audit':text('语义审计','Semantic audit'),'lean-formalization':text('形式化','Formalization'),'lean-selfcheck':text('对齐自查','Alignment self-check'),
   'background-check':text('背景核查','Background check'),'manuscript-completion':text('想法手稿化','Idea-to-manuscript'),'theorem-extension':text('命题拓展','Theorem extension')};
  const tasks={written:text('16项首答','16 initial tasks'),lean:text('8项首答＋3轮固定自查','8 initial tasks + 3 fixed self-checks'),research:text('15项首答','15 initial tasks')};
  const taxonomy=node('table',null,'guide-table'),row=taxonomy.createTHead().insertRow();
  [text('题型','Category'),text('任务范围','Tasks'),text('分值 · 占比','Points · share'),text('子类组成（分）','Components (points)')].forEach(label=>row.append(node('th',label)));
  const body=taxonomy.createTBody();
  d.policy.groups.forEach(group=>{const r=body.insertRow(),label=node('th',names[group.id]);label.scope='row';r.append(label);
   const count=r.insertCell();count.className='guide-category-tasks';count.textContent=tasks[group.id];
   const share=r.insertCell();share.className='guide-category-share';share.textContent=text(group.weight+'分 · '+group.weight+'%',group.weight+' points · '+group.weight+'%');
   const parts=r.insertCell();parts.className='guide-category-parts';parts.textContent=group.children.map(id=>{const part=d.policy.subcategories.find(item=>item.id===id);return names[id]+' '+part.weight}).join(' · ');
  });guide.append(taxonomy);
  const explain=(heading,content,cls='')=>{const block=node('section',null,'guide-section '+cls);block.append(node('h3',heading),node('p',content));guide.append(block);return block};
  explain(text('汇总方法','How scores are combined'),text('逐题审核，相关变体先在同一数学家族内合并，再按固定权重汇总。未测保持未知，不把已测部分重新放大到100分。','Each task is reviewed; related variants are combined within their mathematical family, then aggregated with fixed weights. Unrun work stays unknown; measured coverage is never rescaled to 100.'));
  const flow=explain(text('作答流程','Answering process'),text('39项首答任务分别交付，按规定的有效尝试规则选卷。','The 39 initial tasks are delivered separately and selected under the prescribed effective-attempt rule.'));
  const branches=node('div',null,'guide-flow-branches');
  branches.append(node('p',text('整章Lean（MG-C003）→ 固定3轮自查','Whole-chapter Lean (MG-C003) → 3 fixed self-checks')));
  if(isRevision)branches.append(node('p',text('非Lean已知失分题 → 1次中性续答；首答三项全满免跑','Non-Lean tasks with known loss → 1 neutral continuation; first answers full in all three modes are exempt')));
  else branches.append(node('p',text('其余任务 → 按本版规则选定的首答计分','Other tasks → score the first-answer delivery selected by this edition')));
  flow.append(branches);
  const metrics=node('section',null,'guide-section');metrics.append(node('h3',text('三种指标','Three score concepts')));
  const definitions=node('dl',null,'guide-metrics');
  [['MC',text('经核实的有效数学成果，包括有效部分进展。','Verified useful mathematics, including valid partial progress.')],['RMC',text('可靠性分；在有效成果上扣除有据的错误、回退与误报损失。','Reliability-adjusted credit: valid work less supported penalties for errors, regressions and false claims.')],['SMC',text('默认排序指标。每份交付按整题通过／不通过验收；整章自查按完整三轮轨迹验收。','The default sorting measure. Each delivery passes or fails the whole task; chapter self-checks use the entire three-round trajectory.')]].forEach(([name,meaning])=>{const entry=node('div');entry.append(node('dt',name),node('dd',meaning));definitions.append(entry)});
  metrics.append(definitions);guide.append(metrics);
  if(isRevision){
   const revision=explain(text('续答如何算分','How continuation credit is blended'),text('MC、RMC、SMC都逐题折算，再沿用原家族权重；续答不是额外增加20分。','MC, RMC and SMC are blended per task, retaining the original family weights; continuations do not add a separate 20 points.'),'guide-revision');
   revision.append(node('p',text('80% × 首答 ＋ 20% × 续答','80% × first answer + 20% × continuation'),'neutral-revision-formula'));
   revision.append(node('p',text('例：某题MC或RMC首答80、续答100，最终计84。SMC先分别判定两次交付是否整题通过，再按80/20折算；Lean与原三轮自查不变。','Example: a task with first-answer MC or RMC of 80 and continuation credit of 100 yields 84. SMC first judges each delivery separately, then applies the 80/20 blend. Lean and its three self-check rounds are unchanged.')));
   const details=revisionDetails(guide);if(expanded)details.open=true;
  }
  const method=node('a',text('详细执行与评审规则 →','Detailed execution and review rules →'),'guide-method-link');method.href=MG.href('method.html');guide.append(method);
  return true;
 }
 function header(){
  const navigation={ranking:text('排行榜','Rankings'),categories:text('分项成绩','Category scores'),revision:text('续答变化','Continuation gains'),method:text('方法与数据','Method & data'),'method-short':text('方法','Method'),library:text('题库','Task library'),release:text('1.0.0 分发说明','1.0.0 distribution'),guide:text('其他 Harness 运行指南','External harness guide')};
  document.querySelectorAll('[data-header-label]').forEach(label=>label.textContent=navigation[label.dataset.headerLabel]);
  const note=document.querySelector('.category-ranking-note');
  if(note){let link=note.querySelector('[data-header-contribution]');if(!link){link=node('a');link.href='#capability-section';link.setAttribute('data-header-contribution','');note.append(' ',link)}link.textContent=text('权重与分数构成 →','Weights and score contributions →');}
 }
 function render(){
  header();
  const hasGuide=assessmentGuide();
  if(isRevision){
   if(!hasGuide){const panel=section('neutral-revision-note',text('1.2 · 续答如何计分','1.2 · How continuations are scored'));panel.append(node('p',text('续答题：80% × 首答 ＋ 20% × 续答；SMC先分别判定两份交付，再折算。','Continued tasks: 80% × first answer + 20% × continuation; SMC judges the two deliveries separately before blending.'),'neutral-revision-formula'));revisionDetails(panel);}
   document.querySelectorAll('#content-rates').forEach(element=>element.hidden=true);
   const observations=document.getElementById('research-initiative');
   if(observations){
    observations.hidden=false;
    const meta=observations.querySelector('.initiative-meta');
    if(meta)meta.textContent=text('五道手稿题（公1／私4） · 仅首答A1，不含中性续答','Five manuscript tasks (1 public / 4 private) · first answers only; neutral continuations excluded');
    observations.querySelectorAll('[data-context-link]').forEach(link=>{
     const edition=d.diagnostic_source_edition||'1.1.0',url=new URL(link.href,location.href);
     url.searchParams.set('edition',edition);url.searchParams.set('lang',state.lang);
     link.href=url.href;link.setAttribute('data-fixed-edition',edition);
    });
   }
   if(d.models?.some(model=>model.neutral_revision_delta)){
    const delta=section('revision-score-change',text('续答带来的分数变化','Score changes from continuations'));
    table(delta,[text('模型','Model'),text('续答题数','Continued tasks'),text('满分率','Full-score rate'),'ΔSMC','ΔRMC','ΔMC'],[...d.models].sort(MG.compareModelOrder).map(model=>{
     const completion=model.neutral_revision_completion?.settled?model.neutral_revision_completion:null;
     return [node('span',model.label),completion?String(completion.selected):'—',fullRate(completion),...['strict','partial','capability'].map(mode=>signed(model.neutral_revision_delta?.[mode]))];
    }));
    delta.append(node('p',text('已计入完整100分总分的变化，相比1.1首答成绩；差值可为负。','Changes already included in the full 100-point score, relative to the 1.1 first-answer result; decreases are retained.')));
    delta.append(node('p',text('满分指续答本身未舍入的MC、RMC、SMC三项全满；分母为全部入选续答题，包含未交卷，首答三项全满的免测题不计入。','Full score requires the continuation itself to be full in all three unrounded modes: MC, RMC and SMC. The denominator includes every selected task, including failed deliveries; exempt first answers already full in all modes are excluded.')));
   }
  }
  const partial=d.partial_models||d.models?.filter(model=>model.presentation_eligibility?.ranked===false)||(d.model?.presentation_eligibility?.ranked===false?[d.model]:[]);
  if(partial.length){const panel=section('partial-tests',text('部分测试','Partial tests'));
   panel.append(node('p',text('规定流程未完成、交付覆盖不足，保留部分成绩与原始档案，不参加排行。','The prescribed evaluation is incomplete with insufficient delivery coverage; partial results and the original archive remain available, outside the rankings.')));
   table(panel,[text('模型','Model'),'SMC','RMC','MC',text('主动／强收／初答','Normal / forced / initial'),text('档案','Archive')],[...partial].sort(MG.compareModelOrder).map(model=>{const values=model.score_values||Object.fromEntries(['capability','partial','strict'].map(mode=>[mode,result(model,'nonlogical_retry_3',mode).metrics.earned.confirmed]));const delivery=model.answer_delivery;return [oldLink(model.label,model.id,isRevision?'1.1.0':d.benchmark_version),...['strict','partial','capability'].map(mode=>f(values[mode])),delivery?.active_final==null?'—':delivery.active_final+' / '+delivery.forced_content+' / '+delivery.planned,oldLink(text('详情 →','Details →'),model.id,isRevision?'1.1.0':d.benchmark_version)]}));
  }
 }
 window.addEventListener('mg:updated',render);render();
})();
