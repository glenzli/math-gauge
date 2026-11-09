(() => {
 const {d,state,modes,el,f,node,result,headline,short,table,points,href,download,start}=MG;
 const harnessName=m=>m.harness_display_name||m.harness.name;
 const visibleModels=(key='overall')=>d.models.filter(m=>!MGBoards.readBoard(location.search,key).completeOnly||m.fully_evaluated);
 const deliveryLabel=m=>m.answer_delivery?.delivered==null?'—':m.answer_delivery.delivered+'／'+m.answer_delivery.planned;
 const expanded=new Set();
 const sortDefaults={...Object.fromEntries(d.policy.groups.map(g=>[g.id,'partial'])),gap:'RG',rates:'reliability'};
 const sortChoices={...Object.fromEntries(d.policy.groups.map(g=>[g.id,d.score_modes])),gap:['RG','DG'],rates:['reliability','attainment']};
 const chartSort={...sortDefaults};
 function syncSorts(){
  const q=new URLSearchParams(location.search);
  Object.keys(sortDefaults).forEach(key=>{const value=q.get('sort-'+key);chartSort[key]=sortChoices[key].includes(value)?value:sortDefaults[key];document.querySelectorAll('[data-chart-sort="'+key+'"]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.sortValue===chartSort[key])))});
 }
 function orderedModels(value,ascending=false,key='overall'){
  return visibleModels(key).sort((a,b)=>{const x=value(a),y=value(b);if(x==null||y==null)return x==null?(y==null?a.id.localeCompare(b.id):1):-1;return (ascending?x-y:y-x)||a.id.localeCompare(b.id)});
 }
 function orderChart(id,models){const chart=el(id);if(!chart)return;const ids=new Set(models.map(m=>m.id));chart.querySelectorAll(':scope > [data-model]').forEach(n=>n.hidden=!ids.has(n.dataset.model));models.forEach(m=>chart.append(chart.querySelector(':scope > [data-model="'+m.id+'"]')))}
 function auxiliaryCharts(){
  const gap=Object.fromEntries(d.gap_diagnostics.tables.find(t=>t.id===chartSort.gap).rows.map(r=>[r.model_id,r.value]));
  orderChart('gap-groups',orderedModels(m=>gap[m.id]==null?null:Math.abs(gap[m.id]),true,'gap'));
  const metric=chartSort.rates,field=metric==='reliability'?'observed':'confirmed';
  orderChart('rate-groups',orderedModels(m=>m.content_rates?.metrics[metric][field]??null,false,'rates'));
 }
 let category=new URLSearchParams(location.search).get('category');
 if(!d.policy.groups.some(g=>g.id===category))category=d.policy.groups[0].id;
 function modelLink(m,incomplete,score=state.score){
  const a=node('a',m.label,'model-name');a.href=href('models/'+m.id+'/index.html');
  const u=new URL(a.href);u.searchParams.set('score',score);a.href=u.href;
  if(incomplete){const s=node('sup','*','incomplete-marker');s.setAttribute('aria-label','尚未测完');a.append(s)}
  return a;
 }
 function ranking(){
  const b=el('ranking-body');b.replaceChildren();
  visibleModels().sort((a,b)=>(headline(result(b))??-Infinity)-(headline(result(a))??-Infinity)).forEach((m,i)=>{
   const row=b.insertRow();row.style.setProperty('--model-ink',m.theme.ink);row.insertCell().append(node('span',String(i+1),'rank'+(i===0?' first':'')));
   const wrap=node('div',null,'model'),symbol=node('span',null,'model-symbol'),text=node('div');symbol.style.background=m.theme.tint;symbol.setAttribute('aria-hidden','true');
   const icon=node('img');icon.src=m.logo.data_url;icon.alt='';symbol.append(icon);
   const name=node('a',m.label,'model-name');name.href=href('models/'+m.id+'/index.html');
   if(m.evaluation_progress[state.condition].incomplete){const marker=node('sup','*','incomplete-marker');marker.setAttribute('aria-label','尚未测完');name.append(marker)}
   text.append(name);wrap.append(symbol,text);row.insertCell().append(wrap);
   row.insertCell().append(node('span',harnessName(m),'harness-name'));row.cells[2].className='harness-cell';
   text.append(node('span',harnessName(m),'mobile-harness'));
   text.append(node('span','交卷 '+deliveryLabel(m),'mobile-delivery'));
   const delivery=row.insertCell();delivery.className='numeric delivery-cell';delivery.textContent=deliveryLabel(m);
   delivery.title='初答交卷数（含封卷工程）';
   d.display_score_modes.forEach(mode=>{const cell=row.insertCell();cell.dataset.displayMode=mode.id;cell.className='numeric score-cell'+(mode.id==='partial'?' primary-score':'');cell.append(node('span',f(headline(result(m,state.condition,mode.id))),'score-number'))});
   const a=node('a','详细评测 →','record-link');a.href=name.href;a.setAttribute('aria-label',m.label+' 详细评测');row.insertCell().append(a);
  });
 }
 function taxonomy(){
  const t=el('capabilities');t.replaceChildren();const head=t.createTHead().insertRow(),columns=[];
  const first=node('th','模型');first.scope='col';head.append(first);
  d.policy.groups.forEach(g=>{
   const cell=node('th'),btn=node('button',(expanded.has(g.id)?'▾ ':'▸ ')+g.title,'category-toggle');cell.scope='col';
   btn.id='taxonomy-toggle-'+g.id;btn.setAttribute('aria-expanded',String(expanded.has(g.id)));btn.setAttribute('aria-controls','capabilities');
   btn.setAttribute('aria-label',(expanded.has(g.id)?'收起':'展开')+g.title+'的子类成绩');
   btn.onclick=()=>{if(expanded.has(g.id))expanded.delete(g.id);else expanded.add(g.id);taxonomy();MGI18n.apply(state.lang);el(btn.id).focus({preventScroll:true})};
   cell.append(btn,node('span',' / '+g.weight,'category-weight'));head.append(cell);columns.push({item:g,total:true});
   if(expanded.has(g.id))g.children.forEach(id=>{const c=d.policy.subcategories.find(c=>c.id===id),h=node('th',c.title+' / '+c.weight,'taxonomy-child-heading');h.scope='col';head.append(h);columns.push({item:c,total:false})});
  });
  const body=t.createTBody();
  visibleModels().sort((a,b)=>(headline(result(b))??-Infinity)-(headline(result(a))??-Infinity)).forEach(m=>{
   const row=body.insertRow(),label=node('th');label.scope='row';label.append(modelLink(m,m.evaluation_progress[state.condition].incomplete));row.append(label);
   columns.forEach(({item,total})=>{const c=row.insertCell();c.className=total?'taxonomy-total':'taxonomy-child';c.textContent=points(m,item.id,item.weight);const v=result(m).contributions[item.id];c.title='完整贡献区间 '+f(v.lower)+'–'+f(v.upper)+' / '+item.weight});
  });
 }
 function categoryRanking(){
  d.category_leaderboards.forEach(g=>{
   const byId=Object.fromEntries(visibleModels(g.id).map(m=>[m.id,m]));
   const score=chartSort[g.id];
   table('category-ranking-'+g.id,['#','模型','Harness',...d.display_score_modes.map(m=>m.abbreviation)],[]);
   const t=el('category-ranking-'+g.id);t.tHead.rows[0].cells[2].className='category-harness';
   d.display_score_modes.forEach((mode,index)=>t.tHead.rows[0].cells[index+3].dataset.displayMode=mode.id);
   const views=Object.fromEntries(d.score_modes.map(mode=>[mode,Object.fromEntries(g.views[mode].map(r=>[r.model_id,r]))]));
   const items=g.views[score].filter(item=>byId[item.model_id]);
   orderChart('category-chart-groups-'+g.id,items.map(item=>byId[item.model_id]));
   items.forEach((item,index)=>{
    const m=byId[item.model_id],r=t.tBodies[0].insertRow();r.insertCell().textContent=item.rank==null?'—':index+1;r.insertCell().append(modelLink(m,item.incomplete,score));
    const harness=r.insertCell();harness.className='category-harness';harness.textContent=harnessName(m);
    d.display_score_modes.forEach(mode=>{const v=views[mode.id][m.id],c=r.insertCell();c.dataset.displayMode=mode.id;c.className='numeric score-cell'+(mode.id===score?' primary-score':'');if(v.value<0)c.classList.add('negative');c.append(node('span',f(v.value),'score-number'));c.title='完整分区间 '+f(v.lower)+'–'+f(v.upper)});
   });
  });
  selectCategory(category,false);
 }
 function selectCategory(id,updateUrl=true){
  category=id;
  d.policy.groups.forEach(g=>{const selected=g.id===id,b=el('category-tab-'+g.id);b.setAttribute('aria-selected',String(selected));b.tabIndex=selected?0:-1;el('category-panel-'+g.id).hidden=!selected});
  if(updateUrl){const u=new URL(location.href);u.searchParams.set('category',id);u.hash='category-leaderboards';history.replaceState(null,'',u)}
 }
 d.policy.groups.forEach((g,i)=>{
  const b=el('category-tab-'+g.id);b.onclick=()=>selectCategory(g.id);
  b.onkeydown=e=>{let index;if(e.key==='ArrowRight')index=(i+1)%d.policy.groups.length;else if(e.key==='ArrowLeft')index=(i+d.policy.groups.length-1)%d.policy.groups.length;else if(e.key==='Home')index=0;else if(e.key==='End')index=d.policy.groups.length-1;else return;e.preventDefault();const id=d.policy.groups[index].id;selectCategory(id);el('category-tab-'+id).focus()};
 });
 document.querySelectorAll('[data-chart-sort]').forEach(button=>{
  button.onclick=()=>{
   const key=button.dataset.chartSort,value=button.dataset.sortValue;if(!sortChoices[key]?.includes(value))return;
   const u=new URL(location.href);u.searchParams.set('sort-'+key,value);history.replaceState(null,'',u);
   syncSorts();if(d.policy.groups.some(g=>g.id===key))categoryRanking();else auxiliaryCharts();
   MGI18n.apply(state.lang);
   window.dispatchEvent(new Event('mg:updated'));
  };
 });
 start(()=>{
  syncSorts();ranking();taxonomy();categoryRanking();auxiliaryCharts();
  orderChart('chart-groups',visibleModels().sort((a,b)=>(headline(result(b))??-Infinity)-(headline(result(a))??-Infinity)));
  document.querySelectorAll('.coverage-note').forEach(n=>n.hidden=!visibleModels().some(m=>m.evaluation_progress[state.condition].incomplete));
  const visibleIds=new Set(visibleModels().map(m=>m.id)),initiativeIds=new Set(visibleModels('initiative').map(m=>m.id));
  document.querySelectorAll('[data-model-note]').forEach(n=>n.hidden=!(n.closest('[data-board="initiative"]')?initiativeIds:visibleIds).has(n.dataset.modelNote));
  const pendingObservation=el('initiative-pending-note');if(pendingObservation)pendingObservation.hidden=!d.manuscript_observations.models.some(m=>initiativeIds.has(m.id)&&m.observation.counts.total_groups==null);
  document.querySelectorAll('[data-board-empty]').forEach(n=>n.hidden=visibleModels(n.closest('[data-board]').dataset.board).length>0);
  el('no-completed-models').hidden=visibleModels().length>0;
  const selected=modes[state.score];el('leaderboard-desc').textContent='公开＋私有 · 按'+selected.abbreviation+'排序 · 满分100';el('score-explanation').textContent={capability:'累计有效数学成果。',partial:'按有效成果计分，扣除错误、回退和误报。',strict:'整题及规定自查轨迹全部达标才计分。'}[state.score];
  el('contributions-title').textContent=selected.abbreviation+' · 分类贡献';el('contribution-mode').textContent=selected.abbreviation;el('active-condition').textContent=MG.conditionLabel();
  el('downloads').replaceChildren(...visibleModels().map(m=>{const a=node('a',short(m)+' · JSON ↓','download-link');a.href=download(m);return a}));
 });
})();
