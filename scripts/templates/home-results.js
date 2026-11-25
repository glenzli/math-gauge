(() => {
 const {d,state,modes,el,f,node,result,headline,compareScores,compareModelOrder,rankedScores,short,table,href,download,start}=MG;
 const harnessName=m=>m.harness_display_name||m.harness.name;
 const categoryHarness=d.benchmark_version!=='1.3.0';
 const research=window.MGResearchPreview?.categoryComponents?.(d);
 const visibleModels=(scope='overall')=>(scope==='initiative'?[...d.models,...(d.pending_models||[])]:d.models)
  .filter(m=>m.presentation_eligibility?.ranked!==false);
 const deliveryLabel=m=>{const s=result(m).submission_summary||m.answer_delivery;if(s?.active_final!=null)return s.active_final+'／'+s.forced_content+'／'+s.planned;return s?.delivered==null?'—':s.delivered+'／'+s.planned;};
 const renderedViews=new Map();
 const displayKey=(key,score=state.score)=>JSON.stringify([key,state.condition,score]);
 function scoreReadout(node,metric,text,interval,tooltip=node){
  const status=metric.value==null?window.MGResearchPreview?.categoryStatus?.(metric.state,state.lang):null;
  node.textContent=status?status.text:text;
  if(metric.state!=='not-tested')tooltip.title=interval;
  else tooltip.removeAttribute('title');
  if(status){node.dataset.researchCategoryState=metric.state;node.setAttribute('aria-label',status.label)}
  return status?status.label:text;
 }
 function researchLabel(element,axis,weighted){
  element.dataset.original='';
  element.dataset.researchScoreLabel=axis;
  element.textContent=research.label(axis,state.lang,weighted);
 }
 function editionCharts(){
  Object.entries(d.chart_scenes||{}).forEach(([id,scene])=>{
   const groups=el(id);if(!groups)return;
   const chart=groups.parentElement,axis=id==='gap-groups'?scene.axis:scene;
   chart.style.setProperty('--score-zero',axis.zero+'%');
   chart.style.setProperty('--score-grid-step',(axis.ticks[1].position-axis.ticks[0].position)+'%');
   const labels=chart.querySelector('.score-x-axis');labels.replaceChildren(...axis.ticks.map(t=>{const n=node('span',t.label);n.style.left=t.position+'%';return n}));
   if(id==='gap-groups'){
    scene.tables.forEach(t=>t.rows.forEach(row=>{
     const group=[...groups.children].find(n=>n.dataset.model===row.model_id);if(!group)return;
     const metric=group.querySelector('[data-display-mode="'+t.id+'"]'),track=metric.querySelector('.gap-track');
     let bar=track.querySelector('.gap-bar');
     if(row.plot){if(!bar){bar=node('span',null,'gap-bar gap-'+t.id.toLowerCase());track.append(bar)}bar.dataset.model=row.model_id;bar.dataset.gapMetric=t.id;bar.dataset.gapValue=row.value;bar.style.left=row.plot.left+'%';bar.style.width=row.plot.width+'%'}else if(bar)bar.remove();
     const value=metric.querySelector('.gap-value');value.textContent=row.display;value.setAttribute('aria-label',t.id+' '+row.display);
    }));return;
   }
   Object.entries(scene.bars).forEach(([mid,modes])=>{
    const group=[...groups.children].find(n=>n.dataset.model===mid);if(!group)return;
    const spoken=[];
    Object.entries(modes).forEach(([mode,value])=>{
     const row=group.querySelector('.metric-bar-row[data-score-mode="'+mode+'"]'),bar=row.querySelector('.score-bar'),readout=row.querySelector('.chart-value');
     bar.dataset.score=value.value??'';bar.style.left=value.left+'%';bar.style.width=value.width+'%';
     spoken.push(scoreReadout(readout,value,value.text,value.interval));
    });
    const model=d.models.find(m=>m.id===mid);group.setAttribute('aria-label',model.label+' · '+['MC','RMC','SMC'].map((name,i)=>name+' '+spoken[i]).join('，'));
   });
  });
 }
 editionCharts();
 function renderView(key,render){const value=displayKey('overall');if(renderedViews.get(key)!==value){render();renderedViews.set(key,value)}}
 const sortDefaults={...Object.fromEntries(d.policy.groups.map(g=>[g.id,MG.presentationDefaultScore])),gap:'RG',rates:'reliability'};
 const sortChoices={...Object.fromEntries(d.policy.groups.map(g=>[g.id,d.score_modes])),gap:['RG','DG'],rates:['reliability','attainment']};
 const chartSort={...sortDefaults};
 function syncSorts(){
  const q=new URLSearchParams(location.search);
  const requested=q.get('category');
  category=d.policy.groups.some(group=>group.id===requested)?requested:d.policy.groups[0].id;
  Object.keys(sortDefaults).forEach(key=>{const value=q.get('sort-'+key);chartSort[key]=sortChoices[key].includes(value)?value:sortDefaults[key];document.querySelectorAll('[data-chart-sort="'+key+'"]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.sortValue===chartSort[key])))});
 }
 function orderedModels(value,ascending=false,key='overall'){
  return visibleModels(key).sort((a,b)=>{const x=value(a),y=value(b);if(x==null||y==null)return x==null?(y==null?compareModelOrder(a,b):1):-1;return (ascending?x-y:y-x)||compareModelOrder(a,b)});
 }
 function orderChart(id,models){
  const chart=el(id);if(!chart)return;
  const rows=new Map([...chart.children].map(row=>[row.dataset.model,row])),ids=new Set(models.map(model=>model.id));
  rows.forEach((row,id)=>{const hidden=!ids.has(id);if(row.hidden!==hidden)row.hidden=hidden});
  let previous=null;
  models.forEach(model=>{const row=rows.get(model.id),next=previous?previous.nextElementSibling:chart.firstElementChild;
   if(row!==next)chart.insertBefore(row,next);previous=row});
 }
 function auxiliaryCharts(){
  const gap=Object.fromEntries(d.gap_diagnostics.tables.find(t=>t.id===chartSort.gap).rows.map(r=>[r.model_id,r.value]));
  orderChart('gap-groups',orderedModels(m=>gap[m.id]==null?null:Math.abs(gap[m.id]),true,'gap'));
  const metric=chartSort.rates,field=metric==='reliability'?'observed':'confirmed';
  orderChart('rate-groups',orderedModels(m=>m.content_rates?.metrics[metric][field]??null,false,'rates'));
 }
 let category=new URLSearchParams(location.search).get('category');
 if(!d.policy.groups.some(g=>g.id===category))category=d.policy.groups[0].id;
 function modelLink(m,score=state.score){
  const a=node('a',m.label,'model-name');a.href=href('models/'+m.id+'/index.html');
  const u=new URL(a.href);u.searchParams.set('score',score);a.href=u.href;
  return a;
 }
 function ranking(){
  const b=el('ranking-body');b.replaceChildren();
  document.querySelectorAll('#ranking thead [data-display-mode]').forEach(cell=>cell.classList.toggle('primary-score',cell.dataset.displayMode===state.score));
  rankedScores(visibleModels()).forEach(({model:m,place})=>{
   const row=b.insertRow();row.style.setProperty('--model-ink',m.theme.ink);row.insertCell().append(node('span',place==null?'—':String(place),'rank'+(place===1?' first':'')));
   const wrap=node('div',null,'model'),symbol=node('span',null,'model-symbol'),text=node('div');symbol.style.background=m.theme.tint;symbol.setAttribute('aria-hidden','true');
   const icon=node('img');icon.src=m.logo.data_url;icon.alt='';symbol.append(icon);
   const name=node('a',m.label,'model-name');name.href=href('models/'+m.id+'/index.html');
   text.append(name);wrap.append(symbol,text);row.insertCell().append(wrap);
   row.insertCell().append(node('span',harnessName(m),'harness-name'));row.cells[2].className='harness-cell';
   text.append(node('span',harnessName(m),'mobile-harness'));
   text.append(node('span','交卷 '+deliveryLabel(m),'mobile-delivery'));
   const delivery=row.insertCell();delivery.className='numeric delivery-cell';delivery.textContent=deliveryLabel(m);
   delivery.title='主动交卷／强收有内容／总初答题数';
   d.display_score_modes.forEach(mode=>{const cell=row.insertCell();cell.dataset.displayMode=mode.id;cell.className='numeric score-cell'+(mode.id===state.score?' primary-score':'');cell.append(node('span',f(headline(result(m,state.condition,mode.id))),'score-number'))});
   const a=node('a','详细评测 →','record-link');a.href=name.href;a.setAttribute('aria-label',m.label+' 详细评测');row.insertCell().append(a);
  });
 }
 function categoryRanking(){
  d.category_leaderboards.forEach(g=>{
   const byId=Object.fromEntries(visibleModels(g.id).map(m=>[m.id,m]));
   const score=chartSort[g.id],key='category-'+g.id,value=displayKey(g.id,score);
   if(renderedViews.get(key)===value)return;
   renderedViews.set(key,value);
   const grouped=research?.id===g.id,parts=grouped?['item',...research.axes]:['item'];
   const t=table('category-ranking-'+g.id,['#','模型',...(categoryHarness?['Harness']:[])],[]);
   const header=t.tHead.rows[0];
   if(categoryHarness)header.cells[2].className='category-harness';
   let modeHeader=header;
   if(grouped){
    t.classList.add('research-score-table');
    t.parentElement.tabIndex=0;
    t.parentElement.setAttribute('aria-labelledby','category-tab-'+g.id);
    t.parentElement.setAttribute('role','region');
    for(const cell of header.cells)cell.rowSpan=2;
    for(const axis of parts){
     const cell=node('th');cell.id='research-score-'+axis;
     cell.colSpan=d.display_score_modes.length;cell.dataset.researchScoreGroup='';
     researchLabel(cell,axis,true);header.append(cell);
    }
    modeHeader=t.tHead.insertRow();
   }
   for(const axis of parts)for(const mode of d.display_score_modes){
    const cell=node('th',mode.abbreviation);cell.scope='col';cell.dataset.displayMode=mode.id;
    if(grouped){
     cell.id='research-score-'+axis+'-'+mode.id;cell.className='research-score-mode';
     if(axis==='item'&&mode.id===score)cell.setAttribute('aria-sort','descending');
    }
    modeHeader.append(cell);
   }
   const views=Object.fromEntries(d.score_modes.map(mode=>[mode,Object.fromEntries(g.views[mode].map(r=>[r.model_id,r]))]));
   const items=g.views[score].filter(item=>byId[item.model_id]);
   orderChart('category-chart-groups-'+g.id,items.map(item=>byId[item.model_id]));
   items.forEach(item=>{
    const m=byId[item.model_id],r=t.tBodies[0].insertRow();r.insertCell().textContent=item.rank??'—';r.insertCell().append(modelLink(m,score));
    if(categoryHarness){const harness=r.insertCell();harness.className='category-harness';harness.textContent=harnessName(m);}
    for(const axis of parts)for(const mode of d.display_score_modes){
     const v=grouped?research.metric(m.id,mode.abbreviation,axis):views[mode.id][m.id],c=r.insertCell();
     c.dataset.displayMode=mode.id;c.className='numeric score-cell'+(axis==='item'&&mode.id===score?' primary-score':'');
     if(grouped)c.setAttribute('headers','research-score-'+axis+' research-score-'+axis+'-'+mode.id);
     if(v.value<0)c.classList.add('negative');
     const text=node('span',null,'score-number');scoreReadout(text,v,f(v.value),v.lower==null?'':'完整分区间 '+f(v.lower)+'–'+f(v.upper),c);c.append(text);
    }
   });
  });
  selectCategory(category,false);
 }
 function selectCategory(id,updateUrl=true){
  category=id;
  d.policy.groups.forEach(g=>{const selected=g.id===id,b=el('category-tab-'+g.id);b.setAttribute('aria-selected',String(selected));b.tabIndex=selected?0:-1;el('category-panel-'+g.id).hidden=!selected});
  if(updateUrl){const u=new URL(location.href);u.searchParams.set('category',id);u.hash='category-leaderboards';history.replaceState(null,'',u);window.dispatchEvent(new CustomEvent('mg:updated',{detail:{rendered:false}}))}
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
  syncSorts();renderView('ranking',ranking);categoryRanking();auxiliaryCharts();
  orderChart('chart-groups',visibleModels().sort(compareScores));
  const visibleIds=new Set(visibleModels().map(m=>m.id)),initiativeIds=new Set(visibleModels('initiative').map(m=>m.id));
  const harnessNotes=el('harness-notes');
  if(harnessNotes&&Array.isArray(d.harness_notes))harnessNotes.replaceChildren(...d.harness_notes
   .filter(note=>note.model_ids.some(id=>visibleIds.has(id)))
   .map(note=>{const p=node('p',note.marker+' '+note.text[state.lang==='en'?'en':'zh'],'panel-foot');p.dataset.harnessNote=note.marker;return p}));
  const historyIds=new Set([...d.models,...(d.pending_models||[]),...(d.partial_models||[])].map(m=>m.id));
  document.querySelectorAll('[data-model-note]').forEach(n=>{
   n.hidden=n.closest('.run-history-snapshot')?d.benchmark_version==='1.2.0'&&!historyIds.has(n.dataset.modelNote):!(n.closest('[data-board="initiative"]')?initiativeIds:visibleIds).has(n.dataset.modelNote);
  });
  const selected=modes[state.score];el('leaderboard-desc').textContent='公开＋私有 · 按'+selected.abbreviation+'排序 · 满分100';el('score-explanation').textContent={capability:'累计有效数学成果。',partial:'按有效成果计分，扣除错误、回退和误报。',strict:'整题及规定自查轨迹全部达标才计分。'}[state.score];
  el('downloads').replaceChildren(...visibleModels().sort(compareModelOrder).map(m=>{const a=node('a',short(m)+' · JSON ↓','download-link');a.href=download(m);return a}));
 });
})();
