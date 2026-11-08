(() => {
 const {d,state,modes,el,f,node,result,headline,short,table,points,href,download,start}=MG;
 const expanded=new Set();
 function ranking(){
  const b=el('ranking-body');b.replaceChildren();
  [...d.models].sort((a,b)=>(headline(result(b))??-Infinity)-(headline(result(a))??-Infinity)).forEach((m,i)=>{
   const row=b.insertRow();row.style.setProperty('--model-ink',m.theme.ink);row.insertCell().append(node('span',String(i+1),'rank'+(i===0?' first':'')));
   const wrap=node('div',null,'model'),symbol=node('span',null,'model-symbol'),text=node('div');symbol.style.background=m.theme.tint;symbol.setAttribute('aria-hidden','true');
   const icon=node('img');icon.src=m.logo.data_url;icon.alt='';symbol.append(icon);
   const name=node('a',m.label,'model-name');name.href=href('models/'+m.id+'/index.html');
   if(m.record_kind==='native_harness'){const marker=node('sup','†','source-marker');marker.setAttribute('aria-label','Dot native harness，运行条件见详情');name.append(marker)}
   if(m.evaluation_progress[state.condition].incomplete){const marker=node('sup','*','incomplete-marker');marker.setAttribute('aria-label','尚未测完');name.append(marker)}
   text.append(name);wrap.append(symbol,text);row.insertCell().append(wrap);
   row.insertCell().append(node('span',m.harness.name,'harness-name'));row.cells[2].className='harness-cell';
   text.append(node('span',m.harness.name,'mobile-harness'));
   d.display_score_modes.forEach(mode=>{const cell=row.insertCell();cell.className='numeric score-cell'+(mode.id==='partial'?' primary-score':'');cell.append(node('span',f(headline(result(m,state.condition,mode.id))),'score-number'))});
   const a=node('a','详细评测 →','record-link');a.href=name.href;a.setAttribute('aria-label',m.label+' 详细评测');row.insertCell().append(a);
  });
 }
 function taxonomy(){
  table('capabilities',['大类 / 子类','权重',...d.models.map(short)],[]);const b=el('capabilities').tBodies[0];
  function add(item,group,parent){
   const r=b.insertRow();r.className=group?'tree-group':'tree-child';if(parent){r.dataset.parent=parent;r.hidden=!expanded.has(parent)}
   const title=r.insertCell();
   if(group){const btn=node('button',(expanded.has(item.id)?'▾ ':'▸ ')+item.title,'category-toggle');btn.setAttribute('aria-expanded',String(expanded.has(item.id)));btn.onclick=()=>{if(expanded.has(item.id))expanded.delete(item.id);else expanded.add(item.id);taxonomy()};title.append(btn)}
   else title.append(node('div',item.title,'tree-name'));
   r.insertCell().textContent=item.weight+'%';d.models.forEach(m=>r.insertCell().textContent=points(m,item.id,item.weight));
  }
  d.policy.groups.forEach(g=>{add(g,true);g.children.forEach(id=>add(d.policy.subcategories.find(c=>c.id===id),false,g.id))});
 }
 start(()=>{
  ranking();taxonomy();const ordered=[...d.models].sort((a,b)=>(headline(result(b))??-Infinity)-(headline(result(a))??-Infinity));
  for(const id of ['chart-groups','gap-groups','rate-groups']){const chart=el(id);if(chart)ordered.forEach(m=>chart.append(chart.querySelector(':scope > [data-model="'+m.id+'"]')))}
  const selected=modes[state.score];el('leaderboard-desc').textContent='公开＋私有 · 按'+selected.abbreviation+'排序 · 满分100';el('score-explanation').textContent=selected.description;
  el('contributions-title').textContent=selected.abbreviation+' · 分类贡献';el('contribution-mode').textContent=selected.abbreviation;el('active-condition').textContent=MG.conditionLabel();
  el('downloads').replaceChildren(...d.models.map(m=>{const a=node('a',short(m)+' · JSON ↓','download-link');a.href=download(m);return a}));
 });
})();
