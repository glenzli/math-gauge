/* Shared display state and formatting. All arithmetic stays in scoring.py. */
window.MG = (() => {
 const d=JSON.parse(document.getElementById('data').textContent), q=new URLSearchParams(location.search);
 const state={score:d.score_modes.includes(q.get('score'))?q.get('score'):d.default_score_mode,
  condition:d.default_attempt_condition,lang:q.get('lang')==='en'?'en':'zh',completeOnly:q.get('complete')==='1'};
 const modes=Object.fromEntries(d.display_score_modes.map(m=>[m.id,m]));
 const el=id=>document.getElementById(id), f=v=>v==null?'—':Number(v).toFixed(2);
 const node=(tag,text,cls)=>{const n=document.createElement(tag);if(text!=null)n.textContent=text;if(cls)n.className=cls;return n};
 const result=(m,c=state.condition,mode=state.score)=>mode==='partial'?(c==='single_attempt'?m.combined:m.retry.combined):m[mode][c];
 const headline=r=>r.metrics.earned.confirmed??r.metrics.earned.exact;
 const knownValue=v=>v.exact??((v.coverage.adjudicated>0||v.confirmed)?v.confirmed:null);
 const short=m=>m.short_label||(m.id.startsWith('terra')?'Terra':m.id.startsWith('deepseek')?'DeepSeek':m.id.startsWith('gemini')?'Gemini':m.label);
 const conditionLabel=()=> '规则允许的最终成绩';
 function table(id,headers,rows){const t=el(id);t.replaceChildren();const h=t.createTHead().insertRow();headers.forEach(s=>{const c=node('th',s);c.scope='col';h.append(c)});const b=t.createTBody();rows.forEach(v=>{const r=b.insertRow();v.forEach(s=>{const c=r.insertCell();if(s instanceof Node)c.append(s);else c.textContent=s;if(typeof s==='string'&&s.startsWith('-'))c.className='negative'})});return t}
 function points(m,id,weight){
  const r=result(m),v=r.contributions[id],leaf=d.policy.subcategories.find(c=>c.id===id);
  if(leaf?.status==='under_construction')return '—';
  const value=knownValue(v);
  return value==null?'—':f(value)+'/'+weight;
 }
 function href(path){const u=new URL(path,document.baseURI),current=new URLSearchParams(location.search);u.searchParams.set('score',state.score);u.searchParams.set('condition',state.condition);u.searchParams.set('lang',state.lang);if(state.completeOnly)u.searchParams.set('complete','1');else u.searchParams.delete('complete');const keys=new Set(['show','category','sort-written','sort-lean','sort-research','sort-gap','sort-rates',...current.keys(),...u.searchParams.keys()]);keys.forEach(key=>{if(!/^(show(?:-|$)|complete-|category$|sort-)/.test(key))return;if(current.has(key))u.searchParams.set(key,current.get(key));else u.searchParams.delete(key)});if(u.pathname.endsWith('/method.html'))['review-process','content-rate-method'].forEach(id=>{if(u.hash==='#'+id||u.hash==='#'+id+'-en')u.hash='#'+id+(state.lang==='en'?'-en':'')});return u.href}
 function download(m,prefix=''){return prefix+'downloads/'+m.id+'-combined'+(state.score==='strict'?'-strict':state.score==='capability'?'-capability':'')+(state.condition==='single_attempt'?'':'-retry')+'.json'}
 function taskValue(task){return state.score==='strict'?(task.strict_pass==null?'未知':task.strict_pass?'通过':'未通过'):(task.completion.exact==null?'未知':f(task.completion.exact*100)+'/100')}
 function start(render){
  function update(){
   document.querySelectorAll('[data-score-mode][aria-pressed]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.scoreMode===state.score)));
   document.querySelectorAll('[data-condition][aria-pressed]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.condition===state.condition)));
   document.querySelectorAll('.context-label').forEach(n=>n.textContent=modes[state.score].name+'（'+modes[state.score].abbreviation+'） · '+conditionLabel());
   document.querySelectorAll('[data-context-link]').forEach(a=>a.href=href(a.getAttribute('href')));
   try{history.replaceState(null,'',href(location.href))}catch{}
   render();
   const filter=el('completed-only');if(filter)filter.checked=state.completeOnly;
   MGI18n.apply(state.lang);
   window.dispatchEvent(new Event('mg:updated'));
  }
  document.querySelectorAll('button[data-score-mode]').forEach(b=>b.onclick=()=>{state.score=b.dataset.scoreMode;update()});
  document.querySelectorAll('button[data-condition]').forEach(b=>b.onclick=()=>{state.condition=b.dataset.condition;update()});
  document.querySelectorAll('button[data-language]').forEach(b=>b.onclick=()=>{state.lang=b.dataset.language;update()});
  const filter=el('completed-only');if(filter)filter.onchange=()=>{state.completeOnly=filter.checked;update()};
  window.addEventListener('popstate',()=>{const p=new URLSearchParams(location.search);state.score=d.score_modes.includes(p.get('score'))?p.get('score'):d.default_score_mode;state.lang=p.get('lang')==='en'?'en':'zh';state.completeOnly=p.get('complete')==='1';state.condition=d.default_attempt_condition;update()});
  window.addEventListener('mg:board-settings',update);
  update();
 }
 return {d,state,modes,el,f,node,result,headline,knownValue,short,conditionLabel,table,points,href,download,taskValue,start};
})();
