/* Shared display state and formatting. All arithmetic stays in scoring.py. */
window.MG = (() => {
 const d=JSON.parse(document.getElementById('data').textContent), q=new URLSearchParams(location.search);
 const presentationDefaultScore='strict',presentationScoreOrder=['strict','partial','capability'];
 const scorePreference=(search,key='score')=>{const value=new URLSearchParams(search).get(key);return d.score_modes.includes(value)?value:presentationDefaultScore;};
 d.display_score_modes.sort((a,b)=>presentationScoreOrder.indexOf(a.id)-presentationScoreOrder.indexOf(b.id));
 const state={score:scorePreference(location.search),
  condition:d.default_attempt_condition,lang:q.get('lang')==='en'?'en':'zh'};
 const modes=Object.fromEntries(d.display_score_modes.map(m=>[m.id,m]));
 const el=id=>document.getElementById(id), f=v=>v==null?'—':Number(v).toFixed(2);
 const node=(tag,text,cls)=>{const n=document.createElement(tag);if(text!=null)n.textContent=text;if(cls)n.className=cls;return n};
 const result=(m,c=state.condition,mode=state.score)=>mode==='partial'?(c==='single_attempt'?m.combined:m.retry.combined):m[mode][c];
 const headline=r=>r.metrics.earned.confirmed??r.metrics.earned.exact;
 const displayOrders=new Map([...(d.models||[]),...(d.profile_models||[]),...(d.pending_models||[]),...(d.partial_models||[])]
  .filter(model=>Number.isInteger(model.display_order)).map(model=>[model.id,model.display_order]));
 function compareModelOrder(a,b){
  const x=typeof a==='string'?a:a.id,y=typeof b==='string'?b:b.id;
  const i=displayOrders.get(x)??a.display_order??Infinity,j=displayOrders.get(y)??b.display_order??Infinity;
  return i===j?x.localeCompare(y,'en'):i-j;
 }
 function publishedScore(model,mode) {
  if(Object.hasOwn(model.ranking_values||{},mode))return model.ranking_values[mode];
  const value=headline(result(model,state.condition,mode));
  return value==null?null:Math.round(Number(value.toFixed(2))*100);
 }
 const completeScores=model=>model.ranking_complete!==false&&presentationScoreOrder.every(mode=>publishedScore(model,mode)!=null);
 function comparePublishedScores(a,b,primary){
  const order=[primary,...presentationScoreOrder.filter(mode=>mode!==primary)];
  for(const mode of order){
   const x=publishedScore(a,mode),y=publishedScore(b,mode);
   if(x===y)continue;
   if(x==null)return 1;
   if(y==null)return -1;
   return y-x;
  }
  return 0;
 }
 function compareScores(a,b,primary=state.score){
  return comparePublishedScores(a,b,primary)||Number(completeScores(b))-Number(completeScores(a))||compareModelOrder(a,b);
 }
 function rankedScores(models,primary=state.score){
  let previous=null,place=0;
  return [...models].sort((a,b)=>compareScores(a,b,primary)).map((model,index)=>{
   const key=completeScores(model)?presentationScoreOrder.map(mode=>publishedScore(model,mode)).join('/'):null;
   if(key===null||key!==previous)place=index+1;
   previous=key;
   return {model,place:publishedScore(model,primary)==null?null:place};
  });
 }
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
 function href(path){const u=new URL(path,document.baseURI),current=new URLSearchParams(location.search);u.searchParams.set('score',state.score);u.searchParams.set('condition',state.condition);u.searchParams.set('lang',state.lang);if(window.MGEdition)u.searchParams.set('edition',window.MGEdition.selected);[...u.searchParams.keys()].filter(key=>key==='complete'||key.startsWith('complete-')).forEach(key=>u.searchParams.delete(key));const keys=new Set(['show','category','sort-written','sort-lean','sort-research','sort-gap','sort-rates','cost-axis','cost-score','profile-models','profile-stage',...current.keys(),...u.searchParams.keys()]);keys.forEach(key=>{if(!/^(show(?:-|$)|category$|sort-|view-|cost-(?:axis|score)$|profile-(?:models|stage|view|axis)$)/.test(key))return;if(current.has(key))u.searchParams.set(key,current.get(key));else u.searchParams.delete(key)});if(u.pathname.endsWith('/method.html'))['review-process','content-rate-method'].forEach(id=>{if(u.hash==='#'+id||u.hash==='#'+id+'-en')u.hash='#'+id+(state.lang==='en'?'-en':'')});return u.href}
 function refreshModelLinks(){
  document.querySelectorAll('a[href]').forEach(link=>{
   if(link.hasAttribute('data-fixed-edition'))return;
   const before=new URL(link.href,document.baseURI);
   if(before.origin!==location.origin||!/(?:^|\/)models\/[^/]+\/(?:index\.html)?$/.test(before.pathname))return;
   const after=new URL(href(before.href));
   // Cached category rows retain their independently selected score mode.
   if(before.searchParams.has('score'))after.searchParams.set('score',before.searchParams.get('score'));
   if(link.href!==after.href)link.href=after.href;
  });
 }
 function download(m,prefix=''){return prefix+(d.edition_paths?.download_prefix||'')+'downloads/'+m.id+'-combined'+(state.score==='strict'?'-strict':state.score==='capability'?'-capability':'')+(state.condition==='single_attempt'?'':'-retry')+'.json'}
 function taskValue(task){return state.score==='strict'&&!task.neutral_revision?(task.strict_pass==null?'未知':task.strict_pass?'通过':'未通过'):(task.completion.exact==null?'未知':f(task.completion.exact*100)+'/100')}
 function start(render){let renderKey;
  const signature=()=>JSON.stringify([state.score,state.condition,
   [...new URLSearchParams(location.search)].filter(([key])=>/^(sort-|category$)/.test(key)).sort()]);
  function update(){
   document.querySelectorAll('[data-score-mode][aria-pressed]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.scoreMode===state.score)));
   document.querySelectorAll('[data-condition][aria-pressed]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.condition===state.condition)));
   document.querySelectorAll('.context-label').forEach(n=>n.textContent=modes[state.score].name+'（'+modes[state.score].abbreviation+'） · '+conditionLabel());
   document.querySelectorAll('[data-context-link]').forEach(a=>a.href=href(a.getAttribute('href')));
   document.querySelectorAll('[data-edition-data-link]').forEach(a=>a.href=(d.edition_paths?.download_prefix||'')+'data.json');
   try{history.replaceState(null,'',href(location.href))}catch{}
   const nextKey=signature();
   const rendered=nextKey!==renderKey;
   if(rendered){render();renderKey=nextKey}
   MGI18n.apply(state.lang);
   window.dispatchEvent(new CustomEvent('mg:updated',{detail:{rendered}}));
  }
  document.querySelectorAll('button[data-score-mode]').forEach(b=>b.onclick=()=>{state.score=b.dataset.scoreMode;update()});
  document.querySelectorAll('button[data-condition]').forEach(b=>b.onclick=()=>{state.condition=b.dataset.condition;update()});
  document.querySelectorAll('button[data-language]').forEach(b=>b.onclick=()=>{state.lang=b.dataset.language;update()});
  window.addEventListener('popstate',()=>{const p=new URLSearchParams(location.search);state.score=scorePreference(location.search);state.lang=p.get('lang')==='en'?'en':'zh';state.condition=d.default_attempt_condition;update()});
  window.addEventListener('mg:board-settings',update);
  window.addEventListener('mg:updated',()=>{refreshModelLinks();renderKey=signature()});
  update();
 }
 return {d,state,modes,presentationDefaultScore,presentationScoreOrder,scorePreference,el,f,node,result,headline,compareScores,compareModelOrder,rankedScores,knownValue,short,conditionLabel,table,points,href,download,taskValue,start};
})();
