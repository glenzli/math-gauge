/* Load only existing public code excerpts, and render their original text without executing it. */
(() => {
 'use strict';
 const requests=new Map(),proseRequests=new Map(),pendingProse=new Map();
 window.MGProseData=(key,value)=>{
  const pending=pendingProse.get(key);
  if(!pending||pending.value||!value||typeof value.html!=='string'||value.source!=='assets/content/'+key+'.html')return;
  pending.value=value;
 };
 function visible(record){
  for(let parent=record;parent;parent=parent.parentElement){
   if(parent.hidden||parent.tagName==='DETAILS'&&!parent.open)return false;
  }
  return true;
 }
 async function load(record){
  if(record.dataset.recordLoaded||record.getAttribute('aria-busy')==='true'||!visible(record))return;
  const url=new URL(record.dataset.lazyRecord,document.baseURI).href;
  record.setAttribute('aria-busy','true');
  try{
   if(!requests.has(url))requests.set(url,fetch(url).then(response=>{
    if(!response.ok)throw new Error('Record unavailable: '+response.status);
    return response.arrayBuffer();
   }).then(bytes=>new TextDecoder('utf-8',{fatal:true,ignoreBOM:true}).decode(bytes)).catch(error=>{requests.delete(url);throw error}));
   const text=await requests.get(url),code=document.createElement('code');
   code.className=record.dataset.recordCodeClass;code.textContent=text;
   record.replaceChildren(code);record.dataset.recordLoaded='true';
  }catch{
   // The ordinary source link remains usable after a failed fetch, including file:// viewing.
   record.dataset.recordLoaded='';
  }finally{record.removeAttribute('aria-busy')}
 }
 async function loadProse(record){
  if(!record.dataset.lazyProse||record.dataset.proseLoaded||record.getAttribute('aria-busy')==='true'||!visible(record))return;
  const key=record.dataset.proseKey,url=new URL(record.dataset.lazyProse,document.baseURI);
  if(!/^[a-f0-9]{64}$/.test(key)||!url.pathname.endsWith('/assets/content/'+key+'.js')||url.origin!==new URL(document.baseURI).origin)return;
  record.setAttribute('aria-busy','true');
  try{
   if(!proseRequests.has(key))proseRequests.set(key,new Promise((resolve,reject)=>{
    const pending={value:null},script=document.createElement('script');pendingProse.set(key,pending);script.src=url.href;
    script.onload=()=>{pendingProse.delete(key);script.remove();pending.value?resolve(pending.value):reject(new Error('Missing prose registration'))};
    script.onerror=()=>{pendingProse.delete(key);script.remove();reject(new Error('Prose unavailable'))};document.head.append(script);
   }).catch(error=>{proseRequests.delete(key);throw error}));
   const value=await proseRequests.get(key),template=document.createElement('template');template.innerHTML=value.html;
   template.content.querySelectorAll('script,iframe,object,embed,link,style,meta').forEach(n=>n.remove());
   template.content.querySelectorAll('*').forEach(n=>[...n.attributes].forEach(a=>{if(/^on/i.test(a.name))n.removeAttribute(a.name)}));
   const base=new URL(key+'.html',url);
   template.content.querySelectorAll('[href]').forEach(n=>{const target=new URL(n.getAttribute('href'),base);if(['https:','http:','file:'].includes(target.protocol))n.href=target.href;else if(!n.getAttribute('href').startsWith('#'))n.removeAttribute('href')});
   record.replaceChildren(template.content);record.dataset.proseLoaded='true';
   if(window.MG){
    record.querySelectorAll('[data-context-link]').forEach(n=>n.href=window.MG.href(n.getAttribute('href')));
    record.querySelectorAll('[data-edition-data-link]').forEach(n=>n.href=(window.MG.d.edition_paths?.download_prefix||'')+'data.json');
   }
   window.MGI18n?.apply(window.MG?.state.lang||new URLSearchParams(location.search).get('lang')||'zh');
  }catch{record.dataset.proseLoaded=''}finally{record.removeAttribute('aria-busy')}
 }
 function refresh(){document.querySelectorAll('pre[data-lazy-record]').forEach(load);document.querySelectorAll('[data-lazy-prose]').forEach(loadProse)}
 document.addEventListener('toggle',event=>{if(event.target.tagName==='DETAILS'&&event.target.open)refresh()},true);
 window.addEventListener('mg:updated',refresh);
 refresh();
})();
