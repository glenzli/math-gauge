/* Load only existing public code excerpts, and render their original text without executing it. */
(() => {
 'use strict';
 const requests=new Map();
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
 function refresh(){document.querySelectorAll('pre[data-lazy-record]').forEach(load)}
 document.addEventListener('toggle',event=>{if(event.target.tagName==='DETAILS'&&event.target.open)refresh()},true);
 window.addEventListener('mg:updated',refresh);
 refresh();
})();
