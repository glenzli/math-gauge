/* Translate interface nodes only. Source answers, math, reviews and JSON stay byte-bound. */
window.MGI18n = (() => {
 const messages=@@MG_MESSAGES@@;
 const originals=new WeakMap(), attributes=new WeakMap(), title=document.title;
 const keys=Object.keys(messages).sort((a,b)=>b.length-a.length);
 const phrases=new RegExp(keys.map(k=>k.replace(/[.*+?^${}()|[\]\\]/g,'\\$&')).join('|'),'g');
 const blocked='script,style,pre,code,math,.prose,.review-criteria,.findings,.source-list,[data-original],[data-language]';
 function translate(value){return messages[value]??value.replace(phrases,key=>messages[key]);}
 function eligible(element){return !element.closest(blocked)||!!element.closest('[data-ui-prose]');}
 const pending=[];let lastLanguage;
 const observer=new MutationObserver(records=>pending.push(...records));
 observer.observe(document.body,{childList:true,subtree:true});
 function apply(language){
  const english=language==='en';document.documentElement.lang=english?'en':'zh-CN';
  const nextTitle=english?translate(title):title;if(document.title!==nextTitle)document.title=nextTitle;
  const changes=pending.splice(0).concat(observer.takeRecords());
  const roots=language===lastLanguage?[...new Set(changes.flatMap(record=>[...record.addedNodes]).filter(node=>node.isConnected))]:[document.body];
  const selected=new Set(roots);
  function text(node){
   if(!eligible(node.parentElement))return;
   if(!originals.has(node))originals.set(node,node.nodeValue);
   const value=english?translate(originals.get(node)):originals.get(node);if(node.nodeValue!==value)node.nodeValue=value;
  }
  function attrs(node){
   if(!eligible(node))return;
   if(!attributes.has(node))attributes.set(node,{});
   const saved=attributes.get(node);
   ['aria-label','title','placeholder'].forEach(key=>{
    if(!node.hasAttribute(key))return;if(!(key in saved))saved[key]=node.getAttribute(key);
    const value=english?translate(saved[key]):saved[key];if(node.getAttribute(key)!==value)node.setAttribute(key,value);
   });
  }
  roots.forEach(root=>{
   for(let parent=root.parentNode;parent;parent=parent.parentNode)if(selected.has(parent))return;
   if(root.nodeType===3){text(root);return}
   const walker=document.createTreeWalker(root,NodeFilter.SHOW_TEXT);while(walker.nextNode())text(walker.currentNode);
   if(root.matches?.('[aria-label],[title],[placeholder]'))attrs(root);
   root.querySelectorAll?.('[aria-label],[title],[placeholder]').forEach(attrs);
  });
  document.querySelectorAll('[data-lang-content]').forEach(node=>{const hidden=node.dataset.langContent!==language;if(node.hidden!==hidden)node.hidden=hidden});
  document.querySelectorAll('[data-language]').forEach(node=>{const value=String(node.dataset.language===language);if(node.getAttribute('aria-pressed')!==value)node.setAttribute('aria-pressed',value)});
  lastLanguage=language;
 }
 return {apply,translate};
})();
