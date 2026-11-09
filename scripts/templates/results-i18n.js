/* Translate interface nodes only. Source answers, math, reviews and JSON stay byte-bound. */
window.MGI18n = (() => {
 const messages=@@MG_MESSAGES@@;
 const originals=new WeakMap(), attributes=new WeakMap(), title=document.title;
 const keys=Object.keys(messages).sort((a,b)=>b.length-a.length);
 const phrases=new RegExp(keys.map(k=>k.replace(/[.*+?^${}()|[\]\\]/g,'\\$&')).join('|'),'g');
 const blocked='script,style,pre,code,math,.prose,.review-criteria,.findings,.source-list,[data-original],[data-language]';
 function translate(value){return messages[value]??value.replace(phrases,key=>messages[key]);}
 function eligible(element){return !element.closest(blocked)||!!element.closest('[data-ui-prose]');}
 function apply(language){
  const english=language==='en';document.documentElement.lang=english?'en':'zh-CN';
  document.title=english?translate(title):title;
  const walker=document.createTreeWalker(document.body,NodeFilter.SHOW_TEXT);
  while(walker.nextNode()){
   const n=walker.currentNode;if(!eligible(n.parentElement))continue;
   if(!originals.has(n))originals.set(n,n.nodeValue);
   n.nodeValue=english?translate(originals.get(n)):originals.get(n);
  }
  document.querySelectorAll('[aria-label],[title],[placeholder]').forEach(n=>{
   if(!eligible(n))return;
   if(!attributes.has(n))attributes.set(n,{});
   const saved=attributes.get(n);
   ['aria-label','title','placeholder'].forEach(key=>{if(!n.hasAttribute(key))return;if(!(key in saved))saved[key]=n.getAttribute(key);n.setAttribute(key,english?translate(saved[key]):saved[key])});
  });
  document.querySelectorAll('[data-lang-content]').forEach(n=>n.hidden=n.dataset.langContent!==language);
  document.querySelectorAll('[data-language]').forEach(n=>n.setAttribute('aria-pressed',String(n.dataset.language===language)));
 }
 return {apply,translate};
})();
