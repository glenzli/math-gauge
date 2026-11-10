/* Per-board display preferences. Sorting and mathematical values stay source-owned. */
(() => {
 'use strict';
 const scores=[{id:'capability',key:'mc'},{id:'partial',key:'rmc'},{id:'strict',key:'smc'}];
 const series={overall:scores,written:scores,lean:scores,research:scores,
  gap:[{id:'RG',key:'rg'},{id:'DG',key:'dg'}],
  rates:[{id:'reliability',key:'reliability'},{id:'attainment',key:'attainment'}],
  initiative:[{id:'groups',key:'groups'},{id:'coverage',key:'coverage'}]};
 const ids=key=>series[key].map(s=>s.id);
 function normalizeShown(values,key='overall'){
  const selected=ids(key).filter(id=>values.includes(id));
  return selected.length?selected:ids(key);
 }
 function readBoard(search,key='overall'){
  const q=new URLSearchParams(search),legacy=scores===series[key]?q.get('show'):null;
  const keys=(q.get('show-'+key)??legacy??'').toLowerCase().split(',');
  return {shown:normalizeShown(series[key].filter(s=>keys.includes(s.key)).map(s=>s.id),key),
   completeOnly:(q.get('complete-'+key)??q.get('complete'))==='1'};
 }
 function toggleShown(current,id,checked,key='overall'){
  const selected=normalizeShown(current,key);
  if(!ids(key).includes(id))return selected;
  const next=checked?[...selected,id]:selected.filter(value=>value!==id);
  return next.length?normalizeShown(next,key):selected;
 }
 function boardURL(href,key,patch){
  const url=new URL(href);
  if(patch.shown)url.searchParams.set('show-'+key,series[key].filter(s=>normalizeShown(patch.shown,key).includes(s.id)).map(s=>s.key).join(','));
  if('completeOnly' in patch)url.searchParams.set('complete-'+key,patch.completeOnly?'1':'0');
  return url;
 }
 function applyVisibility(elements,values){elements.forEach(element=>{element.hidden=!values.includes(element.dataset.displayMode)})}
 const api={series,normalizeShown,readBoard,toggleShown,boardURL,applyVisibility};
 if(typeof module!=='undefined'&&module.exports)module.exports=api;
 if(typeof window==='undefined')return;
 window.MGBoards=api;
 if(!window.MG)return;
 const roots=[...document.querySelectorAll('[data-board]')];
 let opened=null;
 function close(restore=false){
  if(!opened)return;
  const {panel,button}=opened;
  panel.hidden=true;button.setAttribute('aria-expanded','false');opened=null;
  if(restore)button.focus({preventScroll:true});
 }
 function position(panel,button){
  const r=button.getBoundingClientRect(),w=Math.min(320,innerWidth-32);
  panel.style.width=w+'px';
  panel.style.left=Math.max(16,Math.min(innerWidth-w-16,r.right-w))+'px';
  const height=panel.getBoundingClientRect().height;
  panel.style.top=Math.max(12,Math.min(r.bottom+10,innerHeight-height-12))+'px';
 }
 function owned(root,selector){return [...root.querySelectorAll(selector)].filter(n=>n.closest('[data-board]')===root)}
 const applied=new WeakMap();
 function sync(event){
  roots.forEach(root=>{
   const key=root.dataset.board,{shown,completeOnly}=readBoard(location.search,key);
   const signature=JSON.stringify([shown,completeOnly]);
   if(event?.detail?.rendered===false&&applied.get(root)===signature)return;
   applied.set(root,signature);
   root.dataset.visibleScores=String(shown.length);
   applyVisibility(owned(root,'[data-display-mode]'),shown);
   owned(root,'[data-show-score]').forEach(input=>{input.checked=shown.includes(input.dataset.showScore);input.disabled=input.checked&&shown.length===1});
   owned(root,'[data-board-complete]').forEach(input=>input.checked=completeOnly);
   owned(root,'[data-filter-active]').forEach(n=>n.hidden=!completeOnly);
  });
 }
 function change(key,patch){
  history.replaceState(null,'',boardURL(location.href,key,patch));
  window.dispatchEvent(new Event('mg:board-settings'));
 }
 roots.forEach(root=>{
  const key=root.dataset.board,button=root.querySelector('[data-board-settings="'+key+'"]'),panel=document.getElementById('board-options-'+key);
  if(!button||!panel)return;
  button.addEventListener('click',()=>{
   if(opened?.panel===panel){close(true);return}
   close();panel.hidden=false;button.setAttribute('aria-expanded','true');opened={panel,button};position(panel,button);
   panel.querySelector('input:not(:disabled)')?.focus({preventScroll:true});
  });
  panel.querySelector('[data-board-close]').addEventListener('click',()=>close(true));
  panel.querySelectorAll('[data-show-score]').forEach(input=>input.addEventListener('change',()=>change(key,{shown:toggleShown(readBoard(location.search,key).shown,input.dataset.showScore,input.checked,key)})));
  panel.querySelector('[data-board-complete]').addEventListener('change',event=>change(key,{completeOnly:event.target.checked}));
  panel.querySelector('[data-show-all]').addEventListener('click',()=>change(key,{shown:ids(key)}));
 });
 document.addEventListener('pointerdown',event=>{if(opened&&!opened.panel.contains(event.target)&&!opened.button.contains(event.target))close()});
 document.addEventListener('keydown',event=>{if(event.key==='Escape'&&opened){event.preventDefault();close(true)}});
 document.addEventListener('scroll',event=>{if(opened&&!opened.panel.contains(event.target))close()},true);
 window.addEventListener('resize',()=>close());
 window.addEventListener('mg:updated',sync);
 sync();
})();
