const {test}=require('node:test');
const assert=require('node:assert/strict');
const {series,readBoard,toggleShown,boardURL,applyVisibility}=require('../scripts/templates/board-controls.js');
const all=['capability','partial','strict'];

test('scoped preferences restore independently while legacy shared links remain readable',()=>{
 assert.deepEqual(readBoard('').shown,all);
 assert.deepEqual(readBoard('?show=smc,mc,smc','written').shown,['capability','strict']);
 const search='?show=rmc&complete=1&show-written=smc&complete-written=0';
 assert.deepEqual(readBoard(search,'overall'),{shown:['partial'],completeOnly:true});
 assert.deepEqual(readBoard(search,'written'),{shown:['strict'],completeOnly:false});
 assert.deepEqual(readBoard(search,'gap'),{shown:['RG','DG'],completeOnly:true});
 assert.deepEqual(readBoard('?show-rates=attainment','rates').shown,['attainment']);
 assert.deepEqual(readBoard('?show-lean=unknown','lean').shown,all);
});

test('changing one board cannot change other boards, scores, sorting, language or anchor',()=>{
 const original=new URL('https://example.test/site/index.html?score=partial&sort-written=strict&sort-gap=DG&complete=1&show=rmc&lang=en&category=research#category-leaderboards');
 for(const key of Object.keys(series)){
  const changed=boardURL(original.href,key,{shown:[series[key][0].id],completeOnly:false});
  for(const other of Object.keys(series))if(other!==key)assert.deepEqual(readBoard(changed.search,other),readBoard(original.search,other));
  assert.deepEqual(readBoard(changed.search,key),{shown:[series[key][0].id],completeOnly:false});
  changed.searchParams.delete('show-'+key);changed.searchParams.delete('complete-'+key);
  assert.equal(changed.href,original.href);
 }
});

test('every board keeps at least one metric and canonical ordering without changing the input',()=>{
 for(const [key,items] of Object.entries(series)){
  const first=items[0].id,last=items.at(-1).id,current=[first];
  assert.deepEqual(toggleShown(current,first,false,key),[first]);
  assert.deepEqual(toggleShown(current,last,true,key),[first,last]);
  assert.deepEqual(current,[first]);
 }
});

test('returning to all metrics overrides a narrow legacy link for this board only',()=>{
 const url=boardURL('https://example.test/?show=rmc&complete=1','overall',{shown:all,completeOnly:false});
 assert.deepEqual(readBoard(url.search),{shown:all,completeOnly:false});
 assert.deepEqual(readBoard(url.search,'lean'),{shown:['partial'],completeOnly:true});
});

test('visibility changes only supplied elements, preserving zero and unknown values',()=>{
 const elements=all.map((id,index)=>({dataset:{displayMode:id},hidden:false,textContent:['0.00','—','15.25'][index]}));
 const original=elements.map(element=>element.textContent);
 applyVisibility(elements,['partial']);
 assert.deepEqual(elements.map(element=>element.hidden),[true,false,true]);
 applyVisibility(elements,all);
 assert.deepEqual(elements.map(element=>element.hidden),[false,false,false]);
 assert.deepEqual(elements.map(element=>element.textContent),original);
});
