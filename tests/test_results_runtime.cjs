const assert=require('node:assert/strict');
const fs=require('node:fs');
const path=require('node:path');
const vm=require('node:vm');
const {test}=require('node:test');
const {setImmediate:nextTurn}=require('node:timers/promises');
const templates=path.resolve(__dirname,'../scripts/templates');

test('language and metric visibility reuse views; history restores dependent filters and sorts',()=>{
 const events=new Map();let renders=0;
 const url='https://example.test/nested/gauge/?lang=zh';
 const link={href:'https://example.test/nested/gauge/models/fixture/index.html?score=strict&lang=zh'};
 const context=vm.createContext({URL,URLSearchParams,Event,CustomEvent,location:new URL(url),
  history:{replaceState(){}},MGI18n:{apply(){}},
  document:{baseURI:url,getElementById:id=>id==='data'?{textContent:JSON.stringify({
   score_modes:['capability','partial','strict'],default_score_mode:'partial',
   default_attempt_condition:'nonlogical_retry_3',display_score_modes:[]})}:null,
   querySelectorAll:selector=>selector==='a[href]'?[link]:[]},
  window:{addEventListener:(name,fn)=>events.set(name,fn),dispatchEvent:event=>events.get(event.type)?.(event)}});
 vm.runInContext(fs.readFileSync(path.join(templates,'results-core.js'),'utf8'),context);
 const display=context.window.MG;
 display.start(()=>renders++);
 display.state.lang='en';events.get('mg:board-settings')();
 assert.equal(renders,1);
 assert.equal(new URL(link.href).searchParams.get('lang'),'en');
 assert.equal(new URL(link.href).searchParams.get('score'),'strict','category link keeps its selected mode');
 context.location.searchParams.set('show-written','smc');events.get('mg:board-settings')();
 assert.equal(renders,1);
 context.location.searchParams.set('complete-written','1');events.get('popstate')();
 assert.equal(renders,2);
 context.location.searchParams.set('sort-written','capability');events.get('popstate')();
 assert.equal(renders,3);
 context.location.searchParams.set('category','research');events.get('popstate')();
 assert.equal(renders,4);
 context.location.searchParams.delete('category');context.location.searchParams.delete('sort-written');events.get('popstate')();
 assert.equal(renders,5);
 // A page-owned category update is already rendered before its notification.
 context.location.searchParams.set('category','lean');events.get('mg:updated')();
 display.state.lang='zh';events.get('mg:board-settings')();
 assert.equal(renders,5);
});

function lazyFixture(records,fetch){
 const documentEvents=new Map(),windowEvents=new Map();
 const context=vm.createContext({URL,TextDecoder,fetch,
  document:{baseURI:'https://example.test/gauge/models/fixture/index.html',
   querySelectorAll:()=>records,addEventListener:(name,fn)=>documentEvents.set(name,fn),
   createElement:tag=>{assert.equal(tag,'code');return {className:'',textContent:''}}},
  window:{addEventListener:(name,fn)=>windowEvents.set(name,fn)}});
 vm.runInContext(fs.readFileSync(path.join(templates,'records.js'),'utf8'),context);
 return {documentEvents,windowEvents};
}
function record(parent,url='../../assets/versioned/record.fixture.txt'){
 const attrs=new Map();
 return {hidden:false,parentElement:parent,dataset:{lazyRecord:url,recordCodeClass:'language-lean'},children:['source link'],
  getAttribute:key=>attrs.get(key)??null,setAttribute:(key,value)=>attrs.set(key,value),removeAttribute:key=>attrs.delete(key),
  replaceChildren(...children){this.children=children}};
}

test('folded and inactive original text waits; opened records share a fetch and render exact inert text',async()=>{
 const parent={tagName:'DETAILS',open:false,parentElement:null};
 const first=record(parent),second=record(parent);second.hidden=true;
 const original='\ufeff原文 <script>globalThis.unsafe=true</script> &amp;\n';
 const urls=[];
 const fixture=lazyFixture([first,second],async url=>{urls.push(url);return {ok:true,arrayBuffer:async()=>Buffer.from(original)}});
 assert.equal(urls.length,0);
 parent.open=true;fixture.documentEvents.get('toggle')({target:parent});await nextTurn();
 assert.equal(urls.length,1);assert.equal(first.children[0].textContent,original);
 assert.deepEqual(second.children,['source link']);
 second.hidden=false;fixture.windowEvents.get('mg:updated')();await nextTurn();
 assert.equal(urls.length,1);assert.equal(second.children[0].textContent,original);
 assert.equal(first.children[0].className,'language-lean');
});

test('a failed lazy request leaves the source link usable and can be retried',async()=>{
 const parent={tagName:'DETAILS',open:false,parentElement:null},item=record(parent);let calls=0;
 const fixture=lazyFixture([item],async()=>{calls++;return calls===1?{ok:false,status:503}:{ok:true,arrayBuffer:async()=>Buffer.from('Original')}});
 parent.open=true;fixture.documentEvents.get('toggle')({target:parent});await nextTurn();
 assert.deepEqual(item.children,['source link']);assert.equal(item.getAttribute('aria-busy'),null);
 fixture.documentEvents.get('toggle')({target:parent});await nextTurn();
 assert.equal(calls,2);assert.equal(item.children[0].textContent,'Original');
});

test('translation revisits only added subtrees until a real language switch',()=>{
 let walks=0;const queue=[];
 const parent=blocked=>({closest:selector=>selector==='[data-ui-prose]'?null:blocked?{}:null});
 const old={nodeType:3,nodeValue:'模型排行榜',parentElement:parent(false),isConnected:true};
 const source={nodeType:3,nodeValue:'模型排行榜',parentElement:parent(true),isConnected:true};
 const body={nodeType:1,texts:[old,source],querySelectorAll:()=>[]};
 old.parentNode=body;source.parentNode=body;
 const document={title:'模型排行榜',body,documentElement:{},querySelectorAll:()=>[],
  createTreeWalker:root=>{walks++;let index=-1;return {nextNode:()=>++index<root.texts.length,get currentNode(){return root.texts[index]}}}};
 const context=vm.createContext({window:{},document,NodeFilter:{SHOW_TEXT:4},
  MutationObserver:class{observe(){}takeRecords(){return queue.splice(0)}}});
 const js=fs.readFileSync(path.join(templates,'results-i18n.js'),'utf8').replace('@@MG_MESSAGES@@',JSON.stringify({'模型排行榜':'Model leaderboard','当前成绩':'Current results'}));
 vm.runInContext(js,context);
 const translate=context.window.MGI18n.apply;
 translate('en');assert.equal(old.nodeValue,'Model leaderboard');assert.equal(source.nodeValue,'模型排行榜');
 const initial=walks;translate('en');assert.equal(walks,initial);
 const added={nodeType:3,nodeValue:'当前成绩',parentElement:parent(false),isConnected:true};
 const subtree={nodeType:1,parentNode:body,isConnected:true,texts:[added],querySelectorAll:()=>[]};
 added.parentNode=subtree;body.texts.push(added);queue.push({addedNodes:[subtree,added]});
 translate('en');assert.equal(walks,initial+1);assert.equal(added.nodeValue,'Current results');
 translate('zh');assert.equal(old.nodeValue,'模型排行榜');assert.equal(added.nodeValue,'当前成绩');assert.equal(source.nodeValue,'模型排行榜');
});
