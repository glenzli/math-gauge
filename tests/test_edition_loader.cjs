/* Synthetic browser contracts only; no network or mathematical scoring. */
const assert=require('node:assert/strict');
const fs=require('node:fs');
const path=require('node:path');
const vm=require('node:vm');
const {test}=require('node:test');
const source=fs.readFileSync(path.join(__dirname,'../scripts/templates/edition-loader.js'),'utf8');

function fixture(options={}){
 const page=options.page||'models/fixture/cases/MG-TX001.html';
 const prefix='../'.repeat(page.split('/').length-1);
 const config={schema:'math-gauge.edition-view-config/v1',latest:'1.1.0',page,versions:{
  '1.1.0':{key:'1'.repeat(64),payload:prefix+'assets/payload-current.js',label:{zh:'1.1.0',en:'1.1.0'},status:{zh:'本地复评',en:'Local reassessment'}},
  '1.0.0':{key:'0'.repeat(64),payload:prefix+'assets/payload-old.js',label:{zh:'1.0.0',en:'1.0.0'},status:{zh:'原评分',en:'Original assessment'}}},
  scripts:[prefix+'assets/versioned/core.fixture.js',prefix+'assets/versioned/case.fixture.js']};
 if(options.configure)options.configure(config);
 const address=options.url||'https://example.test/nested/gauge/'+page+'?edition=1.0.0&score=strict&sort-lean=capability&sort-rates=reliability&cost-axis=time&lang=en#plot';
 const location=new URL(address),navigations=[],elements=new Map(),requests=[],controllers=[],events=new Map(),timers=new Map(),scrolls=[];
 const storage=options.storage||new Map(),history={state:options.historyState||null};
 history.replaceState=(state,title,url)=>{history.state=state;if(url)location.href=url};
 location.assign=url=>navigations.push(url);
 location.reload=()=>navigations.push(location.href);
 let nextTimer=0,context,fetches=0;
 class Element{
  constructor(tag,id=''){this.tagName=tag.toUpperCase();this.id=id;this.type='';this.textContent='';this.children=[];this.dataset={};this.attrs=new Map();this.listeners=new Map();this.hidden=false;this.value='';}
  setAttribute(key,value){this.attrs.set(key,String(value));if(key==='type')this.type=String(value)}
  getAttribute(key){return this.attrs.get(key)??null}
  removeAttribute(key){this.attrs.delete(key)}
  addEventListener(type,callback){this.listeners.set(type,callback)}
  replaceChildren(...children){this.children=children}
  remove(){this.removed=true}
  append(...children){
   this.children.push(...children);
   for(const child of children){
    if(child.id)elements.set(child.id,child);
    if(child.tagName!=='SCRIPT'||!child.src)continue;
    requests.push(child);
    queueMicrotask(()=>{
     const isPayload=child.src.includes('/payload-');
     if(isPayload){
      if(options.payloadWait)return;
      if(options.payloadError){child.onerror();return}
      const selected=new URL(location.href).searchParams.get('edition')||config.latest;
      const expected=config.versions[selected];
      const envelope={schema:'math-gauge.edition-page-data/v1',edition:selected,page:config.page,
       data:{schema:'SYNTHETIC edition data',benchmark_version:selected,marker:selected},
       supplemental:{'cost-reference-data':{marker:selected}}};
      if(options.envelope)options.envelope(envelope);
      if(!options.missingRegistration){
       context.window.MGEditionData(options.wrongKey?'f'.repeat(64):expected.key,envelope);
       if(options.duplicateRegistration)context.window.MGEditionData(expected.key,envelope);
      }
      assert.equal(controllers.length,0,'no controller may run before the payload script finishes');
      child.onload();
     }else{
      controllers.push({url:child.src,data:JSON.parse(elements.get('data').textContent),edition:context.window.MGEdition});
      if(options.controllerRuntimeError&&controllers.length===1){
       context.window.dispatchEvent({type:'error',filename:child.src});
      }else if(options.controllerError&&controllers.length===1)child.onerror();else child.onload();
     }
    });
   }
  }
 }
 const head=new Element('head'),body=new Element('body'),html=new Element('html');
 const configNode=new Element('script','edition-config');configNode.type='application/json';configNode.textContent=options.invalidJSON||JSON.stringify(config);elements.set(configNode.id,configNode);
 const data=new Element('script','data');data.type='application/json';data.textContent=JSON.stringify({benchmark_version:'1.1.0',marker:'embedded latest'});elements.set(data.id,data);
 const select=new Element('select'),version=new Element('span'),status=new Element('span'),content=new Element('main');
 const oldOnly=new Element('section'),newOnly=new Element('section');oldOnly.setAttribute('data-assessment-only','1.0.0');newOnly.setAttribute('data-assessment-only','1.1.0');
 if(options.supplementalCollision)elements.set('cost-reference-data',new Element('div','cost-reference-data'));
 const document={documentElement:html,head,body,baseURI:address,currentScript:options.currentScript?{src:options.currentScript}:null,
  getElementById:id=>elements.get(id)||null,createElement:tag=>new Element(tag),
  querySelectorAll:selector=>({'[data-edition-select]':[select],'[data-edition-version]':[version],
   '[data-edition-status]':[status],'[data-assessment-only]':[oldOnly,newOnly],'[data-edition-content]':[content]})[selector]||[]};
 const window={history,scrollX:options.scrollX||0,scrollY:options.scrollY||0,innerWidth:1440,innerHeight:900,
  sessionStorage:{getItem:key=>storage.get(key)??null,setItem:(key,value)=>{if(options.storageBlocked)throw new Error('Storage blocked');storage.set(key,value)},removeItem:key=>storage.delete(key)},
  scrollTo:position=>{scrolls.push(position);window.scrollX=position.left;window.scrollY=position.top},
  requestAnimationFrame:callback=>queueMicrotask(callback),
  addEventListener:(type,callback)=>{if(!events.has(type))events.set(type,[]);events.get(type).push(callback)},
  removeEventListener:(type,callback)=>events.set(type,(events.get(type)||[]).filter(handler=>handler!==callback)),
  dispatchEvent:event=>{for(const callback of events.get(event.type)||[])callback(event)}};
 context=vm.createContext({URL,URLSearchParams,location,document,window,
  CustomEvent:class{constructor(type,options={}){this.type=type;this.detail=options.detail}},
  setTimeout:callback=>{const id=++nextTimer;timers.set(id,callback);return id},clearTimeout:id=>timers.delete(id),
  fetch:()=>{fetches++;throw new Error('This loader must not fetch local JSON')}});
 vm.runInContext(source,context);
 return {config,context,location,document,window,elements,requests,controllers,html,select,version,status,content,oldOnly,newOnly,navigations,timers,storage,scrolls,history,
  get fetches(){return fetches},ready:window.MGEditionReady};
}

test('one selected edition is installed before controllers, in order, with supplemental JSON and version chrome',async()=>{
 const f=fixture();assert.equal(await f.ready,true);
 assert.equal(f.requests.length,3);assert.match(f.requests[0].src,/payload-old\.js$/);
 assert.deepEqual(f.controllers.map(row=>new URL(row.url).pathname.split('/').at(-1)),['core.fixture.js','case.fixture.js']);
 assert.ok(f.controllers.every(row=>row.data.marker==='1.0.0'&&row.edition.selected==='1.0.0'));
 assert.equal(JSON.parse(f.elements.get('cost-reference-data').textContent).marker,'1.0.0');
 assert.equal(f.elements.get('cost-reference-data').type,'application/json');
 assert.equal(f.version.textContent,'1.0.0');assert.equal(f.status.textContent,'Original assessment');
 assert.equal(f.select.value,'1.0.0');assert.equal(f.oldOnly.hidden,false);assert.equal(f.newOnly.hidden,true);
 assert.equal(f.html.getAttribute('data-edition-loading'),null);assert.equal(f.html.getAttribute('data-edition-ready'),'');
 assert.equal(f.timers.size,0);assert.equal(f.fetches,0);
 assert.equal(f.window.MGEditionData('0'.repeat(64),{}),false,'closed registration cannot replace live data');
});

test('absent edition selects latest and version navigation keeps unrelated query, language and hash',async()=>{
 const f=fixture({url:'https://example.test/nested/gauge/index.html?lang=zh&sort-written=strict&show-overall=mc&view-overall=table#category-leaderboards',page:'index.html'});
 assert.equal(await f.ready,true);assert.equal(f.window.MGEdition.selected,'1.1.0');
 assert.equal(f.select.children[0].textContent,'1.1.0');
 f.location.searchParams.set('lang','en');f.window.dispatchEvent({type:'mg:updated'});
 assert.equal(f.select.children[0].textContent,'1.1.0');assert.equal(f.status.textContent,'Local reassessment');
 f.select.value='1.0.0';f.select.listeners.get('change')();
 const next=new URL(f.navigations[0]);assert.equal(next.pathname,'/nested/gauge/index.html');
 assert.equal(next.searchParams.get('edition'),'1.0.0');assert.equal(next.searchParams.get('lang'),'en');
 assert.equal(next.searchParams.get('sort-written'),'strict');assert.equal(next.searchParams.get('show-overall'),'mc');
 assert.equal(next.searchParams.get('view-overall'),'table');assert.equal(next.hash,'#category-leaderboards');
});

test('file viewing loads the same inert register-script data without requiring fetch',async()=>{
 const f=fixture({url:'file:///Users/fixture/math-gauge/site/models/fixture/cases/MG-TX001.html?edition=1.0.0&lang=en'});
 assert.equal(await f.ready,true);assert.equal(f.fetches,0);
 assert.ok(f.requests.every(script=>script.src.startsWith('file:///Users/fixture/math-gauge/site/assets/')));
 assert.equal(f.controllers[0].data.benchmark_version,'1.0.0');
});

test('edition switching restores the reading position after controllers, despite an existing hash',async()=>{
 const first=fixture({page:'index.html',url:'https://example.test/nested/gauge/index.html?edition=1.1.0&lang=en#category-leaderboards',scrollX:4,scrollY:1863});
 assert.equal(await first.ready,true);assert.equal(first.scrolls.length,0,'ordinary navigation keeps its native anchor behavior');
 first.select.value='1.0.0';first.select.listeners.get('change')();
 const next=fixture({page:'index.html',url:first.navigations[0],storage:first.storage});
 assert.equal(await next.ready,true);
 assert.equal(next.scrolls.length,1);assert.equal(next.scrolls[0].top,1863);assert.equal(next.scrolls[0].left,4);
 assert.equal(next.scrolls[0].behavior,'instant');assert.equal(next.controllers.length,2);assert.equal(next.storage.size,0);
 const fresh=fixture({page:'index.html',url:first.navigations[0],storage:first.storage});
 assert.equal(await fresh.ready,true);assert.equal(fresh.scrolls.length,0,'a consumed snapshot cannot affect a later visit');
});

test('position restoration follows the same content anchor after layout height changes',async()=>{
 const url='https://example.test/nested/gauge/index.html?edition=1.0.0#leaderboard';
 const storage=new Map([['math-gauge:edition-scroll:https://example.test/nested/gauge/',JSON.stringify({to:url,at:Date.now(),x:0,y:1200,anchor:'category-panel',offset:-120})]]);
 const f=fixture({page:'index.html',url,storage});
 f.elements.set('category-panel',{getBoundingClientRect:()=>({top:1500,height:500})});
 assert.equal(await f.ready,true);assert.equal(f.scrolls[0].top,1620);
});

test('unrelated or expired positions do not override ordinary navigation',async()=>{
 const url='https://example.test/nested/gauge/index.html?edition=1.0.0#leaderboard';
 for(const changes of[{to:url+'-other'},{at:Date.now()-600000},{y:-1},{x:Infinity}]){
  const value={to:url,at:Date.now(),x:0,y:1200,anchor:null,offset:0,...changes};
  const storage=new Map([['math-gauge:edition-scroll:https://example.test/nested/gauge/',JSON.stringify(value)]]);
  const f=fixture({page:'index.html',url,storage});assert.equal(await f.ready,true);assert.equal(f.scrolls.length,0);
 }
});

test('blocked local-file storage can preserve the position through the current history entry',async()=>{
 const first=fixture({page:'index.html',url:'file:///Users/fixture/site/index.html?edition=1.1.0#leaderboard',storageBlocked:true,scrollY:1400});
 assert.equal(await first.ready,true);first.select.value='1.0.0';first.select.listeners.get('change')();
 assert.equal(new URL(first.navigations[0]).searchParams.get('edition'),'1.0.0');
 const next=fixture({page:'index.html',url:first.navigations[0],storageBlocked:true,historyState:first.history.state});
 assert.equal(await next.ready,true);assert.equal(next.scrolls[0].top,1400);assert.equal(next.history.state.mathGaugeEditionScroll,undefined);
});

for(const [name,options,code]of[
 ['wrong key',{wrongKey:true},'payload-identity'],
 ['wrong edition',{envelope:e=>e.edition='1.1.0'},'payload-identity'],
 ['wrong page',{envelope:e=>e.page='index.html'},'payload-identity'],
 ['wrong data identity',{envelope:e=>e.data.benchmark_version='1.1.0'},'payload-identity'],
 ['wrong schema',{envelope:e=>e.schema='another-schema'},'payload-identity'],
 ['missing registration',{missingRegistration:true},'payload-missing'],
 ['duplicate registration',{duplicateRegistration:true},'payload-duplicate'],
 ['unreadable payload',{payloadError:true},'payload-load'],
 ['supplemental target collision',{supplementalCollision:true},'invalid-supplemental']
])test(name+' fails explicitly without starting a controller or substituting latest',async()=>{
 const f=fixture(options);assert.equal(await f.ready,false);assert.equal(f.controllers.length,0);
 assert.equal(f.window.MGEdition,undefined);assert.equal(f.content.hidden,true);
 assert.equal(f.html.getAttribute('data-edition-error'),code);
 assert.equal(JSON.parse(f.elements.get('data').textContent).marker,'embedded latest','invalid data is not installed');
 const panel=f.elements.get('edition-load-error');assert.equal(panel.getAttribute('role'),'alert');
 const recovery=new URL(panel.children.at(-1).href);assert.equal(recovery.searchParams.get('edition'),'1.1.0');
 assert.equal(recovery.searchParams.get('score'),'strict');assert.equal(recovery.searchParams.get('cost-axis'),'time');
 assert.equal(recovery.searchParams.get('lang'),'en');assert.equal(recovery.hash,'#plot');
 assert.equal(f.navigations.length,0,'recovery needs an explicit user action');
});

test('unknown edition and malformed config do not request any edition or controller script',async()=>{
 for(const options of[{url:'https://example.test/nested/gauge/index.html?edition=9.9.9&lang=en',page:'index.html'},
  {invalidJSON:'{not JSON'}]){
  const f=fixture(options);assert.equal(await f.ready,false);assert.equal(f.requests.length,0);assert.equal(f.controllers.length,0);
  assert.ok(f.elements.get('edition-load-error'));
 }
});

test('all declared resource paths stay relative, same-origin and inside the site root',async()=>{
 for(const value of['https://outside.test/code.js','//outside.test/code.js','/assets/code.js',
  '../../../../outside.js','../../../%2e%2e/outside.js','../../../assets/%2foutside.js',
  '../../../assets\\outside.js','../../../assets/code.js?version=1','../../../assets/code.js#fragment']){
  const f=fixture({configure:config=>config.versions['1.1.0'].payload=value});
  assert.equal(await f.ready,false,value);assert.equal(f.requests.length,0,value);
  assert.equal(f.html.getAttribute('data-edition-error'),'unsafe-resource',value);
 }
 const f=fixture({configure:config=>config.scripts[0]='../../../../outside.js'});
 assert.equal(await f.ready,false);assert.equal(f.requests.length,0);
});

test('missing load events time out, close registration and cannot trigger a late edition change',async()=>{
 const f=fixture({payloadWait:true});assert.equal(f.requests.length,1);
 const expire=[...f.timers.values()][0];expire();assert.equal(await f.ready,false);
 assert.equal(f.html.getAttribute('data-edition-error'),'payload-load');
 assert.equal(f.window.MGEditionData('0'.repeat(64),{}),false);assert.equal(f.controllers.length,0);
});

test('a controller load failure stops the chain and keeps an explicit selected-edition error',async()=>{
 const f=fixture({controllerError:true});assert.equal(await f.ready,false);
 assert.equal(f.controllers.length,1);assert.equal(f.controllers[0].data.benchmark_version,'1.0.0');
 assert.equal(f.html.getAttribute('data-edition-error'),'controller-load');assert.equal(f.content.hidden,true);
});

test('a controller startup exception is terminal before the remaining controllers execute',async()=>{
 const f=fixture({controllerRuntimeError:true});assert.equal(await f.ready,false);
 assert.equal(f.controllers.length,1);assert.equal(f.html.getAttribute('data-edition-error'),'controller-load');
 assert.equal(f.content.hidden,true);assert.equal(f.timers.size,0);
});

test('the bootstrap cannot be placed in its own controller sequence',async()=>{
 const f=fixture({currentScript:'https://example.test/nested/gauge/assets/versioned/core.fixture.js'});
 assert.equal(await f.ready,false);assert.equal(f.requests.length,0);assert.equal(f.html.getAttribute('data-edition-error'),'invalid-config');
});

test('history changes across editions reload rather than displaying data under a different URL identity',async()=>{
 const f=fixture();assert.equal(await f.ready,true);
 f.location.searchParams.set('edition','1.1.0');f.window.dispatchEvent({type:'popstate'});
 assert.equal(f.navigations.length,1);assert.equal(new URL(f.navigations[0]).searchParams.get('edition'),'1.1.0');
 assert.equal(f.window.MGEdition.selected,'1.0.0','live payload identity is not silently reassigned');
});


test('new models have no fabricated historical page or score controllers',async()=>{
 const f=fixture({envelope:envelope=>{envelope.data={benchmark_version:'1.0.0',edition_unavailable:true,model_id:'new-model'};envelope.supplemental={}}});
 assert.equal(await f.ready,true);assert.equal(f.content.hidden,true);
 assert.equal(f.controllers.length,0);assert.equal(f.html.getAttribute('data-edition-ready'),'');
 const panel=f.document.body.children.find(node=>node.tagName==='SECTION');
 assert.match(panel.children[0].textContent,/not evaluated/);
 assert.equal(new URL(panel.children[1].href).searchParams.get('edition'),'1.1.0');
 assert.equal(JSON.parse(f.elements.get('data').textContent).metrics,undefined);
});
