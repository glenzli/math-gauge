/* Load one allowlisted edition before any shared display controller executes. */
(() => {
 'use strict';
 const CONFIG_SCHEMA='math-gauge.edition-view-config/v1',DATA_SCHEMA='math-gauge.edition-page-data/v1';
 const versionPattern=/^\d+\.\d+\.\d+$/,hashPattern=/^[a-f0-9]{64}$/;
 const own=(value,key)=>Object.prototype.hasOwnProperty.call(value,key);
 const object=value=>value!==null&&typeof value==='object'&&!Array.isArray(value);
 const keys=(value,expected)=>object(value)&&Object.keys(value).length===expected.length&&expected.every(key=>own(value,key));
 const html=document.documentElement;
 const loaderAddress=document.currentScript?.src?new URL(document.currentScript.src,location.href).href:null;
 let config=null,selected=null,siteRoot=null,pageAddress=null,lastChromeLanguage=null;
 const language=()=>new URL(location.href).searchParams.get('lang')==='en'?'en':'zh';
 const fail=(code)=>{const error=new Error(code);error.code=code;return error};
 const require=(condition,code)=>{if(!condition)throw fail(code)};
 const jsonNode=id=>{const element=document.getElementById(id);require(element&&element.tagName==='SCRIPT'&&element.type==='application/json','invalid-config');return element};
 const messages={
  title:{zh:'所选版本未能加载',en:'The selected edition could not be loaded'},
  explanation:{zh:'未显示其他版本的数据。请重试，或选择最新版本。',en:'No other edition has been substituted. Retry or choose the latest edition.'},
  latest:{zh:'查看最新版本',en:'Open the latest edition'},
  unavailable:{zh:'所选版本不可用',en:'Selected edition unavailable'},
  'invalid-config':{zh:'页面的版本配置不完整。',en:'This page has an incomplete edition configuration.'},
  'unknown-edition':{zh:'这个版本不在本页提供的版本中。',en:'This edition is not available on this page.'},
  'unsafe-resource':{zh:'版本资源的路径不符合本地站点边界。',en:'An edition resource is outside the local site boundary.'},
  'payload-identity':{zh:'版本数据的登记与当前页面不一致。',en:'The registered edition data does not match this page.'},
  'payload-missing':{zh:'文件已加载，但没有收到所选版本的数据。',en:'The file loaded without registering the selected edition data.'},
  'payload-duplicate':{zh:'版本文件重复登记了数据。',en:'The edition file registered data more than once.'},
  'payload-load':{zh:'未能读取所选版本的数据文件。',en:'The selected edition data file could not be read.'},
  'controller-load':{zh:'版本数据已确认，但界面程序未能完整加载。',en:'The edition data was confirmed, but the interface could not finish loading.'},
  'invalid-supplemental':{zh:'补充图表数据的目标或格式不正确。',en:'Supplemental chart data has an invalid destination or format.'}
 };
 const text=(key,lang=language())=>(messages[key]||messages['invalid-config'])[lang];
 function readConfig(){
  let parsed;try{parsed=JSON.parse(jsonNode('edition-config').textContent)}catch{throw fail('invalid-config')}
  require(keys(parsed,['schema','latest','page','versions','scripts'])&&parsed.schema===CONFIG_SCHEMA&&
   versionPattern.test(parsed.latest)&&object(parsed.versions)&&own(parsed.versions,parsed.latest)&&
   typeof parsed.page==='string'&&/^[A-Za-z0-9][A-Za-z0-9._/-]*\.html$/.test(parsed.page)&&
   parsed.page.split('/').every(part=>part&&part!=='.'&&part!=='..')&&Array.isArray(parsed.scripts),'invalid-config');
  config=parsed;
  pageAddress=new URL(location.href);
  require(['http:','https:','file:'].includes(pageAddress.protocol),'unsafe-resource');
  siteRoot=new URL('../'.repeat(parsed.page.split('/').length-1)||'./',pageAddress);
  const expectedPage=new URL(parsed.page,siteRoot);
  const pathname=pageAddress.pathname.endsWith('/')?pageAddress.pathname+'index.html':pageAddress.pathname;
  require(expectedPage.pathname===pathname,'invalid-config');
  for(const [version,value]of Object.entries(parsed.versions)){
   require(versionPattern.test(version)&&keys(value,['key','payload','label','status'])&&hashPattern.test(value.key)&&
    object(value.label)&&object(value.status)&&['zh','en'].every(lang=>
     typeof value.label[lang]==='string'&&value.label[lang].length>0&&typeof value.status[lang]==='string'),'invalid-config');
   resource(value.payload);
  }
  const scripts=parsed.scripts.map(resource);
  require(new Set(scripts.map(url=>url.href)).size===scripts.length&&
   !scripts.some(url=>url.href===loaderAddress),'invalid-config');
  return scripts;
 }
 function resource(value){
  require(typeof value==='string'&&value.length>0&&!/^(?:[a-z][a-z0-9+.-]*:|\/)/i.test(value)&&
   !/[\\\u0000-\u0020\u007f]/.test(value)&&!/%(?:2f|5c|00)/i.test(value),'unsafe-resource');
  let url;try{url=new URL(value,pageAddress)}catch{throw fail('unsafe-resource')}
  require(url.protocol===siteRoot.protocol&&url.origin===siteRoot.origin&&url.host===siteRoot.host&&
   url.pathname.startsWith(siteRoot.pathname)&&url.pathname.endsWith('.js')&&!url.search&&!url.hash&&
   !url.username&&!url.password,'unsafe-resource');
  return url;
 }
 const scrollStateKey='mathGaugeEditionScroll';
 const scrollStorageKey=()=> 'math-gauge:edition-scroll:'+siteRoot.href;
 function switchEdition(next){
  const point=document.elementFromPoint?.(window.innerWidth/2,Math.min(100,window.innerHeight/4));
  const anchor=point?.closest('main [id]'),rect=anchor?.getBoundingClientRect();
  const snapshot={to:next.href,at:Date.now(),x:window.scrollX||0,y:window.scrollY||0,
   anchor:anchor?.id||null,offset:rect?.top||0};
  try{window.sessionStorage.setItem(scrollStorageKey(),JSON.stringify(snapshot))}
  catch{
   // Preserve the same behavior when a local-file browser blocks storage.
   if(window.history?.replaceState&&typeof location.reload==='function'){
    window.history.replaceState({...window.history.state,[scrollStateKey]:snapshot},'',next.href);
    location.reload();return;
   }
  }
  location.assign(next.href);
 }
 function takeScrollPosition(){
  let snapshot=null;
  try{
   const raw=window.sessionStorage.getItem(scrollStorageKey());
   window.sessionStorage.removeItem(scrollStorageKey());
   if(raw)snapshot=JSON.parse(raw);
  }catch{}
  const retained=window.history?.state?.[scrollStateKey];
  if(retained){
   const state={...window.history.state};delete state[scrollStateKey];
   window.history.replaceState(state,'');
   if(!snapshot)snapshot=retained;
  }
  if(!object(snapshot)||snapshot.to!==pageAddress.href||!Number.isFinite(snapshot.at)||
   Date.now()-snapshot.at<0||Date.now()-snapshot.at>300000||
   ![snapshot.x,snapshot.y,snapshot.offset].every(Number.isFinite)||snapshot.x<0||snapshot.y<0||
   snapshot.anchor!==null&&(typeof snapshot.anchor!=='string'||snapshot.anchor.length>256))return null;
  return snapshot;
 }
 async function restoreScrollPosition(snapshot){
  if(!snapshot)return;
  try{await document.fonts?.ready}catch{}
  const frame=()=>new Promise(resolve=>window.requestAnimationFrame?window.requestAnimationFrame(resolve):resolve());
  await frame();await frame();
  const anchor=snapshot.anchor&&document.getElementById(snapshot.anchor),rect=anchor?.getBoundingClientRect();
  const top=rect?.height>0?(window.scrollY||0)+rect.top-snapshot.offset:snapshot.y;
  window.scrollTo({left:snapshot.x,top:Math.max(0,top),behavior:'instant'});
  await frame();
 }
 function chrome(){
  if(!config||!selected)return;
  const lang=language(),entry=config.versions[selected];
  document.querySelectorAll('[data-edition-version]').forEach(node=>node.textContent=selected);
  document.querySelectorAll('[data-edition-status]').forEach(node=>node.textContent=entry?entry.status[lang]:'');
  document.querySelectorAll('[data-assessment-only]').forEach(node=>node.hidden=node.getAttribute('data-assessment-only')!==selected);
  if(lastChromeLanguage===lang)return;
  lastChromeLanguage=lang;
  const versions=[config.latest,...Object.keys(config.versions).filter(version=>version!==config.latest)];
  document.querySelectorAll('[data-edition-select]').forEach(select=>{
   const options=versions.map(version=>{const option=document.createElement('option');option.value=version;option.textContent=config.versions[version].label[lang];return option});
   if(!entry){const option=document.createElement('option');option.value='';option.textContent=text('unavailable',lang);option.disabled=true;options.unshift(option)}
   select.replaceChildren(...options);select.value=entry?selected:'';
   if(select.dataset.editionBound)return;
   select.dataset.editionBound='true';
   select.addEventListener('change',()=>{
    if(!own(config.versions,select.value))return;
    const next=new URL(location.href);next.searchParams.set('edition',select.value);switchEdition(next);
   });
  });
 }
 function script(url,code){
  return new Promise((resolve,reject)=>{
   const element=document.createElement('script');element.async=false;element.src=url.href;
   let finished=false;
   const runtime=event=>{if(event.filename&&new URL(event.filename,pageAddress).href===url.href)finish(fail(code))};
   const finish=error=>{if(finished)return;finished=true;clearTimeout(timer);window.removeEventListener('error',runtime);element.onload=null;element.onerror=null;if(error){element.remove();reject(error)}else resolve()};
   const timer=setTimeout(()=>finish(fail(code)),30000);
   window.addEventListener('error',runtime);
   element.onload=()=>finish(null);element.onerror=()=>finish(fail(code));
   (document.head||document.body).append(element);
  });
 }
 async function payload(url,expected){
  let pending=null,registrationError=null,closed=false,calls=0;
  window.MGEditionData=(key,envelope)=>{
   if(closed)return false;
   calls++;
   try{
    require(calls===1,'payload-duplicate');
    require(key===expected.key&&keys(envelope,['schema','edition','page','data','supplemental'])&&
     envelope.schema===DATA_SCHEMA&&envelope.edition===selected&&envelope.page===config.page&&
     object(envelope.data)&&envelope.data.benchmark_version===selected&&object(envelope.supplemental),'payload-identity');
    pending=envelope;
   }catch(error){registrationError=error}
   return registrationError===null;
  };
  try{
   await script(url,'payload-load');
   if(registrationError)throw registrationError;
   require(pending!==null,'payload-missing');
   return pending;
  }finally{closed=true;window.MGEditionData=()=>false}
 }
 function install(envelope){
  const primary=jsonNode('data'),supplemental=[];
  for(const [id,value]of Object.entries(envelope.supplemental)){
   require(/^[a-z][a-z0-9-]*-data$/.test(id),'invalid-supplemental');
   const existing=document.getElementById(id);
   require(!existing||existing.tagName==='SCRIPT'&&existing.type==='application/json','invalid-supplemental');
   let serialized;try{serialized=JSON.stringify(value)}catch{throw fail('invalid-supplemental')}
   require(serialized!==undefined,'invalid-supplemental');
   supplemental.push({id,existing,serialized});
  }
  const data=JSON.stringify(envelope.data);
  primary.textContent=data;
  for(const item of supplemental){
   const target=item.existing||document.createElement('script');
   if(!item.existing){target.id=item.id;target.type='application/json';(document.head||document.body).append(target)}
   target.textContent=item.serialized;
  }
 }
 function errorPanel(error){
  const code=messages[error.code]?error.code:'invalid-config';
  html.setAttribute('data-edition-error',code);html.removeAttribute('data-edition-loading');
  document.querySelectorAll('[data-edition-content]').forEach(node=>node.hidden=true);
  const panel=document.createElement('section');panel.id='edition-load-error';panel.className='panel edition-error';panel.setAttribute('role','alert');panel.dataset.editionErrorCode=code;
  const title=document.createElement('h2');title.textContent=text('title');
  const reason=document.createElement('p');reason.textContent=text(code);
  const explanation=document.createElement('p');explanation.textContent=text('explanation');
  const link=document.createElement('a'),next=new URL(location.href);
  if(config&&own(config.versions,config.latest))next.searchParams.set('edition',config.latest);else next.searchParams.delete('edition');
  link.href=next.href;link.textContent=text('latest');link.setAttribute('data-edition-recovery','');
  panel.append(title,reason,explanation,link);document.body.append(panel);
 }
 async function start(){
  html.setAttribute('data-edition-loading','');
  try{
   const controllers=readConfig();
   selected=new URL(location.href).searchParams.get('edition')||config.latest;
   chrome();require(own(config.versions,selected),'unknown-edition');
   const scrollPosition=takeScrollPosition();
   const entry=config.versions[selected],url=resource(entry.payload);
   require(!controllers.some(controller=>controller.href===url.href),'invalid-config');
   const envelope=await payload(url,entry);install(envelope);
   if(envelope.data.edition_unavailable===true){
    document.querySelectorAll('[data-edition-content]').forEach(node=>node.hidden=true);
    const panel=document.createElement('section');panel.className='panel';
    const p=document.createElement('p');p.textContent=language()==='en'?'This model was not evaluated in this edition.':'此模型未在本版本评测。';
    const link=document.createElement('a'),next=new URL(location.href);next.searchParams.set('edition',config.latest);
    link.href=next.href;link.textContent=language()==='en'?'Return to '+config.latest:'返回 '+config.latest;
    panel.append(p,link);document.body.append(panel);html.removeAttribute('data-edition-loading');html.setAttribute('data-edition-ready','');return true;
   }
   window.MGEdition=Object.freeze({selected,latest:config.latest,page:config.page});
   window.addEventListener('mg:updated',chrome);
   window.addEventListener('popstate',()=>{
    const requested=new URL(location.href).searchParams.get('edition')||config.latest;
    if(requested!==selected){location.assign(location.href);return}chrome();
   });
   chrome();for(const controller of controllers)await script(controller,'controller-load');
   await restoreScrollPosition(scrollPosition);
   html.removeAttribute('data-edition-loading');html.removeAttribute('data-edition-error');html.setAttribute('data-edition-ready','');
   window.dispatchEvent(new CustomEvent('mg:edition-ready',{detail:window.MGEdition}));
   return true;
  }catch(error){errorPanel(error);return false}
 }
 window.MGEditionReady=start();
})();
