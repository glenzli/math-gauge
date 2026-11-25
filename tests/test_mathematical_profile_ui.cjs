/* Supplied-axis presentation tests; no model evaluation or score arithmetic. */
const assert=require('node:assert/strict');
const {test}=require('node:test');
const ui=require('../scripts/templates/mathematical-profile.js');

const ids=['astra-6-max','sol-6.2-max','astra-6-xhigh','sol-6.1-max','sol-6.1-xhigh',
 'terra-6.1-max','terra-6.1-xhigh','dot-underlying-model-20261108','claude-opus-5.5-max',
 'claude-sonnet-5.5-max','gemini-4-carbon-medium','gemini-4-hydrogen-xhigh','gemini-4-carbon-high',
 'gemini-4-argon','gemini-3.8-flash-high','kimi-3.1-pro-max','deepseek-v4.1-flash-1017','glm-5.3-max'];
const compare=(a,b)=>b.rmc-a.rmc||a.id.localeCompare(b.id);
function dataFixture(version='0.4.0'){
 const models=ids.map((id,index)=>({id,label:'Model '+id,rmc:100-index,
  logo:{label:id.startsWith('claude-')?'Anthropic':id.startsWith('gemini-')?'Google':id.startsWith('kimi-')?'Kimi':id.startsWith('deepseek-')?'DeepSeek':id.startsWith('glm-')?'Z.ai':'OpenAI',data_url:'assets/'+id+'.svg'}}));
 const axes=ui.AXES.map(id=>({id,label:{zh:'中'+id,en:'English '+id},description:{zh:'说明 '+id,en:'Description '+id}}));

 const profile={schema:'math-gauge.mathematical-profile/v1',version,benchmark_version:'1.1.0',
  axes,models:models.map((model,index)=>({id:model.id,metrics:Object.fromEntries(axes.map((axis,i)=>[axis.id,
   {exact:80-index-i,confirmed:80-index-i,lower:80-index-i,upper:80-index-i,coverage:{unit:axis.id==='completion'?'benchmark_subcategory':'mathematical_family',planned:axis.id==='completion'?8:35,reviewed:axis.id==='completion'?8:35}}]))})),reviewer_kind:'ai',human_review:'pending'};
 return {benchmark_version:'1.1.0',models,mathematical_profile:profile};
}
function nodesBelow(node){return [node,...node.children.flatMap(nodesBelow)]}
function fixture(data=dataFixture(),query='?edition=1.1.0&lang=zh&score=capability&sort-research=strict#mathematical-profile'){
 const documentNodes=new Map(),events=new Map(),comparisons=[],changes=[];
 class Element{
  constructor(tag){this.tagName=tag;this.children=[];this.attrs=new Map();this.style={setProperty(){}};this.dataset={};this.listeners=new Map();this.hidden=false;this.checked=false;this.textContent='';}
  append(...children){for(const child of children){child.remove();this.children.push(child);child.parentElement=this}}
  replaceChildren(...children){for(const child of this.children)child.parentElement=null;this.children=[];this.append(...children)}
  closest(selector){
   for(let node=this;node;node=node.parentElement){
    if(selector.startsWith('.')?node.className===selector.slice(1):node.tagName===selector)return node;
   }
   return null;
  }
  remove(){if(this.parentElement){const siblings=this.parentElement.children;siblings.splice(siblings.indexOf(this),1);this.parentElement=null}}
  before(node){node.remove();const siblings=this.parentElement.children;siblings.splice(siblings.indexOf(this),0,node);node.parentElement=this.parentElement}
  after(node){node.remove();const siblings=this.parentElement.children;siblings.splice(siblings.indexOf(this)+1,0,node);node.parentElement=this.parentElement}
  setAttribute(key,value){this.attrs.set(key,String(value))}
  getAttribute(key){return this.attrs.get(key)??null}
  removeAttribute(key){this.attrs.delete(key)}
  addEventListener(key,callback){if(!this.listeners.has(key))this.listeners.set(key,[]);this.listeners.get(key).push(callback)}
  fire(key){for(const callback of this.listeners.get(key)||[])callback({target:this})}
 }
 for(const name of ['', '-title','-description','-review','-continuation-control','-continuation','-continuation-label',
  '-controls','-count','-picker','-picker-title','-choices',
  '-chart','-note','-legend','-focus-note','-empty','-values-title','-coverage-note','-values',
  '-meanings','-meanings-title','-meanings-scope','-meanings-list']){
  const element=new Element('div');element.id='mathematical-profile'+name;documentNodes.set(element.id,element);
 }
 const section=documentNodes.get('mathematical-profile');section.setAttribute('data-assessment-only','1.1.0');
 const find=name=>documentNodes.get('mathematical-profile-'+name),radar=new Element('div'),values=new Element('details');
 const toolbar=new Element('div');toolbar.className='mp-toolbar';
 find('continuation-control').append(find('continuation'),find('continuation-label'));
 find('picker').append(find('picker-title'),find('count'));
 toolbar.append(find('continuation-control'),find('controls'),find('picker'));
 radar.className='mp-layout';radar.append(find('chart'),find('legend'));values.append(find('values-title'),find('coverage-note'),find('values'));
 section.append(toolbar,find('choices'),radar,find('empty'),values);
 const profileNav=new Element('a');profileNav.setAttribute('data-assessment-only','1.2.0');
 profileNav.hidden=data.benchmark_version!=='1.2.0';
 documentNodes.get('mathematical-profile-choices').hidden=true;
 documentNodes.get('mathematical-profile-picker').setAttribute('aria-expanded','false');
 const location=new URL('https://example.test/math-gauge/index.html'+query);
 const win={location,document:{getElementById:id=>documentNodes.get(id)||null,createElement:tag=>new Element(tag),createElementNS:(_,tag)=>new Element(tag),
  querySelector:selector=>selector==='a[data-assessment-only="1.2.0"][href="#mathematical-profile"]'?profileNav:null},
  MG:{d:data,state:{score:'capability'},compareScores:(a,b,mode)=>{comparisons.push(mode);return compare(a,b)}},
  history:{replaceState:(_,__,url)=>{changes.push(url);location.href=url}},
  addEventListener:(key,callback)=>{if(!events.has(key))events.set(key,[]);events.get(key).push(callback)},
  fire:key=>{for(const callback of events.get(key)||[])callback({type:key})}};
 const controller=ui.mount(win);
 const el=name=>documentNodes.get('mathematical-profile'+(name?'-'+name:''));
 return {win,controller,el,profileNav,changes,comparisons,series:()=>nodesBelow(el('chart')).filter(node=>node.getAttribute('class')==='mp-series')};
}

test('default representatives choose the SMC winner per brand, limited to the top five brands',()=>{
 const data=dataFixture(),expected=['astra-6-max','claude-opus-5.5-max','gemini-4-carbon-medium','kimi-3.1-pro-max','deepseek-v4.1-flash-1017'];
 assert.deepEqual(ui.representatives(data.models,compare),expected);
 assert.deepEqual(ui.representatives([...data.models].reverse(),compare),expected);
 const f=fixture(data);assert.deepEqual(f.controller.selected(),expected);assert.ok(f.comparisons.every(mode=>mode==='strict'));
 f.win.MG.state.score='strict';f.win.fire('mg:updated');assert.deepEqual(f.controller.selected(),expected,'independent axes do not follow the main score selector');
});

test('same-brand dash/marker styles are unique for retained configurations and independent of selection order',()=>{
 const data=dataFixture(),openai=data.models.filter(model=>ui.brand(model).key==='openai');
 const signatures=openai.map(model=>{const style=ui.styleFor(model);return style.dash+'|'+style.marker});
 assert.equal(new Set(signatures).size,openai.length);
 const original=new Map(data.models.map(model=>[model.id,ui.styleFor(model)]));
 for(const model of [...data.models].reverse())assert.deepEqual(ui.styleFor(model),original.get(model.id));
 assert.equal(ui.brand(data.models.find(model=>model.id.startsWith('glm-'))).key,'glm');
 assert.equal(ui.brand(data.models.find(model=>model.id.startsWith('deepseek-'))).key,'deepseek');
 const f=fixture(data),first=f.series()[0],style=[first.getAttribute('data-profile-dash'),first.getAttribute('data-profile-marker')];
 f.controller.setSelection(['sol-6.2-max','astra-6-max']);
 const same=f.series().find(node=>node.getAttribute('data-profile-model')==='astra-6-max');
 assert.deepEqual([same.getAttribute('data-profile-dash'),same.getAttribute('data-profile-marker')],style);
});

test('unknown evidence is a gap or interval rather than an invented zero vertex',()=>{
 const data=dataFixture(),axes=data.mathematical_profile.axes,metrics=data.mathematical_profile.models[0].metrics;
 metrics.proof={exact:0,confirmed:0,lower:0,upper:0,coverage:{unit:'mathematical_family',reviewed:35,planned:35}};
 metrics.completion={exact:null,confirmed:0,lower:0,upper:100,coverage:{unit:'benchmark_subcategory',reviewed:0,planned:8}};
 metrics.depth={exact:null,confirmed:35,lower:20,upper:80,coverage:{unit:'mathematical_family',reviewed:6,planned:35}};
 const shape=ui.geometry(axes,metrics);assert.equal(shape.complete,false);assert.equal(shape.vertices[2],null);assert.equal(shape.vertices[5],null);
 assert.equal(shape.vertices[0].value,0,'an actual reviewed zero remains an actual zero');
 assert.deepEqual(shape.intervals.map(interval=>[interval.axis,interval.lower,interval.upper]),[['depth',20,80]]);
 const f=fixture(data,'?edition=1.1.0&profile-models=astra-6-max');
 const points=nodesBelow(f.series()[0]).filter(node=>node.getAttribute('data-profile-point'));
 assert.equal(points.length,5);assert.ok(!points.some(node=>node.getAttribute('data-profile-point')==='completion'));
 assert.ok(points.some(node=>node.getAttribute('data-profile-point')==='proof'&&node.getAttribute('data-value')==='0'));
 const line=nodesBelow(f.series()[0]).find(node=>node.getAttribute('class')==='mp-model-line');
 assert.equal(line.getAttribute('fill'),'none');assert.ok(!line.getAttribute('d').endsWith('Z'));
 const table=f.el('values'),row=table.children[2].children[0];
 assert.equal(row.children[3].className,'mp-uncertain');assert.equal(row.children[3].children[0].textContent,'0.0–100.0');
 assert.equal(row.children[6].children[2].textContent,'6/35 家族已结算');
});

test('explicit empty or unknown URL selection does not silently select default models',()=>{
 const data=dataFixture();assert.deepEqual(ui.readSelection('?profile-models=',data.models,compare),[]);
 assert.deepEqual(ui.readSelection('?profile-models=unknown-model',data.models,compare),[]);
 assert.deepEqual(ui.readSelection('?profile-models=sol-6.2-max,astra-6-max,sol-6.2-max',data.models,compare),['astra-6-max','sol-6.2-max']);
 const f=fixture(data,'?edition=1.1.0&profile-models=');assert.deepEqual(f.controller.selected(),[]);assert.equal(f.series().length,0);assert.equal(f.el('empty').hidden,false);
});

test('presets and all-model multiselect preserve URL context and retain checkbox focus targets',()=>{
 const f=fixture(),picker=f.el('picker');
 assert.equal(f.el('continuation-control').hidden,true);
 assert.equal(f.el('choices').hidden,true);
 picker.fire('click');
 assert.equal(f.el('choices').hidden,false);
 assert.equal(picker.getAttribute('aria-expanded'),'true');
 const originalCheckboxes=nodesBelow(f.el('choices')).filter(node=>node.type==='checkbox');
 assert.equal(originalCheckboxes.length,18);
 const presets=f.el('controls').children;
 presets.find(button=>button.dataset.profilePreset==='leader').fire('click');assert.deepEqual(f.controller.selected(),['astra-6-max']);
 presets.find(button=>button.dataset.profilePreset==='clear').fire('click');assert.deepEqual(f.controller.selected(),[]);
 for(const checkbox of originalCheckboxes){checkbox.checked=true;checkbox.fire('change')}
 assert.equal(f.controller.selected().length,18);assert.equal(f.series().length,18);
 assert.ok(originalCheckboxes.every(checkbox=>nodesBelow(f.el('choices')).includes(checkbox)));
 const url=new URL(f.win.location.href);assert.equal(url.searchParams.get('edition'),'1.1.0');assert.equal(url.searchParams.get('score'),'capability');
 assert.equal(url.searchParams.get('sort-research'),'strict');assert.equal(url.searchParams.get('lang'),'zh');assert.equal(url.hash,'#mathematical-profile');
 presets.find(button=>button.dataset.profilePreset==='brands').fire('click');assert.equal(f.controller.selected().length,5);
 picker.fire('click');
 assert.equal(f.el('choices').hidden,true);
 assert.equal(picker.getAttribute('aria-expanded'),'false');
});

test('keyboard focus and pinning emphasize one model and fade the other curves',()=>{
 const f=fixture(),button=f.el('legend').children[0],firstId=f.controller.selected()[0];
 button.fire('focus');assert.equal(f.series().find(node=>node.getAttribute('data-profile-model')===firstId).getAttribute('data-focused'),'true');
 assert.ok(f.series().filter(node=>node.getAttribute('data-profile-model')!==firstId).every(node=>node.getAttribute('data-muted')==='true'));
 button.fire('click');button.fire('blur');assert.equal(button.getAttribute('aria-pressed'),'true');
 const other=f.controller.selected().slice(1);f.controller.setSelection(other);assert.ok(f.series().every(node=>node.getAttribute('data-muted')==='false'),'removed focus cannot leave all remaining curves faded');
});

test('language and history events update labels, coverage and selections while preserving supplied model names',()=>{
 const f=fixture();const names=f.el('legend').children.map(button=>button.children.at(-1).children[0].textContent);
 f.win.location.searchParams.set('lang','en');f.win.fire('mg:updated');
 assert.equal(f.el('title').textContent,'Mathematical profile');
 assert.deepEqual(f.el('legend').children.map(button=>button.children.at(-1).children[0].textContent),names);
 const row=f.el('values').children[2].children[0];assert.equal(row.children[1].children[1].textContent,'35/35 families settled');
 f.win.location.searchParams.set('profile-models','glm-5.3-max');f.win.fire('popstate');assert.deepEqual(f.controller.selected(),['glm-5.3-max']);
});

test('edition 1.0 and missing profiles hide the entire region without a generic edition toggle reviving it',()=>{
 const old=dataFixture();old.benchmark_version='1.0.0';const first=fixture(old);assert.equal(first.controller,null);assert.equal(first.el('').hidden,true);
 assert.equal(first.el('').getAttribute('data-assessment-only'),null);
 const missing=dataFixture();delete missing.mathematical_profile;const second=fixture(missing);assert.equal(second.controller,null);assert.equal(second.el('').hidden,true);
 const invalid=dataFixture();invalid.mathematical_profile.axes.pop();assert.equal(ui.prepare(invalid,compare),null);
});


test('Sol xHigh has a ninth explicit same-brand identity while all retained styles stay stable',()=>{
 const legacy=['astra-6-max','astra-6-xhigh','sol-6.2-max','sol-6.1-max','sol-6.1-xhigh',
  'terra-6.1-max','terra-6.1-xhigh','dot-underlying-model-20261108'];
 const old=legacy.map(id=>ui.styleFor({id})),fresh=ui.styleFor({id:'sol-6.2-xhigh'});
 assert.deepEqual(old.map(style=>style.index),[0,1,2,3,4,5,6,7]);
 assert.equal(fresh.index,8);assert.equal(fresh.marker,'pentagon');
 assert.ok(old.every(style=>style.color===fresh.color));
 assert.equal(new Set([...old,fresh].map(style=>style.dash+'|'+style.marker)).size,9);
 const data=dataFixture(),model={...data.models[0],id:'sol-6.2-xhigh',label:'Sol 6.2 (xhigh)'};
 data.models.push(model);data.mathematical_profile.models.push({...data.mathematical_profile.models[0],id:model.id});
 const f=fixture(data,'?edition=1.1.0&profile-models=sol-6.2-xhigh');
 const series=f.series().find(node=>node.getAttribute('data-profile-model')===model.id);
 assert.ok(series);assert.equal(series.getAttribute('data-profile-marker'),'pentagon');
 assert.equal(nodesBelow(series).filter(node=>node.tagName==='polygon'&&node.getAttribute('class')==='mp-marker').length,7);
});

test('current profile settles known zero deliveries and shows true missing evidence without a zero-of-seven legend',()=>{
 const data=dataFixture(),profiles=data.mathematical_profile.models;
 profiles[0].metrics.proof={exact:0,confirmed:0,lower:0,upper:0,coverage:{unit:'mathematical_family',reviewed:35,planned:35}};
 const glm=profiles.find(model=>model.id==='glm-5.3-max');
 for(const [axis,metric]of Object.entries(glm.metrics)){Object.assign(metric,{exact:null,confirmed:50,lower:50,upper:50+100/70});metric.coverage.reviewed=axis==='completion'?7:34}
 const f=fixture(data,'?edition=1.1.0&profile-models=astra-6-max,glm-5.3-max');
 const labels=f.el('legend').children.map(button=>button.children.at(-1).children[1].textContent);
 assert.deepEqual(labels,['35/35 家族已结算','34/35 家族已结算']);
 const rows=f.el('values').children[2].children;
 assert.equal(rows[0].children[1].children[0].textContent,'0.0');
 assert.equal(rows[0].children[1].children[1].textContent,'35/35 家族已结算');
 assert.equal(rows[1].children[1].className,'mp-uncertain');
 assert.equal(rows[1].children[1].children[2].textContent,'34/35 家族已结算');
 assert.ok(f.el('description').textContent.includes('主榜SMC'));
 assert.ok(f.el('note').textContent.includes('截止前内容按实际论证评估'));
 assert.ok(f.el('note').textContent.includes('真正未知'));
 f.win.location.searchParams.set('lang','en');f.win.fire('mg:updated');
 assert.equal(f.el('legend').children[1].children.at(-1).children[1].textContent,'34/35 families settled');
});

test('current meanings use supplied bilingual axes and preserve the native disclosure on language changes',()=>{
 const data=dataFixture(),axes=data.mathematical_profile.axes;
 axes.find(axis=>axis.id==='depth').label={zh:'数学深度',en:'Mathematical depth'};
 axes.find(axis=>axis.id==='closure').label={zh:'成果闭合度',en:'Result closure'};
 const f=fixture(data),list=f.el('meanings-list');
 assert.equal(f.el('meanings').hidden,false);assert.equal(list.children.length,7);
 assert.deepEqual(list.children.map(item=>item.children[0].textContent),axes.map(axis=>axis.label.zh));
 assert.deepEqual(list.children.map(item=>item.children[1].textContent),axes.map(axis=>axis.description.zh));
 assert.ok(f.el('meanings-scope').textContent.includes('39道初答与3轮自查'));
 assert.ok(f.el('meanings-scope').textContent.includes('不限六道命题拓展题'));
 assert.equal(list.children[2].children[1].children[0].textContent,'沿用主榜SMC的全部严格完成门槛，不另算家族平均完成率。');
 f.el('meanings').open=true;f.win.location.searchParams.set('lang','en');f.win.fire('mg:updated');
 assert.equal(f.el('meanings').open,true);
 assert.deepEqual(list.children.map(item=>item.children[0].textContent),axes.map(axis=>axis.label.en));
 assert.ok(list.children[6].children[1].children[0].textContent.includes('substantive results actually delivered'));
 assert.ok(f.el('meanings-scope').textContent.includes('39 initial answers and 3 rounds'));
});

test('six-axis legend reports a settled-family range when supplied axis coverage differs',()=>{
 const data=dataFixture(),metrics=data.mathematical_profile.models[0].metrics;
 metrics.proof.coverage.reviewed=33;metrics.completion.coverage.reviewed=7;
 const f=fixture(data,'?edition=1.1.0&profile-models=astra-6-max');
 assert.equal(f.el('legend').children[0].children.at(-1).children[1].textContent,'33–35/35 家族已结算');
 const rows=f.el('values').children[2].children;
 assert.equal(rows[0].children[1].children[1].textContent,'33/35 家族已结算');
 assert.equal(rows[0].children[3].children[1].textContent,'主榜SMC · 7/8');
});

test('only the current profile is accepted and SMC coverage stays separate from family coverage',()=>{
 const f=fixture();assert.ok(f.el('description').textContent.includes('主榜SMC'));
 assert.equal(f.el('legend').children[0].children.at(-1).children[1].textContent,'35/35 家族已结算');
 for(const version of ['0.1.0','0.2.0','0.3.0'])assert.equal(ui.prepare(dataFixture(version),compare),null);
 const wrong=dataFixture();wrong.mathematical_profile.models.forEach(model=>{model.metrics.completion.coverage={unit:'mathematical_family',planned:35,reviewed:35}});
 assert.equal(ui.prepare(wrong,compare),null);
 const data=dataFixture(),model=data.mathematical_profile.models[0];model.metrics.completion.exact=32.833333333333336;
 model.metrics.completion.confirmed=model.metrics.completion.lower=model.metrics.completion.upper=model.metrics.completion.exact;
 const selected=fixture(data,'?profile-models=astra-6-max'),row=selected.el('values').children[2].children[0];
 assert.equal(row.children[3].children[0].textContent,'32.8');assert.equal(row.children[3].children[1].textContent,'主榜SMC · 8/8');
 selected.win.MG.state.score='capability';selected.win.fire('mg:updated');
 assert.equal(selected.el('values').children[2].children[0].children[3].children[0].textContent,'32.8');
});

test('all21 model choices preserve retained styles and give Opus xHigh its own Claude variant',()=>{
 const data=dataFixture();
 for(const [id,label]of [['sol-6.2-xhigh','Sol 6.2 (xHigh)'],['astra-6.2-max','Astra 6.2 (Max)'],['claude-opus-5.5-xhigh','Opus 5.5 (xHigh)']]){
  const model={...data.models[0],id,label,logo:{label:id.startsWith('claude-')?'Anthropic':'OpenAI',data_url:'assets/'+id+'.svg'}};
  data.models.push(model);data.mathematical_profile.models.push({...data.mathematical_profile.models[0],id});
 }
 const claude=data.models.filter(model=>ui.brand(model).key==='claude'),styles=claude.map(model=>ui.styleFor(model));
 assert.deepEqual(styles.map(style=>style.index),[0,1,2]);
 assert.equal(new Set(styles.map(style=>style.dash+'|'+style.marker)).size,3);
 assert.equal(ui.styleFor({id:'astra-6.2-max'}).index,9);
 const f=fixture(data);f.controller.setSelection(data.models.map(model=>model.id));
 assert.equal(f.controller.selected().length,21);assert.equal(f.series().length,21);
 const fresh=f.series().find(node=>node.getAttribute('data-profile-model')==='claude-opus-5.5-xhigh');
 assert.equal(fresh.getAttribute('data-profile-marker'),'triangle');assert.equal(fresh.getAttribute('data-profile-dash'),'2 3');
 const choices=nodesBelow(f.el('choices')).filter(node=>node.type==='checkbox');assert.equal(choices.length,21);
 assert.ok(choices.some(node=>node.value==='claude-opus-5.5-xhigh'));
});

function revisionFixture(){
 const data=dataFixture();data.benchmark_version='1.2.0';
 data.profile_models=data.models.map(model=>({...model}));
 data.profile_models.find(model=>model.id==='glm-5.3-max').presentation_eligibility={ranked:false};
 data.models=data.models.slice(0,7).map(model=>({...model,
  neutral_revision_completion:{selected:6,full_rate:{exact:.5}},neutral_revision_delta:{strict:2.5}}));
 const profile=structuredClone(data.mathematical_profile);
 profile.schema='math-gauge.mathematical-profile-revision/v1';profile.version='0.1.0';profile.benchmark_version='1.2.0';
 profile.models=profile.models.slice(0,7);
 for(const model of profile.models){const metric=model.metrics.proof;metric.exact=metric.confirmed=metric.lower=metric.upper=40;}
 data.mathematical_profile_revision=profile;
 return data;
}

test('edition1.2 switches between all reviewed first answers and only adopted continuation profiles',()=>{
 const data=revisionFixture(),f=fixture(data,'?edition=1.2.0&lang=zh&score=partial#mathematical-profile');
 const control=f.el('continuation');
 assert.equal(f.controller.stage(),'revision');
 assert.equal(control.checked,true);
 assert.equal(f.el('continuation-control').hidden,false);
 assert.equal(nodesBelow(f.el('choices')).filter(node=>node.type==='checkbox').length,7);
 assert.equal(f.el('').hidden,false);assert.equal(f.el('').getAttribute('data-assessment-only'),null);
 assert.equal(f.el('values').children[2].children[0].children[1].children[0].textContent,'40.0');
 assert.ok(f.el('legend').children[0].children.at(-1).children[2].textContent.includes('6 续答'));
 control.checked=false;control.fire('change');
 assert.equal(f.controller.stage(),'first');
 assert.equal(control.checked,false);
 assert.equal(nodesBelow(f.el('choices')).filter(node=>node.type==='checkbox').length,17);
 assert.ok(!nodesBelow(f.el('choices')).some(node=>node.value==='glm-5.3-max'));
 assert.ok(f.controller.selected().includes('claude-opus-5.5-max'),'pending models retain their original reviewed profile');
 assert.equal(new URL(f.win.location.href).searchParams.get('profile-stage'),'first');
 assert.equal(new URL(f.win.location.href).searchParams.get('score'),'partial');
 assert.ok(f.comparisons.every(mode=>mode==='strict'));
 f.win.location.searchParams.set('profile-stage','revision');f.win.fire('popstate');
 assert.equal(f.controller.stage(),'revision');
 assert.equal(control.checked,true);
});

test('a pending first-answer selection never inherits an unreviewed continuation value',()=>{
 const data=revisionFixture(),f=fixture(data,'?edition=1.2.0&profile-stage=first&profile-models=claude-opus-5.5-max');
 const control=f.el('continuation');
 assert.deepEqual(f.controller.selected(),['claude-opus-5.5-max']);
 control.checked=true;control.fire('change');
 assert.equal(f.controller.stage(),'revision');assert.deepEqual(f.controller.selected(),[]);assert.equal(f.series().length,0);
 control.checked=false;control.fire('change');
 assert.deepEqual(f.controller.selected(),['claude-opus-5.5-max']);
 f.win.location.searchParams.set('lang','en');f.win.fire('mg:updated');
 assert.equal(control.checked,false);
});

test('current first-answer stage uses the explicit corrected baseline while archived0.4 values stay intact',()=>{
 const data=revisionFixture(),original=data.mathematical_profile.models[0].metrics.proof.exact;
 const baseline=structuredClone(data.mathematical_profile);
 Object.assign(baseline,{schema:'math-gauge.mathematical-profile-baseline/v1',version:'0.1.0',benchmark_version:'1.2.0'});
 const metric=baseline.models[0].metrics.proof;metric.exact=metric.confirmed=metric.lower=metric.upper=original-1;
 data.mathematical_profile_baseline=baseline;
 const f=fixture(data,'?edition=1.2.0&profile-stage=first&profile-models=astra-6-max');
 assert.equal(f.el('values').children[2].children[0].children[1].children[0].textContent,(original-1).toFixed(1));
 assert.equal(data.mathematical_profile.models[0].metrics.proof.exact,original);
 data.benchmark_version='1.1.0';const historical=fixture(data,'?edition=1.1.0&profile-models=astra-6-max');
 assert.equal(historical.el('values').children[2].children[0].children[1].children[0].textContent,original.toFixed(1));
});


function researchFixture(){
 const data=dataFixture();data.benchmark_version='1.2.0';
 const metric=value=>({exact:value,confirmed:value,lower:value,upper:value,unknown_weight:0,
  coverage:{unit:'open_research_family',planned:5,reviewed:5}});
 data.open_research={schema:'math-gauge.open-research/v1',version:'0.1.0',benchmark_version:'1.2.0',
  axis:{id:'open_research',label:{zh:'开放研究能力',en:'Open research capability'},
   description:{zh:'五个共同开放任务上的实际研究成果',en:'Delivered work on five common open tasks'}},
  pending_metric:{exact:null,confirmed:0,lower:0,upper:100,unknown_weight:100,coverage:{unit:'open_research_family',planned:5,reviewed:0}},
  models:data.models.map(model=>({id:model.id,first:metric(80),revision:metric(85)}))};
 data.mathematical_profile_revision={...structuredClone(data.mathematical_profile),
  schema:'math-gauge.mathematical-profile-revision/v1',version:'0.1.0',benchmark_version:'1.2.0'};
 return data;
}

test('current research capability augments rather than rewrites the seven retained axes',()=>{
 const data=researchFixture(),original=structuredClone(data.mathematical_profile);
 const prepared=ui.prepare(data,compare,'first');
 assert.equal(prepared.axes.length,8);
 assert.deepEqual(prepared.axes.slice(-2).map(axis=>axis.id),['open_research','initiative']);
 assert.equal(prepared.axes.at(-1).label.zh,'研究主动性');
 assert.equal(prepared.models[0].profile_metrics.open_research.exact,80);
 assert.equal(prepared.models[0].profile_metrics.open_research.coverage.planned,5);
 for(const axis of ui.AXES)assert.deepEqual(prepared.models[0].profile_metrics[axis],original.models[0].metrics[axis]);
 assert.deepEqual(data.mathematical_profile,original);
});

test('a pending research continuation stays an unknown interval instead of inheriting first-answer capability',()=>{
 const data=researchFixture();data.open_research.models[0].revision=null;
 const prepared=ui.prepare(data,compare,'revision'),model=prepared.models.find(row=>row.id===ids[0]);
 assert.equal(model.profile_metrics.open_research.exact,null);
 assert.deepEqual([model.profile_metrics.open_research.lower,model.profile_metrics.open_research.upper],[0,100]);
 const shape=ui.geometry(prepared.axes,model.profile_metrics);
 assert.equal(shape.vertices.length,8);assert.equal(shape.complete,false);
 assert.equal(shape.vertices[6],null);assert.ok(shape.vertices[7]);
});

test('eight-axis stage and language switching preserve initiative and independent coverage units',()=>{
 const data=researchFixture(),f=fixture(data,'?edition=1.2.0&profile-models=astra-6-max&profile-stage=first&score=partial');
 let points=nodesBelow(f.el('chart')).filter(node=>node.getAttribute('data-profile-point'));
 assert.equal(points.length,8);
 assert.equal(points.find(node=>node.getAttribute('data-profile-point')==='open_research').getAttribute('data-value'),'80');
 const initiative=points.find(node=>node.getAttribute('data-profile-point')==='initiative').getAttribute('data-value');
 f.el('continuation').checked=true;f.el('continuation').fire('change');
 points=nodesBelow(f.el('chart')).filter(node=>node.getAttribute('data-profile-point'));
 assert.equal(points.find(node=>node.getAttribute('data-profile-point')==='open_research').getAttribute('data-value'),'85');
 assert.equal(points.find(node=>node.getAttribute('data-profile-point')==='initiative').getAttribute('data-value'),initiative);
 assert.equal(f.el('values').children[2].children[0].children.length,9);
 assert.match(f.el('values').children[2].children[0].children[7].children[1].textContent,/5\/5/);
 assert.equal(new URL(f.win.location.href).searchParams.get('score'),'partial');
 f.win.location.searchParams.set('lang','en');f.win.fire('mg:updated');
 assert.match(f.el('meanings-title').textContent,/eight/);
});

test('old editions keep seven axes and an invalid new research denominator is rejected',()=>{
 const data=researchFixture();data.benchmark_version='1.1.0';
 assert.equal(ui.prepare(data,compare).axes.length,7);
 data.benchmark_version='1.2.0';data.open_research.models[0].first.coverage.planned=35;
 assert.equal(ui.prepare(data,compare),null);
});

function formalizationFixture(){
 const data=researchFixture();
 data.formalization_profile={schema:'math-gauge.formalization-profile/v1',version:'0.1.0',benchmark_version:'1.2.0',
  axis:{id:'formalization',label:{zh:'形式化能力',en:'Formalization'},
   description:{zh:'Lean整体SMC，含审计、工程与自查',en:'Full Lean SMC: audits, engineering and self-checks'}},
  models:data.models.map(model=>({id:model.id,metric:{exact:65,confirmed:65,lower:65,upper:65,
   unknown_weight:0,coverage:{unit:'lean_subcategory',planned:3,reviewed:3}}}))};
 return data;
}

test('nine axes preserve full Lean SMC through stage, language and score-mode changes',()=>{
 const data=formalizationFixture(),original=structuredClone(data.mathematical_profile);
 const first=ui.prepare(data,compare,'first'),last=ui.prepare(data,compare,'revision');
 assert.equal(first.axes.length,9);assert.equal(first.axes[1].id,'formalization');
 assert.deepEqual(first.models[0].profile_metrics.formalization,last.models[0].profile_metrics.formalization);
 assert.deepEqual(first.axes.slice(-2).map(axis=>axis.id),['open_research','initiative']);
 const f=fixture(data,'?edition=1.2.0&profile-models=astra-6-max&profile-stage=first&score=partial');
 let points=nodesBelow(f.el('chart')).filter(node=>node.getAttribute('data-profile-point'));
 assert.equal(points.length,9);
 f.el('continuation').checked=true;f.el('continuation').fire('change');
 points=nodesBelow(f.el('chart')).filter(node=>node.getAttribute('data-profile-point'));
 assert.equal(points.find(node=>node.getAttribute('data-profile-point')==='formalization').getAttribute('data-value'),'65');
 assert.match(f.el('values').children[2].children[0].children[2].children[1].textContent,/3\/3/);
 f.win.location.searchParams.set('lang','en');f.win.fire('mg:updated');
 assert.match(f.el('meanings-title').textContent,/nine/);
 assert.equal(new URL(f.win.location.href).searchParams.get('score'),'partial');
 assert.deepEqual(data.mathematical_profile,original);
});

test('unknown formalization is a ninth-axis gap and never becomes a measured zero',()=>{
 const data=formalizationFixture(),m=data.formalization_profile.models[0].metric;
 Object.assign(m,{exact:null,confirmed:25,lower:25,upper:75,unknown_weight:50});m.coverage.reviewed=1;
 const ready=ui.prepare(data,compare),shape=ui.geometry(ready.axes,ready.models.find(row=>row.id===ids[0]).profile_metrics);
 assert.equal(shape.vertices.length,9);assert.equal(shape.vertices[1],null);
 assert.ok(shape.intervals.some(value=>value.axis==='formalization'&&value.lower===25&&value.upper===75));
 data.benchmark_version='1.1.0';assert.equal(ui.prepare(data,compare).axes.length,7);
});

test('current profile uses adopted evidence and shows the whole eligible cohort outside the radar view',()=>{
 const original=formalizationFixture(),data=structuredClone(original);
 data.benchmark_version='1.3.0';
 const [measured,zero,unmeasured]=ids;
 data.models.at(-1).presentation_eligibility={ranked:false};
 const eligible=data.models.filter(model=>model.presentation_eligibility?.ranked!==false);
 const point=exact=>({exact,lower:exact,upper:exact,confirmed:exact});
 const mixed=(exact,unit='mathematical_family',planned=35,components=1)=>({...point(exact),
  base_coverage:{unit,planned,reviewed:planned},task_coverage:{unit:'independent_open_research_task',planned:1,
   reviewed:1,components_planned:components,components_reviewed:components}});
 const taste=(result,reviewed,state='reviewed')=>({...result,
  independent_metric:{state},independent_coverage:{unit:'taste_checkpoint',planned:3,reviewed:state==='reviewed'?3:0},
  legacy_review_available:state==='reviewed',legacy_metric:{coverage:{unit:'theorem_extension_family',planned:6,reviewed,observed:reviewed}}});
 const stage=(initiative,mathematical_taste)=>({initiative_v130:mixed(initiative),depth_v130:mixed(77),
  open_research_v130:mixed(66,'open_research_family',5,2),discernment_v130:mixed(88),mathematical_taste});
 const measuredProfile={independent_taste:point(86),independent_taste_smc:point(100),stages:{first:stage(62,taste(point(90),6)),
  revision:stage(72,taste({lower:83,upper:93,confirmed:83,exact:null},3))},completion_v130:{...point(74),
  coverage:{unit:'fixed_weighted_category',planned:4,adjudicated:4,unknown:0}}};
 const zeroProfile={stages:Object.fromEntries(['first','revision'].map(stage=>[stage,{mathematical_taste:taste(point(0),6)}]))};
 const untested=taste({lower:0,upper:100,confirmed:0,exact:null},0,'not-tested');
 const untestedProfile={stages:{first:{mathematical_taste:untested},revision:{mathematical_taste:untested}}};
 data.independent_research_abilities={schema:'math-gauge.independent-research-abilities/v4',edition:'1.3.0',
  taste_blend:{legacy_percent:20,independent_mode:'SMC',legacy_component_version:'0.2.0'},
  legacy_taste_binding:{version:'0.2.0',review_coverage:{planned:7,assessed:7,scored:6,source_missing:1,verification_unresolved:0}},
  source_stages:{first:'first-answer',revision:'revision-inclusive'},
  by_model:{[measured]:measuredProfile,[zero]:zeroProfile,[unmeasured]:untestedProfile}};
 data.research_preview={rows:[{id:measured,components:{taste:{state:'reviewed',value:86,strict:false}},
  task_strict:0,composites:{RMC:{exact:57}}}]};
 for(const stage of ['first','revision']){
  const legacy=ui.prepare(original,compare,stage),prepared=ui.prepare(data,compare,stage);
  assert.deepEqual(prepared.axes.slice(0,9).map(axis=>axis.id),legacy.axes.map(axis=>axis.id));
  assert.equal(prepared.axes.length,10);
  assert.equal(prepared.axes[9].id,'mathematical_taste');
  for(const model of prepared.models){
   const old=legacy.models.find(row=>row.id===model.id).profile_metrics;
   for(const axis of ['proof','fidelity','closure','formalization'])assert.deepEqual(model.profile_metrics[axis],old[axis]);
   const {mathematical_taste,completion,initiative}=model.profile_metrics;
   assert.equal(mathematical_taste.exact,model.id===measured&&stage==='first'?90:model.id===zero?0:null);
   assert.equal(completion.exact,model.id===measured?74:null);
   assert.equal(initiative.exact,model.id===measured?(stage==='first'?62:72):null);
  }
 }
 const query='&lang=zh&score=strict&profile-models='+[measured,zero,unmeasured].join(',');
 assert.equal(ui.prepare(data,compare).stage,'revision');
 const f=fixture(data,'?edition=1.3.0&profile-stage=first'+query+'#mathematical-profile');
 assert.equal(f.el('').hidden,false);
 assert.ok(!nodesBelow(f.el('')).includes(f.el('continuation-control')));
 assert.equal(f.profileNav.hidden,false);assert.equal(f.profileNav.getAttribute('data-assessment-only'),'1.3.0');
 assert.equal(f.controller.stage(),'revision');
 assert.equal(f.win.location.searchParams.has('profile-stage'),false);
 assert.equal(f.win.location.hash,'#mathematical-profile');
 const tastePoint=id=>nodesBelow(f.series().find(group=>group.getAttribute('data-profile-model')===id)).find(
  node=>node.getAttribute('data-profile-point')==='mathematical_taste')?.getAttribute('data-value');
 assert.equal(tastePoint(measured),undefined);assert.equal(tastePoint(zero),'0');assert.equal(tastePoint(unmeasured),undefined);
 const measuredSeries=f.series().find(group=>group.getAttribute('data-profile-model')===measured);
 assert.ok(nodesBelow(measuredSeries).some(node=>node.getAttribute('data-profile-interval')==='mathematical_taste'));
 assert.match(f.el('legend').children[2].children.at(-1).children[1].textContent,/0\/3 · 新题未测 · 旧题有确值家族 · 0\/6 · 旧题严格复核汇总未提供/);
 assert.equal(f.el('legend').children[0].children.at(-1).children[1].textContent,'旧题有确值家族 · 3/6');
 assert.match(f.el('meanings-scope').textContent,/已审查 7\/7 份.*原文缺失 1 份/);
 const profileNodes=()=>nodesBelow(f.el(''));
 const activePanes=()=>profileNodes().filter(node=>node.dataset.profilePane&&!node.hidden).map(node=>node.dataset.profilePane);
 const switchView=view=>profileNodes().find(node=>node.dataset.profileView===view).fire('click');
 const tableTaste=()=>f.el('values').children[2].children.map(row=>row.children.at(-1).children[0].textContent);
 const rankRows=()=>profileNodes().filter(node=>node.dataset.profileBarModel).map(node=>
  [node.dataset.profileBarModel,node.dataset.profileBarRank??null,nodesBelow(node).find(child=>child.className==='mp-rank-score').textContent]);
 const radar=profileNodes().find(node=>node.dataset.profilePane==='radar');
 f.el('picker').fire('click');
 for(const key of ['controls','picker','choices','empty'])assert.ok(nodesBelow(radar).includes(f.el(key)));
 assert.deepEqual(activePanes(),['radar']);
 switchView('table');assert.deepEqual(activePanes(),['table']);
 assert.equal(radar.hidden,true);
 assert.deepEqual(f.el('values').children[2].children.map(row=>row.children[0].textContent),eligible.map(model=>model.label));
 assert.deepEqual(tableTaste().slice(0,3),['83.0–93.0','0.0','未知']);
 const tasteCells=()=>f.el('values').children[2].children.map(row=>row.children.at(-1));
 assert.equal(tasteCells()[0].children.at(-1).textContent,'旧题有确值家族 · 3/6');
 assert.equal(tasteCells()[1].children.length,1,'a fully reviewed true zero needs no coverage row');
 switchView('bars');assert.deepEqual(activePanes(),['bars']);
 const axis=profileNodes().find(node=>node.tagName==='select');
 axis.value='mathematical_taste';axis.fire('change');
 const allRanks=rankRows();
 assert.equal(allRanks.length,eligible.length);
 assert.deepEqual(allRanks.slice(0,3),[[zero,'1','0.0'],[measured,null,'83.0–93.0'],[unmeasured,null,'未知']]);
 f.win.location.searchParams.set('profile-stage','first');f.win.fire('popstate');
 assert.equal(f.controller.stage(),'revision');
 assert.equal(f.win.location.searchParams.has('profile-stage'),false);
 assert.deepEqual(rankRows(),allRanks);
 assert.equal(f.win.location.searchParams.get('profile-view'),'bars');
 assert.equal(f.win.location.searchParams.get('profile-axis'),'mathematical_taste');
 const restored=fixture(data,f.win.location.search);
 assert.ok(nodesBelow(restored.el('')).some(node=>node.dataset.profilePane==='bars'&&!node.hidden));
 assert.equal(nodesBelow(restored.el('')).find(node=>node.tagName==='select').value,'mathematical_taste');
 switchView('radar');assert.equal(tastePoint(measured),undefined);
 assert.deepEqual(f.controller.selected(),[measured,zero,unmeasured]);
 assert.equal(f.el('choices').hidden,false);
 f.el('controls').children.find(node=>node.dataset.profilePreset==='clear').fire('click');
 assert.deepEqual(f.controller.selected(),[]);
 switchView('table');assert.equal(tableTaste().length,eligible.length);
 switchView('bars');assert.deepEqual(rankRows(),allRanks);
 assert.equal(f.win.location.searchParams.get('profile-models'),'');
 switchView('radar');assert.equal(f.series().length,0);
 assert.equal(new URL(f.win.location.href).searchParams.get('score'),'strict');

 const weighted=structuredClone(data),binding={version:'0.1.0',policy_sha256:'a'.repeat(64)};
 weighted.research_preview.item_weight_binding=binding;
 const companion=weighted.independent_research_abilities;
 companion.schema='math-gauge.independent-research-abilities/v7';
 companion.item_weight_binding={...binding};
 Object.assign(companion.by_model[measured].completion_v130,point(76));
 for(const stage of ['first','revision']){
  const row=ui.prepare(weighted,compare,stage).models.find(model=>model.id===measured);
  assert.equal(row.profile_metrics.completion.exact,76);
  assert.deepEqual(row.profile_metrics.mathematical_taste,
   ui.prepare(data,compare,stage).models.find(model=>model.id===measured).profile_metrics.mathematical_taste);
 }
 companion.item_weight_binding.policy_sha256='b'.repeat(64);
 assert.equal(ui.prepare(weighted,compare).models.find(model=>model.id===measured).profile_metrics.completion.exact,null);

 const added=structuredClone(weighted),c=added.independent_research_abilities,b=added.research_preview;
 c.schema='math-gauge.independent-research-abilities/v9';b.schema='math-gauge.research-board-preview/v7';
 c.item_weight_binding={...b.item_weight_binding};
 c.source_binding=b.source_binding={edition:'1.2.0',sha256:'1'.repeat(64)};
 c.value_binding={policy_sha256:'2'.repeat(64)};c.strict_credit_binding={policy_sha256:'3'.repeat(64)};
 const parentHash='4'.repeat(64);
 c.native_additions_binding={'gemini-4-carbon-medium':{parent:{edition:'1.2.0',
  path:`results/independent-research-baselines/v0.1.0/${parentHash}/data.json`,bytes:123,sha256:parentHash},
  index_sha256:'5'.repeat(64),adoption_sha256:'6'.repeat(64),human_review:'pending',
  legacy_taste_sha256:null,source_kind:'user-selected-native-cutoff-deliveries',policy_bindings:{
   value:c.value_binding.policy_sha256,strict_credit:c.strict_credit_binding.policy_sha256,
   item_weight:c.item_weight_binding.policy_sha256}}};
 b.native_additions_binding=structuredClone(c.native_additions_binding);
 c.by_model['gemini-4-carbon-medium']=structuredClone(c.by_model[measured]);
 const withAddition=ui.prepare(added,compare),carbon=withAddition.models.find(model=>model.id==='gemini-4-carbon-medium');
 assert.equal(withAddition.axes.length,10);assert.equal(carbon.profile_metrics.completion.exact,76);
 assert.equal(carbon.profile_metrics.mathematical_taste.exact,null,'missing revision taste remains an interval');
 const damaged=structuredClone(added);
 damaged.independent_research_abilities.native_additions_binding['gemini-4-carbon-medium'].parent.private_quote='forbidden';
 damaged.research_preview.native_additions_binding=structuredClone(damaged.independent_research_abilities.native_additions_binding);
 assert.equal(ui.prepare(damaged,compare).models.find(model=>model.id==='gemini-4-carbon-medium').profile_metrics.completion.exact,null);
 const rebound=structuredClone(added);rebound.independent_research_abilities.native_additions_binding['gemini-4-carbon-medium'].parent.sha256='7'.repeat(64);
 assert.equal(ui.prepare(rebound,compare).models.find(model=>model.id==='gemini-4-carbon-medium').profile_metrics.completion.exact,null);

 const oldWithCompanion={...original,independent_research_abilities:data.independent_research_abilities};
 const oldQuery='?edition=1.2.0'+query,old=fixture(original,oldQuery),same=fixture(oldWithCompanion,oldQuery);
 const tableText=page=>nodesBelow(page.el('values')).map(node=>[node.tagName,node.textContent]);
 assert.deepEqual(tableText(same),tableText(old));assert.equal(same.profileNav.getAttribute('data-assessment-only'),'1.2.0');
 assert.ok(!nodesBelow(same.el('')).some(node=>node.dataset.profileView));
});

test('formalization rejects a changed denominator, duplicate or missing selected model',()=>{
 const data=formalizationFixture();data.formalization_profile.models[0].metric.coverage.planned=35;
 assert.equal(ui.prepare(data,compare),null);
 const missing=formalizationFixture();missing.formalization_profile.models.shift();
 assert.equal(ui.prepare(missing,compare),null);
 const duplicate=formalizationFixture();duplicate.formalization_profile.models.push(duplicate.formalization_profile.models[0]);
 assert.equal(ui.prepare(duplicate,compare),null);
});

test('the newly admitted Astra configuration has its own stable same-brand style',()=>{
 const models=['astra-6-max','astra-6-xhigh','sol-6.2-max','sol-6.1-max','sol-6.1-xhigh',
  'terra-6.1-max','terra-6.1-xhigh','dot-underlying-model-20261108','sol-6.2-xhigh','astra-6.2-max','astra-6.2-xhigh'];
 const styles=models.map(id=>ui.styleFor({id}));
 assert.equal(new Set(styles.map(style=>style.dash+'|'+style.marker)).size,11);
 assert.equal(styles.at(-1).index,10);
 assert.deepEqual(styles.slice(0,10).map(style=>style.index),[0,1,2,3,4,5,6,7,8,9]);
});

function opportunityFixture(){
 const data=formalizationFixture();data.benchmark_version='1.3.0';
 const metric=(value,planned,reviewed=planned)=>({exact:value,confirmed:value??0,lower:value??0,upper:value??100,
  coverage:{unit:'research_opportunity',planned,reviewed}});
 data.research_initiative={schema:'math-gauge.research-initiative/v1',version:'0.1.0',benchmark_version:'1.3.0',
  reviewer_kind:'ai',human_review:'pending',post_observation:true,new_candidate_calls:0,main_scores_modified:false,
  original_bytes_rewritten:false,policy_sha256:'a'.repeat(64),source:{sha256:'b'.repeat(64)},
  models:data.models.map((model,index)=>({id:model.id,metric:metric(index===0?25:0,28),
   legacy_metric:metric(index===0?25:0,27),extension_metric:metric(index===0?25:0,1),
   legacy_weight:'27/28',extension_weight:'1/28'}))};
 const pending=data.research_initiative.models[2];
 pending.extension_metric=metric(null,1,0);
 pending.metric={...metric(null,28,27),upper:100/28};
 return data;
}

test('common-opportunity reviews replace only current initiative, without mutating source scores or historical profiles',()=>{
 const data=opportunityFixture(),original=structuredClone(data),without=structuredClone(data);delete without.research_initiative;
 const prior=ui.prepare(without,compare),current=ui.prepare(data,compare);
 for(const model of current.models){
  const old=prior.models.find(row=>row.id===model.id);
  for(const axis of current.axes.filter(axis=>axis.id!=='initiative'))
   assert.deepEqual(model.profile_metrics[axis.id],old.profile_metrics[axis.id]);
  assert.deepEqual(model.profile_metrics.initiative,data.research_initiative.models.find(row=>row.id===model.id).metric);
 }
 assert.deepEqual(data,original);
 data.benchmark_version='1.2.0';without.benchmark_version='1.2.0';
 assert.deepEqual(ui.prepare(data,compare),ui.prepare(without,compare),'1.2 ignores the new current-only component');
});

test('known-zero initiative remains zero while missing new-task evidence retains the fixed opportunity interval',()=>{
 const data=opportunityFixture(),prepared=ui.prepare(data,compare),models=new Map(prepared.models.map(row=>[row.id,row]));
 assert.equal(models.get(ids[1]).profile_metrics.initiative.exact,0);
 const pending=models.get(ids[2]).profile_metrics.initiative;
 assert.equal(pending.exact,null);assert.equal(pending.upper,100/28);assert.equal(pending.coverage.reviewed,27);
 data.research_initiative.models=data.research_initiative.models.filter(row=>row.id!==ids[0]);
 const missing=ui.prepare(data,compare).models.find(row=>row.id===ids[0]).profile_metrics.initiative;
 assert.deepEqual([missing.exact,missing.lower,missing.upper,missing.coverage.reviewed],[null,0,100,0],
  'a configuration without the new review must not inherit the old, differently weighted score');
});

test('opportunity source, weights and coverage are validated before displaying revised initiative',()=>{
 for(const change of [d=>d.research_initiative.policy_sha256='bad',
  d=>d.research_initiative.models[0].extension_weight='1/5',
  d=>d.research_initiative.models[0].metric.coverage.planned=35,
  d=>d.research_initiative.models[0].metric.coverage.reviewed=27,
  d=>d.research_initiative.models.push(d.research_initiative.models[0])]){
  const data=opportunityFixture();change(data);assert.equal(ui.prepare(data,compare),null);
 }
});

test('initiative coverage uses opportunities separately from family coverage and preserves URL controls',()=>{
 const f=fixture(opportunityFixture(),'?edition=1.3.0&profile-models='+ids[2]+'&profile-view=radar&profile-axis=initiative&score=strict');
 const legend=nodesBelow(f.el('legend')).map(node=>node.textContent).join(' ');
 assert.match(legend,/拓展机会 · 27\/28/);assert.doesNotMatch(legend,/27–35\/35/);
 assert.match(f.el('meanings-scope').textContent,/28个拓展机会/);
 f.win.location.searchParams.set('lang','en');f.win.fire('mg:updated');
 assert.match(f.el('meanings-scope').textContent,/28 common extension opportunities/);
 assert.equal(new URL(f.win.location.href).searchParams.get('profile-axis'),'initiative');
 assert.deepEqual(f.controller.selected(),[ids[2]]);
});

function structureFixture(){
 const data=opportunityFixture(),shape={depth:{unit:'depth_family',planned:28,weight:69},open_research:{unit:'open_research_opportunity',planned:6,weight:11}};
 const metric=(axis,value,pending=false)=>{const s=shape[axis],missing=pending?3:0,upper=pending?300/s.weight:value;
  return {exact:pending?null:value,confirmed:pending?0:value,lower:pending?0:value,upper,unknown_weight:pending?upper:0,
   coverage:{unit:s.unit,planned:s.planned,reviewed:s.planned-(pending?1:0),weight_planned:s.weight,weight_reviewed:s.weight-missing}}};
 data.profile_structure={schema:'math-gauge.profile-structure/v1',version:'0.1.0',benchmark_version:'1.3.0',condition:'nonlogical_retry_3',
  reviewer_kind:'ai',human_review:'pending',post_observation:true,formal_comparison_eligible:false,new_candidate_calls:0,
  main_scores_modified:false,original_bytes_rewritten:false,policy_sha256:'c'.repeat(64),source:{sha256:'d'.repeat(64)},
  planned:{depth:28,open_research:6},weights:{depth:69,open_research:11},
  axes:[{id:'depth',label:{zh:'数学深度',en:'Mathematical depth'},description:{zh:'题内机制与结构。',en:'Mechanisms and structure in prescribed problems.'}},
   {id:'open_research',label:{zh:'开放研究能力',en:'Open research capability'},description:{zh:'开放请求中的可用成果。',en:'Usable results under open requests.'}}],
  models:data.models.map((model,index)=>{const make=()=>({depth:metric('depth',index===1?0:83,index===2),open_research:metric('open_research',index===1?0:71,index===2)});
   return {id:model.id,first:make(),revision:make()}})};
 return data;
}

test('independent structure source replaces only depth and open research without changing old scores or other axes',()=>{
 const data=structureFixture(),original=structuredClone(data),without=structuredClone(data);delete without.profile_structure;
 const old=ui.prepare(without,compare),current=ui.prepare(data,compare);
 for(const model of current.models){
  const prior=old.models.find(row=>row.id===model.id),source=data.profile_structure.models.find(row=>row.id===model.id);
  assert.deepEqual(model.profile_metrics.depth,source.revision.depth);
  assert.deepEqual(model.profile_metrics.open_research,source.revision.open_research);
  for(const axis of current.axes.filter(axis=>!['depth','open_research'].includes(axis.id)))
   assert.deepEqual(model.profile_metrics[axis.id],prior.profile_metrics[axis.id]);
 }
 assert.deepEqual(data,original);
 const changed=structuredClone(data),mixed=(unit,planned)=>({lower:4,upper:4,exact:4,confirmed:4,base_coverage:{unit,planned,reviewed:planned}});
 const stage=()=>({depth_v130:mixed('mathematical_family',35),open_research_v130:mixed('open_research_family',5),
  discernment_v130:mixed('mathematical_family',35),initiative_v130:mixed('mathematical_family',35)});
 changed.independent_research_abilities={schema:'math-gauge.independent-research-abilities/v2',edition:'1.3.0',
  source_stages:{first:'first-answer',revision:'revision-inclusive'},
  by_model:Object.fromEntries(changed.models.map(model=>[model.id,{stages:{first:stage(),revision:stage()}}]))};
 const legacyChanged=structuredClone(changed);delete legacyChanged.profile_structure;
 assert.equal(ui.prepare(legacyChanged,compare).models[0].profile_metrics.depth.exact,4);
 assert.deepEqual(ui.prepare(changed,compare).models.map(row=>[row.profile_metrics.depth,row.profile_metrics.open_research]),
  current.models.map(row=>[row.profile_metrics.depth,row.profile_metrics.open_research]),'old capacity/profile mixtures cannot influence the new source');
});

test('new structure zeros remain known and a missing model uses fixed unknowns without old-capacity fallback',()=>{
 const data=structureFixture(),models=new Map(ui.prepare(data,compare).models.map(row=>[row.id,row]));
 assert.equal(models.get(ids[1]).profile_metrics.depth.exact,0);
 assert.equal(models.get(ids[1]).profile_metrics.open_research.exact,0);
 assert.equal(models.get(ids[2]).profile_metrics.depth.coverage.planned,28);
 assert.equal(models.get(ids[2]).profile_metrics.open_research.coverage.planned,6);
 data.profile_structure.models=data.profile_structure.models.filter(row=>row.id!==ids[0]);
 const missing=ui.prepare(data,compare).models.find(row=>row.id===ids[0]);
 for(const axis of ['depth','open_research'])assert.deepEqual([missing.profile_metrics[axis].exact,missing.profile_metrics[axis].lower,missing.profile_metrics[axis].upper],[null,0,100]);
});

test('structural source rejects wrong denominators, weights, identities and unknown markers',()=>{
 const changes=[d=>d.profile_structure.weights.depth=70,d=>d.profile_structure.models[0].revision.depth.coverage.planned=35,
  d=>d.profile_structure.models[0].revision.open_research.coverage.weight_planned=12,d=>d.profile_structure.policy_sha256='bad',
  d=>d.profile_structure.models.push(d.profile_structure.models[0]),d=>d.profile_structure.models[0].revision.depth.coverage.reviewed=27];
 for(const change of changes){const data=structureFixture();change(data);assert.equal(ui.prepare(data,compare),null)}
});

test('current depth and open research keep separate coverage while preserving language and URL model selection',()=>{
 const f=fixture(structureFixture(),'?edition=1.3.0&profile-models='+ids[2]+'&profile-axis=depth&profile-view=radar&score=strict');
 const legend=()=>nodesBelow(f.el('legend')).map(node=>node.textContent).join(' ');
 assert.match(legend(),/深度家族 · 27\/28/);assert.match(legend(),/开放研究机会 · 5\/6/);assert.doesNotMatch(legend(),/27–35\/35/);
 assert.match(f.el('meanings-scope').textContent,/28个给定问题家族/);
 f.win.location.searchParams.set('lang','en');f.win.fire('mg:updated');
 assert.match(legend(),/Depth families · 27\/28/);assert.match(legend(),/Open research opportunities · 5\/6/);
 assert.equal(new URL(f.win.location.href).searchParams.get('profile-axis'),'depth');assert.deepEqual(f.controller.selected(),[ids[2]]);
});

test('historical profile editions ignore the current-only structural overlay',()=>{
 for(const edition of ['1.1.0','1.2.0']){
  const withSource=structureFixture();withSource.benchmark_version=edition;
  const without=structuredClone(withSource);delete without.profile_structure;
  assert.deepEqual(ui.prepare(withSource,compare,'first'),ui.prepare(without,compare,'first'));
 }
});
