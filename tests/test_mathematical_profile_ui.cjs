/* Supplied-axis presentation tests; no model evaluation or score arithmetic. */
const assert=require('node:assert/strict');
const {test}=require('node:test');
const ui=require('../scripts/templates/mathematical-profile.js');

const ids=['astra-6-max','sol-6.2-max','astra-6-xhigh','sol-6.1-max','sol-6.1-xhigh',
 'terra-6.1-max','terra-6.1-xhigh','dot-underlying-model-20261108','claude-opus-5.5-max',
 'claude-sonnet-5.5-max','gemini-4-carbon-medium','gemini-4-hydrogen-xhigh','gemini-4-carbon-high',
 'gemini-4-argon','gemini-3.8-flash-high','kimi-3.1-pro-max','deepseek-v4.1-flash-1017','glm-5.3-max'];
const compare=(a,b)=>b.rmc-a.rmc||a.id.localeCompare(b.id);
function dataFixture(version='0.1.0'){
 const models=ids.map((id,index)=>({id,label:'Model '+id,rmc:100-index,
  logo:{label:id.startsWith('claude-')?'Anthropic':id.startsWith('gemini-')?'Google':id.startsWith('kimi-')?'Kimi':id.startsWith('deepseek-')?'DeepSeek':id.startsWith('glm-')?'Z.ai':'OpenAI',data_url:'assets/'+id+'.svg'}}));
 const axes=ui.AXES.map(id=>({id,label:{zh:'中'+id,en:'English '+id},description:{zh:'说明 '+id,en:'Description '+id}}));
 const planned=version==='0.2.0'?35:12;
 const profile={schema:'math-gauge.mathematical-profile/v1',version,benchmark_version:'1.1.0',
  axes,models:models.map((model,index)=>({id:model.id,metrics:Object.fromEntries(axes.map((axis,i)=>[axis.id,
   {exact:80-index-i,confirmed:80-index-i,lower:80-index-i,upper:80-index-i,reviewed_families:planned,planned_families:planned}]))})),reviewer_kind:'ai',human_review:'pending'};
 return {benchmark_version:'1.1.0',models,mathematical_profile:profile};
}
function nodesBelow(node){return [node,...node.children.flatMap(nodesBelow)]}
function fixture(data=dataFixture(),query='?edition=1.1.0&lang=zh&score=capability&sort-research=strict#mathematical-profile'){
 const documentNodes=new Map(),events=new Map(),comparisons=[],changes=[];
 class Element{
  constructor(tag){this.tagName=tag;this.children=[];this.attrs=new Map();this.style={setProperty(){}};this.dataset={};this.listeners=new Map();this.hidden=false;this.checked=false;this.textContent='';}
  append(...children){this.children.push(...children)}
  replaceChildren(...children){this.children=children}
  setAttribute(key,value){this.attrs.set(key,String(value))}
  getAttribute(key){return this.attrs.get(key)??null}
  removeAttribute(key){this.attrs.delete(key)}
  addEventListener(key,callback){if(!this.listeners.has(key))this.listeners.set(key,[]);this.listeners.get(key).push(callback)}
  fire(key){for(const callback of this.listeners.get(key)||[])callback({target:this})}
 }
 for(const name of ['', '-title','-description','-review','-controls','-count','-picker-title','-choices',
  '-chart','-note','-legend','-focus-note','-empty','-values-title','-coverage-note','-values',
  '-meanings','-meanings-title','-meanings-scope','-meanings-list']){
  const element=new Element('div');element.id='mathematical-profile'+name;documentNodes.set(element.id,element);
 }
 const section=documentNodes.get('mathematical-profile');section.setAttribute('data-assessment-only','1.1.0');
 const location=new URL('https://example.test/math-gauge/index.html'+query);
 const win={location,document:{getElementById:id=>documentNodes.get(id)||null,createElement:tag=>new Element(tag),createElementNS:(_,tag)=>new Element(tag)},
  MG:{d:data,state:{score:'capability'},compareScores:(a,b,mode)=>{comparisons.push(mode);return compare(a,b)}},
  history:{replaceState:(_,__,url)=>{changes.push(url);location.href=url}},
  addEventListener:(key,callback)=>{if(!events.has(key))events.set(key,[]);events.get(key).push(callback)},
  fire:key=>{for(const callback of events.get(key)||[])callback({type:key})}};
 const controller=ui.mount(win);
 const el=name=>documentNodes.get('mathematical-profile'+(name?'-'+name:''));
 return {win,controller,el,changes,comparisons,series:()=>nodesBelow(el('chart')).filter(node=>node.getAttribute('class')==='mp-series')};
}

test('default representatives choose the RMC winner per brand, limited to the top five brands',()=>{
 const data=dataFixture(),expected=['astra-6-max','claude-opus-5.5-max','gemini-4-carbon-medium','kimi-3.1-pro-max','deepseek-v4.1-flash-1017'];
 assert.deepEqual(ui.representatives(data.models,compare),expected);
 assert.deepEqual(ui.representatives([...data.models].reverse(),compare),expected);
 const f=fixture(data);assert.deepEqual(f.controller.selected(),expected);assert.ok(f.comparisons.every(mode=>mode==='partial'));
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
 metrics.proof={exact:0,confirmed:0,lower:0,upper:0,reviewed_families:12,planned_families:12};
 metrics.completion={exact:null,confirmed:0,lower:0,upper:100,reviewed_families:0,planned_families:12};
 metrics.depth={exact:null,confirmed:35,lower:20,upper:80,reviewed_families:6,planned_families:12};
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
 assert.equal(row.children[6].children[2].textContent,'6/12 家族');
});

test('explicit empty or unknown URL selection does not silently select default models',()=>{
 const data=dataFixture();assert.deepEqual(ui.readSelection('?profile-models=',data.models,compare),[]);
 assert.deepEqual(ui.readSelection('?profile-models=unknown-model',data.models,compare),[]);
 assert.deepEqual(ui.readSelection('?profile-models=sol-6.2-max,astra-6-max,sol-6.2-max',data.models,compare),['astra-6-max','sol-6.2-max']);
 const f=fixture(data,'?edition=1.1.0&profile-models=');assert.deepEqual(f.controller.selected(),[]);assert.equal(f.series().length,0);assert.equal(f.el('empty').hidden,false);
});

test('presets and all-model multiselect preserve URL context and retain checkbox focus targets',()=>{
 const f=fixture();const originalCheckboxes=nodesBelow(f.el('choices')).filter(node=>node.type==='checkbox');
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
 const row=f.el('values').children[2].children[0];assert.equal(row.children[1].children[1].textContent,'12/12 families');
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

test('v0.2 settles known zero deliveries and shows true missing evidence without a zero-of-seven legend',()=>{
 const data=dataFixture('0.2.0'),profiles=data.mathematical_profile.models;
 profiles[0].metrics.proof={exact:0,confirmed:0,lower:0,upper:0,reviewed_families:35,planned_families:35};
 const glm=profiles.find(model=>model.id==='glm-5.3-max');
 for(const metric of Object.values(glm.metrics))Object.assign(metric,{exact:null,confirmed:50,lower:50,upper:50+100/70,reviewed_families:34});
 const f=fixture(data,'?edition=1.1.0&profile-models=astra-6-max,glm-5.3-max');
 const labels=f.el('legend').children.map(button=>button.children.at(-1).children[1].textContent);
 assert.deepEqual(labels,['35/35 家族已结算','34/35 家族已结算']);
 const rows=f.el('values').children[2].children;
 assert.equal(rows[0].children[1].children[0].textContent,'0.0');
 assert.equal(rows[0].children[1].children[1].textContent,'35/35 家族已结算');
 assert.equal(rows[1].children[1].className,'mp-uncertain');
 assert.equal(rows[1].children[1].children[2].textContent,'34/35 家族已结算');
 assert.ok(f.el('description').textContent.includes('同一35个数学家族'));
 assert.ok(f.el('note').textContent.includes('截止前内容可得部分分'));
 assert.ok(f.el('note').textContent.includes('真正未运行或缺证据'));
 f.win.location.searchParams.set('lang','en');f.win.fire('mg:updated');
 assert.equal(f.el('legend').children[1].children.at(-1).children[1].textContent,'34/35 families settled');
});

test('v0.2 meanings use supplied bilingual axes and preserve the native disclosure on language changes',()=>{
 const data=dataFixture('0.2.0'),axes=data.mathematical_profile.axes;
 axes.find(axis=>axis.id==='depth').label={zh:'数学深度',en:'Mathematical depth'};
 axes.find(axis=>axis.id==='closure').label={zh:'成果闭合度',en:'Result closure'};
 const f=fixture(data),list=f.el('meanings-list');
 assert.equal(f.el('meanings').hidden,false);assert.equal(list.children.length,7);
 assert.deepEqual(list.children.map(item=>item.children[0].textContent),axes.map(axis=>axis.label.zh));
 assert.deepEqual(list.children.map(item=>item.children[1].textContent),axes.map(axis=>axis.description.zh));
 assert.ok(f.el('meanings-scope').textContent.includes('39道初答与3轮自查'));
 assert.ok(f.el('meanings-scope').textContent.includes('不限六道命题拓展题'));
 assert.equal(list.children[2].children[1].children[0].textContent,'衡量原任务要求的完整目标。');
 f.el('meanings').open=true;f.win.location.searchParams.set('lang','en');f.win.fire('mg:updated');
 assert.equal(f.el('meanings').open,true);
 assert.deepEqual(list.children.map(item=>item.children[0].textContent),axes.map(axis=>axis.label.en));
 assert.ok(list.children[6].children[1].children[0].textContent.includes('substantive results actually delivered'));
 assert.ok(f.el('meanings-scope').textContent.includes('39 initial answers and 3 rounds'));
});

test('v0.2 legend reports a settled-family range when supplied axis coverage differs',()=>{
 const data=dataFixture('0.2.0'),metrics=data.mathematical_profile.models[0].metrics;
 metrics.proof.reviewed_families=33;metrics.completion.reviewed_families=34;
 const f=fixture(data,'?edition=1.1.0&profile-models=astra-6-max');
 assert.equal(f.el('legend').children[0].children.at(-1).children[1].textContent,'33–35/35 家族已结算');
 const rows=f.el('values').children[2].children;
 assert.equal(rows[0].children[1].children[1].textContent,'33/35 家族已结算');
 assert.equal(rows[0].children[3].children[1].textContent,'34/35 家族已结算');
});

test('legacy profile copy and exact-axis legend stay compatible while unknown versions are rejected',()=>{
 const f=fixture();assert.equal(f.el('description').textContent,'七个独立维度 · 每轴0–100');
 assert.equal(f.el('legend').children[0].children.at(-1).children[1].textContent,'7/7 轴完整计分');
 assert.equal(f.el('meanings').hidden,true);
 const unsupported=dataFixture('0.3.0');assert.equal(ui.prepare(unsupported,compare),null);
 const wrongPlan=dataFixture('0.2.0');
 for(const model of wrongPlan.mathematical_profile.models)for(const metric of Object.values(model.metrics))metric.planned_families=36;
 assert.equal(ui.prepare(wrongPlan,compare),null);
});

test('all21 model choices preserve retained styles and give Opus xHigh its own Claude variant',()=>{
 const data=dataFixture('0.2.0');
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
