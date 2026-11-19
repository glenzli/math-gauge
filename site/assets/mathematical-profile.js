/* Independent supplied mathematical axes. This UI never computes benchmark credit. */
(function(root,factory){
 const api=factory();
 if(typeof module==='object'&&module.exports)module.exports=api;
 if(root&&root.document){root.MGMathematicalProfile=api;api.mount(root)}
})(typeof window==='object'?window:null,()=>{
 'use strict';
 const AXES=['proof','fidelity','completion','discernment','initiative','depth','closure'];
 const BRANDS={openai:{label:'OpenAI',color:'#252525'},claude:{label:'Claude',color:'#d97757'},google:{label:'Google',color:'#45965d'},kimi:{label:'Kimi',color:'#3568d4'},deepseek:{label:'DeepSeek',color:'#7651bb'},glm:{label:'GLM',color:'#af7b15'}};
 const VARIANTS=[{dash:'',marker:'circle'},{dash:'7 3',marker:'square'},{dash:'2 3',marker:'triangle'},
  {dash:'12 4',marker:'diamond'},{dash:'9 3 2 3',marker:'plus'},{dash:'4 3 1 3',marker:'cross'},
  {dash:'15 3 2 3',marker:'hexagon'},{dash:'18 4 3 4',marker:'ring'},{dash:'6 3 6 3 1 3',marker:'pentagon'},
  {dash:'10 2 2 2 2 2',marker:'circle'}];
 const LEGACY_FALLBACK_VARIANTS=8;
 const STYLE_IDS={'astra-6-max':0,'astra-6-xhigh':1,'sol-6.2-max':2,'sol-6.1-max':3,'sol-6.1-xhigh':4,
  'terra-6.1-max':5,'terra-6.1-xhigh':6,'dot-underlying-model-20261108':7,'sol-6.2-xhigh':8,'astra-6.2-max':9,
  'claude-opus-5.5-max':0,'claude-sonnet-5.5-max':1,'claude-opus-5.5-xhigh':2,'gemini-4-carbon-medium':0,
  'gemini-4-hydrogen-xhigh':1,'gemini-4-carbon-high':2,'gemini-4-argon':3,'gemini-3.8-flash-high':4};
 const messages={title:['数学画像','Mathematical profile'],description:['七个独立维度 · 每轴0–100','Seven independent dimensions · 0–100 per axis'],
  review:['AI评审 · 人工审核待完成','AI reviewed · Human review pending'],leader:['单榜首','RMC leader'],brands:['品牌代表','Brand representatives'],clear:['清空','Clear'],
  picker:['选择模型','Choose models'],selected:['已选','Selected'],of:['／',' / '],models:['个模型','models'],
  note:['逐轴比较；区间与断线表示证据缺口。','Compare individual axes. Intervals and gaps indicate missing evidence.'],
  focus:['悬停或聚焦模型可突出曲线；点击可固定。','Hover or focus a model to emphasize its curve; click to pin.'],
  values:['数值与家族覆盖','Values and family coverage'],coverage:['覆盖数按各轴统计，轴间不相加。画像不随顶部计分口径切换。','Coverage is reported per axis and is not added across axes. The profile is independent of the score selector.'],
  empty:['选择模型开始对照。','Choose models to compare.'],model:['模型','Model'],families:['家族','families'],confirmed:['已确认','Confirmed'],
  exactAxes:['轴完整计分','axes with exact scores'],range:['区间','Interval'],unknown:['证据未齐','Evidence incomplete'],
  chart:['七轴数学画像，固定0至100刻度','Seven-axis mathematical profile, fixed scale from 0 to 100'],table:['所选模型的独立数学维度及审核家族覆盖','Independent mathematical axes and reviewed-family coverage for selected models']};
 const messagesV2={description:['七个维度 · 同一35个数学家族 · 每轴0–100','Seven dimensions · the same 35 mathematical families · 0–100 per axis'],
  note:['已结案的空白或无可核成果的失败计0；经核实的截止前内容可得部分分。区间与断线仅表示真正未运行或缺证据。','Settled blanks and failures without verified work receive 0. Verified cutoff content may receive partial credit. Intervals and gaps indicate only unrun tasks or missing evidence.'],
  values:['数值与已结算范围','Values and settled coverage'],
  coverage:['各轴固定35个家族；已结算范围包括已确定的0分交付。未运行或缺证据保留区间，画像不随顶部计分口径切换。','Each axis retains 35 fixed families. Settled coverage includes confirmed zero deliveries. Unrun tasks or missing evidence retain intervals. The profile is independent of the score selector.'],
  settled:['家族已结算','families settled'],table:['所选模型各数学维度的数值与已结算范围','Supplied mathematical axes and settled-family coverage for selected models'],
  meanings:['七轴含义与范围','What the seven axes measure'],
  scope:['七轴均纳入39道初答与3轮自查，固定为同一35个数学家族；相关变体与自查在家族内聚合。范围覆盖全卷，不限六道命题拓展题。','All seven axes cover 39 initial answers and 3 rounds of self review in the same 35 mathematical families. Related variants and review rounds stay within their families. Coverage extends across the assessment, beyond the six theorem extension tasks.']};
 const axisContext={completion:['衡量原任务要求的完整目标。','This concerns the complete goals required by the original task.'],
  initiative:['衡量超出该题要求且有数学依据的推进。','This concerns mathematically supported progress beyond the task requirements.'],
  depth:['衡量实际成立的机制、自然范围与结构解释。','This concerns mechanisms, natural scope and structural insight that have actually been established.'],
  closure:['衡量实际交付的实质结果是否证明完整、依赖齐全、范围明确。','This concerns complete proofs, dependencies and explicit scope for the substantive results actually delivered.']};
 const finite=value=>typeof value==='number'&&Number.isFinite(value)&&value>=0&&value<=100;
 function brand(model){
  const name=String(model.logo?.label||'').toLowerCase().replace(/[^a-z0-9]/g,'');
  let key={openai:'openai',anthropic:'claude',claude:'claude',google:'google',kimi:'kimi',moonshot:'kimi',deepseek:'deepseek',zai:'glm',glm:'glm'}[name];
  if(!key)key=/^(astra|terra|sol|dot)-/.test(model.id)?'openai':/^claude-/.test(model.id)?'claude':/^gemini-/.test(model.id)?'google':/^kimi-/.test(model.id)?'kimi':/^deepseek-/.test(model.id)?'deepseek':/^glm-/.test(model.id)?'glm':null;
  return key?{key,...BRANDS[key]}:{key:'other-'+name,label:model.logo?.label||'Other',color:'#667085'};
 }
 function styleFor(model){
  let index=STYLE_IDS[model.id];
  if(index===undefined){let hash=0;for(const char of model.id)hash=(Math.imul(hash,31)+char.charCodeAt(0))>>>0;index=hash%LEGACY_FALLBACK_VARIANTS}
  return {...brand(model),...VARIANTS[index],index};
 }
 function representatives(models,compare,limit=5){
  const seen=new Set(),selected=[];
  for(const model of [...models].sort(compare)){const key=brand(model).key;if(!seen.has(key)){seen.add(key);selected.push(model.id);if(selected.length===limit)break}}
  return selected;
 }
 function readSelection(search,models,compare){
  const params=new URLSearchParams(search),valid=new Set(models.map(model=>model.id));
  if(!params.has('profile-models'))return representatives(models,compare);
  const requested=new Set(params.get('profile-models').split(',').filter(id=>valid.has(id)));
  return [...models].sort(compare).filter(model=>requested.has(model.id)).map(model=>model.id);
 }
 function selectionUrl(address,ids){const url=new URL(address);url.searchParams.set('profile-models',ids.join(','));return url.href}
 function validMetric(metric){return metric&&finite(metric.confirmed)&&finite(metric.lower)&&finite(metric.upper)&&metric.lower<=metric.upper&&
  (metric.exact===null||finite(metric.exact)&&metric.exact>=metric.lower&&metric.exact<=metric.upper)&&
  Number.isInteger(metric.reviewed_families)&&Number.isInteger(metric.planned_families)&&metric.reviewed_families>=0&&metric.planned_families>=metric.reviewed_families}
 function point(index,value){const angle=-Math.PI/2+index*2*Math.PI/7;return {x:260+Math.cos(angle)*148*value/100,y:225+Math.sin(angle)*148*value/100}}
 function geometry(axes,metrics){
  const vertices=axes.map((axis,index)=>metrics[axis.id].exact===null?null:{...point(index,metrics[axis.id].exact),axis:axis.id,value:metrics[axis.id].exact});
  const segments=[];for(let i=0;i<7;i++){const next=(i+1)%7;if(vertices[i]&&vertices[next])segments.push([vertices[i],vertices[next]])}
  const intervals=axes.flatMap((axis,index)=>{const metric=metrics[axis.id];return metric.exact===null&&metric.reviewed_families>0?
   [{axis:axis.id,index,lower:metric.lower,upper:metric.upper,from:point(index,metric.lower),to:point(index,metric.upper)}]:[]});
  return {vertices,segments,intervals,complete:vertices.every(Boolean)};
 }
 function prepare(data,compare){
  const profile=data?.mathematical_profile;
  if(data?.benchmark_version!=='1.1.0'||profile?.schema!=='math-gauge.mathematical-profile/v1'||!['0.1.0','0.2.0','0.3.0'].includes(profile.version)||profile.benchmark_version!=='1.1.0'||
   profile.reviewer_kind!=='ai'||profile.human_review!=='pending'||!Array.isArray(profile.axes)||profile.axes.length!==7||
   new Set(profile.axes.map(axis=>axis.id)).size!==7||profile.axes.some(axis=>!AXES.includes(axis.id)||!axis.label?.zh||!axis.label?.en||!axis.description?.zh||!axis.description?.en)||
   !Array.isArray(profile.models)||!Array.isArray(data.models))return null;
  const profiles=new Map(profile.models.map(model=>[model.id,model.metrics]));
  const models=data.models.filter(model=>profiles.has(model.id)&&profile.axes.every(axis=>validMetric(profiles.get(model.id)?.[axis.id])&&
    (profile.version==='0.1.0'||profiles.get(model.id)[axis.id].planned_families===35)))
   .map(model=>({...model,profile_metrics:profiles.get(model.id)})).sort(compare);
  return models.length?{profile,axes:profile.axes,models}:null;
 }
 function mount(win){
  const document=win.document,section=document.getElementById('mathematical-profile');if(!section)return null;
  const display=win.MG,data=display?.d||win.MGResults?.data;
  const compare=display?.compareScores?((a,b)=>display.compareScores(a,b,'partial')):((a,b)=>a.id.localeCompare(b.id));
  const prepared=prepare(data,compare);if(!prepared){section.removeAttribute('data-assessment-only');section.hidden=true;return null}section.hidden=false;
  const {models,axes,profile}=prepared,modern=profile.version!=='0.1.0',copy=modern?{...messages,...messagesV2}:messages,
   byId=new Map(models.map(model=>[model.id,model])),svgNS='http://www.w3.org/2000/svg';
  if(profile.version==='0.3.0')copy.coverage=[copy.coverage[0]+'要求完成度按整题及完整三轮自查验收，必需目标不以部分成果抵补。',copy.coverage[1]+' Requested completion requires every visible task goal and the entire three-round review trajectory; partial results cannot replace a required goal.'];
  const el=id=>document.getElementById('mathematical-profile-'+id),node=(tag,text,className)=>{const item=document.createElement(tag);if(text!==undefined)item.textContent=text;if(className)item.className=className;return item};
  const svg=(tag,attrs={})=>{const item=document.createElementNS(svgNS,tag);for(const [key,value]of Object.entries(attrs))item.setAttribute(key,String(value));return item};
  let lang='zh',selected=[],signature='',pinned=null,hovered=null,keyboard=null;
  const controls=new Map(),checkboxes=new Map(),series=new Map(),legendButtons=new Map();
  const t=key=>copy[key][lang==='en'?1:0],format=value=>value.toLocaleString(lang==='en'?'en-US':'zh-CN',{minimumFractionDigits:1,maximumFractionDigits:1});
  const coverage=metric=>metric.reviewed_families+'/'+metric.planned_families+' '+t(modern?'settled':'families');
  const settledCoverage=model=>{const counts=axes.map(axis=>model.profile_metrics[axis.id].reviewed_families),low=Math.min(...counts),high=Math.max(...counts);
   return (low===high?low:low+'–'+high)+'/35 '+t('settled')};
  const appendLogo=(target,model)=>{if(model.logo?.data_url){const image=node('img');image.src=model.logo.data_url;image.alt='';target.append(image)}};
  function marker(parent,shape,x,y,color){
   let mark;const r=3.5;
   if(shape==='circle'||shape==='ring')mark=svg('circle',{cx:x,cy:y,r,fill:shape==='ring'?'none':'white'});
   else if(shape==='square')mark=svg('rect',{x:x-r,y:y-r,width:2*r,height:2*r,fill:'white'});
   else if(shape==='triangle')mark=svg('path',{d:`M${x} ${y-r-1}L${x+r+1} ${y+r}L${x-r-1} ${y+r}Z`,fill:'white'});
   else if(shape==='diamond')mark=svg('path',{d:`M${x} ${y-r-1}L${x+r+1} ${y}L${x} ${y+r+1}L${x-r-1} ${y}Z`,fill:'white'});
   else if(shape==='pentagon')mark=svg('polygon',{points:Array.from({length:5},(_,i)=>{const a=-Math.PI/2+i*2*Math.PI/5;return (x+Math.cos(a)*(r+1))+','+(y+Math.sin(a)*(r+1))}).join(' '),fill:'white'});
   else if(shape==='hexagon')mark=svg('polygon',{points:Array.from({length:6},(_,i)=>{const a=i*Math.PI/3;return (x+Math.cos(a)*(r+1))+','+(y+Math.sin(a)*(r+1))}).join(' '),fill:'white'});
   else mark=svg('path',{d:shape==='plus'?`M${x-r-1} ${y}H${x+r+1}M${x} ${y-r-1}V${y+r+1}`:`M${x-r} ${y-r}L${x+r} ${y+r}M${x-r} ${y+r}L${x+r} ${y-r}`,fill:'none'});
   mark.setAttribute('class','mp-marker');mark.setAttribute('stroke',color);parent.append(mark);return mark;
  }
  function focus(){
   const active=hovered||keyboard||pinned;
   for(const [id,item]of series){item.setAttribute('data-focused',String(active===id));item.setAttribute('data-muted',String(!!active&&active!==id))}
   for(const [id,item]of legendButtons){item.setAttribute('data-focused',String(active===id));item.setAttribute('data-muted',String(!!active&&active!==id));item.setAttribute('aria-pressed',String(pinned===id))}
  }
  function focusEvents(target,id){target.addEventListener('pointerenter',()=>{hovered=id;focus()});target.addEventListener('pointerleave',()=>{hovered=null;focus()});
   target.addEventListener('focus',()=>{keyboard=id;focus()});target.addEventListener('blur',()=>{keyboard=null;focus()})}
  function labelLines(value){const words=value.split(/\s+/),lines=[];let current='';for(const word of words){if(current&&(current+' '+word).length>15){lines.push(current);current=word}else current=current?current+' '+word:word}if(current)lines.push(current);return lines.length>2?[lines[0],lines.slice(1).join(' ')]:lines}
  function renderChart(){
   series.clear();const chart=svg('svg',{viewBox:'0 0 520 460',role:'img','aria-labelledby':'mp-chart-title mp-chart-description'});
   const title=svg('title',{id:'mp-chart-title'});title.textContent=t('chart');const description=svg('desc',{id:'mp-chart-description'});description.textContent=t('note');chart.append(title,description);
   for(const tick of [20,40,60,80,100]){const ring=axes.map((_,index)=>point(index,tick));chart.append(svg('polygon',{points:ring.map(p=>p.x+','+p.y).join(' '),class:'mp-grid'+(tick===100?' mp-grid-outer':'')}));const label=svg('text',{x:270,y:point(0,tick).y+4,class:'mp-tick'});label.textContent=String(tick);chart.append(label)}
   const zero=svg('text',{x:267,y:237,class:'mp-tick'});zero.textContent='0';chart.append(zero);
   axes.forEach((axis,index)=>{const end=point(index,100);chart.append(svg('line',{x1:260,y1:225,x2:end.x,y2:end.y,class:'mp-axis'}));
    const a=-Math.PI/2+index*2*Math.PI/7,x=260+Math.cos(a)*193,y=225+Math.sin(a)*193,lines=labelLines(axis.label[lang]);
    const label=svg('text',{x,y:y-(lines.length-1)*8,class:'mp-axis-label'});const tip=svg('title');tip.textContent=axis.description[lang];label.append(tip);
    lines.forEach((line,i)=>{const span=svg('tspan',{x,dy:i?18:0});span.textContent=line;label.append(span)});chart.append(label);
   });
   for(const id of selected){const model=byId.get(id),style=styleFor(model),shape=geometry(axes,model.profile_metrics),group=svg('g',{class:'mp-series','data-profile-model':id,'data-profile-dash':style.dash,'data-profile-marker':style.marker});
    const d=shape.complete?'M'+shape.vertices.map(p=>p.x+' '+p.y).join('L')+'Z':shape.segments.map(([a,b])=>'M'+a.x+' '+a.y+'L'+b.x+' '+b.y).join('');
    if(d)group.append(svg('path',{class:'mp-model-line',d,stroke:style.color,'stroke-dasharray':style.dash,fill:shape.complete?style.color:'none','fill-opacity':selected.length>7?.012:.03}));
    for(const interval of shape.intervals){const line=svg('line',{class:'mp-interval',x1:interval.from.x,y1:interval.from.y,x2:interval.to.x,y2:interval.to.y,stroke:style.color,'stroke-dasharray':'2 3','data-profile-interval':interval.axis});
     const tip=svg('title');tip.textContent=model.label+' · '+axes[interval.index].label[lang]+' · '+t('range')+' '+format(interval.lower)+'–'+format(interval.upper);line.append(tip);group.append(line);
     const a=-Math.PI/2+interval.index*2*Math.PI/7,dx=Math.cos(a+Math.PI/2)*4,dy=Math.sin(a+Math.PI/2)*4;
     for(const p of [interval.from,interval.to])group.append(svg('line',{class:'mp-interval',x1:p.x-dx,y1:p.y-dy,x2:p.x+dx,y2:p.y+dy,stroke:style.color}));
    }
    shape.vertices.forEach((p,index)=>{if(!p)return;const mark=marker(group,style.marker,p.x,p.y,style.color);mark.setAttribute('data-profile-point',axes[index].id);mark.setAttribute('data-value',p.value);const tip=svg('title');tip.textContent=model.label+' · '+axes[index].label[lang]+' '+format(p.value)+' / 100 · '+coverage(model.profile_metrics[axes[index].id]);mark.append(tip)});
    focusEvents(group,id);series.set(id,group);chart.append(group);
   }el('chart').replaceChildren(chart);
  }
  function renderLegend(){legendButtons.clear();const items=[];
   for(const id of selected){const model=byId.get(id),style=styleFor(model),button=node('button',undefined,'mp-legend-button');button.type='button';button.title=model.label;button.setAttribute('aria-pressed',String(pinned===id));
    const sample=svg('svg',{viewBox:'0 0 40 18','aria-hidden':'true'});sample.append(svg('line',{x1:1,y1:9,x2:39,y2:9,stroke:style.color,'stroke-width':2,'stroke-dasharray':style.dash}));marker(sample,style.marker,20,9,style.color);button.append(sample);appendLogo(button,model);
    const identity=node('span'),name=node('span',model.label,'mp-legend-name'),known=axes.filter(axis=>model.profile_metrics[axis.id].exact!==null).length;
    identity.append(name,node('span',modern?settledCoverage(model):known+'/7 '+t('exactAxes'),'mp-legend-coverage'));button.append(identity);focusEvents(button,id);button.addEventListener('click',()=>{pinned=pinned===id?null:id;focus()});legendButtons.set(id,button);items.push(button);
   }el('legend').replaceChildren(...items);
  }
  function renderTable(){const table=el('values'),caption=node('caption',t('table'));caption.className='mp-sr-only';const head=node('thead'),row=node('tr');const first=node('th',t('model'));first.scope='col';row.append(first);
   axes.forEach(axis=>{const cell=node('th',axis.label[lang]);cell.scope='col';cell.title=axis.description[lang];row.append(cell)});head.append(row);const body=node('tbody');
   for(const id of selected){const model=byId.get(id),tr=node('tr'),name=node('th',model.label);name.scope='row';tr.append(name);
    axes.forEach(axis=>{const metric=model.profile_metrics[axis.id],cell=node('td');if(metric.exact===null){cell.className='mp-uncertain';cell.append(node('span',format(metric.lower)+'–'+format(metric.upper),'mp-axis-value'),node('small',t('confirmed')+' '+format(metric.confirmed),'mp-cell-confirmed'))}else cell.append(node('span',format(metric.exact),'mp-axis-value'));cell.append(node('small',coverage(metric),'mp-cell-coverage'));tr.append(cell)});body.append(tr);
   }table.replaceChildren(caption,head,body);
  }
  function renderMeanings(){el('meanings').hidden=!modern;if(!modern)return;
   el('meanings-title').textContent=t('meanings');el('meanings-scope').textContent=t('scope');
   el('meanings-list').replaceChildren(...axes.map(axis=>{const item=node('div',undefined,'mp-axis-definition'),description=node('dd',axis.description[lang]);
    if(axisContext[axis.id])description.append(node('span',axisContext[axis.id][lang==='en'?1:0],'mp-axis-context'));
    item.append(node('dt',axis.label[lang]),description);return item}));
  }
  function setSelection(ids){const chosen=new Set(ids);selected=models.filter(model=>chosen.has(model.id)).map(model=>model.id);if(!chosen.has(pinned))pinned=null;hovered=null;keyboard=null;
   win.history.replaceState(null,'',selectionUrl(win.location.href,selected));signature='';render()}
  function buildControls(){
   const target=el('controls');const items=[];for(const key of ['leader','brands','clear']){const button=node('button',undefined,'mp-preset');button.type='button';button.dataset.profilePreset=key;button.addEventListener('click',()=>setSelection(key==='leader'?[models[0].id]:key==='brands'?representatives(models,compare):[]));controls.set(key,button);items.push(button)}target.replaceChildren(...items);
   const groups=new Map();for(const model of models){const style=brand(model);if(!groups.has(style.key))groups.set(style.key,{style,models:[]});groups.get(style.key).models.push(model)}
   const choices=[];for(const {style,models:members}of groups.values()){const fieldset=node('fieldset',undefined,'mp-choice-group'),legend=node('legend',style.label);fieldset.append(legend);
    for(const model of members){const label=node('label',undefined,'mp-choice');label.style.setProperty('--mp-brand',style.color);label.title=model.label;const checkbox=node('input');checkbox.type='checkbox';checkbox.value=model.id;checkbox.setAttribute('aria-label',model.label);checkbox.addEventListener('change',()=>{const next=new Set(selected);if(checkbox.checked)next.add(model.id);else next.delete(model.id);setSelection(next)});checkboxes.set(model.id,checkbox);label.append(checkbox);appendLogo(label,model);label.append(node('span',model.label,'mp-choice-name'));fieldset.append(label)}choices.push(fieldset);
   }el('choices').replaceChildren(...choices);
  }
  function render(){lang=new URL(win.location.href).searchParams.get('lang')==='en'?'en':'zh';selected=readSelection(new URL(win.location.href).search,models,compare);const key=lang+'|'+selected.join(',');if(key===signature)return;signature=key;
   if(!selected.includes(pinned))pinned=null;if(!selected.includes(hovered))hovered=null;if(!selected.includes(keyboard))keyboard=null;
   for(const [id,message]of Object.entries({title:'title',description:'description',review:'review',note:'note','focus-note':'focus','values-title':'values','coverage-note':'coverage',empty:'empty','picker-title':'picker'}))el(id).textContent=t(message);
   for(const [key,button]of controls)button.textContent=t(key);for(const [id,checkbox]of checkboxes)checkbox.checked=selected.includes(id);
   el('count').textContent=t('selected')+' '+selected.length+t('of')+models.length+' '+t('models');el('empty').hidden=selected.length>0;
   renderMeanings();renderChart();renderLegend();renderTable();focus();
  }
  buildControls();render();win.addEventListener('mg:updated',render);win.addEventListener('popstate',render);
  return {render,setSelection,selected:()=>[...selected]};
 }
 return {AXES,brand,styleFor,representatives,readSelection,selectionUrl,validMetric,geometry,prepare,mount};
});
