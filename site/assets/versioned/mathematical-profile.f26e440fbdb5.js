/* Independent supplied mathematical axes. This UI never computes benchmark credit. */
(function(root,factory){
 const api=factory();
 if(typeof module==='object'&&module.exports)module.exports=api;
 if(root&&root.document){root.MGMathematicalProfile=api;api.mount(root)}
})(typeof window==='object'?window:null,()=>{
 'use strict';
 const AXES=['proof','fidelity','completion','discernment','initiative','depth','closure'];
 const BRANDS={openai:{label:'OpenAI',color:'#252525'},claude:{label:'Claude',color:'#d97757'},google:{label:'Google',color:'#45965d'},kimi:{label:'Kimi',color:'#3568d4'},deepseek:{label:'DeepSeek',color:'#4d6bfe'},glm:{label:'GLM',color:'#af7b15'}};
 const VARIANTS=[{dash:'',marker:'circle'},{dash:'7 3',marker:'square'},{dash:'2 3',marker:'triangle'},
  {dash:'12 4',marker:'diamond'},{dash:'9 3 2 3',marker:'plus'},{dash:'4 3 1 3',marker:'cross'},
  {dash:'15 3 2 3',marker:'hexagon'},{dash:'18 4 3 4',marker:'ring'},{dash:'6 3 6 3 1 3',marker:'pentagon'},
  {dash:'10 2 2 2 2 2',marker:'circle'},{dash:'18 3 2 3 2 3',marker:'diamond'}];
 const FALLBACK_VARIANTS=8;
 const STYLE_IDS={'astra-6.2-xhigh':10,'astra-6-max':0,'astra-6-xhigh':1,'sol-6.2-max':2,'sol-6.1-max':3,'sol-6.1-xhigh':4,
  'terra-6.1-max':5,'terra-6.1-xhigh':6,'dot-underlying-model-20261108':7,'sol-6.2-xhigh':8,'astra-6.2-max':9,
  'claude-opus-5.5-max':0,'claude-sonnet-5.5-max':1,'claude-opus-5.5-xhigh':2,'gemini-4-carbon-medium':0,
  'gemini-4-hydrogen-xhigh':1,'gemini-4-carbon-high':2,'gemini-4-argon':3,'gemini-3.8-flash-high':4};
 const messages={title:['数学画像','Mathematical profile'],description:['七个独立维度 · 每轴0–100','Seven independent dimensions · 0–100 per axis'],
  review:['AI评审 · 人工审核待完成','AI reviewed · Human review pending'],leader:['SMC榜首','SMC leader'],brands:['厂商首名','Vendor leaders'],clear:['清空','Clear'],
  brandHint:['按当前画像阶段的 SMC 选取最多五家厂商，各取首名。','Select the SMC leader from up to five vendors in the current profile stage.'],
  picker:['选择模型','Choose models'],selected:['已选','Selected'],of:['／',' / '],models:['个模型','models'],
  note:['逐轴比较；区间与断线表示证据缺口。','Compare individual axes. Intervals and gaps indicate missing evidence.'],
  focus:['悬停或聚焦模型可突出曲线；点击可固定。','Hover or focus a model to emphasize its curve; click to pin.'],
  values:['数值与家族覆盖','Values and family coverage'],coverage:['覆盖数按各轴统计，轴间不相加。画像不随顶部计分口径切换。','Coverage is reported per axis and is not added across axes. The profile is independent of the score selector.'],
  empty:['选择模型开始对照。','Choose models to compare.'],model:['模型','Model'],families:['家族','families'],confirmed:['已确认','Confirmed'],
  exactAxes:['轴完整计分','axes with exact scores'],range:['区间','Interval'],unknown:['证据未齐','Evidence incomplete'],
  chart:['七轴数学画像，固定0至100刻度','Seven-axis mathematical profile, fixed scale from 0 to 100'],table:['所选模型的独立数学维度及审核家族覆盖','Independent mathematical axes and reviewed-family coverage for selected models']};
 Object.assign(messages,{
  description:['六轴独立评审 · 严格完成度取主榜SMC · 每轴0–100','Six reviewed axes · strict completion uses official SMC · 0–100 per axis'],
  note:['已结算空白计0；可核实的截止前内容按实际论证评估，未交卷仍影响SMC。区间与断线表示真正未知。','Settled blanks receive 0. Verified cutoff work is assessed for its reasoning; nondelivery still affects SMC. Intervals and gaps indicate genuine unknowns.'],
  values:['数值与已结算范围','Values and settled coverage'],
  coverage:['六个独立评审轴各用35家族；严格完成度直接取规则选定答卷的正式SMC，沿用主榜权重与三轮自查规则。画像固定使用这组答卷，不随顶部显示口径切换。','The six reviewed axes each use 35 families. Strict completion copies the official SMC for the rule-selected answers, retaining its weights and three-round self-review rules. The profile stays bound to these answers and does not follow the display selector.'],
  settled:['家族已结算','families settled'],smc:['主榜SMC','Official SMC'],categories:['计分类别','scoring categories'],
  meanings:['七轴含义与范围','What the seven axes measure'],
  scope:['六轴覆盖39道初答与3轮自查、固定35家族，不限六道命题拓展题。SMC使用正式主榜权重，整条自查占10%；论证高档要求原题核心成立，局部成果不能抵补核心缺口。','Six axes cover 39 initial answers and 3 rounds of self review across 35 fixed families, beyond the six theorem extension tasks. SMC retains the official weights, including 10% for the whole review trajectory. High reasoning grades require the original core; partial results cannot compensate for an essential gap.']
 });
 const researchMessages={
  description:['能力与主动行为分开看 · 每轴0–100','Capability and unsolicited behavior, separately · 0–100 per axis'],
  meanings:['八轴含义与范围','What the eight axes measure'],
  chart:['八轴数学画像，固定0至100刻度','Eight-axis mathematical profile, fixed scale from 0 to 100'],
  coverage:['原有五个能力评审轴与研究主动性沿用35家族；开放研究能力独立使用五个共同开放家族；严格完成度取正式SMC。各轴覆盖分别展示，不按雷达面积排名。','The five original reviewed capability axes and initiative retain 35 families. Open research capability independently uses five common open-task families; strict completion copies official SMC. Coverage is separate per axis, and polygon area is not a ranking.'],
  scope:['开放研究能力看明确要求研究时实际交出的机制、条件和闭合成果；完成原题即可得最高档。末位研究主动性只观察未被要求时是否自行展开，不表示能力上限或越高越合适。其余轴与主分不变。','Open research capability evaluates mechanisms, justified conditions and closed results under an explicitly open request; completing the actual task can earn the highest grade. Initiative, shown last, describes unsolicited first-answer behavior, not a capability ceiling or automatic suitability. Other axes and main scores are unchanged.'],
  openResearch:['开放研究','Open research']
 };
 const axisContext={completion:['沿用主榜SMC的全部严格完成门槛，不另算家族平均完成率。','This retains every official SMC completion gate, without a separate family-average completion rate.'],
  initiative:['自发行为需要与问题忠实度一起看；不从主动程度推断能力上限。','Read this behavior together with problem fidelity; initiative does not determine a capability ceiling.'],
  depth:['衡量实际成立的机制、自然范围与结构解释。','This concerns mechanisms, natural scope and structural insight that have actually been established.'],
  closure:['衡量实际交付的实质结果是否证明完整、依赖齐全、范围明确。','This concerns complete proofs, dependencies and explicit scope for the substantive results actually delivered.']};
 Object.assign(messages,{continuation:['含续答','Include continuations'],
  continued:['续答','continued'],full:['满分率','full-score rate']});
 const finite=value=>typeof value==='number'&&Number.isFinite(value)&&value>=0&&value<=100;
 function brand(model){
  const name=String(model.logo?.label||'').toLowerCase().replace(/[^a-z0-9]/g,'');
  let key={openai:'openai',anthropic:'claude',claude:'claude',google:'google',kimi:'kimi',moonshot:'kimi',deepseek:'deepseek',zai:'glm',glm:'glm'}[name];
  if(!key)key=/^(astra|terra|sol|dot)-/.test(model.id)?'openai':/^claude-/.test(model.id)?'claude':/^gemini-/.test(model.id)?'google':/^kimi-/.test(model.id)?'kimi':/^deepseek-/.test(model.id)?'deepseek':/^glm-/.test(model.id)?'glm':null;
  return key?{key,...BRANDS[key]}:{key:'other-'+name,label:model.logo?.label||'Other',color:'#667085'};
 }
 function styleFor(model){
  let index=STYLE_IDS[model.id];
  if(index===undefined){let hash=0;for(const char of model.id)hash=(Math.imul(hash,31)+char.charCodeAt(0))>>>0;index=hash%FALLBACK_VARIANTS}
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
  metric.coverage&&Number.isInteger(metric.coverage.reviewed)&&Number.isInteger(metric.coverage.planned)&&metric.coverage.reviewed>=0&&metric.coverage.planned>=metric.coverage.reviewed}
 function point(index,value,count=7){const angle=-Math.PI/2+index*2*Math.PI/count;return {x:260+Math.cos(angle)*148*value/100,y:225+Math.sin(angle)*148*value/100}}
 function geometry(axes,metrics){
  const vertices=axes.map((axis,index)=>metrics[axis.id].exact===null?null:{...point(index,metrics[axis.id].exact,axes.length),axis:axis.id,value:metrics[axis.id].exact});
  const segments=[];for(let i=0;i<axes.length;i++){const next=(i+1)%axes.length;if(vertices[i]&&vertices[next])segments.push([vertices[i],vertices[next]])}
  const intervals=axes.flatMap((axis,index)=>{const metric=metrics[axis.id];return metric.exact===null&&metric.coverage.reviewed>0?
   [{axis:axis.id,index,lower:metric.lower,upper:metric.upper,from:point(index,metric.lower,axes.length),to:point(index,metric.upper,axes.length)}]:[]});
  return {vertices,segments,intervals,complete:vertices.every(Boolean)};
 }
 function stageFor(data,search=''){
  const requested=new URLSearchParams(search).get('profile-stage');
  return data?.benchmark_version==='1.2.0'&&requested!=='first'&&data?.mathematical_profile_revision?'revision':'first';
 }
 function prepare(data,compare,stage='first'){
  const revised=stage==='revision',corrected=!revised&&data?.benchmark_version==='1.2.0'&&data?.mathematical_profile_baseline,
   profile=revised?data?.mathematical_profile_revision:corrected||data?.mathematical_profile;
  if(!['1.1.0','1.2.0'].includes(data?.benchmark_version)||revised&&data.benchmark_version!=='1.2.0'||
   profile?.schema!==(revised?'math-gauge.mathematical-profile-revision/v1':corrected?'math-gauge.mathematical-profile-baseline/v1':'math-gauge.mathematical-profile/v1')||
   profile.version!==(revised||corrected?'0.1.0':'0.4.0')||profile.benchmark_version!==(revised||corrected?'1.2.0':'1.1.0')||
   profile.reviewer_kind!=='ai'||profile.human_review!=='pending'||!Array.isArray(profile.axes)||profile.axes.length!==7||
   new Set(profile.axes.map(axis=>axis.id)).size!==7||profile.axes.some(axis=>!AXES.includes(axis.id)||!axis.label?.zh||!axis.label?.en||!axis.description?.zh||!axis.description?.en)||
   !Array.isArray(profile.models)||!Array.isArray(data.models))return null;
  const profiles=new Map(profile.models.map(model=>[model.id,model.metrics]));
  const pool=!revised&&data.profile_models?.length?data.profile_models:data.models;
  let models=pool.filter(model=>model.presentation_eligibility?.ranked!==false&&profiles.has(model.id)&&profile.axes.every(axis=>validMetric(profiles.get(model.id)?.[axis.id])&&
    (profiles.get(model.id)[axis.id].coverage.planned===(axis.id==='completion'?8:35)&&profiles.get(model.id)[axis.id].coverage.unit===(axis.id==='completion'?'benchmark_subcategory':'mathematical_family'))))
   .map(model=>({...model,profile_metrics:profiles.get(model.id)})).sort(compare),axes=profile.axes;
  const capability=data.benchmark_version==='1.2.0'?data.open_research:null;
  if(capability){
   const valid=metric=>validMetric(metric)&&metric.coverage.unit==='open_research_family'&&metric.coverage.planned===5;
   if(capability.schema!=='math-gauge.open-research/v1'||capability.version!=='0.1.0'||capability.benchmark_version!=='1.2.0'||
    capability.axis?.id!=='open_research'||!capability.axis.label?.zh||!capability.axis.label?.en||
    !capability.axis.description?.zh||!capability.axis.description?.en||!Array.isArray(capability.models)||
    !valid(capability.pending_metric)||capability.models.some(row=>!valid(row.first)||row.revision!==null&&!valid(row.revision)))return null;
   const supplied=new Map(capability.models.map(row=>[row.id,row]));
   const behavior={...axes.find(axis=>axis.id==='initiative'),label:{zh:'研究主动性',en:'Research initiative'},description:{
    zh:'未被要求额外研究时，是否自行发现并验证值得追问的问题；这是首答中的自发行为观察，不能作为开放研究能力上限。',
    en:'Unsolicited, mathematically supported exploration in the first answer: a behavioral observation, not an estimate of open research capability.'}};
   axes=[...axes.filter(axis=>axis.id!=='initiative'),capability.axis,behavior];
   models=models.map(model=>({...model,profile_metrics:{...model.profile_metrics,
    open_research:supplied.get(model.id)?.[revised?'revision':'first']||capability.pending_metric}}));
  }
  return models.length?{profile,axes,models,stage}:null;
 }
 function mount(win){
  const document=win.document,section=document.getElementById('mathematical-profile');if(!section)return null;
  const display=win.MG,data=display?.d||win.MGResults?.data;
  const compare=display?.compareScores?((a,b)=>display.compareScores(a,b,'strict')):((a,b)=>a.id.localeCompare(b.id));
  let stage=stageFor(data,new URL(win.location.href).search),prepared=prepare(data,compare,stage);if(!prepared){section.removeAttribute('data-assessment-only');section.hidden=true;return null}section.hidden=false;
  let {models,axes,profile}=prepared;const copy=messages,byId=new Map(models.map(model=>[model.id,model])),svgNS='http://www.w3.org/2000/svg';
  section.removeAttribute('data-assessment-only');
  const el=id=>document.getElementById('mathematical-profile-'+id),node=(tag,text,className)=>{const item=document.createElement(tag);if(text!==undefined)item.textContent=text;if(className)item.className=className;return item};
  const stageSwitch=el('continuation'),picker=el('picker'),modelChoices=el('choices');
  const svg=(tag,attrs={})=>{const item=document.createElementNS(svgNS,tag);for(const [key,value]of Object.entries(attrs))item.setAttribute(key,String(value));return item};
  let lang='zh',selected=[],signature='',pinned=null,hovered=null,keyboard=null;
  const controls=new Map(),checkboxes=new Map(),series=new Map(),legendButtons=new Map();
  const t=key=>(axes.some(axis=>axis.id==='open_research')&&researchMessages[key]||copy[key])[lang==='en'?1:0],format=value=>value.toLocaleString(lang==='en'?'en-US':'zh-CN',{minimumFractionDigits:1,maximumFractionDigits:1});
  const coverage=metric=>metric.coverage.unit==='open_research_family'?t('openResearch')+' · '+metric.coverage.reviewed+'/'+metric.coverage.planned:metric.coverage.unit==='benchmark_subcategory'?t('smc')+' · '+metric.coverage.reviewed+'/'+metric.coverage.planned:metric.coverage.reviewed+'/'+metric.coverage.planned+' '+t('settled');
  const settledCoverage=model=>{const counts=axes.filter(axis=>!['completion','open_research'].includes(axis.id)).map(axis=>model.profile_metrics[axis.id].coverage.reviewed),low=Math.min(...counts),high=Math.max(...counts);
   return (low===high?low:low+'–'+high)+'/35 '+t('settled')+(model.profile_metrics.open_research?' · '+coverage(model.profile_metrics.open_research):'')};
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
   for(const tick of [20,40,60,80,100]){const center=point(0,0,axes.length),edge=point(0,tick,axes.length);chart.append(svg('circle',{cx:center.x,cy:center.y,r:center.y-edge.y,class:'mp-grid'+(tick===100?' mp-grid-outer':'')}));const label=svg('text',{x:270,y:point(0,tick,axes.length).y+4,class:'mp-tick'});label.textContent=String(tick);chart.append(label)}
   const zero=svg('text',{x:267,y:237,class:'mp-tick'});zero.textContent='0';chart.append(zero);
   axes.forEach((axis,index)=>{const end=point(index,100,axes.length);chart.append(svg('line',{x1:260,y1:225,x2:end.x,y2:end.y,class:'mp-axis'}));
    const a=-Math.PI/2+index*2*Math.PI/axes.length,x=260+Math.cos(a)*193,y=225+Math.sin(a)*193,lines=labelLines(axis.label[lang]);
    const label=svg('text',{x,y:y-(lines.length-1)*8,class:'mp-axis-label'});const tip=svg('title');tip.textContent=axis.description[lang];label.append(tip);
    lines.forEach((line,i)=>{const span=svg('tspan',{x,dy:i?18:0});span.textContent=line;label.append(span)});chart.append(label);
   });
   for(const id of selected){const model=byId.get(id),style=styleFor(model),shape=geometry(axes,model.profile_metrics),group=svg('g',{class:'mp-series','data-profile-model':id,'data-profile-dash':style.dash,'data-profile-marker':style.marker});
    const d=shape.complete?'M'+shape.vertices.map(p=>p.x+' '+p.y).join('L')+'Z':shape.segments.map(([a,b])=>'M'+a.x+' '+a.y+'L'+b.x+' '+b.y).join('');
    if(d)group.append(svg('path',{class:'mp-model-line',d,stroke:style.color,'stroke-dasharray':style.dash,fill:shape.complete?style.color:'none','fill-opacity':selected.length>7?.012:.03}));
    for(const interval of shape.intervals){const line=svg('line',{class:'mp-interval',x1:interval.from.x,y1:interval.from.y,x2:interval.to.x,y2:interval.to.y,stroke:style.color,'stroke-dasharray':'2 3','data-profile-interval':interval.axis});
     const tip=svg('title');tip.textContent=model.label+' · '+axes[interval.index].label[lang]+' · '+t('range')+' '+format(interval.lower)+'–'+format(interval.upper);line.append(tip);group.append(line);
     const a=-Math.PI/2+interval.index*2*Math.PI/axes.length,dx=Math.cos(a+Math.PI/2)*4,dy=Math.sin(a+Math.PI/2)*4;
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
    identity.append(name,node('span',settledCoverage(model),'mp-legend-coverage'));
    if(stage==='revision'&&model.neutral_revision_completion){const detail=model.neutral_revision_completion,rate=detail.full_rate?.exact,delta=model.neutral_revision_delta?.strict;
     identity.append(node('span',detail.selected+' '+t('continued')+' · '+t('full')+' '+(rate==null?'—':format(rate*100)+'%')+' · ΔSMC '+(delta==null?'—':(delta>0?'+':'')+format(delta)),'mp-revision-summary'))}
button.append(identity);focusEvents(button,id);button.addEventListener('click',()=>{pinned=pinned===id?null:id;focus()});legendButtons.set(id,button);items.push(button);
   }el('legend').replaceChildren(...items);
  }
  function renderTable(){const table=el('values'),caption=node('caption',t('table'));caption.className='mp-sr-only';const head=node('thead'),row=node('tr');const first=node('th',t('model'));first.scope='col';row.append(first);
   axes.forEach(axis=>{const cell=node('th',axis.label[lang]);cell.scope='col';cell.title=axis.description[lang];row.append(cell)});head.append(row);const body=node('tbody');
   for(const id of selected){const model=byId.get(id),tr=node('tr'),name=node('th',model.label);name.scope='row';tr.append(name);
    axes.forEach(axis=>{const metric=model.profile_metrics[axis.id],cell=node('td');if(metric.exact===null){cell.className='mp-uncertain';cell.append(node('span',format(metric.lower)+'–'+format(metric.upper),'mp-axis-value'),node('small',t('confirmed')+' '+format(metric.confirmed),'mp-cell-confirmed'))}else cell.append(node('span',format(metric.exact),'mp-axis-value'));cell.append(node('small',coverage(metric),'mp-cell-coverage'));tr.append(cell)});body.append(tr);
   }table.replaceChildren(caption,head,body);
  }
  function renderMeanings(){el('meanings').hidden=false;
   el('meanings-title').textContent=t('meanings');el('meanings-scope').textContent=t('scope');
   el('meanings-list').replaceChildren(...axes.map(axis=>{const item=node('div',undefined,'mp-axis-definition'),description=node('dd',axis.description[lang]);
    if(axisContext[axis.id])description.append(node('span',axisContext[axis.id][lang==='en'?1:0],'mp-axis-context'));
    item.append(node('dt',axis.label[lang]),description);return item}));
  }
  function setSelection(ids){const chosen=new Set(ids);selected=models.filter(model=>chosen.has(model.id)).map(model=>model.id);if(!chosen.has(pinned))pinned=null;hovered=null;keyboard=null;
   win.history.replaceState(null,'',selectionUrl(win.location.href,selected));signature='';render()}
  function buildControls(){
   controls.clear();checkboxes.clear();const target=el('controls');const items=[];for(const key of ['leader','brands','clear']){const button=node('button',undefined,'mp-preset');button.type='button';button.dataset.profilePreset=key;button.addEventListener('click',()=>setSelection(key==='leader'?[models[0].id]:key==='brands'?representatives(models,compare):[]));controls.set(key,button);items.push(button)}target.replaceChildren(...items);
   const groups=new Map();for(const model of models){const style=brand(model);if(!groups.has(style.key))groups.set(style.key,{style,models:[]});groups.get(style.key).models.push(model)}
   const choices=[];for(const {style,models:members}of groups.values()){const fieldset=node('fieldset',undefined,'mp-choice-group'),legend=node('legend',style.label);fieldset.append(legend);
    for(const model of members){const label=node('label',undefined,'mp-choice');label.style.setProperty('--mp-brand',style.color);label.title=model.label;const checkbox=node('input');checkbox.type='checkbox';checkbox.value=model.id;checkbox.setAttribute('aria-label',model.label);checkbox.addEventListener('change',()=>{const next=new Set(selected);if(checkbox.checked)next.add(model.id);else next.delete(model.id);setSelection(next)});checkboxes.set(model.id,checkbox);label.append(checkbox);appendLogo(label,model);label.append(node('span',model.label,'mp-choice-name'));fieldset.append(label)}choices.push(fieldset);
   }modelChoices.replaceChildren(...choices);
  }
  function render(){
   const query=new URL(win.location.href).search,nextStage=stageFor(data,query);
   if(nextStage!==stage){const next=prepare(data,compare,nextStage);if(next){stage=nextStage;({models,axes,profile}=next);byId.clear();for(const model of models)byId.set(model.id,model);pinned=null;hovered=null;keyboard=null;buildControls();signature=''}}
   stageSwitch.checked=stage==='revision';
   lang=new URLSearchParams(query).get('lang')==='en'?'en':'zh';selected=readSelection(query,models,compare);
   const key=stage+'|'+lang+'|'+selected.join(',');if(key===signature)return;signature=key;
   if(!selected.includes(pinned))pinned=null;if(!selected.includes(hovered))hovered=null;if(!selected.includes(keyboard))keyboard=null;
   for(const [id,message]of Object.entries({title:'title',description:'description',review:'review',note:'note','focus-note':'focus','values-title':'values','coverage-note':'coverage',empty:'empty','picker-title':'picker'}))el(id).textContent=t(message);
   el('continuation-label').textContent=t('continuation');
   for(const [key,button]of controls)button.textContent=t(key);for(const [id,checkbox]of checkboxes)checkbox.checked=selected.includes(id);
   controls.get('brands').title=t('brandHint');
   el('count').textContent=selected.length+'/'+models.length;
   picker.setAttribute('aria-label',t('picker')+' · '+t('selected')+' '+selected.length+t('of')+models.length+' '+t('models'));
   el('empty').hidden=selected.length>0;
   renderMeanings();renderChart();renderLegend();renderTable();focus();
  }
  el('continuation-control').hidden=data.benchmark_version!=='1.2.0'||!data.mathematical_profile_revision;
  stageSwitch.addEventListener('change',()=>{
   const url=new URL(win.location.href);
   url.searchParams.set('profile-stage',stageSwitch.checked?'revision':'first');
   win.history.replaceState(null,'',url.href);render();
  });
  picker.addEventListener('click',()=>{
   modelChoices.hidden=!modelChoices.hidden;
   picker.setAttribute('aria-expanded',String(!modelChoices.hidden));
  });
  buildControls();render();win.addEventListener('mg:updated',render);win.addEventListener('popstate',render);
  return {render,setSelection,selected:()=>[...selected],stage:()=>stage};
 }
 return {AXES,brand,styleFor,representatives,readSelection,selectionUrl,validMetric,geometry,stageFor,prepare,mount};
});
