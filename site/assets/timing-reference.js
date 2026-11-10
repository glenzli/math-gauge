/* Descriptive clocks only; mathematical scores and weights stay source-owned. */
(() => {
 'use strict';
 const root=document.getElementById('answer-times');if(!root)return;
 const data=JSON.parse(document.getElementById('timing-reference-data').textContent);
 const keys=['lean','weighted','median'],validSort=key=>keys.includes(key)?key:data.default_sort;
 const state={lang:'zh',sort:validSort(new URLSearchParams(location.search).get('sort-time'))};
 const messages={
  title:['答题耗时参考','Answer-time reference'],subtitle:['整章形式化与日常五道典型题的耗时比较。单位：分钟。','Whole-chapter formalization and five shared everyday tasks. Minutes.'],
  sort:['排序','Sort'],weighted:['加权均值','Weighted mean'],median:['中位数','Median'],lean:['整章形式化','Whole-chapter formalization'],leanSort:['整章形式化','Whole chapter'],model:['模型','Model'],unit:['分钟','min'],leanShort:['整章','Chapter'],weightedShort:['均值','Mean'],medianShort:['中位','Median'],everyday:['日常','Everyday'],
  chart:['当前采用答卷的三项耗时比较','Three timing measures for the selected answers'],solid:['实心：正常交卷','Solid: normal delivery'],striped:['斜纹：含未正常交卷','Striped: includes non-delivery'],
  scales:['三项共用分钟刻度，所有模型统一。','All three measures share one time scale across models.'],
  note:['实际运行耗时，含工具和等待；未正常交卷的已知耗时也计入。Harness、网络与硬件各异，仅供参考。','Observed execution time, including tools and waits. Known non-delivery times are included. Harness, network and hardware vary; practical reference only.'],
  method:['典型题、权重与来源','Sample, weights & sources'],selection:['日常五题分别代表书面论证、论证审阅、背景核查、命题拓展和想法手稿化。加权均值沿用五类现有权重 25:10:10:10:10，中位数直接取五题的中位。','Five everyday tasks cover written argument, argument review, background check, theorem extension and manuscript completion. The mean uses their existing 25:10:10:10:10 weights; the median is over the five durations.'],
  missing:['五题计时须齐全才给出汇总，缺少的整章形式化计时留空。自查和额外重试不在本表内。','All five clocks are required for a summary; missing chapter-formalization clocks stay blank. Self-checks and extra retries are separate.'],
  other:['仅比较当前采用答卷，已废弃的重跑不展示、不计入汇总。Gemini 3.8 合计原始运行与同工程续作，两段间等待不计入。','Only selected answers are compared; abandoned reruns are excluded from this display and its summaries. Gemini 3.8 sums its initial run and continuation of the same engineering, excluding the pause between them.'],
  doc:['完整计时说明 ↗','Full timing documentation ↗'],passed:['整题达标','SMC passed'],incomplete:['未完全达标','SMC not met'],delivered:['已交卷','Delivered'],nondelivery:['未正常交卷','No normal final answer'],notrun:['未运行','Not run'],missingClock:['无计时','No timing'],timed:['计时','Timed'],includes:['含','Includes']
 };
 const el=id=>document.getElementById(id),t=key=>messages[key][state.lang==='en'?1:0];
 const node=(tag,text,cls)=>{const n=document.createElement(tag);if(text!=null)n.textContent=text;if(cls)n.className=cls;return n};
 const number=(value,digits=1)=>value.toLocaleString(state.lang==='en'?'en-US':'zh-CN',{minimumFractionDigits:digits,maximumFractionDigits:digits});
 const duration=seconds=>seconds==null?'—':number(seconds/60);
 function value(model,key){return key==='lean'?model.summaries['MG-C003'].median_seconds:model.summaries.daily[key==='weighted'?'weighted_mean_seconds':'median_seconds']}
 function scale(values){
  const maximum=Math.max(1,...values.filter(v=>v!=null).map(v=>v/60)),rough=maximum/4,power=10**Math.floor(Math.log10(rough));
  const step=([1,2,2.5,5,10].find(v=>v*power>=rough)||10)*power;
  const limit=Math.ceil(maximum/step)*step;
  return {maximum:limit,step,ticks:Array.from({length:Math.round(limit/step)+1},(_,i)=>i*step)};
 }
 function axis(axis){
  const ticks=node('div',null,'timing-axis');ticks.setAttribute('aria-hidden','true');
  axis.ticks.forEach(v=>{const tick=node('span',v.toLocaleString(state.lang==='en'?'en-US':'zh-CN',{maximumFractionDigits:2}));tick.style.left=(v/axis.maximum*100)+'%';ticks.append(tick)});
  return ticks;
 }
 function status(model,key,seconds){
  if(key!=='lean'){
   const daily=model.summaries.daily;
   if(seconds==null)return {text:t('timed')+' '+daily.timed+'/'+daily.planned,failed:false};
   return {text:daily.nondelivery?t('includes')+' '+daily.nondelivery+'/'+daily.planned+' '+t('nondelivery'):'',failed:daily.nondelivery>0};
  }
  const row=model.rows.find(r=>r.case_id==='MG-C003');
  if(row.delivery_status==='not_run')return {text:t('notrun'),failed:false};
  if(row.delivery_status==='delivery_failed')return {text:t('nondelivery'),failed:true};
  if(seconds==null)return {text:t('missingClock'),failed:false};
  return {text:row.strict_pass===true?t('passed'):row.strict_pass===false?t('incomplete'):t('delivered'),failed:false,passed:row.strict_pass===true};
 }
 function render(){
  const params=new URLSearchParams(location.search);state.lang=params.get('lang')==='en'?'en':'zh';state.sort=validSort(params.get('sort-time'));
  root.querySelectorAll('[data-timing-t]').forEach(n=>n.textContent=t(n.dataset.timingT));
  document.querySelectorAll('[data-timing-language]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.timingLanguage===state.lang)));
  if(document.body.classList.contains('timing-page')){document.documentElement.lang=state.lang==='en'?'en':'zh-CN';document.title=t('title')+' · Math Gauge'}
  el('timing-sort').setAttribute('aria-label',t('title')+' · '+t('sort'));
  root.querySelectorAll('[data-timing-sort]').forEach(button=>button.setAttribute('aria-pressed',String(button.dataset.timingSort===state.sort)));
  const shared=scale(data.models.flatMap(model=>keys.map(key=>value(model,key))));
  const ordered=[...data.models].sort((a,b)=>{const x=value(a,state.sort),y=value(b,state.sort);return x==null?(y==null?a.id.localeCompare(b.id):1):y==null?-1:x-y||a.id.localeCompare(b.id)});
  const chart=el('timing-chart');chart.setAttribute('aria-label',t('chart'));
  const caption=node('div',null,'timing-chart-caption'),legend=node('div',null,'timing-series-legend');
  keys.forEach(key=>{const item=node('span'),swatch=node('i',null,'timing-tone-swatch '+key);swatch.setAttribute('aria-hidden','true');item.append(swatch,node('span',t(key)));legend.append(item)});
  caption.append(node('span',t('unit')),legend);
  const sharedAxis=axis(shared),body=node('div',null,'timing-chart-body');
  ordered.forEach(model=>{
   const row=node('div',null,'timing-row');row.dataset.timingModel=model.id;row.style.setProperty('--timing-brand',model.theme.color);row.setAttribute('role','group');row.setAttribute('aria-label',model.label);
   const identity=node('div',null,'timing-model'),img=node('img');img.src=model.logo.data_url;img.alt=model.logo.label;
   const name=node('div'),link=node('a',model.label);link.href=data.link_prefix+'models/'+encodeURIComponent(model.id)+'/index.html?lang='+state.lang+'&score=partial';
   name.append(link,node('span',model.harness,'timing-harness'));
   const chapterStatus=status(model,'lean',value(model,'lean')),dailyStatus=status(model,'weighted',value(model,'weighted'));
   const notes=node('div',null,'timing-run-notes');notes.append(node('span',t('leanShort')+' · '+chapterStatus.text,chapterStatus.failed?'fail':chapterStatus.passed?'pass':''));
   if(dailyStatus.text)notes.append(node('span',t('everyday')+' · '+dailyStatus.text,dailyStatus.failed?'fail':''));
   name.append(notes);identity.append(img,name);row.append(identity);
   const bars=node('div',null,'timing-bars');
   keys.forEach(key=>{
    const seconds=value(model,key),info=status(model,key,seconds),cell=node('div',null,'timing-cell timing-'+key+(key===state.sort?' timing-primary':'')+(info.failed?' timing-unfinished':''));
    cell.dataset.metric=key;cell.dataset.scaleMax=String(shared.maximum);cell.dataset.seconds=seconds==null?'':String(seconds);cell.setAttribute('role','group');cell.setAttribute('aria-label',t(key));
    const track=node('div',null,'timing-track');track.style.setProperty('--timing-grid-step',(shared.step/shared.maximum*100)+'%');track.setAttribute('aria-hidden','true');
    if(seconds!=null){const fill=node('div',null,'timing-fill');fill.style.width=(seconds/60/shared.maximum*100)+'%';track.append(fill)}
    const readout=node('span',null,'timing-readout');readout.append(node('small',t(key+'Short')),node('span',duration(seconds),'timing-number'));
    cell.append(track,readout);bars.append(cell);
   });row.append(bars);body.append(row);
  });chart.replaceChildren(caption,sharedAxis,body);
  const weightSum=Object.values(data.daily_weights).reduce((a,b)=>a+b,0);el('timing-sample-list').replaceChildren(...data.cases.filter(c=>data.daily_case_ids.includes(c.id)).map(c=>node('li',c.id+' · '+c.title[state.lang]+' · '+(data.daily_weights[c.id]/weightSum*100).toFixed(1)+'%')));
  el('timing-doc').href=data.link_prefix+'../docs/answer-timings.md';el('timing-json').href=data.data_link;
 }
 root.querySelectorAll('[data-timing-sort]').forEach(button=>button.addEventListener('click',()=>{const u=new URL(location.href);u.searchParams.set('sort-time',button.dataset.timingSort);history.replaceState(null,'',u);render()}));
 document.querySelectorAll('[data-timing-language]').forEach(b=>b.onclick=()=>{const u=new URL(location.href);u.searchParams.set('lang',b.dataset.timingLanguage);history.replaceState(null,'',u);render()});
 window.addEventListener('mg:updated',render);window.addEventListener('popstate',render);render();
})();
