/* Total cost observations; scores and timing samples come from their existing owners. */
(() => {
 'use strict';
 const source=document.getElementById('cost-reference-data');if(!source)return;
 const data=JSON.parse(source.textContent),board=document.getElementById('cost-board'),plot=document.getElementById('cost-plot');
 const ns='http://www.w3.org/2000/svg',modes=['capability','partial','strict'];
 const labels={
  title:['总成本参考','Total cost reference'],subtitle:['当前留档答卷 · 美元','Retained attempts · USD'],
  method:['计算口径 ↗','Method ↗'],scope:['每题只计留档采用的一次作答；全部未交卷时取最后留档尝试。三轮固定自查各计一次，其余重试不计。','One retained attempt per task; if none delivered, use the last retained failed attempt. Each prescribed self-check round is included once. Other retries are excluded.'],
  priceNote:['Dot 使用2026-11-08测试时订阅附赠的独立额度，额外费用 $0；有可核实单价的型号按公开 API 价格折算并计缓存优惠。DeepSeek 统一采用官方峰价，保留缓存优惠。','Dot used a separate subscription-bundled allowance on 2026-11-08, with $0 additional cost; models with verified tariffs use public API reference prices with cache discounts. DeepSeek uses uniform official peak rates, retaining cache discounts.'],
  argonPriceLabel:['Argon 限时五折：','Argon introductory 50% discount: '],
  argonPriceNote:['当前 $33.84 按截至2026-11-30的优惠价计算；2026-12-01起单价翻倍，同一用量约 $67.67。','The $33.84 total uses the introductory rates through November 30, 2026. Unit prices double from December 1; the same usage would cost about $67.67.'],
  officialPrice:['官方定价 ↗','Official pricing ↗'],
  costSubtitle:['横轴为总成本（美元，从0开始的线性刻度），纵轴为{score}。越靠左上越好。','X: total cost in USD (linear scale starting at zero); Y: {score}. Upper left is better.'],
  timeSubtitle:['横轴为日常五题加权耗时（分钟），纵轴为{score}。越靠左上越好。','X: weighted time for the five everyday tasks (minutes); Y: {score}. Upper left is better.'],
  costAxisButton:['成本—成绩','Cost vs score'],timeAxisButton:['耗时—成绩','Time vs score'],estimated:['估算','Estimated'],frontier:['完整数据的 Pareto 前沿','Pareto frontier of complete data'],
  fullSubmission:['完整交卷（39/39）','All 39 answers delivered normally'],partialSubmission:['未完整交卷','Incomplete normal submission'],normalSubmissions:['正常交卷','Normal submissions'],
  submissionNote:['实心表示39题均正常交卷，空心表示正常交卷不足39题；强制收取的内容不计为正常交卷。','Solid points mean all 39 tasks have normal final submissions. Hollow points have fewer than 39; forcibly collected content is excluded.'],
  chartData:['查看图表数据','View chart data'],model:['模型','Model'],total:['总成本','Total cost'],timeLabel:['典型题耗时 / 分钟','Typical time / min'],unknown:['未取得成本','Cost unavailable'],partial:['用量不齐','Usage incomplete'],estimatedNote:['含用量估算','Includes imputed usage'],
  costAxis:['总成本 / 美元（线性刻度）','Total cost / USD (linear scale)'],timeAxis:['典型题耗时 / 分钟','Typical task time / min'],
  range:['估算范围','Scenario range'],minutes:['分钟','min'],
  costNote:['实线连接费用已核对且具有完整成绩的 Pareto 前沿模型。','The line connects Pareto-frontier models with verified costs and complete evaluations.'],
  timeNote:['实线按同一组日常五题的已记录加权耗时与完整数学成绩计算。耗时包含工具和等待。','The time frontier uses recorded weighted time for the same five everyday tasks and completed mathematical evaluations. Time includes tools and waiting.'],
  noData:['没有足够的数据绘图。','Insufficient data to plot.'],score:['成绩','Score'],lowerBound:['仅有成本下限','Cost lower bound only'],
  highlight:['高亮','Highlight'],
  clearSelection:['清除高亮','Clear highlights'],pinLabel:['固定高亮','Pin highlight'],unpinLabel:['取消高亮','Unpin highlight'],
  selectionCount:['已固定 {count} 个','{count} pinned'],
  interactionHint:['悬停查看详情，点击点或名称可固定高亮。','Hover for details; click a point or name to pin its highlight.']
 };
 const node=(tag,text,cls)=>{const n=document.createElement(tag);if(text!=null)n.textContent=text;if(cls)n.className=cls;return n};
 const svg=(tag,attrs={},text)=>{const n=document.createElementNS(ns,tag);Object.entries(attrs).forEach(([k,v])=>n.setAttribute(k,String(v)));if(text!=null)n.textContent=text;return n};
 let lang='zh',axis='cost',mode='partial',selected=new Set();
 const t=key=>labels[key][lang==='en'?1:0],locale=()=>lang==='en'?'en-US':'zh-CN';
 const money=v=>'$'+v.toLocaleString(locale(),{minimumFractionDigits:2,maximumFractionDigits:2});
 const amount=m=>m.total_usd??(m.status==='partial'?m.known_usd:null);
 const costText=m=>amount(m)==null?'—':(m.status==='estimated'?'≈ ':m.status==='partial'?'≥ ':'')+money(amount(m));
 const brand=m=>m.theme.color||m.theme.ink||'#556f98';
 function link(m){const a=node('a',m.label);a.href='models/'+encodeURIComponent(m.model_id)+'/index.html?lang='+lang+'&score='+mode;return a}
 function icon(m){const img=node('img');img.src=m.logo.data_url;img.alt='';return img}
 function renderBoard(){
  const ranked=data.models.filter(m=>m.total_usd!=null).sort((a,b)=>a.total_usd-b.total_usd||a.model_id.localeCompare(b.model_id));
  const maximum=Math.max(1,...ranked.map(m=>m.total_usd));board.replaceChildren();
  ranked.forEach((m,index)=>{
   const row=node('div',null,'cost-row '+m.status);row.setAttribute('role','listitem');row.dataset.costModel=m.model_id;row.style.setProperty('--cost-brand',brand(m));
   const identity=node('div',null,'cost-identity');identity.append(node('span',String(index+1),'cost-rank'),icon(m),link(m));
   const track=node('div',null,'cost-track');track.setAttribute('aria-hidden','true');const fill=node('div',null,'cost-fill');fill.style.width=(m.total_usd===0?0:Math.max(.25,m.total_usd/maximum*100))+'%';fill.hidden=m.total_usd===0;track.append(fill);
   const readout=node('span',costText(m),'cost-readout');if(m.estimate_range_usd)readout.title=t('range')+' '+m.estimate_range_usd.map(money).join('–');
   row.append(identity,track,readout);board.append(row);
  });
  const missing=document.getElementById('cost-unavailable');missing.replaceChildren();
  data.models.filter(m=>m.total_usd==null).forEach(m=>{const item=node('span',null,'cost-unavailable-item');item.append(icon(m),link(m),node('strong',costText(m)),node('span',m.status==='partial'?t('partial'):t('unknown')));missing.append(item)});
 }
 function renderPlot(){
  const W=1040,H=520,left=70,right=955,top=38,bottom=438;
  plot.replaceChildren(svg('title',{id:'cost-svg-title'},t(axis==='cost'?'costAxisButton':'timeAxisButton')),
   svg('desc',{id:'cost-svg-desc'},t(axis==='cost'?'costNote':'timeNote')+' '+t('submissionNote')));
  const rows=data.models.filter(m=>axis==='cost'?amount(m)!=null:m.seconds!=null);
  if(!rows.length){plot.append(svg('text',{x:W/2,y:H/2,'text-anchor':'middle'},t('noData')));return}
  let x,ticks;
  if(axis==='cost'){
   const high=Math.max(...rows.map(m=>m.estimate_range_usd?.[1]??amount(m)),1);
   const base=10**Math.floor(Math.log10(high/5)),step=[1,2,5,10].find(n=>n*base>=high/5)*base;
   const limit=Math.ceil(high/step)*step;
   x=v=>left+v/limit*(right-left);
   ticks=Array.from({length:Math.round(limit/step)+1},(_,i)=>i*step);
  }else{
   const max=Math.max(...rows.map(m=>m.seconds/60),1),step=max>100?30:max>40?10:max>15?5:2,limit=Math.ceil(max/step)*step;
   x=v=>left+v/limit*(right-left);ticks=Array.from({length:Math.round(limit/step)+1},(_,i)=>i*step);
  }
  const y=v=>bottom-Math.max(0,Math.min(100,v))/100*(bottom-top);
  for(let value=0;value<=100;value+=20){plot.append(svg('line',{x1:left,y1:y(value),x2:right,y2:y(value),class:'cost-grid'}),svg('text',{x:left-14,y:y(value)+4,'text-anchor':'end',class:'cost-axis-text'},value))}
  ticks.forEach(value=>{plot.append(svg('line',{x1:x(value),y1:top,x2:x(value),y2:bottom,class:'cost-grid'}),svg('text',{x:x(value),y:bottom+24,'text-anchor':'middle',class:'cost-axis-text'},axis==='cost'?'$'+value.toLocaleString(locale()):value))});
  plot.append(svg('text',{x:left,y:19,class:'cost-axis-title'},({capability:'MC',partial:'RMC',strict:'SMC'})[mode]+' / 100'),svg('text',{x:(left+right)/2,y:493,'text-anchor':'middle',class:'cost-axis-title'},t(axis==='cost'?'costAxis':'timeAxis')));
  const frontier=new Set(data.frontiers[mode][axis]),byId=Object.fromEntries(rows.map(m=>[m.model_id,m]));
  const fp=data.frontiers[mode][axis].filter(id=>byId[id]).map(id=>byId[id]);
  if(fp.length>1)plot.append(svg('path',{d:fp.map((m,i)=>(i?'L':'M')+x(axis==='cost'?amount(m):m.seconds/60)+','+y(m.scores[mode].value)).join(' '),class:'cost-frontier-path'}));
  // Geometry is independent of score projection; only labels may move.
  const connectorLayer=svg('g',{class:'cost-connectors','aria-hidden':'true'}),pointLayer=svg('g'),labelLayer=svg('g');
  plot.append(connectorLayer,pointLayer,labelLayer);
  const placed=[],states=new Map(),tooltip=document.getElementById('cost-tooltip'),wrap=plot.parentElement;
  const screenScale=plot.getBoundingClientRect().width/W||1,fontSize=Math.max(12,Math.min(16,12/screenScale)),labelPadding=3;
  rows.forEach((m,index)=>{
   const value=axis==='cost'?amount(m):m.seconds/60,cx=x(value),cy=y(m.scores[mode].value),r=3.5;
   const resourceStatus=axis==='cost'?m.status:'observed';
   const complete=m.answer_delivery.complete===true,delivery=t('normalSubmissions')+' '+(m.answer_delivery.active_final??'—')+'/39';
   if(axis==='cost'&&m.estimate_range_usd)pointLayer.append(svg('line',{x1:x(m.estimate_range_usd[0]),y1:cy,x2:x(m.estimate_range_usd[1]),y2:cy,class:'cost-error-bar',stroke:brand(m)}));
   const resourceText=axis==='cost'?costText(m):(m.seconds/60).toFixed(1)+' '+t('minutes');
   const p=svg('circle',{cx,cy,r,class:'cost-model-point '+resourceStatus,
    fill:complete?brand(m):'#fff',stroke:brand(m),tabindex:0,role:'button','data-cost-point':m.model_id,
    'aria-pressed':selected.has(m.model_id),
    'aria-label':m.label+' · '+resourceText+' · '+({capability:'MC',partial:'RMC',strict:'SMC'})[mode]+' '+m.scores[mode].value.toFixed(2)+' · '+delivery});
   if(frontier.has(m.model_id))p.setAttribute('stroke-width','3');
   const target=svg('g',{class:'cost-model-target','data-cost-model':m.model_id});
   const halo=svg('circle',{cx,cy,r:7,class:'cost-point-halo',fill:'none',stroke:brand(m),'aria-hidden':'true'});
   target.append(halo,p);pointLayer.append(target);
   if(axis==='cost'&&m.status==='partial')target.append(svg('path',{d:`M${cx+r+4},${cy}h18m-5,-4l5,4l-5,4`,fill:'none',stroke:brand(m),'stroke-width':1.5}));
   const text=svg('text',{class:'cost-label',fill:brand(m),'font-size':fontSize,visibility:'hidden'},m.label);
   text.style.fontSize=fontSize+'px';labelLayer.append(text);
   const measured=text.getBBox();text.removeAttribute('visibility');
   const label=svg('g',{class:'cost-label-target','data-cost-label':m.model_id,'data-cost-model':m.model_id,role:'button','aria-label':m.label,'aria-pressed':selected.has(m.model_id)});
   const hit=svg('rect',{fill:'transparent',rx:3});label.append(hit,text);labelLayer.append(label);
   const line=svg('line',{class:'cost-label-connector',stroke:brand(m),'data-cost-model':m.model_id,'data-cost-connector':m.model_id});connectorLayer.append(line);
   const isolation=Math.min(...rows.filter(o=>o!==m).map(o=>Math.hypot(cx-x(axis==='cost'?amount(o):o.seconds/60),cy-y(o.scores[mode].value))),1000);
   placed.push({id:m.model_id,cx,cy,r,width:measured.width+labelPadding*2,height:measured.height+labelPadding*2,
    priority:(frontier.has(m.model_id)?10000:0)+isolation,required:selected.has(m.model_id)});
   states.set(m.model_id,{m,p,target,label,text,hit,line,measured,delivery});
  });
  const segments=fp.slice(1).map((m,i)=>({x1:x(axis==='cost'?amount(fp[i]):fp[i].seconds/60),y1:y(fp[i].scores[mode].value),x2:x(axis==='cost'?amount(m):m.seconds/60),y2:y(m.scores[mode].value)}));
  const layouts=globalThis.MathGaugeCostLabels.layout(placed,{bounds:{left:left-8,top:top-8,right:W-8,bottom:bottom-4},
   mode:'all',padding:4,lines:segments});
  layouts.forEach(layout=>{
   const state=states.get(layout.id);state.layout=layout;
   state.text.setAttribute('x',layout.x+labelPadding-state.measured.x);state.text.setAttribute('y',layout.y+labelPadding-state.measured.y);
   for(const [attr,value] of Object.entries({x:layout.x,y:layout.y,width:layout.width,height:layout.height}))state.hit.setAttribute(attr,value);
   for(const attr of ['x1','y1','x2','y2'])state.line.setAttribute(attr,layout.connector[attr]);
   state.label.dataset.costVisible=String(layout.visible);
  });
  let hoverId=null,focusId=null;
  function highlight(id,event){
   plot.classList.toggle('cost-has-active',id!=null);
   states.forEach((state,key)=>{
    const active=key===id,pinned=selected.has(key);
    for(const part of [state.target,state.label,state.line]){part.classList.toggle('cost-active',active);part.classList.toggle('cost-pinned',pinned)}
    state.label.style.display='';state.line.style.display=active||pinned||state.layout.connector.needed?'':'none';
   });
   if(id==null){tooltip.hidden=true;return}
   const state=states.get(id),m=state.m,score=({capability:'MC',partial:'RMC',strict:'SMC'})[mode]+' '+m.scores[mode].value.toFixed(2);
   tooltip.textContent=m.label+'\n'+state.delivery+'\n'+t('total')+' '+costText(m)+'\n'+score+(m.seconds==null?'':'\n'+t('timeLabel')+' '+(m.seconds/60).toFixed(1))+
    (m.status==='estimated'?'\n'+t('range')+' '+m.estimate_range_usd.map(money).join('–'):m.status==='partial'?'\n'+t('lowerBound'):'');
   tooltip.hidden=false;
   const box=wrap.getBoundingClientRect(),pbox=state.p.getBoundingClientRect(),px=event?.clientX??pbox.left+pbox.width/2,py=event?.clientY??pbox.top;
   tooltip.style.left=Math.max(wrap.scrollLeft+4,Math.min(px-box.left+wrap.scrollLeft+12,wrap.scrollLeft+box.width-tooltip.offsetWidth-8))+'px';
   tooltip.style.top=Math.max(5,py-box.top-tooltip.offsetHeight-12)+'px';
  }
  function hitModel(event){
   const label=event.target.closest('[data-cost-label]');if(label)return label.dataset.costLabel;
   const matrix=plot.getScreenCTM();if(!matrix)return null;
   const at=new DOMPoint(event.clientX,event.clientY).matrixTransform(matrix.inverse());
   const threshold=(event.pointerType==='touch'?22:12)/Math.hypot(matrix.a,matrix.b);
   let nearest=null,distance=threshold;
   placed.forEach(point=>{const d=Math.hypot(point.cx-at.x,point.cy-at.y);if(d<distance){distance=d;nearest=point.id}});
   return nearest;
  }
  plot.onpointermove=event=>{if(event.pointerType==='touch')return;hoverId=hitModel(event);highlight(hoverId??focusId,event)};
  plot.onpointerleave=()=>{hoverId=null;highlight(focusId)};
  plot.onfocusin=event=>{focusId=event.target.dataset.costPoint??null;highlight(focusId)};
  plot.onfocusout=()=>{focusId=null;highlight(hoverId)};
  plot.onclick=event=>{const id=hitModel(event);if(id)toggleSelection(id,true)};
  plot.onkeydown=event=>{const id=event.target.dataset.costPoint;if(id&&['Enter',' '].includes(event.key)){event.preventDefault();toggleSelection(id,true)}};
  highlight(null);
  const table=document.getElementById('cost-plot-table');table.replaceChildren();
  rows.forEach(m=>{
   const tr=document.createElement('tr'),name=node('th');name.scope='row';name.append(link(m));tr.append(name);
   for(const text of [costText(m),m.scores[mode].value.toFixed(2),m.seconds==null?'—':(m.seconds/60).toFixed(1)])tr.append(node('td',text,'numeric'));
   const cell=node('td'),pin=node('button',t(selected.has(m.model_id)?'unpinLabel':'pinLabel'),'cost-pin-button');pin.type='button';pin.dataset.costPin=m.model_id;
   pin.setAttribute('aria-pressed',String(selected.has(m.model_id)));pin.setAttribute('aria-label',t(selected.has(m.model_id)?'unpinLabel':'pinLabel')+' · '+m.label);
   pin.addEventListener('click',()=>{toggleSelection(m.model_id);document.querySelector('[data-cost-pin="'+m.model_id+'"]').focus({preventScroll:true})});
   cell.append(pin);tr.append(cell);table.append(tr);
  });
 }
 function toggleSelection(id,restorePoint=false){
  const ids=new Set(selected);if(ids.has(id))ids.delete(id);else ids.add(id);
  const url=new URL(location.href);if(ids.size)url.searchParams.set('cost-selected',[...ids].sort().join(','));else url.searchParams.delete('cost-selected');
  history.replaceState(null,'',url);render();
  if(restorePoint)plot.querySelector('[data-cost-point="'+id+'"]')?.focus({preventScroll:true});
 }
 function clearSelection(){
  if(!selected.size)return;
  const url=new URL(location.href);url.searchParams.delete('cost-selected');history.replaceState(null,'',url);render();
 }

 function render(){
  const params=new URLSearchParams(location.search);lang=params.get('lang')==='en'?'en':'zh';axis=params.get('cost-axis')==='time'?'time':'cost';mode=modes.includes(params.get('cost-score'))?params.get('cost-score'):'partial';
  const validIds=new Set(data.models.map(m=>m.model_id));selected=new Set((params.get('cost-selected')||'').split(',').filter(id=>validIds.has(id)));
  document.getElementById('cost-tooltip').hidden=true;
  document.querySelectorAll('[data-cost-t]').forEach(n=>n.textContent=t(n.dataset.costT));
  document.querySelectorAll('[data-cost-axis]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.costAxis===axis)));
  document.querySelectorAll('[data-cost-score]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.costScore===mode)));
  document.getElementById('cost-selection-count').textContent=selected.size?t('selectionCount').replace('{count}',selected.size):'';
  document.getElementById('cost-clear-selection').hidden=!selected.size;
  document.getElementById('cost-interaction-hint').textContent=t('interactionHint');
  const scoreName=({capability:'MC',partial:'RMC',strict:'SMC'})[mode];
  document.getElementById('cost-frontier-title').textContent=t(axis==='cost'?'costAxisButton':'timeAxisButton');
  document.getElementById('cost-frontier-subtitle').textContent=t(axis==='cost'?'costSubtitle':'timeSubtitle').replace('{score}',scoreName);
  document.getElementById('cost-measure-legend').textContent=t('fullSubmission');
  const hasEstimates=axis==='cost'&&data.models.some(m=>m.status==='estimated');
  document.getElementById('cost-estimate-legend').hidden=!hasEstimates;
  document.getElementById('cost-estimate-legend').style.display=hasEstimates?'':'none';
  document.getElementById('cost-frontier-note').textContent=t(axis==='cost'?'costNote':'timeNote');document.getElementById('cost-table-score').textContent=scoreName;
  board.setAttribute('aria-label',t('title'));renderBoard();renderPlot();
 }
 document.querySelectorAll('[data-cost-axis],[data-cost-score]').forEach(b=>b.addEventListener('click',()=>{const u=new URL(location.href);if(b.dataset.costAxis)u.searchParams.set('cost-axis',b.dataset.costAxis);else u.searchParams.set('cost-score',b.dataset.costScore);history.replaceState(null,'',u);render()}));
 document.getElementById('cost-clear-selection').addEventListener('click',()=>{clearSelection();document.querySelector('[data-cost-score="'+mode+'"]').focus({preventScroll:true})});
 document.getElementById('cost-frontier').addEventListener('keydown',event=>{if(event.key==='Escape'){event.preventDefault();clearSelection();document.getElementById('cost-tooltip').hidden=true}});
 let resizeFrame=0,lastWidth=plot.getBoundingClientRect().width;
 const observer=new ResizeObserver(()=>{const width=plot.getBoundingClientRect().width;if(Math.abs(width-lastWidth)<1)return;lastWidth=width;cancelAnimationFrame(resizeFrame);resizeFrame=requestAnimationFrame(renderPlot)});observer.observe(plot);
 document.fonts.ready.then(()=>renderPlot());
 window.addEventListener('mg:updated',render);window.addEventListener('popstate',render);render();
})();
