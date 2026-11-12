/* Total cost observations; scores and timing samples come from their existing owners. */
(() => {
 'use strict';
 const source=document.getElementById('cost-reference-data');if(!source)return;
 const data=JSON.parse(source.textContent),board=document.getElementById('cost-board'),plot=document.getElementById('cost-plot');
 const ns='http://www.w3.org/2000/svg',modes=['capability','partial','strict'];
 const labels={
  title:['总成本参考','Total cost reference'],subtitle:['当前留档答卷 · 美元','Retained attempts · USD'],
  method:['计算口径 ↗','Method ↗'],scope:['每题只计留档采用的一次作答；全部未交卷时取最后留档尝试。三轮固定自查各计一次，其余重试不计。','One retained attempt per task; if none delivered, use the last retained failed attempt. Each prescribed self-check round is included once. Other retries are excluded.'],
  priceNote:['Dot 使用2026-11-08测试时订阅附赠的独立额度，额外费用 $0；其余按公开 API 价格折算并计缓存优惠。≈ 为用量估算；≥ 为已知小计，不参与成本排名。','Dot used a separate subscription-bundled allowance on 2026-11-08, with $0 additional cost; other models use public API reference prices with cache discounts. ≈ marks imputation; ≥ is an unranked known subtotal.'],
  costSubtitle:['横轴为总成本（美元，从0开始的线性刻度），纵轴为{score}。越靠左上越好。','X: total cost in USD (linear scale starting at zero); Y: {score}. Upper left is better.'],
  timeSubtitle:['横轴为日常五题加权耗时（分钟），纵轴为{score}。越靠左上越好。','X: weighted time for the five everyday tasks (minutes); Y: {score}. Upper left is better.'],
  costAxisButton:['成本—成绩','Cost vs score'],timeAxisButton:['耗时—成绩','Time vs score'],measured:['费用已核对','Cost verified'],estimated:['估算','Estimated'],frontier:['完整数据的 Pareto 前沿','Pareto frontier of complete data'],
  chartData:['查看图表数据','View chart data'],model:['模型','Model'],total:['总成本','Total cost'],timeLabel:['典型题耗时 / 分钟','Typical time / min'],unknown:['未取得成本','Cost unavailable'],partial:['用量不齐','Usage incomplete'],estimatedNote:['含用量估算','Includes imputed usage'],
  costAxis:['总成本 / 美元（线性刻度）','Total cost / USD (linear scale)'],timeAxis:['典型题耗时 / 分钟','Typical task time / min'],timeMeasured:['已记录耗时','Recorded time'],
  range:['估算范围','Scenario range'],minutes:['分钟','min'],
  costNote:['实线只连接费用已核对且成绩已测完的模型。估算与成本下限点不用于确定成本前沿。','The cost frontier uses only verified costs and completed evaluations. Imputed totals and cost lower bounds do not define it.'],
  timeNote:['实线按同一组日常五题的已记录加权耗时与完整数学成绩计算。耗时包含工具和等待。','The time frontier uses recorded weighted time for the same five everyday tasks and completed mathematical evaluations. Time includes tools and waiting.'],
  noData:['没有足够的数据绘图。','Insufficient data to plot.'],score:['成绩','Score'],lowerBound:['仅有成本下限','Cost lower bound only']
 };
 const node=(tag,text,cls)=>{const n=document.createElement(tag);if(text!=null)n.textContent=text;if(cls)n.className=cls;return n};
 const svg=(tag,attrs={},text)=>{const n=document.createElementNS(ns,tag);Object.entries(attrs).forEach(([k,v])=>n.setAttribute(k,String(v)));if(text!=null)n.textContent=text;return n};
 let lang='zh',axis='cost',mode='partial';
 const t=key=>labels[key][lang==='en'?1:0],locale=()=>lang==='en'?'en-US':'zh-CN';
 const money=v=>'$'+v.toLocaleString(locale(),{minimumFractionDigits:2,maximumFractionDigits:2});
 const amount=m=>m.total_usd??(m.status==='partial'?m.known_usd:null);
 const costText=m=>amount(m)==null?'—':(m.status==='estimated'?'≈ ':m.status==='partial'?'≥ ':'')+money(amount(m));
 const short=m=>m.label.replace('Claude ','').replace('Gemini ','').replace('DeepSeek v4.1 Flash','DeepSeek').replace('Underlying','').trim();
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
   svg('desc',{id:'cost-svg-desc'},t(axis==='cost'?'costNote':'timeNote')));
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
  const occupied=[],placed=[];
  rows.forEach((m,index)=>{
   const value=axis==='cost'?amount(m):m.seconds/60,cx=x(value),cy=y(m.scores[mode].value),r=3.5;
   const resourceStatus=axis==='cost'?m.status:'observed';
   if(axis==='cost'&&m.estimate_range_usd){plot.append(svg('line',{x1:x(m.estimate_range_usd[0]),y1:cy,x2:x(m.estimate_range_usd[1]),y2:cy,class:'cost-error-bar',stroke:brand(m)}))}
   const resourceText=axis==='cost'?costText(m):(m.seconds/60).toFixed(1)+' '+t('minutes');
   const p=svg('circle',{cx,cy,r,class:'cost-model-point '+resourceStatus,
    fill:resourceStatus==='observed'?brand(m):'#fff',stroke:brand(m),tabindex:0,role:'img','data-cost-point':m.model_id,
    'aria-label':m.label+' · '+resourceText+' · '+({capability:'MC',partial:'RMC',strict:'SMC'})[mode]+' '+m.scores[mode].value.toFixed(2)});
   if(frontier.has(m.model_id))p.setAttribute('stroke-width','3');
   const target=svg('g',{class:'cost-model-target'});
   target.append(svg('circle',{cx,cy,r:7,fill:'transparent','aria-hidden':'true'}),p);
   const tooltip=document.getElementById('cost-tooltip'),wrap=plot.parentElement;
   const show=event=>{
    const score=({capability:'MC',partial:'RMC',strict:'SMC'})[mode]+' '+m.scores[mode].value.toFixed(2);
    tooltip.textContent=m.label+'\n'+t('total')+' '+costText(m)+'\n'+score+(m.seconds==null?'':'\n'+t('timeLabel')+' '+(m.seconds/60).toFixed(1))+
     (m.status==='estimated'?'\n'+t('range')+' '+m.estimate_range_usd.map(money).join('–'):m.status==='partial'?'\n'+t('lowerBound'):'');
    tooltip.hidden=false;
    const box=wrap.getBoundingClientRect(),pbox=p.getBoundingClientRect(),px=event?.clientX??pbox.left,py=event?.clientY??pbox.top;
    tooltip.style.left=Math.max(4,Math.min(px-box.left+12,box.width-tooltip.offsetWidth-8))+'px';tooltip.style.top=Math.max(5,py-box.top-tooltip.offsetHeight-12)+'px';
   };
   target.addEventListener('mouseenter',show);target.addEventListener('mousemove',show);p.addEventListener('focus',()=>show());target.addEventListener('mouseleave',()=>tooltip.hidden=true);p.addEventListener('blur',()=>tooltip.hidden=true);
   plot.append(target);placed.push({m,cx,cy,r,index});
   if(axis==='cost'&&m.status==='partial')plot.append(svg('path',{d:`M${cx+r+4},${cy}h18m-5,-4l5,4l-5,4`,fill:'none',stroke:brand(m),'stroke-width':1.5}));
  });
  const pointBoxes=placed.map(p=>[p.cx-p.r-3,p.cy-p.r-3,p.cx+p.r+3,p.cy+p.r+3]);
  placed.sort((a,b)=>a.cy-b.cy).forEach(({m,cx,cy,r})=>{
   const text=short(m),width=Math.min(200,text.length*6.5),candidates=[[cx+r+7,cy-8],[cx-width-r-7,cy-8],[cx+r+7,cy+18],[cx-width-r-7,cy+18],[cx-width/2,cy-r-10],[cx-width/2,cy+r+22]];
   const overlaps=(a,b)=>a[0]<b[2]&&a[2]>b[0]&&a[1]<b[3]&&a[3]>b[1];
   let chosen=null;
   for(const [px,py] of candidates){const box=[px,py-12,px+width,py+4];if(px>=left-8&&px+width<=W-8&&py>=top-6&&py<bottom+3&&![...occupied,...pointBoxes].some(o=>overlaps(box,o))){chosen=[px,py,box];break}}
   if(!chosen){const px=Math.min(W-width-8,Math.max(left,cx+r+7)),py=Math.min(bottom-3,cy+31);chosen=[px,py,[px,py-12,px+width,py+4]]}
   occupied.push(chosen[2]);plot.append(svg('text',{x:chosen[0],y:chosen[1],class:'cost-label',fill:brand(m)},text));
  });
  const table=document.getElementById('cost-plot-table');table.replaceChildren();
  rows.forEach(m=>{const tr=document.createElement('tr'),name=node('th');name.scope='row';name.append(link(m));tr.append(name);for(const text of [costText(m),m.scores[mode].value.toFixed(2),m.seconds==null?'—':(m.seconds/60).toFixed(1)])tr.append(node('td',text,'numeric'));table.append(tr)});
 }
 function render(){
  const params=new URLSearchParams(location.search);lang=params.get('lang')==='en'?'en':'zh';axis=params.get('cost-axis')==='time'?'time':'cost';mode=modes.includes(params.get('cost-score'))?params.get('cost-score'):'partial';
  document.querySelectorAll('[data-cost-t]').forEach(n=>n.textContent=t(n.dataset.costT));
  document.querySelectorAll('[data-cost-axis]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.costAxis===axis)));
  document.querySelectorAll('[data-cost-score]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.costScore===mode)));
  const scoreName=({capability:'MC',partial:'RMC',strict:'SMC'})[mode];
  document.getElementById('cost-frontier-title').textContent=t(axis==='cost'?'costAxisButton':'timeAxisButton');
  document.getElementById('cost-frontier-subtitle').textContent=t(axis==='cost'?'costSubtitle':'timeSubtitle').replace('{score}',scoreName);
  document.getElementById('cost-measure-legend').textContent=t(axis==='cost'?'measured':'timeMeasured');
  document.getElementById('cost-estimate-legend').hidden=axis!=='cost';
  document.getElementById('cost-estimate-legend').style.display=axis==='cost'?'':'none';
  document.getElementById('cost-frontier-note').textContent=t(axis==='cost'?'costNote':'timeNote');document.getElementById('cost-table-score').textContent=scoreName;
  board.setAttribute('aria-label',t('title'));renderBoard();renderPlot();
 }
 document.querySelectorAll('[data-cost-axis],[data-cost-score]').forEach(b=>b.addEventListener('click',()=>{const u=new URL(location.href);if(b.dataset.costAxis)u.searchParams.set('cost-axis',b.dataset.costAxis);else u.searchParams.set('cost-score',b.dataset.costScore);history.replaceState(null,'',u);document.getElementById('cost-tooltip').hidden=true;render()}));
 window.addEventListener('mg:updated',render);window.addEventListener('popstate',render);render();
})();
