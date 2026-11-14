;(function (global) {
 'use strict';

 const EPSILON=1e-7;
 const clamp=(value,min,max)=>Math.max(min,Math.min(max,value));
 const finite=(value,fallback)=>Number.isFinite(Number(value))?Number(value):fallback;
 const squared=(x,y)=>x*x+y*y;

 function nearest(box,x,y){
  return {x:clamp(x,box.x,box.x+box.width),y:clamp(y,box.y,box.y+box.height)};
 }

 function pointGap(point,box){
  const edge=nearest(box,point.cx,point.cy);
  return Math.hypot(point.cx-edge.x,point.cy-edge.y)-point.r;
 }

 function connector(point,box,points,padding){
  const edge=nearest(box,point.cx,point.cy);
  const dx=edge.x-point.cx,dy=edge.y-point.cy,distance=Math.hypot(dx,dy);
  const start=distance>EPSILON?Math.min(point.r/distance,1):0;
  const gap=distance-point.r;
  const ambiguous=points.some(other=>other.index!==point.index&&pointGap(other,box)<=gap+padding);
  return {x1:point.cx+dx*start,y1:point.cy+dy*start,x2:edge.x,y2:edge.y,
   needed:gap>Math.max(8,padding+4)||ambiguous};
 }

 function overlap(a,b,padding){
  const width=Math.min(a.x+a.width+padding,b.x+b.width+padding)-Math.max(a.x,b.x);
  const height=Math.min(a.y+a.height+padding,b.y+b.height+padding)-Math.max(a.y,b.y);
  return width>EPSILON&&height>EPSILON?width*height:0;
 }

 function segmentHitsBox(line,box,padding){
  const left=box.x-padding,right=box.x+box.width+padding;
  const top=box.y-padding,bottom=box.y+box.height+padding;
  let first=0,last=1;
  for(const [origin,delta,min,max] of [[line.x1,line.x2-line.x1,left,right],[line.y1,line.y2-line.y1,top,bottom]]){
   if(Math.abs(delta)<EPSILON){if(origin<min||origin>max)return false;continue;}
   const a=(min-origin)/delta,b=(max-origin)/delta;
   first=Math.max(first,Math.min(a,b));last=Math.min(last,Math.max(a,b));
   if(first>last+EPSILON)return false;
  }
  return last>EPSILON&&first<1-EPSILON;
 }

 function segmentHitsPoint(line,point,padding){
  const dx=line.x2-line.x1,dy=line.y2-line.y1,length=squared(dx,dy);
  const t=length>EPSILON?clamp(((point.cx-line.x1)*dx+(point.cy-line.y1)*dy)/length,0,1):0;
  return squared(line.x1+t*dx-point.cx,line.y1+t*dy-point.cy)<squared(point.r+padding,0)-EPSILON;
 }

 function segmentsCross(a,b){
  const ax=a.x2-a.x1,ay=a.y2-a.y1,bx=b.x2-b.x1,by=b.y2-b.y1;
  const cross=ax*by-ay*bx;
  if(Math.abs(cross)<EPSILON)return false;
  const dx=b.x1-a.x1,dy=b.y1-a.y1;
  const t=(dx*by-dy*bx)/cross,u=(dx*ay-dy*ax)/cross;
  return t>EPSILON&&t<1-EPSILON&&u>EPSILON&&u<1-EPSILON;
 }

 function compare(a,b){
  for(let i=0;i<a.length;i++)if(Math.abs(a[i]-b[i])>EPSILON)return a[i]-b[i];
  return 0;
 }

 function candidates(point,bounds,padding,placed){
  const result=[],seen=new Set(),width=point.width,height=point.height;
  const maxX=Math.max(bounds.left,bounds.right-width),maxY=Math.max(bounds.top,bounds.bottom-height);
  function add(x,y){
   x=clamp(x,bounds.left,maxX);y=clamp(y,bounds.top,maxY);
   const key=Math.round(x*1000)+','+Math.round(y*1000);
   if(!seen.has(key)){seen.add(key);result.push({x,y,width,height});}
  }
  // Near positions are tried in every direction, then in successively wider rings.
  for(const gap of [padding+2,12,22,36,56,82,116,164,228,310]){
   for(let direction=0;direction<24;direction++){
    const angle=direction*Math.PI/12,dx=Math.cos(angle),dy=Math.sin(angle);
    const reach=point.r+gap+Math.min(Math.abs(dx)>EPSILON?width/2/Math.abs(dx):Infinity,
     Math.abs(dy)>EPSILON?height/2/Math.abs(dy):Infinity);
    add(point.cx+dx*reach-width/2,point.cy+dy*reach-height/2);
   }
  }
  // Exact obstacle edges find narrow spaces that a regular fallback grid can miss.
  for(const label of placed){
   const box=label.box;
   for(const x of [box.x-width-padding,box.x+box.width+padding]){
    add(x,box.y);add(x,box.y+box.height-height);add(x,point.cy-height/2);
   }
   for(const y of [box.y-height-padding,box.y+box.height+padding]){
    add(box.x,y);add(box.x+box.width-width,y);add(point.cx-width/2,y);
   }
  }
  // Dense high-score clusters can use the chart's empty lower and side regions.
  const stepX=Math.max(18,Math.min(36,width/2)),stepY=Math.max(12,height+padding+2);
  for(let y=bounds.top;y<maxY+stepY;y+=stepY){
   for(let x=bounds.left;x<maxX+stepX;x+=stepX)add(x,y);
  }
  add(maxX,maxY);
  return result;
 }

 function evaluate(point,box,placed,points,lines,padding,interactiveConnectors){
  let labelHits=0,pointHits=0,area=0,leaderLabels=0,leaderPoints=0,crossings=0,plotHits=0;
  const line=connector(point,box,points,padding);
  for(const other of points){
   const gap=pointGap(other,box);
   if(gap<padding-EPSILON){pointHits++;area+=padding-gap;}
   if(line.needed&&other.index!==point.index&&segmentHitsPoint(line,other,1))leaderPoints++;
  }
  for(const label of placed){
   const intersection=overlap(box,label.box,padding);
   if(intersection){labelHits++;area+=intersection;}
   if(line.needed&&segmentHitsBox(line,label.box,1))leaderLabels++;
   if(label.line.needed&&segmentHitsBox(label.line,box,1))leaderLabels++;
   if(line.needed&&label.line.needed&&segmentsCross(line,label.line))crossings++;
  }
  for(const frontier of lines){
   if(segmentHitsBox(frontier,box,0))plotHits++;
   if(line.needed&&segmentsCross(line,frontier))plotHits+=0.25;
  }
  const distance=Math.hypot(line.x2-point.cx,line.y2-point.cy)-point.r;
  const proximity=distance*distance+plotHits*900+Math.abs(box.y+box.height/2-point.cy)*0.1;
  // Transient connectors do not justify moving a permanent name far from its
  // point. Keep collision avoidance hard, but make leader routing a soft cost.
  const score=interactiveConnectors?
   [labelHits+pointHits,pointHits,area,proximity+leaderLabels*36+leaderPoints*36+crossings*12]:
   [labelHits+pointHits,pointHits,area,leaderLabels,leaderPoints,crossings,proximity];
  return {box,line,unsafeLeader:leaderLabels+leaderPoints,score};
 }

 function choose(point,placed,points,options){
  let best;
  for(const box of candidates(point,options.bounds,options.padding,placed)){
   const candidate=evaluate(point,box,placed,points,options.lines,options.padding,options.interactiveConnectors);
   if(!best||compare(candidate.score,best.score)<0)best=candidate;
  }
  return best;
 }

 /** Place measured label boxes without changing any data-point coordinates.
  * Hidden boxes are also positioned, so a temporary hover can use the same API.
  */
 function layout(input,settings){
  settings=settings||{};
  const supplied=settings.bounds||{},left=finite(supplied.left,0),top=finite(supplied.top,0);
  const options={bounds:{left,top,right:Math.max(left,finite(supplied.right,1040)),bottom:Math.max(top,finite(supplied.bottom,520))},
   padding:Math.max(0,finite(settings.padding,4)),interactiveConnectors:settings.interactiveConnectors===true,lines:(settings.lines||[]).filter(line=>
    [line.x1,line.y1,line.x2,line.y2].every(Number.isFinite))};
  const points=input.map((point,index)=>({id:point.id,index,cx:finite(point.cx,0),cy:finite(point.cy,0),
   r:Math.max(0,finite(point.r,0)),width:Math.max(0,finite(point.width,0)),height:Math.max(0,finite(point.height,0)),
   priority:finite(point.priority,0),required:Boolean(point.required)}));
  const mode=settings.mode||'auto',required=points.filter(point=>point.required).length;
  const budget=mode==='all'?points.length:mode==='selected'?required:
   Math.max(required,Math.max(0,Math.floor(finite(settings.maxLabels,8))));
  const density=point=>points.reduce((total,other)=>other.index===point.index?total:
   total+1/Math.max(12,Math.hypot(other.cx-point.cx,other.cy-point.cy)),0);
  // Route permanent leaders from constrained clusters first. With transient
  // leaders, reserve nearby space for the frontier before placing other names.
  const crowdedFirst=mode==='all'&&!options.interactiveConnectors;
  const order=points.slice().sort((a,b)=>(mode==='all'?0:Number(b.required)-Number(a.required))||
   (crowdedFirst?density(b)-density(a):b.priority-a.priority)||
   (crowdedFirst?b.priority-a.priority:density(b)-density(a))||b.width*b.height-a.width*a.height||a.index-b.index);
  const placed=[],byIndex=new Map();
  const maxAutoDistance=Math.max(64,Math.min(180,(options.bounds.right-options.bounds.left)*0.23));
  for(const point of order){
   if((mode==='selected'&&!point.required)||placed.length>=budget)continue;
   const chosen=choose(point,placed,points,options);
   const distance=Math.hypot(chosen.line.x2-point.cx,chosen.line.y2-point.cy)-point.r;
   if(mode==='auto'&&!point.required&&(chosen.score[0]>0||(!options.interactiveConnectors&&chosen.unsafeLeader>0)||distance>maxAutoDistance))continue;
   const label={point,box:chosen.box,line:chosen.line};placed.push(label);byIndex.set(point.index,label);
  }
  // Coordinate descent untangles early greedy choices while preserving every
  // required/all-mode label. Pairwise penalties count both directions equally.
  for(let pass=0;pass<3;pass++){
   let changed=false;
   const sequence=pass%2?placed.slice():placed.slice().reverse();
   for(const label of sequence){
    const others=placed.filter(other=>other!==label);
    const before=evaluate(label.point,label.box,others,points,options.lines,options.padding,options.interactiveConnectors);
    const after=choose(label.point,others,points,options);
    if(compare(after.score,before.score)<0){label.box=after.box;label.line=after.line;changed=true;}
   }
   if(!changed)break;
  }
  // A long label can be trapped behind one early placement. Refit that pair
  // together rather than sending a permanent name into empty chart space.
  if(options.interactiveConnectors){
   for(let pass=0;pass<2;pass++){
    let changed=false;
    for(const label of placed.slice().sort((a,b)=>pointGap(b.point,b.box)-pointGap(a.point,a.box))){
     if(pointGap(label.point,label.box)<36)continue;
     let best=null;
     for(const other of placed){
      if(other===label)continue;
      const rest=placed.filter(item=>item!==label&&item!==other);
      const oldA=evaluate(label.point,label.box,placed.filter(item=>item!==label),points,options.lines,options.padding,true);
      const oldB=evaluate(other.point,other.box,placed.filter(item=>item!==other),points,options.lines,options.padding,true);
      const a=choose(label.point,rest,points,options),b=choose(other.point,[...rest,{point:label.point,box:a.box,line:a.line}],points,options);
      if(a.score[0]||b.score[0])continue;
      const gain=oldA.score[3]+oldB.score[3]-a.score[3]-b.score[3];
      if(gain>EPSILON&&(!best||gain>best.gain))best={other,a,b,gain};
     }
     if(best){label.box=best.a.box;label.line=best.a.line;best.other.box=best.b.box;best.other.line=best.b.line;changed=true;}
    }
    if(!changed)break;
   }
  }
  return points.map(point=>{
   const visible=byIndex.has(point.index);
   const label=byIndex.get(point.index)||choose(point,placed,points,options);
   const box=label.box,line=label.line;
   return {id:point.id,x:box.x,y:box.y,width:point.width,height:point.height,visible,
    connector:{x1:line.x1,y1:line.y1,x2:line.x2,y2:line.y2,needed:line.needed}};
  });
 }

 const api={layout};
 global.MathGaugeCostLabels=api;
 if(typeof module==='object'&&module.exports)module.exports=api;
})(globalThis);
