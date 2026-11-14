const test=require('node:test');
const assert=require('node:assert/strict');
const {layout}=require('../scripts/templates/cost-label-layout.js');

const bounds={left:62,top:30,right:1032,bottom:434};
const densePoints=()=>[
 [71,52,115],[78,53,128],[85,59,151],[113,61,123],[127,69,144],
 [143,71,138],[164,79,137],[182,94,142],[207,105,144],[236,117,154],
 [270,139,136],[317,161,126],[381,204,138],[454,256,151],[509,338,107]
].map(([cx,cy,width],index)=>({id:'model-'+index,cx,cy,r:6,width,height:22,priority:index<3?2:0,required:false}));

function assertInside(labels,box=bounds){
 for(const label of labels){
  assert.ok(label.x>=box.left-1e-6&&label.y>=box.top-1e-6,label.id+' starts inside bounds');
  assert.ok(label.x+label.width<=box.right+1e-6&&label.y+label.height<=box.bottom+1e-6,label.id+' ends inside bounds');
 }
}

function assertClear(labels,points){
 const visible=labels.filter(label=>label.visible);
 for(let i=0;i<visible.length;i++){
  const label=visible[i];
  for(const other of visible.slice(i+1)){
   assert.ok(label.x+label.width<=other.x||other.x+other.width<=label.x||
    label.y+label.height<=other.y||other.y+other.height<=label.y,label.id+' overlaps '+other.id);
  }
  for(const point of points){
   const x=Math.max(label.x,Math.min(label.x+label.width,point.cx));
   const y=Math.max(label.y,Math.min(label.y+label.height,point.cy));
   assert.ok(Math.hypot(x-point.cx,y-point.cy)>=point.r-1e-6,label.id+' covers '+point.id);
  }
 }
}

function lineEntersBox(line,box){
 const dx=line.x2-line.x1,dy=line.y2-line.y1;
 const intersections=[0,1];
 if(dx)intersections.push((box.x-line.x1)/dx,(box.x+box.width-line.x1)/dx);
 if(dy)intersections.push((box.y-line.y1)/dy,(box.y+box.height-line.y1)/dy);
 const fractions=intersections.filter(t=>t>=0&&t<=1).sort((a,b)=>a-b);
 for(let i=1;i<fractions.length;i++){
  const t=(fractions[i-1]+fractions[i])/2,x=line.x1+dx*t,y=line.y1+dy*t;
  if(x>box.x+1e-6&&x<box.x+box.width-1e-6&&y>box.y+1e-6&&y<box.y+box.height-1e-6)return true;
 }
 return false;
}

function assertLeadersClear(labels,points){
 for(const label of labels.filter(label=>label.visible&&label.connector.needed)){
  const line=label.connector,dx=line.x2-line.x1,dy=line.y2-line.y1;
  for(const other of labels.filter(other=>other.visible&&other.id!==label.id)){
   assert.equal(lineEntersBox(line,other),false,label.id+' leader crosses '+other.id);
  }
  for(const point of points.filter(point=>point.id!==label.id)){
   const t=Math.max(0,Math.min(1,((point.cx-line.x1)*dx+(point.cy-line.y1)*dy)/(dx*dx+dy*dy)));
   assert.ok(Math.hypot(line.x1+dx*t-point.cx,line.y1+dy*t-point.cy)>=point.r-1e-6,
    label.id+' leader covers '+point.id);
  }
 }
}

test('all mode uses empty chart space for fifteen clustered measured labels',()=>{
 const points=densePoints(),labels=layout(points,{bounds,mode:'all',padding:4,
  lines:[{x1:71,y1:52,x2:509,y2:338}]});
 assert.equal(labels.length,points.length);
 assert.ok(labels.every(label=>label.visible));
 assertInside(labels);assertClear(labels,points);
 assertLeadersClear(labels,[]);
});

test('measured narrow-screen cluster leaves every label and leader clear',()=>{
 // A real fifteen-model cost/MC layout, measured in Chromium at a 390px viewport.
 // This tests geometry rather than pinning model scores or exact label positions.
 const measurements=[
  [118.47959731,107.513719807,107.15625,31],[173.579122724,190.720652174,111.450897217,61],
  [86.74079452,119.165799453,115.784233093,17],[219.722995953,130.010555556,104.254470825,19],
  [149.31797278,60.722222222,93.498512268,10018],[142.70153755,77.509661836,102.126495361,18],
  [804.62324791,62.953888889,110.212799072,67],[738.321338732,70.213888889,122.245536804,67],
  [455.2166758,60.722222222,97.947921753,58],[397.90596085,72.20531401,106.575897217,58],
  [202.1017198,136.883494364,128.107147217,19],[250.882247023,272.081944444,106.150299072,112],
  [298.483550266,86.780555556,137.528274536,90],[98.376761865,131.170128824,118.608634949,17],
  [70,71.362318841,126.250007629,10051]
 ];
 const points=measurements.map(([cx,cy,width,priority],index)=>({id:'measured-'+index,cx,cy,width,
  height:24.571430206,r:3.5,priority}));
 const labels=layout(points,{bounds,mode:'all',padding:4,
  lines:[{x1:70,y1:71.362318841,x2:149.31797278,y2:60.722222222}]});
 assert.equal(labels.filter(label=>label.visible).length,15);
 assertInside(labels);assertClear(labels,points);assertLeadersClear(labels,points);
 const selected=points.map((point,index)=>({...point,required:index===2}));
 assert.deepEqual(layout(selected,{bounds,mode:'all',padding:4,
  lines:[{x1:70,y1:71.362318841,x2:149.31797278,y2:60.722222222}]}),labels,
  'selection should keep all-mode labels and connectors stable');
});

test('layout is deterministic, keeps measured sizes, and never mutates frozen inputs',()=>{
 const points=densePoints().map(Object.freeze);Object.freeze(points);
 const options=Object.freeze({bounds:Object.freeze({...bounds}),mode:'all',padding:4,
  lines:Object.freeze([Object.freeze({x1:62,y1:100,x2:310,y2:100})])});
 const before=JSON.stringify({points,options});
 const first=layout(points,options),second=layout(points,options);
 assert.deepEqual(first,second);assert.equal(JSON.stringify({points,options}),before);
 assert.deepEqual(first.map(label=>[label.id,label.width,label.height]),points.map(point=>[point.id,point.width,point.height]));
 assertInside(first);assertClear(first,points);
});

test('auto keeps required labels even above budget and admits priority labels first',()=>{
 const points=[
  {id:'required-a',cx:100,cy:60,r:5,width:80,height:22,priority:0,required:true},
  {id:'required-b',cx:180,cy:60,r:5,width:80,height:22,priority:0,required:true},
  {id:'frontier',cx:320,cy:170,r:5,width:80,height:22,priority:10},
  {id:'ordinary',cx:500,cy:240,r:5,width:80,height:22,priority:0}
 ];
 const requiredOnly=layout(points,{bounds,mode:'auto',maxLabels:1});
 assert.deepEqual(requiredOnly.filter(label=>label.visible).map(label=>label.id),['required-a','required-b']);
 const three=layout(points,{bounds,mode:'auto',maxLabels:3});
 assert.deepEqual(three.filter(label=>label.visible).map(label=>label.id),['required-a','required-b','frontier']);
 assertInside(three);assertClear(three,points);
});

test('selected mode retains only required labels and gives hidden hover labels bounded fallbacks',()=>{
 const points=densePoints();points[0].required=true;points[3].required=true;
 const labels=layout(points,{bounds,mode:'selected',maxLabels:1});
 assert.deepEqual(labels.filter(label=>label.visible).map(label=>label.id),[points[0].id,points[3].id]);
 assertInside(labels);assertClear(labels,points);
 for(const label of labels.filter(label=>!label.visible)){
  assertClear([...labels.filter(other=>other.visible),{...label,visible:true}],points);
 }
});

test('distant or ambiguous labels keep point-edge connectors, isolated adjacent labels may omit them',()=>{
 const point={id:'isolated',cx:400,cy:200,r:7,width:110,height:22,required:true};
 const near=layout([point],{bounds,mode:'all'})[0];
 assert.equal(near.connector.needed,false);
 const points=densePoints(),labels=layout(points,{bounds,mode:'all'});
 assert.ok(labels.some(label=>label.connector.needed));
 for(const label of labels){
  const source=points.find(point=>point.id===label.id),line=label.connector;
  assert.ok(Math.abs(Math.hypot(line.x1-source.cx,line.y1-source.cy)-source.r)<1e-6);
  assert.ok(line.x2>=label.x-1e-6&&line.x2<=label.x+label.width+1e-6);
  assert.ok(line.y2>=label.y-1e-6&&line.y2<=label.y+label.height+1e-6);
  assert.ok(Math.abs(line.x2-label.x)<1e-6||Math.abs(line.x2-label.x-label.width)<1e-6||
   Math.abs(line.y2-label.y)<1e-6||Math.abs(line.y2-label.y-label.height)<1e-6);
 }
});

test('transient connectors keep clustered names local without covering points or labels',()=>{
 const points=densePoints(),labels=layout(points,{bounds,mode:'all',padding:4,interactiveConnectors:true});
 assert.ok(labels.every(label=>label.visible));assertInside(labels);assertClear(labels,points);
 for(const label of labels){
  const point=points.find(point=>point.id===label.id),line=label.connector;
  const gap=Math.hypot(line.x2-point.cx,line.y2-point.cy)-point.r;
  assert.ok(gap<=point.height*6,label.id+' drifts too far from its point');
 }
});
