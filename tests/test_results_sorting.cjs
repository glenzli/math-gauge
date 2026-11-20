const test=require('node:test');
const assert=require('node:assert/strict');
const fs=require('node:fs');
const vm=require('node:vm');
const source=fs.readFileSync(require('node:path').join(__dirname,'../scripts/templates/results-core.js'),'utf8');
function runtime(){
 const data={score_modes:['capability','partial','strict'],default_score_mode:'partial',
  default_attempt_condition:'nonlogical_retry_3',display_score_modes:[]};
 const window={},document={getElementById:()=>({textContent:JSON.stringify(data)})};
 vm.runInNewContext(source,{window,document,location:{search:''},URLSearchParams});
 return window.MG;
}
const m=(id,mc,rmc,smc,order)=>({id,ranking_values:{capability:mc,partial:rmc,strict:smc},display_order:order});
test('selected score stays primary; remaining scores follow SMC, RMC, MC',()=>{
 const {compareScores:compare}=runtime(),models=[m('base',9000,8000,7000),m('mc',9500,8000,7000),
  m('rmc',9000,8500,7000),m('smc',9000,8000,7500)];
 for(const [mode,expected]of Object.entries({capability:['mc','smc','rmc','base'],
  partial:['rmc','smc','mc','base'],strict:['smc','rmc','mc','base']}))
  assert.deepEqual([...models].sort((a,b)=>compare(a,b,mode)).map(m=>m.id),expected);
});
test('equal settled triples share places in model order; unknowns stay unranked',()=>{
 const {rankedScores}=runtime(),models=[m('older',8000,8000,8000,2),m('newer',8000,8000,8000,1),
  m('known-zero',0,0,0,3),m('unknown',null,null,null,0)];
 models[0].test_order={date:'2026-10-01'};
 models[1].test_order={date:'2026-11-01'};
 assert.deepEqual(Array.from(rankedScores(models), row=>[row.model.id,row.place]),
  [['newer',1],['older',1],['known-zero',3],['unknown',null]]);
});
test('undeclared model order falls back to ID; unsettled points do not share a place',()=>{
 const {rankedScores,compareModelOrder}=runtime(),a=m('a',80,80,80),b=m('b',80,80,80);
 const pending={...m('pending',80,80,80,0),ranking_complete:false};
 assert.deepEqual([b,a].sort(compareModelOrder).map(m=>m.id),['a','b']);
 assert.deepEqual(Array.from(rankedScores([pending,b,a]), row=>[row.model.id,row.place]),
  [['a',1],['b',1],['pending',3]]);
});
