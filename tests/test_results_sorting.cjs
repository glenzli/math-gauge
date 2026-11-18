const test=require('node:test');
const assert=require('node:assert/strict');
const fs=require('node:fs');
const vm=require('node:vm');
const source=fs.readFileSync(require('node:path').join(__dirname,'../scripts/templates/results-core.js'),'utf8');
function comparator(){
 const data={score_modes:['capability','partial','strict'],default_score_mode:'partial',
  default_attempt_condition:'nonlogical_retry_3',display_score_modes:[]};
 const window={},document={getElementById:()=>({textContent:JSON.stringify(data)})};
 vm.runInNewContext(source,{window,document,location:{search:''},URLSearchParams});
 return window.MG.compareScores;
}
const m=(id,mc,rmc,smc,date=null)=>({id,ranking_values:{capability:mc,partial:rmc,strict:smc},test_order:{date}});
test('selected score stays primary; remaining scores follow RMC, SMC, MC',()=>{
 const compare=comparator(),models=[m('base',9000,8000,7000),m('mc',9500,8000,7000),
  m('rmc',9000,8500,7000),m('smc',9000,8000,7500)];
 for(const [mode,expected]of Object.entries({capability:['mc','rmc','smc','base'],
  partial:['rmc','smc','mc','base'],strict:['smc','rmc','mc','base']}))
  assert.deepEqual([...models].sort((a,b)=>compare(a,b,mode)).map(m=>m.id),expected);
});
test('known scores and dates precede unknowns; exact ties keep source order',()=>{
 const compare=comparator(),models=[m('no-date',0,0,0),m('later',0,0,0,'2026-11-18'),
  m('earlier-z',0,0,0,'2026-11-04'),m('earlier-a',0,0,0,'2026-11-04'),m('unknown',null,null,null,'2026-11-01')];
 assert.deepEqual([...models].sort((a,b)=>compare(a,b,'partial')).map(m=>m.id),
  ['earlier-z','earlier-a','later','no-date','unknown']);
 assert.equal(compare(models[2],models[3],'partial'),0);
});
test('an available native timestamp resolves ties within the same test day',()=>{
 const compare=comparator(),later=m('later',80,80,80,'2026-11-09'),earlier=m('earlier',80,80,80,'2026-11-09');
 later.test_order.started_at='2026-11-08T23:30:00+00:00';
 earlier.test_order.started_at='2026-11-08T23:00:00+00:00';
 assert.deepEqual([later,earlier].sort(compare).map(m=>m.id),['earlier','later']);
});
