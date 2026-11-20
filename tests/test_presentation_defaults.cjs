const {test}=require('node:test');
const assert=require('node:assert/strict');
const fs=require('node:fs');
const path=require('node:path');
const vm=require('node:vm');
const source=fs.readFileSync(path.join(__dirname,'../scripts/templates/results-core.js'),'utf8');

function load(search=''){
 const data={score_modes:['capability','partial','strict'],default_score_mode:'partial',
  score_mode_catalog:{default:'partial',primary:'partial'},default_attempt_condition:'nonlogical_retry_3',
  display_score_modes:[{id:'capability'},{id:'partial'},{id:'strict'}]};
 const window={},document={getElementById:()=>({textContent:JSON.stringify(data)})};
 vm.runInNewContext(source,{window,document,location:{search},URLSearchParams});
 return window.MG;
}

test('presentation defaults to SMC without changing the archived RMC policy',()=>{
 const display=load();
 assert.equal(display.state.score,'strict');
 assert.equal(display.d.default_score_mode,'partial');
 assert.equal(display.d.score_mode_catalog.default,'partial');
 assert.equal(display.d.score_mode_catalog.primary,'partial');
 assert.deepEqual(Array.from(display.d.display_score_modes,m=>m.id),['strict','partial','capability']);
 assert.deepEqual(Array.from(display.d.score_modes),['capability','partial','strict']);
});

test('explicit old score links remain valid and each panel restores its own choice',()=>{
 const search='?score=partial&sort-written=capability&sort-lean=strict&cost-score=partial';
 const display=load(search);
 assert.equal(display.state.score,'partial');
 assert.equal(display.scorePreference(search,'sort-written'),'capability');
 assert.equal(display.scorePreference(search,'sort-lean'),'strict');
 assert.equal(display.scorePreference(search,'cost-score'),'partial');
 assert.equal(display.scorePreference(search,'sort-research'),'strict');
});

test('invalid or absent values fall back locally without overriding another panel',()=>{
 const search='?score=unknown&sort-written=capability&cost-score=unknown',display=load(search);
 assert.equal(display.state.score,'strict');
 assert.equal(display.scorePreference(search,'sort-written'),'capability');
 assert.equal(display.scorePreference(search,'cost-score'),'strict');
 assert.equal(display.scorePreference('?score=capability','cost-score'),'strict');
});
