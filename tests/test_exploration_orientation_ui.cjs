/* Synthetic public aggregates only; no model evaluation or mathematical answers. */
const assert=require('node:assert/strict');
const {test}=require('node:test');
const ui=require('../scripts/templates/exploration-orientation.js');
const POLICY='3affe9a8ad2a7e3af36279bac65a04adec242a5453858a57f01f2e01455e4f7b';
const ids=['sol-6.1-max','sol-6.2-max','terra-6.1-max','astra-6-max','astra-6-xhigh','astra-6.2-max','sol-6.1-xhigh','sol-6.2-xhigh','terra-6.1-xhigh','claude-opus-5.5-max','claude-opus-5.5-xhigh','claude-sonnet-5.5-max','kimi-3.1-pro-max','astra-6.2-xhigh','deepseek-v4.1-flash-1017','gemini-4-neon-xhigh','gemini-4-hydrogen-xhigh','gemini-4-carbon-medium','dot-20261125'];
function fixture(){return {benchmark_version:'1.3.0',models:ids.map(id=>({id,label:id})),exploration_orientation:{schema:'math-gauge.exploration-orientation/v1',edition:'1.3.0',policy_sha256:POLICY,axis_order:ui.AXES,scale:[0,4],source_index:{path:'results/exploration-orientation/v0.1.0/index.json',sha256:'a'.repeat(64)},models:ids.map(id=>({model_id:id,policy_sha256:POLICY,is_score:false,higher_is_better:null,axes:Object.fromEntries(ui.AXES.map(a=>[a,{grade:2,state:'reviewed'}])),corroboration:Object.fromEntries(ui.AXES.map(a=>[a,{support:0,difference:0,insufficient:27,observed_fragment_families:0,screened_families:27}]))}))}}}
test('only the exact current cohort and unchanged descriptive policy can register',()=>{
 const d=fixture();assert(ui.prepare(d));d.benchmark_version='1.2.0';assert.equal(ui.prepare(d),null);
 d.benchmark_version='1.3.0';d.exploration_orientation.models.pop();assert.equal(ui.prepare(d),null);
 const other=fixture();other.exploration_orientation.models[0].is_score=true;assert.equal(ui.prepare(other),null);
});
test('the display adapter preserves integer levels, genuine zero and unknown without rewriting the source',()=>{
 const data=fixture(),report=data.exploration_orientation.models[0];report.axes.horizontal_expansion={grade:0,state:'reviewed_absence'};
 report.axes.experimental_exploration={grade:null,state:'missing_source'};
 const before=structuredClone(data),project=ui.createProject(ui.prepare(data));
 assert.equal(project.maximum,4);assert.deepEqual(project.ticks,[1,2,3,4]);
 assert.equal(project.metrics[ids[0]].horizontal_expansion.exact,0);
 assert.equal(project.metrics[ids[0]].experimental_exploration.exact,null);
 assert.equal(project.coverage(project.metrics[ids[0]].horizontal_expansion,'en'),'Not observed here');
 assert.equal(project.coverage(project.metrics[ids[0]].experimental_exploration,'en'),'Source missing');
 assert.deepEqual(data,before);
});
test('mount delegates to the existing profile controller instead of creating another picker or selection state',()=>{
 const data=fixture(),extras={hidden:true},registered=[];
 const win={MG:{d:data},document:{getElementById:()=>extras},MGMathematicalProfile:{controller:{registerProject(project){registered.push(project);return true}}}};
 const project=ui.mount(win);assert.equal(registered[0],project);assert.equal(project.extras,extras);
 assert.equal(ui.readSelection,undefined);assert.equal(ui.selectionUrl,undefined);
 delete win.MGMathematicalProfile;assert.equal(ui.mount(win),null);
});
