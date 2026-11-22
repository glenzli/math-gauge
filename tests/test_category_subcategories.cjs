const {test}=require('node:test');
const assert=require('node:assert/strict');
const {project}=require('../scripts/templates/category-subcategories.js');

function fixture(){
 const metric=value=>({exact:value,confirmed:value,lower:value,upper:value,complete:true,coverage:{adjudicated:1}});
 const models=['a','b','hidden'].map(id=>({id,presentation_eligibility:{ranked:id!=='hidden'}}));
 const data={models,policy:{groups:[{id:'lean',children:['audit','engineering','selfcheck']}],
  subcategories:[{id:'audit',weight:10},{id:'engineering',weight:15},{id:'selfcheck',weight:10}]},
  category_leaderboards:[{id:'lean',views:{strict:[{model_id:'b'},{model_id:'hidden'},{model_id:'a'}],
   partial:[{model_id:'a'},{model_id:'b'}]}}]};
 const reports=Object.fromEntries(models.map(model=>[model.id,Object.fromEntries(['strict','partial'].map(mode=>[mode,
  {contributions:{audit:metric(mode==='strict'?0:7.5),engineering:metric(15),selfcheck:metric(0)}}]))]));
 return {data,reports,select:(model,mode)=>reports[model.id][mode]};
}

test('subcategory rows use the parent category order and selected report, independently of overall sorting',()=>{
 const {data,reports,select}=fixture(),original=structuredClone(data),calls=[];
 const view=project(data,'lean','partial',(model,mode)=>{calls.push([model.id,mode]);return select(model,mode)});
 assert.deepEqual(view.rows.map(row=>row.model.id),['a','b']);
 assert.deepEqual(calls,[['a','partial'],['b','partial']]);
 assert.equal(view.rows[0].cells[0],reports.a.partial.contributions.audit);
 assert.deepEqual(view.columns.map(column=>column.weight),[10,15,10]);
 assert.deepEqual(data,original);
 assert.deepEqual(project(data,'lean','strict',select).rows.map(row=>row.model.id),['b','a']);
});

test('saved zero, signed credit and unknown intervals survive without normalization or recomputation',()=>{
 const {data,reports,select}=fixture();
 const unknown={exact:null,confirmed:0,lower:0,upper:10,complete:false,coverage:{adjudicated:0}};
 reports.b.partial.contributions.audit={exact:-2,confirmed:-2,lower:-2,upper:-2};
 reports.b.partial.contributions.selfcheck=unknown;
 const row=project(data,'lean','partial',select).rows.find(row=>row.model.id==='b');
 assert.equal(row.cells[0].exact,-2);
 assert.equal(row.cells[1].exact,15);
 assert.equal(row.cells[2],unknown);
 assert.equal(project(data,'lean','strict',select).rows[0].cells[0].exact,0);
});

test('missing category or score mode never fabricates subcategory results',()=>{
 const {data,select}=fixture();
 assert.equal(project(data,'missing','strict',select),null);
 assert.equal(project(data,'lean','capability',select),null);
});
