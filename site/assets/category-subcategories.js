/* Category disclosures reuse saved contributions and the parent board's order. */
(function(root,factory){
 const api=factory();
 if(typeof module==='object'&&module.exports)module.exports=api;
 if(root?.MG)api.mount(root);
})(typeof window==='object'?window:null,()=>{
 'use strict';
 function project(data,groupId,score,selectResult){
  const group=data.policy.groups.find(group=>group.id===groupId);
  const board=data.category_leaderboards.find(board=>board.id===groupId);
  if(!group||!board?.views[score])return null;
  const models=new Map(data.models.filter(model=>model.presentation_eligibility?.ranked!==false).map(model=>[model.id,model]));
  const columns=group.children.map(id=>data.policy.subcategories.find(item=>item.id===id));
  return {columns,rows:board.views[score].filter(row=>models.has(row.model_id)).map(row=>{
   const model=models.get(row.model_id),report=selectResult(model,score);
   return {model,cells:columns.map(column=>report.contributions[column.id])};
  })};
 }
 function mount(win){
  const {d,state,modes,node,f,result,knownValue,href}=win.MG;
  const signatures=new Map();
  function render(){
   let changed=false;
   for(const group of d.policy.groups){
    const section=win.document.getElementById('category-subcategories-'+group.id);
    if(!section)continue;
    const score=win.MG.scorePreference(win.location.search,'sort-'+group.id);
    const signature=JSON.stringify([state.condition,score]);
    if(signatures.get(group.id)===signature)continue;
    signatures.set(group.id,signature);
    const view=project(d,group.id,score,(model,mode)=>result(model,state.condition,mode));
    if(!view)continue;
    section.querySelector('[data-subcategory-mode]').textContent=modes[score].abbreviation;
    const table=win.document.getElementById('subcategory-table-'+group.id);
    table.replaceChildren();
    const header=table.createTHead().insertRow(),first=node('th','模型');first.scope='col';header.append(first);
    for(const column of view.columns){const cell=node('th',column.title+' / '+column.weight);cell.scope='col';header.append(cell)}
    const body=table.createTBody();
    for(const row of view.rows){
     const line=body.insertRow(),label=node('th'),link=node('a',row.model.label,'model-name');label.scope='row';
     const target=new URL(href('models/'+row.model.id+'/index.html'));target.searchParams.set('score',score);link.href=target.href;
     label.append(link);line.append(label);
     row.cells.forEach((metric,index)=>{
      const value=knownValue(metric),cell=line.insertCell();
      cell.textContent=value==null?'—':f(value)+' / '+view.columns[index].weight;
      if(value<0)cell.classList.add('negative');
      cell.title='完整贡献区间 '+f(metric.lower)+'–'+f(metric.upper)+' / '+view.columns[index].weight;
     });
    }
    changed=true;
   }
   if(changed)win.MGI18n.apply(state.lang);
  }
  win.addEventListener('mg:updated',render);
  render();
  return {render};
 }
 return {project,mount};
});
