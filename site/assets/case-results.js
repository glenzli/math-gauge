(() => {
 const {d,state,modes,el,node,taskValue,start}=MG;
 start(()=>{
  const task=d.case.views[state.score][state.condition], n=el('case-score');n.replaceChildren(node('span',taskValue(task),'metric-value'),node('span',modes[state.score].abbreviation,'tag mono'));
  el('case-score-note').textContent=task.strict_pass==null?'Strict：未知。':task.strict_pass?'Strict：通过。':'Strict：未通过。';
  document.querySelectorAll('[data-evidence-condition]').forEach(n=>n.hidden=n.dataset.evidenceCondition!==state.condition);
 });
})();
