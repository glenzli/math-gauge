(() => {
 const {d,state,modes,el,node,taskValue,start}=MG;
 const revisionNote=()=>{const task=d.case.views[state.score][state.condition];if(task.neutral_revision)el('case-score-note').textContent=state.lang==='en'?'SMC blends 80% first answer with 20% continuation; the original judgments are retained separately.':'SMC按首答80%＋续答20%合成；原首答判定和续答原评分别保留。';};
 start(()=>{
  const task=d.case.views[state.score][state.condition], n=el('case-score');n.replaceChildren(node('span',taskValue(task),'metric-value'),node('span',modes[state.score].abbreviation,'tag mono'));
  el('case-score-note').textContent=task.neutral_revision?(state.lang==='en'?'SMC blends 80% first answer with 20% continuation; the original judgments are retained separately.':'SMC按首答80%＋续答20%合成；原首答判定和续答原评分别保留。'):task.strict_pass==null?'SMC：未知。':task.strict_pass?'SMC：通过。':'SMC：未通过。';
  document.querySelectorAll('[data-evidence-condition]').forEach(n=>n.hidden=n.dataset.evidenceCondition!==state.condition);
 });
 window.addEventListener('mg:updated',revisionNote);revisionNote();
})();
