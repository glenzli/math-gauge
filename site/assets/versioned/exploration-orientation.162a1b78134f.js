/* Descriptive source adapter for the shared mathematical-profile interface. */
(function(root,factory){
 const api=factory();
 if(typeof module==='object'&&module.exports)module.exports=api;
 if(root&&root.document){root.MGExplorationOrientation=api;api.mount(root)}
})(typeof window==='object'?window:null,()=>{
 'use strict';
 const AXES=['horizontal_expansion','vertical_deepening','structural_reframing','boundary_probing','experimental_exploration'];
 const POLICY='3affe9a8ad2a7e3af36279bac65a04adec242a5453858a57f01f2e01455e4f7b';
 const states={not_identifiable:['未能识别取向','Not identifiable'],missing_source:['原文缺失','Source missing'],unsettled_source:['来源未结算','Source unsettled'],incomplete_trajectory:['轨迹未齐','Trajectory incomplete'],unobservable_freedom:['自由度不可观察','Choice not observable'],exposure_blocked:['存在观察阻碍','Observation blocked'],classification_unresolved:['分类未决','Classification unresolved'],review_pending:['待评审','Review pending']};
 const roles=[['本次未观察','偶发探针','局部路线','持续主线','中心策略'],['Not observed here','Incidental probe','Local route','Sustained mainline','Central strategy']];
 const tags={restructured_route:['后续重构路线','Later route reframing'],abandoned_route:['后续放弃路线','Later route abandoned'],corrected_route:['后续修正路线','Later route corrected'],unclosed_attempt:['含未闭合尝试','Includes unclosed work'],failed_attempt_observed:['含失败尝试','Includes failed attempts']};
 const definitions={
  horizontal_expansion:[['横向拓展','Horizontal expansion'],['实际研究相邻对象、问题或情境，并追查它们之间的联系。','Investigating adjacent objects, questions or settings and their connections.']],
  vertical_deepening:[['纵向深挖','Vertical deepening'],['围绕同一问题继续追查机制、依赖、精确程度或具体瓶颈。','Following mechanisms, dependencies, precision or concrete bottlenecks within a question.']],
  structural_reframing:[['结构重构','Structural reframing'],['改换对象、表示、不变量或组织方式，并实际检验新旧关系。','Changing objects, representations, invariants or organization and testing the resulting bridge.']],
  boundary_probing:[['边界探查','Boundary probing'],['研究额外的假设放松、退化、锐性、可行性、反例或障碍。','Investigating additional relaxations, degeneracies, sharpness, feasibility, counterexamples or barriers.']],
  experimental_exploration:[['实验探索','Experimental exploration'],['用有问题指向的数值、符号、枚举或手工试验推动后续选择。','Using question-directed numerical, symbolic, enumerative or manual probes to guide subsequent choices.']]
 };
 const messages={
  description:['五种探索取向 · 每轴0–4 · 描述研究方式，不计总分','Five exploration orientations · 0–4 per axis · Research approach, no total'],
  note:['0 本次未观察 · 1 偶发探针 · 2 局部路线 · 3 持续主线 · 4 中心策略。缺口留空，不比较面积。','0 Not observed here · 1 Incidental probe · 2 Local route · 3 Sustained mainline · 4 Central strategy. Gaps stay open; no area comparison.'],
  values:['五轴档位与观察状态','Five-axis levels and observation states'],
  coverage:['同一三轮研究轨迹的组织方式；数值不是能力分数，其他题的补证不混入档位。','Organizing roles in the same three-round research trajectory, not capability scores. Cross-task corroboration does not enter these levels.'],
  meanings:['五种探索方式与观察范围','Five research approaches and observation scope'],
  scope:['主图统一观察采用的三轮原稿及明确附件，包含第二轮受邀推进。它描述本次选择，不代表稳定偏好；认真失败或未闭合的路线可以体现取向，数学真伪仍单独判断。','The anchor is the complete adopted three-round trajectory and delivered companions, including invited follow-up in round two. This describes choices here, not a stable preference. Serious failed or unclosed work may reveal orientation; mathematical truth remains separate.'],
  chart:['五轴探索取向，固定0至4刻度，不计总分','Five-axis exploration orientation, fixed scale 0–4, no total'],
  table:['所选来源的五轴探索档位与观察状态，不作排名','Five exploration levels and observation states, without ranking']
 };
 function prepare(data){
  const value=data?.exploration_orientation;
  if(data?.benchmark_version!=='1.3.0'||value?.schema!=='math-gauge.exploration-orientation/v1'||value.edition!=='1.3.0'||value.policy_sha256!==POLICY||value.axis_order?.join('|')!==AXES.join('|')||value.scale?.join('|')!=='0|4'||value.source_index?.path!=='results/exploration-orientation/v0.1.0/index.json'||!/^[a-f0-9]{64}$/.test(value.source_index?.sha256||''))return null;
  if(!Array.isArray(data.models)||!Array.isArray(value.models)||value.models.length!==19)return null;
  const current=new Map(data.models.map(model=>[model.id,model]));
  if(current.size!==19||new Set(value.models.map(model=>model.model_id)).size!==19)return null;
  const models=[];
  for(const profile of value.models){
   if(!current.has(profile.model_id)||profile.policy_sha256!==POLICY||profile.is_score!==false||profile.higher_is_better!==null)return null;
   for(const axis of AXES){const row=profile.axes?.[axis];if(!row||!(row.grade===null&&Object.hasOwn(states,row.state)||Number.isInteger(row.grade)&&row.grade>=0&&row.grade<=4&&row.state===(row.grade===0?'reviewed_absence':'reviewed')))return null}
   models.push({...current.get(profile.model_id),profile});
  }
  return {component:value,models};
 }
 function createProject(ready){
  const reports=new Map(ready.models.map(model=>[model.id,model.profile]));
  // Bounds are plotting coordinates only. Source levels remain integers0–4;
  // null never becomes a score or a filled vertex.
  const metrics=Object.fromEntries(ready.models.map(model=>[model.id,Object.fromEntries(AXES.map(axis=>{
   const row=model.profile.axes[axis],value=row.grade;
   return [axis,{exact:value,lower:value??0,upper:value??4,confirmed:value??0,state:row.state,coverage:{unit:'orientation_axis',planned:1,reviewed:value===null?0:1}}];
  }))]));
  return {id:'exploration',label:['探索取向','Exploration orientation'],maximum:4,ticks:[1,2,3,4],metrics,messages,
   axes:AXES.map(id=>({id,label:{zh:definitions[id][0][0],en:definitions[id][0][1]},description:{zh:definitions[id][1][0],en:definitions[id][1][1]}})),
   coverage:(metric,lang)=>metric.exact===null?states[metric.state][lang==='en'?1:0]:roles[lang==='en'?1:0][metric.exact],
   legend:(model,lang)=>(reports.get(model.id).tags||[]).filter(key=>tags[key]).map(key=>tags[key][lang==='en'?1:0]).join(' · '),reports};
 }
 function mount(win){
  const data=win.MG?.d||win.MG?.data||win.MGResults?.data,ready=prepare(data);
  const controller=win.MGMathematicalProfile?.controller,extras=win.document.getElementById('exploration-orientation');
  if(!ready||!controller?.registerProject||!extras)return null;
  const project=createProject(ready);project.extras=extras;
  const doc=win.document,node=(tag,text,cls)=>{const item=doc.createElement(tag);if(text!==undefined)item.textContent=text;if(cls)item.className=cls;return item};
  project.renderExtras=({models,lang})=>{
   const english=lang==='en',get=key=>extras.querySelector('[data-eo="'+key+'"]');
   for(const [key,text]of Object.entries({'support-title':['跨题补证','Cross-task corroboration'],'method-link':['方法与边界','Method and limits'],'json-link':['下载数据','Download data']}))get(key).textContent=text[english?1:0];
   const table=node('table',undefined,'compact mp-table'),head=node('thead'),row=node('tr');row.append(node('th',english?'Model':'模型'));
   project.axes.forEach(axis=>row.append(node('th',axis.label[lang])));head.append(row);const body=node('tbody');
   for(const model of models){const tr=node('tr');tr.append(node('th',model.label));for(const axis of AXES){
    const value=project.reports.get(model.id).corroboration[axis],cell=node('td');
    const lines=value.support===null?[english?'Main axis unknown; corroboration does not fill it':'主轴未知，补证不代填']:
     [(english?'Also observed elsewhere: ':'跨题亦见：')+value.support,(english?'Another context: ':'异境亦见：')+value.difference,(english?'Insufficient: ':'补证不足：')+value.insufficient];
    lines.push((english?'Screened: ':'已筛查：')+value.screened_families+'/27');lines.forEach(text=>cell.append(node('span',text,'eo-corroboration-value')));tr.append(cell);
   }body.append(tr)}table.append(head,body);get('support').replaceChildren(table);
   get('support-note').textContent=english?'The same 27 first-answer families reuse existing full reviews and independently checked extra passages. These observations do not enter the radar; insufficient corroboration does not imply no other exploration.':'另27个共同首答家族复用既有全文审核，并核读候选额外片段。只作补证，不进入雷达；补证不足不表示没有其他探索。';
  };
  return controller.registerProject(project)?project:null;
 }
 return {AXES,prepare,createProject,mount};
});
