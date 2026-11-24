/* Independent supplied mathematical axes. This UI never computes benchmark credit. */
(function(root,factory){
 const api=factory();
 if(typeof module==='object'&&module.exports)module.exports=api;
 if(root&&root.document){root.MGMathematicalProfile=api;api.mount(root)}
})(typeof window==='object'?window:null,()=>{
 'use strict';
 const AXES=['proof','fidelity','completion','discernment','initiative','depth','closure'];
 const BRANDS={openai:{label:'OpenAI',color:'#252525'},claude:{label:'Claude',color:'#d97757'},google:{label:'Google',color:'#45965d'},kimi:{label:'Kimi',color:'#3568d4'},deepseek:{label:'DeepSeek',color:'#4d6bfe'},glm:{label:'GLM',color:'#af7b15'}};
 const VARIANTS=[{dash:'',marker:'circle'},{dash:'7 3',marker:'square'},{dash:'2 3',marker:'triangle'},
  {dash:'12 4',marker:'diamond'},{dash:'9 3 2 3',marker:'plus'},{dash:'4 3 1 3',marker:'cross'},
  {dash:'15 3 2 3',marker:'hexagon'},{dash:'18 4 3 4',marker:'ring'},{dash:'6 3 6 3 1 3',marker:'pentagon'},
  {dash:'10 2 2 2 2 2',marker:'circle'},{dash:'18 3 2 3 2 3',marker:'diamond'}];
 const FALLBACK_VARIANTS=8;
 const STYLE_IDS={'astra-6.2-xhigh':10,'astra-6-max':0,'astra-6-xhigh':1,'sol-6.2-max':2,'sol-6.1-max':3,'sol-6.1-xhigh':4,
  'terra-6.1-max':5,'terra-6.1-xhigh':6,'dot-underlying-model-20261108':7,'sol-6.2-xhigh':8,'astra-6.2-max':9,
  'claude-opus-5.5-max':0,'claude-sonnet-5.5-max':1,'claude-opus-5.5-xhigh':2,'gemini-4-carbon-medium':0,
  'gemini-4-hydrogen-xhigh':1,'gemini-4-carbon-high':2,'gemini-4-argon':3,'gemini-3.8-flash-high':4};
 const messages={title:['数学画像','Mathematical profile'],description:['七个独立维度 · 每轴0–100','Seven independent dimensions · 0–100 per axis'],
  review:['AI评审 · 人工审核待完成','AI reviewed · Human review pending'],leader:['SMC榜首','SMC leader'],brands:['厂商首名','Vendor leaders'],clear:['清空','Clear'],
  brandHint:['按当前画像阶段的 SMC 选取最多五家厂商，各取首名。','Select the SMC leader from up to five vendors in the current profile stage.'],
  picker:['选择模型','Choose models'],selected:['已选','Selected'],of:['／',' / '],models:['个模型','models'],
  note:['逐轴比较；区间与断线表示证据缺口。','Compare individual axes. Intervals and gaps indicate missing evidence.'],
  focus:['悬停或聚焦模型可突出曲线；点击可固定。','Hover or focus a model to emphasize its curve; click to pin.'],
  values:['数值与家族覆盖','Values and family coverage'],coverage:['覆盖数按各轴统计，轴间不相加。画像不随顶部计分口径切换。','Coverage is reported per axis and is not added across axes. The profile is independent of the score selector.'],
  empty:['选择模型开始对照。','Choose models to compare.'],model:['模型','Model'],families:['家族','families'],confirmed:['已确认','Confirmed'],
  exactAxes:['轴完整计分','axes with exact scores'],range:['区间','Interval'],unknown:['证据未齐','Evidence incomplete'],
  chart:['七轴数学画像，固定0至100刻度','Seven-axis mathematical profile, fixed scale from 0 to 100'],table:['所选模型的独立数学维度及审核家族覆盖','Independent mathematical axes and reviewed-family coverage for selected models']};
 Object.assign(messages,{
  description:['六轴独立评审 · 严格完成度取主榜SMC · 每轴0–100','Six reviewed axes · strict completion uses official SMC · 0–100 per axis'],
  note:['已结算空白计0；可核实的截止前内容按实际论证评估，未交卷仍影响SMC。区间与断线表示真正未知。','Settled blanks receive 0. Verified cutoff work is assessed for its reasoning; nondelivery still affects SMC. Intervals and gaps indicate genuine unknowns.'],
  values:['数值与已结算范围','Values and settled coverage'],
  coverage:['六个独立评审轴各用35家族；严格完成度直接取规则选定答卷的正式SMC，沿用主榜权重与三轮自查规则。画像固定使用这组答卷，不随顶部显示口径切换。','The six reviewed axes each use 35 families. Strict completion copies the official SMC for the rule-selected answers, retaining its weights and three-round self-review rules. The profile stays bound to these answers and does not follow the display selector.'],
  settled:['家族已结算','families settled'],smc:['主榜SMC','Official SMC'],categories:['计分类别','scoring categories'],
  meanings:['七轴含义与范围','What the seven axes measure'],
  scope:['六轴覆盖39道初答与3轮自查、固定35家族，不限六道命题拓展题。SMC使用正式主榜权重，整条自查占10%；论证高档要求原题核心成立，局部成果不能抵补核心缺口。','Six axes cover 39 initial answers and 3 rounds of self review across 35 fixed families, beyond the six theorem extension tasks. SMC retains the official weights, including 10% for the whole review trajectory. High reasoning grades require the original core; partial results cannot compensate for an essential gap.']
 });
 const researchMessages={
  description:['能力与主动行为分开看 · 每轴0–100','Capability and unsolicited behavior, separately · 0–100 per axis'],
  meanings:['八轴含义与范围','What the eight axes measure'],
  chart:['八轴数学画像，固定0至100刻度','Eight-axis mathematical profile, fixed scale from 0 to 100'],
  coverage:['原有五个能力评审轴与研究主动性沿用35家族；开放研究能力独立使用五个共同开放家族；严格完成度取正式SMC。各轴覆盖分别展示，不按雷达面积排名。','The five original reviewed capability axes and initiative retain 35 families. Open research capability independently uses five common open-task families; strict completion copies official SMC. Coverage is separate per axis, and polygon area is not a ranking.'],
  scope:['开放研究能力看明确要求研究时实际交出的机制、条件和闭合成果；完成原题即可得最高档。末位研究主动性只观察未被要求时是否自行展开，不表示能力上限或越高越合适。其余轴与主分不变。','Open research capability evaluates mechanisms, justified conditions and closed results under an explicitly open request; completing the actual task can earn the highest grade. Initiative, shown last, describes unsolicited first-answer behavior, not a capability ceiling or automatic suitability. Other axes and main scores are unchanged.'],
  openResearch:['开放研究','Open research']
 };
 const formalizationMessages={
  description:['论证、研究与形式化 · 每轴0–100','Reasoning, research and formalization · 0–100 per axis'],
  meanings:['九轴含义与范围','What the nine axes measure'],
  chart:['九轴数学画像，固定0至100刻度','Nine-axis mathematical profile, fixed scale from 0 to 100'],
  coverage:['形式化能力取Lean整体SMC，含语义审计、工程和三轮对齐自查；开放研究能力独立使用五个共同开放家族；严格完成度取正式SMC；其余评审轴沿用35家族。各轴覆盖分别展示，不按雷达面积排名。','Formalization projects SMC for the full Lean category: audits, engineering and three-round alignment self-checks. Open research independently uses five common open-task families; strict completion copies official SMC; the other reviewed axes retain 35 families. Coverage is separate per axis, and polygon area is not a ranking.'],
  scope:['形式化能力采用Lean整体SMC：审计10分、工程15分、三轮对齐自查10分；每题与整条自查须全部要求达标，两个阶段使用同一初答与原有自查轨迹。开放研究能力看明确开放请求下的研究交付；末位研究主动性观察首答自发行为。','Formalization uses full Lean SMC: audits (10), engineering (15) and the three-round self-check trajectory (10). Every required task/trajectory condition must pass. Both stages use the same initial answers and prescribed trajectory. Open research concerns explicitly requested research; initiative, shown last, describes unsolicited first-answer behavior.'],
  formalization:['Lean子类','Lean subcategories']
 };
 const tasteAxis={id:'mathematical_taste',label:{zh:'数学品味',en:'Mathematical taste'},description:{
  zh:'独立开放研究三稿的数学品味连续评审分（RMC 展示）。',
  en:'Mathematical taste from the continuous review of three independent open research manuscripts (RMC display).'}};
 const tasteMessages={
  description:['每轴0–100 · 研究主动性含受邀自主 · 数学品味 RMC','0–100 per axis · Initiative includes invited autonomy · Mathematical taste (RMC)'],
  meanings:['十轴含义与范围','What the ten axes measure'],
  chart:['十轴数学画像，固定0至100刻度','Ten-axis mathematical profile, fixed scale from 0 to 100'],
  scope:['画像采用含已接纳续答的证据。受邀自主、研究能力和品味来自同一三轮研究题。严格完成度取 1.3 主榜 SMC。','The profile uses evidence including adopted continuations. Invited autonomy, research capacity and taste use the same three-round research task. Strict completion uses the official 1.3 SMC.'],
  coverage:['画像分别显示基底和本题覆盖。数学品味使用三份研究稿，严格完成度使用 1.3 主榜覆盖。','The profile reports retained and new-task coverage separately. Taste covers three manuscripts and strict completion uses the 1.3 leaderboard coverage.'],
  tasteManuscripts:['品味稿件','Taste manuscripts'],tasteUnknown:['未知','Unknown'],
  newTask:['本题','New task'],components:['分项','components'],baseUnknown:['基底覆盖未知','Base coverage unknown']
 };
 const blendedTasteMessages={...tasteMessages,
  scope:['研究自主（A）进入研究主动性和开放研究能力，研究能力（C）进入数学深度和开放研究能力，数学品味（T）进入品味和数学审辨力。品味还合并六个旧题家族含已接纳续答的直接评审。严格完成度取 1.3 主榜 SMC。','Research autonomy (A) contributes to initiative and open research capability. Research capacity (C) contributes to mathematical depth and open research capability. Mathematical taste (T) contributes to taste and discernment. Taste also includes direct reviews of six retained families, including adopted continuations. Strict completion uses the official 1.3 SMC.'],
  coverage:['品味分别显示三稿与六家族的覆盖，缺少可评证据时保留区间。','Taste reports coverage separately for three manuscripts and six families. Missing evidence leaves an interval.'],
  legacyTaste:['旧题家族','Retained families']};
 const strictTasteMessages={...blendedTasteMessages,
  description:['每轴0–100 · 数学品味采用严格检查与复核','0–100 per axis · Strict mathematical taste assessment'],
  scope:['研究自主（A）用于研究主动性和开放研究能力，研究能力（C）用于数学深度和开放研究能力。数学品味（T）采用新题严格检查和含已接纳续答的旧题严格复核。数学审辨力仍使用新题品味 RMC。严格完成度取 1.3 主榜 SMC。','Research autonomy (A) contributes to initiative and open research capability. Research capacity (C) contributes to mathematical depth and open research capability. Taste (T) uses new-task strict checks and strict reviews of retained answers, including adopted continuations. Discernment continues to use new-task taste RMC. Strict completion uses the official 1.3 SMC.'],
  coverage:['新题覆盖按已判定的品味检查统计。旧题覆盖按该阶段可确定品味分的家族统计。','New-task coverage counts settled taste checkpoints. Retained coverage counts families with a determinate taste score for this stage.'],
  tasteCheckpoints:['品味检查已判定','Taste checks settled'],legacyTaste:['旧题有确值家族','Retained families scored'],
  strictSourceUnavailable:['旧题严格复核汇总未提供','Retained strict assessment unavailable']};
 const valueTasteMessages={...strictTasteMessages,
  scope:['研究主动性保留首答自发拓展基底，再吸收本题中研究能力既定范围之外的自主拓展档位。研究能力（C）进入数学深度和开放研究能力。数学审辨力使用本题品味 RMC。数学品味采用新题严格检查和含已接纳续答的旧题严格复核。严格完成度取 1.3 主榜 SMC。',
   'Research initiative retains the unsolicited first-answer evidence and adds one extension level for work beyond the new task’s capacity scope. Capacity (C) contributes to depth and open research capability. Discernment uses task taste RMC. Mathematical taste combines new-task strict checks with retained strict reviews, including adopted continuations. Strict completion uses the official 1.3 SMC.'],
  extension:['自主拓展','Autonomous extension']};
 const strictCreditTasteMessages={...valueTasteMessages,
  scope:['研究主动性保留首答自发拓展基底，再吸收本题中研究能力既定范围之外的自主拓展档位。研究能力（C）进入数学深度和开放研究能力。数学审辨力使用本题品味 RMC。数学品味采用新题通过检查部分的净信用和含已接纳续答的旧题严格复核。严格完成度取 1.3 主榜 SMC。',
   'Research initiative retains unsolicited first-answer evidence and adds the extension level. Capacity (C) contributes to depth and open research capability. Discernment uses task taste RMC. Mathematical taste combines the net credit of passed checks with retained strict reviews, including adopted continuations. Strict completion uses the official 1.3 SMC.'],
  coverage:['新题检查覆盖与严格净信用分开。旧题覆盖按本阶段品味有确值的家族统计。',
   'New-task checkpoint coverage is shown separately from strict net credit. Retained coverage counts families with a determinate taste score for the selected stage.']};
 const opportunityMessages={
  scope:['研究主动性按共同的28个拓展机会重新评审：27个原题首答，加上独立研究三稿中的一个域外机会。每个机会等权，统一评0–4档；必做证明和常规工具不算拓展，实际成立的深入追问或明确障碍才计入。其余轴与主榜成绩保持原口径。',
   'Research initiative is independently reviewed on 28 common extension opportunities: 27 original first answers and one beyond-scope opportunity across the three research manuscripts. Each has equal weight on one 0–4 scale. Required proofs and routine tools are excluded; verified further inquiry and precise barriers count. Other axes and leaderboard scores retain their existing methods.'],
  coverage:['研究主动性单独显示28个拓展机会的覆盖；新题未测保留未知，不补零。其他维度仍分别显示原有家族、子类或检查覆盖。',
   'Initiative reports coverage of 28 extension opportunities separately. An untested new task remains unknown. Other axes retain their family, subcategory or checkpoint coverage.'],
  initiativeOpportunities:['拓展机会','Extension opportunities']};
 const opportunityDescription={zh:'27个原题首答与独立研究三稿中的1个拓展机会，等权按0–4档核验实际自发追问；不由完成分或旧E档换算，也不表示能力上限。',
  en:'Verified unsolicited inquiry across 27 original first answers and one opportunity in the three research manuscripts, equally weighted on a common 0–4 scale. It is not inferred from completion scores or old E labels, and is not a capability ceiling.'};
 const strictTasteStates={
  'not-tested':['新题未测','New task untested'], 'review-pending':['品味待评','Taste review pending'],
  'insufficient-evidence':['检查证据不足','Insufficient checkpoint evidence'], 'delivery-failed':['未正常交付','No normal delivery'],
  unavailable:['品味检查未提供','Taste checkpoints unavailable']};
 const strictTasteSchema='math-gauge.independent-research-abilities/v4';
 const valueTasteSchema='math-gauge.independent-research-abilities/v5';
 const strictCreditTasteSchema='math-gauge.independent-research-abilities/v6';
 const itemWeightTasteSchema='math-gauge.independent-research-abilities/v7';
 const externalTasteSchema='math-gauge.independent-research-abilities/v8';
 const strictCreditTasteCompanion=companion=>[strictCreditTasteSchema,itemWeightTasteSchema,externalTasteSchema].includes(companion?.schema);
 const valueTasteCompanion=companion=>companion?.schema===valueTasteSchema||strictCreditTasteCompanion(companion);
 const strictTasteCompanion=companion=>companion?.schema===strictTasteSchema||valueTasteCompanion(companion);
 function matchesItemWeightSource(companion,board){
  const expected=board?.item_weight_binding,binding=companion.item_weight_binding;
  return expected?.version==='0.1.0'&&binding&&Object.keys(expected).length===Object.keys(binding).length&&
   Object.entries(expected).every(([key,value])=>binding[key]===value)&&
   (companion.schema!==externalTasteSchema||board?.schema==='math-gauge.research-board-preview/v6'&&
    JSON.stringify(companion.external_binding)===JSON.stringify(board.external_binding));
 }
 const profileViews={radar:['雷达图','Radar'],bars:['按轴排名','Axis ranking'],table:['表格','Table']};
 const profileViewCopy={mode:['画像展示方式','Profile view'],axis:['排名维度','Ranking axis'],
  tableCaption:['本版全部合格模型的数学画像及审核覆盖','Mathematical profiles and review coverage for all eligible models in this edition'],
  unranked:['证据未齐 · 未排名','Incomplete evidence · Unranked'],unknown:['未知','Unknown'],scale:['分数 · 0–100','Score · 0–100']};
 const profileMixes={initiative:'initiative_v130',depth:'depth_v130',open_research:'open_research_v130',discernment:'discernment_v130'};
 const versionedDescriptions={
  initiative:{zh:'首答的自发拓展观察，加上受邀研究中的自主推进证据。',en:'Unsolicited first-answer initiative combined with independent progress on the invited research task.'},
  depth:{zh:'原阶段的数学深度，加上本题核验的研究成果。',en:'Mathematical depth from the selected stage combined with verified results on the new research task.'},
  open_research:{zh:'原阶段的开放研究能力，加上本题的受邀自主与研究能力。',en:'Open research capability from the selected stage combined with invited autonomy and research capacity in the new task.'},
  discernment:{zh:'原阶段的数学审辨力，加上本题的数学品味。',en:'Mathematical discernment from the selected stage combined with mathematical taste on the new task.'},
  completion:{zh:'直接采用 1.3 主榜 SMC。',en:'Uses the official 1.3 leaderboard SMC directly.'}
 };
 const valueDescriptions={...versionedDescriptions,
  initiative:{zh:'首答的自发拓展基底，加上本题超出研究能力既定范围的自主拓展档位。',
   en:'Unsolicited first-answer initiative plus a level for independent extension beyond the new task’s capacity scope.'},
  open_research:{zh:'原阶段的开放研究能力，加上本题核验的研究能力（C）。',
   en:'Open research capability from the selected stage plus verified research capacity (C) on the new task.'}
 };
 const axisContext={completion:['沿用主榜SMC的全部严格完成门槛，不另算家族平均完成率。','This retains every official SMC completion gate, without a separate family-average completion rate.'],
  initiative:['自发行为需要与问题忠实度一起看；不从主动程度推断能力上限。','Read this behavior together with problem fidelity; initiative does not determine a capability ceiling.'],
  depth:['衡量实际成立的机制、自然范围与结构解释。','This concerns mechanisms, natural scope and structural insight that have actually been established.'],
  closure:['衡量实际交付的实质结果是否证明完整、依赖齐全、范围明确。','This concerns complete proofs, dependencies and explicit scope for the substantive results actually delivered.'],
  formalization:['复用已核准的Lean整体SMC（35分映射为100）；含语义审计、初答工程及原有三轮自查。首答与含续答同值。','This projects official Lean SMC (35 points mapped to 100), including audits, initial engineering and the original three-round trajectory. Both stages use the same values.']};
 Object.assign(messages,{continuation:['含续答','Include continuations'],
  continued:['续答','continued'],full:['满分率','full-score rate']});
 const finite=value=>typeof value==='number'&&Number.isFinite(value)&&value>=0&&value<=100;
 function brand(model){
  const name=String(model.logo?.label||'').toLowerCase().replace(/[^a-z0-9]/g,'');
  let key={openai:'openai',anthropic:'claude',claude:'claude',google:'google',kimi:'kimi',moonshot:'kimi',deepseek:'deepseek',zai:'glm',glm:'glm'}[name];
  if(!key)key=/^(astra|terra|sol|dot)-/.test(model.id)?'openai':/^claude-/.test(model.id)?'claude':/^gemini-/.test(model.id)?'google':/^kimi-/.test(model.id)?'kimi':/^deepseek-/.test(model.id)?'deepseek':/^glm-/.test(model.id)?'glm':null;
  return key?{key,...BRANDS[key]}:{key:'other-'+name,label:model.logo?.label||'Other',color:'#667085'};
 }
 function styleFor(model){
  let index=STYLE_IDS[model.id];
  if(index===undefined){let hash=0;for(const char of model.id)hash=(Math.imul(hash,31)+char.charCodeAt(0))>>>0;index=hash%FALLBACK_VARIANTS}
  return {...brand(model),...VARIANTS[index],index};
 }
 function representatives(models,compare,limit=5){
  const seen=new Set(),selected=[];
  for(const model of [...models].sort(compare)){const key=brand(model).key;if(!seen.has(key)){seen.add(key);selected.push(model.id);if(selected.length===limit)break}}
  return selected;
 }
 function readSelection(search,models,compare){
  const params=new URLSearchParams(search),valid=new Set(models.map(model=>model.id));
  if(!params.has('profile-models'))return representatives(models,compare);
  const requested=new Set(params.get('profile-models').split(',').filter(id=>valid.has(id)));
  return [...models].sort(compare).filter(model=>requested.has(model.id)).map(model=>model.id);
 }
 function selectionUrl(address,ids){const url=new URL(address);url.searchParams.set('profile-models',ids.join(','));return url.href}
 function viewFor(search,axes){
  const query=new URLSearchParams(search),view=query.get('profile-view'),axis=query.get('profile-axis');
  return {view:Object.hasOwn(profileViews,view)?view:'radar',axis:axes.some(item=>item.id===axis)?axis:axes[0].id};
 }
 function rankAxis(models,axis){
  const ranked=[],unknown=[];
  for(const model of models){
   const metric=model.profile_metrics[axis];
   if(finite(metric.exact))ranked.push({model,metric,displayed:Math.round(metric.exact*10)});
   else unknown.push({model,metric});
  }
  ranked.sort((a,b)=>b.displayed-a.displayed);
  ranked.forEach((item,index)=>item.rank=ranked[index-1]?.displayed===item.displayed?ranked[index-1].rank:index+1);
  return {ranked,unknown};
 }
 function validMetric(metric){return metric&&finite(metric.confirmed)&&finite(metric.lower)&&finite(metric.upper)&&metric.lower<=metric.upper&&
  (metric.exact===null||finite(metric.exact)&&metric.exact>=metric.lower&&metric.exact<=metric.upper)&&
  metric.coverage&&Number.isInteger(metric.coverage.reviewed)&&Number.isInteger(metric.coverage.planned)&&metric.coverage.reviewed>=0&&metric.coverage.planned>=metric.coverage.reviewed}
 function opportunityProjection(data){
  if(data.benchmark_version!=='1.3.0'||!Object.hasOwn(data,'research_initiative'))return null;
  const source=data.research_initiative,hash=value=>typeof value==='string'&&/^[a-f0-9]{64}$/.test(value);
  const valid=(metric,planned)=>validMetric(metric)&&metric.coverage.unit==='research_opportunity'&&metric.coverage.planned===planned&&
   metric.confirmed>=metric.lower&&metric.confirmed<=metric.upper&&
   (metric.exact===null)===(metric.coverage.reviewed<planned)&&
   (metric.exact===null||metric.lower===metric.exact&&metric.upper===metric.exact);
  if(source?.schema!=='math-gauge.research-initiative/v1'||source.version!=='0.1.0'||source.benchmark_version!=='1.3.0'||
   source.reviewer_kind!=='ai'||source.human_review!=='pending'||source.post_observation!==true||
   source.new_candidate_calls!==0||source.main_scores_modified!==false||source.original_bytes_rewritten!==false||
   !hash(source.policy_sha256)||!hash(source.source?.sha256)||!Array.isArray(source.models)||
   new Set(source.models.map(row=>row.id)).size!==source.models.length||source.models.some(row=>typeof row.id!=='string'||
    row.legacy_weight!=='27/28'||row.extension_weight!=='1/28'||
    !valid(row.metric,28)||!valid(row.legacy_metric,27)||!valid(row.extension_metric,1)||
    row.metric.coverage.reviewed!==row.legacy_metric.coverage.reviewed+row.extension_metric.coverage.reviewed))return false;
  return new Map(source.models.map(row=>[row.id,row.metric]));
 }
 function point(index,value,count=7){const angle=-Math.PI/2+index*2*Math.PI/count;return {x:260+Math.cos(angle)*148*value/100,y:225+Math.sin(angle)*148*value/100}}
 function geometry(axes,metrics){
  const vertices=axes.map((axis,index)=>metrics[axis.id].exact===null?null:{...point(index,metrics[axis.id].exact,axes.length),axis:axis.id,value:metrics[axis.id].exact});
  const segments=[];for(let i=0;i<axes.length;i++){const next=(i+1)%axes.length;if(vertices[i]&&vertices[next])segments.push([vertices[i],vertices[next]])}
  const intervals=axes.flatMap((axis,index)=>{const metric=metrics[axis.id];return metric.exact===null&&(metric.coverage.reviewed>0||metric.coverage.observed>0||metric.task_coverage?.components_reviewed>0||metric.taste_coverage?.reviewed>0)?
   [{axis:axis.id,index,lower:metric.lower,upper:metric.upper,from:point(index,metric.lower,axes.length),to:point(index,metric.upper,axes.length)}]:[]});
  return {vertices,segments,intervals,complete:vertices.every(Boolean)};
 }
 const hasRevisionStage=data=>['1.2.0','1.3.0'].includes(data?.benchmark_version);
 const fixedRevisionStage=data=>data?.benchmark_version==='1.3.0';
 function stageFor(data,search=''){
  if(fixedRevisionStage(data))return 'revision';
  const requested=new URLSearchParams(search).get('profile-stage');
  return hasRevisionStage(data)&&requested!=='first'&&data.mathematical_profile_revision?'revision':'first';
 }
 function tasteMetric(value){
  const known=finite(value?.exact)&&value.lower===value.exact&&value.upper===value.exact&&
   value.observed===3&&value.denominator?.unit==='manuscript'&&value.denominator.planned===3;
  const exact=known?value.exact:null;
  return {exact,lower:exact??0,upper:exact??100,confirmed:exact??0,
   coverage:{unit:'manuscript',planned:3,reviewed:known?3:0}};
 }
 function displayMetric(record,coverage){
  const metric={...record,coverage};
  return validMetric(metric)?metric:{exact:null,lower:0,upper:100,confirmed:0,coverage};
 }
 function blendedTasteMetric(value,strict){
  const families=value?.legacy_metric?.coverage,coverage=value?.independent_coverage;
  const unit=strict?'taste_checkpoint':'manuscript';
  const reviewed=strict?[0,1,2,3]:[0,3];
  if(families?.unit==='theorem_extension_family'&&families.planned===6&&coverage?.unit===unit&&
   coverage.planned===3&&reviewed.includes(coverage.reviewed)&&validMetric({...value,coverage:families})){
   return {...value,coverage:families,taste_coverage:coverage};
  }
  return {...displayMetric(null,{unit:'theorem_extension_family',planned:6,reviewed:0,observed:0}),
   taste_coverage:{unit,planned:3,reviewed:0},...(strict?{legacy_review_available:false}:{})};
 }
 function projectResearchMetrics(model,record,stage,blended,strict){
  const metrics={...model.profile_metrics};
  for(const [axis,key] of Object.entries(profileMixes)){
   const mixed=record?.stages?.[stage]?.[key],base=metrics[axis].coverage;
   metrics[axis]=displayMetric(mixed,mixed?.base_coverage||{unit:base.unit,planned:base.planned,reviewed:0});
  }
  const extension=record?.autonomous_extension?.level;
  if(['E0','E1','E2','E3'].includes(extension))metrics.initiative.extension_level=extension;
  const completion=record?.completion_v130,official=completion?.coverage;
  metrics.completion=displayMetric(completion,{unit:'fixed_weighted_category',planned:official?.planned??4,reviewed:official?.adjudicated??0});
  metrics[tasteAxis.id]=blended?blendedTasteMetric(record?.stages?.[stage]?.mathematical_taste,strict):tasteMetric(record?.mathematical_taste);
  return {...model,profile_metrics:metrics};
 }
 function prepare(data,compare,stage=fixedRevisionStage(data)?'revision':'first'){
  const modern=hasRevisionStage(data),revised=stage==='revision',corrected=!revised&&modern&&data.mathematical_profile_baseline,
   profile=revised?data?.mathematical_profile_revision:corrected||data?.mathematical_profile;
  if(!(modern||data?.benchmark_version==='1.1.0')||revised&&!modern||
   profile?.schema!==(revised?'math-gauge.mathematical-profile-revision/v1':corrected?'math-gauge.mathematical-profile-baseline/v1':'math-gauge.mathematical-profile/v1')||
   profile.version!==(revised||corrected?'0.1.0':'0.4.0')||profile.benchmark_version!==(revised||corrected?'1.2.0':'1.1.0')||
   profile.reviewer_kind!=='ai'||profile.human_review!=='pending'||!Array.isArray(profile.axes)||profile.axes.length!==7||
   new Set(profile.axes.map(axis=>axis.id)).size!==7||profile.axes.some(axis=>!AXES.includes(axis.id)||!axis.label?.zh||!axis.label?.en||!axis.description?.zh||!axis.description?.en)||
   !Array.isArray(profile.models)||!Array.isArray(data.models))return null;
  const profiles=new Map(profile.models.map(model=>[model.id,model.metrics]));
  const pool=!revised&&data.profile_models?.length?data.profile_models:data.models;
  let models=pool.filter(model=>model.presentation_eligibility?.ranked!==false&&profiles.has(model.id)&&profile.axes.every(axis=>validMetric(profiles.get(model.id)?.[axis.id])&&
    (profiles.get(model.id)[axis.id].coverage.planned===(axis.id==='completion'?8:35)&&profiles.get(model.id)[axis.id].coverage.unit===(axis.id==='completion'?'benchmark_subcategory':'mathematical_family'))))
   .map(model=>({...model,profile_metrics:profiles.get(model.id)})).sort(compare),axes=profile.axes;
  const capability=modern?data.open_research:null;
  if(capability){
   const valid=metric=>validMetric(metric)&&metric.coverage.unit==='open_research_family'&&metric.coverage.planned===5;
   if(capability.schema!=='math-gauge.open-research/v1'||capability.version!=='0.1.0'||capability.benchmark_version!=='1.2.0'||
    capability.axis?.id!=='open_research'||!capability.axis.label?.zh||!capability.axis.label?.en||
    !capability.axis.description?.zh||!capability.axis.description?.en||!Array.isArray(capability.models)||
    !valid(capability.pending_metric)||capability.models.some(row=>!valid(row.first)||row.revision!==null&&!valid(row.revision)))return null;
   const supplied=new Map(capability.models.map(row=>[row.id,row]));
   const behavior={...axes.find(axis=>axis.id==='initiative'),label:{zh:'研究主动性',en:'Research initiative'},description:{
    zh:'未被要求额外研究时，是否自行发现并验证值得追问的问题；这是首答中的自发行为观察，不能作为开放研究能力上限。',
    en:'Unsolicited, mathematically supported exploration in the first answer: a behavioral observation, not an estimate of open research capability.'}};
   axes=[...axes.filter(axis=>axis.id!=='initiative'),capability.axis,behavior];
   models=models.map(model=>({...model,profile_metrics:{...model.profile_metrics,
    open_research:supplied.get(model.id)?.[revised?'revision':'first']||capability.pending_metric}}));
  }
  const formalization=modern?data.formalization_profile:null;
  if(formalization){
   const valid=metric=>validMetric(metric)&&metric.coverage.unit==='lean_subcategory'&&metric.coverage.planned===3;
   if(formalization.schema!=='math-gauge.formalization-profile/v1'||formalization.version!=='0.1.0'||
    formalization.benchmark_version!=='1.2.0'||formalization.axis?.id!=='formalization'||
    !formalization.axis.label?.zh||!formalization.axis.label?.en||!formalization.axis.description?.zh||
    !formalization.axis.description?.en||!Array.isArray(formalization.models)||
    new Set(formalization.models.map(row=>row.id)).size!==formalization.models.length||
    formalization.models.some(row=>!valid(row.metric)))return null;
   const supplied=new Map(formalization.models.map(row=>[row.id,row.metric]));
   if(models.some(model=>!supplied.has(model.id)))return null;
   axes=[axes[0],formalization.axis,...axes.slice(1)];
   models=models.map(model=>({...model,profile_metrics:{...model.profile_metrics,formalization:supplied.get(model.id)}}));
  }
  if(data.benchmark_version==='1.3.0'&&axes.length===9){
   const companion=data.independent_research_abilities;
   const strict=strictTasteCompanion(companion);
   const strictCredit=strictCreditTasteCompanion(companion);
   const descriptions=valueTasteCompanion(companion)?valueDescriptions:versionedDescriptions;
   const blended=strict||companion?.schema==='math-gauge.independent-research-abilities/v3';
   const strictSources=!strict||companion.taste_blend?.independent_mode==='SMC'&&companion.taste_blend?.legacy_component_version==='0.2.0';
   const weightSource=![itemWeightTasteSchema,externalTasteSchema].includes(companion?.schema)||matchesItemWeightSource(companion,data.research_preview);
   const byModel=strictSources&&weightSource&&(blended||companion?.schema==='math-gauge.independent-research-abilities/v2')&&companion.edition==='1.3.0'&&
    companion.source_stages?.[stage]===(revised?'revision-inclusive':'first-answer')?companion.by_model:null;
   const weight=companion?.taste_blend?.legacy_percent;
   const described=Number.isInteger(weight)&&weight>0&&weight<100;
   const displayedTaste=blended&&described?{...tasteAxis,description:strictCredit?{
    zh:(100-weight)+'% 独立开放研究品味 SMC，保留已通过检查的净信用。'+weight+'% 六个旧题家族含已接纳续答的严格复核分。',
    en:(100-weight)+'% independent research taste SMC, using the net credit of passed checks. '+weight+'% strict review of six retained families including adopted continuations.'}:strict?{
    zh:(100-weight)+'% 独立开放研究品味 SMC（三项严格检查），'+weight+'% 六个旧题家族含已接纳续答的百分制严格复核分。',
    en:(100-weight)+'% independent open research taste SMC (three strict checkpoints) and '+weight+'% strict 0–100 taste review of six retained families including adopted continuations.'}:{
    zh:(100-weight)+'% 独立开放研究三稿品味 RMC，'+weight+'% 六个旧题家族含已接纳续答的直接评审。',
    en:(100-weight)+'% mathematical taste RMC on the three independent open research manuscripts and '+weight+'% direct taste reviews of six retained families including adopted continuations.'}}:tasteAxis;
   axes=[...axes.map(axis=>descriptions[axis.id]?{...axis,description:descriptions[axis.id]}:axis),displayedTaste];
   models=models.map(model=>projectResearchMetrics(model,byModel?.[model.id],stage,blended,strict));
  }
  const initiative=opportunityProjection(data);
  if(initiative===false)return null;
  if(initiative){
   axes=axes.map(axis=>axis.id==='initiative'?{...axis,description:opportunityDescription}:axis);
   models=models.map(model=>({...model,profile_metrics:{...model.profile_metrics,initiative:initiative.get(model.id)||{
    exact:null,lower:0,upper:100,confirmed:0,coverage:{unit:'research_opportunity',planned:28,reviewed:0}}}}));
  }
  return models.length?{profile,axes,models,stage}:null;
 }
 function mount(win){
  const document=win.document,section=document.getElementById('mathematical-profile');if(!section)return null;
  const display=win.MG,data=display?.d||win.MGResults?.data;
  const current=fixedRevisionStage(data);
  const compare=display?.compareScores?((a,b)=>display.compareScores(a,b,'strict')):((a,b)=>a.id.localeCompare(b.id));
  let stage=stageFor(data,new URL(win.location.href).search),prepared=prepare(data,compare,stage);if(!prepared){section.removeAttribute('data-assessment-only');section.hidden=true;return null}section.hidden=false;
  let {models,axes,profile}=prepared;const copy=messages,byId=new Map(models.map(model=>[model.id,model])),svgNS='http://www.w3.org/2000/svg';
  section.removeAttribute('data-assessment-only');
  if(current){
   const nav=document.querySelector?.('a[data-assessment-only="1.2.0"][href="#mathematical-profile"]');
   if(nav){nav.setAttribute('data-assessment-only','1.3.0');nav.hidden=false}
  }
  const el=id=>document.getElementById('mathematical-profile-'+id),node=(tag,text,className)=>{const item=document.createElement(tag);if(text!==undefined)item.textContent=text;if(className)item.className=className;return item};
  const stageControl=el('continuation-control'),stageSwitch=current?null:el('continuation');
  const picker=el('picker'),modelChoices=el('choices');
  if(current)stageControl?.remove();
  const svg=(tag,attrs={})=>{const item=document.createElementNS(svgNS,tag);for(const [key,value]of Object.entries(attrs))item.setAttribute(key,String(value));return item};
  let lang='zh',selected=[],signature='',pinned=null,hovered=null,keyboard=null;
  const controls=new Map(),checkboxes=new Map(),series=new Map(),legendButtons=new Map();
  const tasteCompanion=data.independent_research_abilities;
  const strictTaste=strictTasteCompanion(tasteCompanion);
  const tasteCopy=strictCreditTasteCompanion(tasteCompanion)?strictCreditTasteMessages:
   valueTasteCompanion(tasteCompanion)?valueTasteMessages:strictTaste?strictTasteMessages:
   tasteCompanion?.schema==='math-gauge.independent-research-abilities/v3'?blendedTasteMessages:tasteMessages;
  const opportunityBased=current&&!!data.research_initiative;
  const t=key=>(opportunityBased&&opportunityMessages[key]||axes.some(axis=>axis.id===tasteAxis.id)&&tasteCopy[key]||axes.some(axis=>axis.id==='formalization')&&formalizationMessages[key]||axes.some(axis=>axis.id==='open_research')&&researchMessages[key]||copy[key])[lang==='en'?1:0],format=value=>value.toLocaleString(lang==='en'?'en-US':'zh-CN',{minimumFractionDigits:1,maximumFractionDigits:1});
  const viewText=pair=>pair[lang==='en'?1:0];
  const views=current?buildViews():null;
  const compactCoverage=current;
  const coverageNames={lean_subcategory:'formalization',open_research_family:'openResearch',benchmark_subcategory:'smc',
   fixed_weighted_category:'smc',manuscript:'tasteManuscripts',theorem_extension_family:'legacyTaste',research_opportunity:'initiativeOpportunities'};
  const coverage=metric=>{const {unit,reviewed,planned}=metric.coverage,count=reviewed+'/'+planned,key=coverageNames[unit];
   const base=compactCoverage&&reviewed===planned?'':key?t(key)+' · '+count:count+' '+t('settled');
   const taste=metric.taste_coverage;
   if(taste){
    const checkpoints=taste.unit==='taste_checkpoint';
    const status=checkpoints?strictTasteStates[metric.independent_metric?.state]:null;
    let text=compactCoverage&&taste.reviewed===taste.planned?'':t(checkpoints?'tasteCheckpoints':'tasteManuscripts')+' · '+taste.reviewed+'/'+taste.planned;
    if(status)text=[text,viewText(status)].filter(Boolean).join(' · ');
    return [text,base,metric.legacy_review_available===false?t('strictSourceUnavailable'):''].filter(Boolean).join(' · ');
   }
   const task=metric.task_coverage;
   if(!task)return base;
   const componentsMissing=task.components_reviewed!==task.components_planned;
   const extension=task.unit==='independent_extension_opportunity';
   const observed=extension?t('extension')+' '+(metric.extension_level??task.reviewed+'/'+task.planned):
    compactCoverage&&task.reviewed===task.planned&&!componentsMissing?'':t('newTask')+' '+task.reviewed+'/'+task.planned;
   const components=task.components_planned>1&&(!compactCoverage||componentsMissing)?' ('+t('components')+' '+task.components_reviewed+'/'+task.components_planned+')':'';
   return [metric.base_coverage?base:t('baseUnknown'),observed+components].filter(Boolean).join(' · ');};
  const separateCoverage=['formalization','open_research',tasteAxis.id,...(opportunityBased?['initiative']:[])];
  const settledCoverage=model=>{const counts=axes.filter(axis=>axis.id!=='completion'&&!separateCoverage.includes(axis.id)).map(axis=>model.profile_metrics[axis.id].coverage.reviewed),low=Math.min(...counts),high=Math.max(...counts);
   const families=compactCoverage&&low===35?'':(low===high?low:low+'–'+high)+'/35 '+t('settled');
   return [families,...separateCoverage.filter(id=>model.profile_metrics[id]).map(id=>coverage(model.profile_metrics[id]))].filter(Boolean).join(' · ')};
  const appendLogo=(target,model)=>{if(model.logo?.data_url){const image=node('img');image.src=model.logo.data_url;image.alt='';target.append(image)}};
  function buildViews(){
   const layout=el('chart').closest('.mp-layout'),selection=picker.closest('.mp-toolbar');
   const radar=node('div'),table=el('values').closest('details');
   const toolbar=node('div',undefined,'mp-view-control'),buttons=node('div',undefined,'segmented');
   const bars=node('section',undefined,'mp-rank-panel'),axisLabel=node('label',undefined,'mp-rank-axis-label');
   const axisName=node('span'),axisSelect=node('select'),plot=node('div');
   plot.setAttribute('role','group');
   axisLabel.append(axisName,axisSelect);bars.append(axisLabel,plot);
   const panes={radar,bars,table},toggles={};
   function choose(key,value){
    const url=new URL(win.location.href);url.searchParams.set('profile-'+key,value);
    win.history.replaceState(null,'',url.href);render();
   }
   for(const [key,pane] of Object.entries(panes)){
    pane.id='mathematical-profile-'+key+'-view';pane.dataset.profilePane=key;
    const button=node('button');button.type='button';button.dataset.profileView=key;
    button.setAttribute('aria-controls',pane.id);button.addEventListener('click',()=>choose('view',key));
    toggles[key]=button;buttons.append(button);
   }
   buttons.setAttribute('role','group');toolbar.append(buttons);
   axisSelect.addEventListener('change',()=>choose('axis',axisSelect.value));
   table.open=true;el('values-title').hidden=true;
   selection.before(toolbar);toolbar.after(radar);
   radar.append(selection,modelChoices,layout,el('empty'));
   radar.after(bars);bars.after(table);
   return {panes,toggles,buttons,axisName,axisSelect,plot};
  }
  function renderRank(axis){
   const definition=axes.find(item=>item.id===axis);
   views.axisName.textContent=viewText(profileViewCopy.axis);
   views.axisSelect.replaceChildren(...axes.map(item=>{const option=node('option',item.label[lang]);option.value=item.id;return option}));
   views.axisSelect.value=axis;
   views.plot.setAttribute('aria-label',definition.label[lang]+' · '+viewText(profileViewCopy.scale));
   const {ranked,unknown}=rankAxis(models,axis),content=[];
   const label=model=>{const name=node('span',undefined,'mp-rank-model');appendLogo(name,model);name.append(node('span',model.label));return name;};
   if(ranked.length){
    const scale=node('div',undefined,'mp-rank-scale'),ticks=node('div',undefined,'mp-rank-ticks'),rows=node('ol',undefined,'mp-rank-rows');
    scale.setAttribute('aria-hidden','true');ticks.append(...[0,20,40,60,80,100].map(n=>node('span',String(n))));scale.append(ticks);
    for(const {model,metric,rank} of ranked){
     const row=node('li',undefined,'mp-rank-row'),track=node('div',undefined,'mp-rank-track'),bar=node('span',undefined,'mp-rank-bar');
     row.dataset.profileBarModel=model.id;row.dataset.profileBarRank=String(rank);
     row.style.setProperty('--mp-model-color',model.theme?.color||brand(model).color);
     track.setAttribute('aria-hidden','true');bar.style.width=metric.exact+'%';track.append(bar);
     row.append(node('span',String(rank),'mp-rank-position'),label(model),track,node('span',format(metric.exact),'mp-rank-score'));
     rows.append(row);
    }
    content.push(scale,rows);
   }
   if(unknown.length){
    const list=node('ul',undefined,'mp-unranked-rows');
    for(const {model,metric} of unknown){
     const row=node('li',undefined,'mp-unranked-row');row.dataset.profileBarModel=model.id;
     const interval=metric.lower===0&&metric.upper===100?viewText(profileViewCopy.unknown):format(metric.lower)+'–'+format(metric.upper);
     row.append(label(model),node('span',interval,'mp-rank-score'));
     const detail=coverage(metric);if(detail)row.append(node('small',detail,'mp-cell-coverage'));
     list.append(row);
    }
    content.push(node('p',viewText(profileViewCopy.unranked),'mp-unranked-title'),list);
   }
   views.plot.replaceChildren(...content);
  }
  function marker(parent,shape,x,y,color){
   let mark;const r=3.5;
   if(shape==='circle'||shape==='ring')mark=svg('circle',{cx:x,cy:y,r,fill:shape==='ring'?'none':'white'});
   else if(shape==='square')mark=svg('rect',{x:x-r,y:y-r,width:2*r,height:2*r,fill:'white'});
   else if(shape==='triangle')mark=svg('path',{d:`M${x} ${y-r-1}L${x+r+1} ${y+r}L${x-r-1} ${y+r}Z`,fill:'white'});
   else if(shape==='diamond')mark=svg('path',{d:`M${x} ${y-r-1}L${x+r+1} ${y}L${x} ${y+r+1}L${x-r-1} ${y}Z`,fill:'white'});
   else if(shape==='pentagon')mark=svg('polygon',{points:Array.from({length:5},(_,i)=>{const a=-Math.PI/2+i*2*Math.PI/5;return (x+Math.cos(a)*(r+1))+','+(y+Math.sin(a)*(r+1))}).join(' '),fill:'white'});
   else if(shape==='hexagon')mark=svg('polygon',{points:Array.from({length:6},(_,i)=>{const a=i*Math.PI/3;return (x+Math.cos(a)*(r+1))+','+(y+Math.sin(a)*(r+1))}).join(' '),fill:'white'});
   else mark=svg('path',{d:shape==='plus'?`M${x-r-1} ${y}H${x+r+1}M${x} ${y-r-1}V${y+r+1}`:`M${x-r} ${y-r}L${x+r} ${y+r}M${x-r} ${y+r}L${x+r} ${y-r}`,fill:'none'});
   mark.setAttribute('class','mp-marker');mark.setAttribute('stroke',color);parent.append(mark);return mark;
  }
  function focus(){
   const active=hovered||keyboard||pinned;
   for(const [id,item]of series){item.setAttribute('data-focused',String(active===id));item.setAttribute('data-muted',String(!!active&&active!==id))}
   for(const [id,item]of legendButtons){item.setAttribute('data-focused',String(active===id));item.setAttribute('data-muted',String(!!active&&active!==id));item.setAttribute('aria-pressed',String(pinned===id))}
  }
  function focusEvents(target,id){target.addEventListener('pointerenter',()=>{hovered=id;focus()});target.addEventListener('pointerleave',()=>{hovered=null;focus()});
   target.addEventListener('focus',()=>{keyboard=id;focus()});target.addEventListener('blur',()=>{keyboard=null;focus()})}
  function labelLines(value){const words=value.split(/\s+/),lines=[];let current='';for(const word of words){if(current&&(current+' '+word).length>15){lines.push(current);current=word}else current=current?current+' '+word:word}if(current)lines.push(current);return lines.length>2?[lines[0],lines.slice(1).join(' ')]:lines}
  function renderChart(){
   series.clear();const chart=svg('svg',{viewBox:'0 0 520 460',role:'img','aria-labelledby':'mp-chart-title mp-chart-description'});
   const title=svg('title',{id:'mp-chart-title'});title.textContent=t('chart');const description=svg('desc',{id:'mp-chart-description'});description.textContent=t('note');chart.append(title,description);
   for(const tick of [20,40,60,80,100]){const center=point(0,0,axes.length),edge=point(0,tick,axes.length);chart.append(svg('circle',{cx:center.x,cy:center.y,r:center.y-edge.y,class:'mp-grid'+(tick===100?' mp-grid-outer':'')}));const label=svg('text',{x:270,y:point(0,tick,axes.length).y+4,class:'mp-tick'});label.textContent=String(tick);chart.append(label)}
   const zero=svg('text',{x:267,y:237,class:'mp-tick'});zero.textContent='0';chart.append(zero);
   axes.forEach((axis,index)=>{const end=point(index,100,axes.length);chart.append(svg('line',{x1:260,y1:225,x2:end.x,y2:end.y,class:'mp-axis'}));
    const a=-Math.PI/2+index*2*Math.PI/axes.length,x=260+Math.cos(a)*193,y=225+Math.sin(a)*193,lines=labelLines(axis.label[lang]);
    const label=svg('text',{x,y:y-(lines.length-1)*8,class:'mp-axis-label'});const tip=svg('title');tip.textContent=axis.description[lang];label.append(tip);
    lines.forEach((line,i)=>{const span=svg('tspan',{x,dy:i?18:0});span.textContent=line;label.append(span)});chart.append(label);
   });
   for(const id of selected){const model=byId.get(id),style=styleFor(model),shape=geometry(axes,model.profile_metrics),group=svg('g',{class:'mp-series','data-profile-model':id,'data-profile-dash':style.dash,'data-profile-marker':style.marker});
    const d=shape.complete?'M'+shape.vertices.map(p=>p.x+' '+p.y).join('L')+'Z':shape.segments.map(([a,b])=>'M'+a.x+' '+a.y+'L'+b.x+' '+b.y).join('');
    if(d)group.append(svg('path',{class:'mp-model-line',d,stroke:style.color,'stroke-dasharray':style.dash,fill:shape.complete?style.color:'none','fill-opacity':selected.length>7?.012:.03}));
    for(const interval of shape.intervals){const line=svg('line',{class:'mp-interval',x1:interval.from.x,y1:interval.from.y,x2:interval.to.x,y2:interval.to.y,stroke:style.color,'stroke-dasharray':'2 3','data-profile-interval':interval.axis});
     const tip=svg('title');tip.textContent=model.label+' · '+axes[interval.index].label[lang]+' · '+t('range')+' '+format(interval.lower)+'–'+format(interval.upper);line.append(tip);group.append(line);
     const a=-Math.PI/2+interval.index*2*Math.PI/axes.length,dx=Math.cos(a+Math.PI/2)*4,dy=Math.sin(a+Math.PI/2)*4;
     for(const p of [interval.from,interval.to])group.append(svg('line',{class:'mp-interval',x1:p.x-dx,y1:p.y-dy,x2:p.x+dx,y2:p.y+dy,stroke:style.color}));
    }
    shape.vertices.forEach((p,index)=>{if(!p)return;const mark=marker(group,style.marker,p.x,p.y,style.color);mark.setAttribute('data-profile-point',axes[index].id);mark.setAttribute('data-value',p.value);const tip=svg('title');tip.textContent=[model.label,axes[index].label[lang]+' '+format(p.value)+' / 100',coverage(model.profile_metrics[axes[index].id])].filter(Boolean).join(' · ');mark.append(tip)});
    focusEvents(group,id);series.set(id,group);chart.append(group);
   }el('chart').replaceChildren(chart);
  }
  function renderLegend(){legendButtons.clear();const items=[];
   for(const id of selected){const model=byId.get(id),style=styleFor(model),button=node('button',undefined,'mp-legend-button');button.type='button';button.title=model.label;button.setAttribute('aria-pressed',String(pinned===id));
    const sample=svg('svg',{viewBox:'0 0 40 18','aria-hidden':'true'});sample.append(svg('line',{x1:1,y1:9,x2:39,y2:9,stroke:style.color,'stroke-width':2,'stroke-dasharray':style.dash}));marker(sample,style.marker,20,9,style.color);button.append(sample);appendLogo(button,model);
    const identity=node('span'),name=node('span',model.label,'mp-legend-name'),known=axes.filter(axis=>model.profile_metrics[axis.id].exact!==null).length;
    identity.append(name);const detail=settledCoverage(model);if(detail)identity.append(node('span',detail,'mp-legend-coverage'));
    if(stage==='revision'&&model.neutral_revision_completion){const detail=model.neutral_revision_completion,rate=detail.full_rate?.exact,delta=model.neutral_revision_delta?.strict;
     identity.append(node('span',detail.selected+' '+t('continued')+' · '+t('full')+' '+(rate==null?'—':format(rate*100)+'%')+' · ΔSMC '+(delta==null?'—':(delta>0?'+':'')+format(delta)),'mp-revision-summary'))}
button.append(identity);focusEvents(button,id);button.addEventListener('click',()=>{pinned=pinned===id?null:id;focus()});legendButtons.set(id,button);items.push(button);
   }el('legend').replaceChildren(...items);
  }
  function renderTable(displayed){const table=el('values'),caption=node('caption',current?viewText(profileViewCopy.tableCaption):t('table'));caption.className='mp-sr-only';const head=node('thead'),row=node('tr');const first=node('th',t('model'));first.scope='col';row.append(first);
   axes.forEach(axis=>{const cell=node('th',axis.label[lang]);cell.scope='col';cell.title=axis.description[lang];row.append(cell)});head.append(row);const body=node('tbody');
   for(const model of displayed){const tr=node('tr'),name=node('th',model.label);name.scope='row';tr.append(name);
    axes.forEach(axis=>{const metric=model.profile_metrics[axis.id],cell=node('td');
     if(metric.exact===null){cell.className='mp-uncertain';
      if(axis.id===tasteAxis.id&&metric.lower===0&&metric.upper===100)cell.append(node('span',t('tasteUnknown'),'mp-axis-value'));
      else cell.append(node('span',format(metric.lower)+'–'+format(metric.upper),'mp-axis-value'),node('small',t('confirmed')+' '+format(metric.confirmed),'mp-cell-confirmed'));
     }else cell.append(node('span',format(metric.exact),'mp-axis-value'));
     const detail=coverage(metric);if(detail)cell.append(node('small',detail,'mp-cell-coverage'));tr.append(cell)});body.append(tr);
   }table.replaceChildren(caption,head,body);
  }
  function renderMeanings(){el('meanings').hidden=false;
   el('meanings-title').textContent=t('meanings');
   const reviews=strictTaste?tasteCompanion.legacy_taste_binding?.review_coverage:null;
   const reviewScope=reviews?viewText([
    `旧题严格复核已审查 ${reviews.assessed}/${reviews.planned} 份，其中 ${reviews.scored} 份可评分。原文缺失 ${reviews.source_missing} 份，核验未决 ${reviews.verification_unresolved} 份。`,
    `Strict review assessed ${reviews.assessed}/${reviews.planned} retained submissions and scored ${reviews.scored}. Source files were missing for ${reviews.source_missing}, and verification remains unresolved for ${reviews.verification_unresolved}.`
   ]):'';
   el('meanings-scope').textContent=[t('scope'),reviewScope].filter(Boolean).join(' ');
   el('meanings-list').replaceChildren(...axes.map(axis=>{const item=node('div',undefined,'mp-axis-definition'),description=node('dd',axis.description[lang]);
    if(axisContext[axis.id])description.append(node('span',axisContext[axis.id][lang==='en'?1:0],'mp-axis-context'));
    item.append(node('dt',axis.label[lang]),description);return item}));
  }
  function setSelection(ids){const chosen=new Set(ids);selected=models.filter(model=>chosen.has(model.id)).map(model=>model.id);if(!chosen.has(pinned))pinned=null;hovered=null;keyboard=null;
   win.history.replaceState(null,'',selectionUrl(win.location.href,selected));signature='';render()}
  function buildControls(){
   controls.clear();checkboxes.clear();const target=el('controls');const items=[];for(const key of ['leader','brands','clear']){const button=node('button',undefined,'mp-preset');button.type='button';button.dataset.profilePreset=key;button.addEventListener('click',()=>setSelection(key==='leader'?[models[0].id]:key==='brands'?representatives(models,compare):[]));controls.set(key,button);items.push(button)}target.replaceChildren(...items);
   const groups=new Map();for(const model of models){const style=brand(model);if(!groups.has(style.key))groups.set(style.key,{style,models:[]});groups.get(style.key).models.push(model)}
   const choices=[];for(const {style,models:members}of groups.values()){const fieldset=node('fieldset',undefined,'mp-choice-group'),legend=node('legend',style.label);fieldset.append(legend);
    for(const model of members){const label=node('label',undefined,'mp-choice');label.style.setProperty('--mp-brand',style.color);label.title=model.label;const checkbox=node('input');checkbox.type='checkbox';checkbox.value=model.id;checkbox.setAttribute('aria-label',model.label);checkbox.addEventListener('change',()=>{const next=new Set(selected);if(checkbox.checked)next.add(model.id);else next.delete(model.id);setSelection(next)});checkboxes.set(model.id,checkbox);label.append(checkbox);appendLogo(label,model);label.append(node('span',model.label,'mp-choice-name'));fieldset.append(label)}choices.push(fieldset);
   }modelChoices.replaceChildren(...choices);
  }
  function render(){
   const url=new URL(win.location.href);
   if(current&&url.searchParams.has('profile-stage')){
    url.searchParams.delete('profile-stage');win.history.replaceState(win.history.state,'',url.href);
   }
   const query=url.search,nextStage=stageFor(data,query);
   if(nextStage!==stage){const next=prepare(data,compare,nextStage);if(next){stage=nextStage;({models,axes,profile}=next);byId.clear();for(const model of models)byId.set(model.id,model);pinned=null;hovered=null;keyboard=null;buildControls();signature=''}}
   if(stageSwitch)stageSwitch.checked=stage==='revision';
   lang=new URLSearchParams(query).get('lang')==='en'?'en':'zh';selected=readSelection(query,models,compare);
   const {view,axis}=views?viewFor(query,axes):{view:null,axis:null};
   const key=[stage,lang,selected.join(','),view,axis].join('|');if(key===signature)return;signature=key;
   if(!selected.includes(pinned))pinned=null;if(!selected.includes(hovered))hovered=null;if(!selected.includes(keyboard))keyboard=null;
   for(const [id,message]of Object.entries({title:'title',description:'description',review:'review',note:'note','focus-note':'focus','values-title':'values','coverage-note':'coverage',empty:'empty','picker-title':'picker'}))el(id).textContent=t(message);
   if(stageSwitch)el('continuation-label').textContent=t('continuation');
   for(const [key,button]of controls)button.textContent=t(key);for(const [id,checkbox]of checkboxes)checkbox.checked=selected.includes(id);
   controls.get('brands').title=t('brandHint');
   el('count').textContent=selected.length+'/'+models.length;
   picker.setAttribute('aria-label',t('picker')+' · '+t('selected')+' '+selected.length+t('of')+models.length+' '+t('models'));
   el('empty').hidden=selected.length>0;
   renderMeanings();
   if(views){
    views.buttons.setAttribute('aria-label',viewText(profileViewCopy.mode));
    for(const [name,button] of Object.entries(views.toggles)){
     button.textContent=viewText(profileViews[name]);button.setAttribute('aria-pressed',String(name===view));
     views.panes[name].hidden=name!==view;
    }
    if(view==='bars')renderRank(axis);
   }
   if(!views||view==='radar'){renderChart();renderLegend();focus()}
   if(!views||view==='table')renderTable(views?models:selected.map(id=>byId.get(id)));
  }
  if(stageSwitch){
   stageControl.hidden=!hasRevisionStage(data)||!data.mathematical_profile_revision;
   stageSwitch.addEventListener('change',()=>{
    const url=new URL(win.location.href);
    url.searchParams.set('profile-stage',stageSwitch.checked?'revision':'first');
    win.history.replaceState(null,'',url.href);render();
   });
  }
  picker.addEventListener('click',()=>{
   modelChoices.hidden=!modelChoices.hidden;
   picker.setAttribute('aria-expanded',String(!modelChoices.hidden));
  });
  buildControls();render();win.addEventListener('mg:updated',render);win.addEventListener('popstate',render);
  return {render,setSelection,selected:()=>[...selected],stage:()=>stage};
 }
 return {AXES,brand,styleFor,representatives,readSelection,selectionUrl,validMetric,geometry,stageFor,prepare,mount};
});
