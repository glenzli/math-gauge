(function (root) {
  'use strict';
  const axes = [['autonomy', '研究自主'], ['taste', '数学品味'], ['capacity', '研究能力']];
  const states = { 'not-tested': '未测', unreviewed: '待评', 'insufficient-evidence': '证据不足', 'delivery-failed': '未正常交付' };
  const esc = value => String(value).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' })[c]);
  const keys = (obj, expected) => obj && Object.keys(obj).sort().join('|') === [...expected].sort().join('|');
  const score = value => typeof value === 'number' && Number.isFinite(value) && value >= 0 && value <= 100;
  function bounds(value) {
    return keys(value, ['exact', 'lower', 'upper']) && score(value.lower) && score(value.upper) && value.lower <= value.upper &&
      (value.exact === null || score(value.exact) && value.exact === value.lower && value.exact === value.upper);
  }
  function validate(data) {
    const baseline = data.kind === 'existing-model-unmeasured';
    const settled = data.kind === 'settled-selected-configurations';
    const fields = ['schema', 'edition', 'kind', 'category', 'rank_eligible', 'default_order', 'weights_ratified', 'rows'];
    if (baseline || settled) fields.push('source_binding');
    if (settled) fields.push('adoption');
    if (!keys(data, fields) ||
        data.schema !== 'math-gauge.research-board-preview/v1' || data.edition !== '1.3.0' || (!baseline && !settled && data.kind !== 'synthetic-fixture') ||
        data.rank_eligible !== false || data.weights_ratified !== false || data.default_order !== 'retained-base-SMC' ||
        !keys(data.category, ['id', 'zh', 'en']) || data.category.id !== 'open-research' || !Array.isArray(data.rows)) {
      throw new Error('Unrecognized local display projection');
    }
    if ((baseline || settled) && (!keys(data.source_binding, ['edition', 'sha256']) || data.source_binding.edition !== '1.2.0' || !/^[a-f0-9]{64}$/.test(data.source_binding.sha256))) throw new Error('Unbound baseline');
    const uniqueIds = ids => Array.isArray(ids) && ids.length && new Set(ids).size === ids.length;
    if (settled && (!keys(data.adoption, ['batch_sha256', 'index_sha256', 'cohort', 'planned_cohort', 'human_review']) ||
        !/^[a-f0-9]{64}$/.test(data.adoption.batch_sha256) || !/^[a-f0-9]{64}$/.test(data.adoption.index_sha256) ||
        data.adoption.human_review !== 'pending' || !uniqueIds(data.adoption.cohort) || !uniqueIds(data.adoption.planned_cohort) ||
        !data.adoption.cohort.every(id => data.adoption.planned_cohort.includes(id)))) throw new Error('Unbound configuration adoption');
    const seen = new Set();
    for (const row of data.rows) {
      if (!keys(row, ['id', 'label', 'kind', 'base_smc', 'components', 'task_strict', 'item', 'coverage', 'strict_overall', 'composite', 'composites', 'confirmed', 'strict_confirmed', 'delivery']) ||
          !((baseline || settled) ? /^[a-z0-9.-]+$/.test(row.id) : /^fixture-[a-z]+$/.test(row.id)) || seen.has(row.id) || row.kind !== data.kind || typeof row.label !== 'string' ||
          !(score(row.base_smc) || bounds(row.base_smc)) || !keys(row.components, axes.map(a => a[0])) || !bounds(row.strict_overall) || !bounds(row.composite) || !keys(row.composites, ['MC','RMC','SMC']) || !Object.values(row.composites).every(bounds) || !keys(row.confirmed,['MC','RMC','SMC']) || !Object.values(row.confirmed).every(score) || !score(row.strict_confirmed) || !keys(row.delivery,['planned','normal','unknown']) || row.delivery.planned!==45 || !Number.isInteger(row.delivery.normal) || !Number.isInteger(row.delivery.unknown) || row.delivery.normal<0 || row.delivery.unknown<0 || row.delivery.normal+row.delivery.unknown>45 || !bounds(row.item) ||
          ![0, 100, null].includes(row.task_strict) || !keys(row.coverage, ['planned', 'reviewed', 'components_planned', 'components_reviewed']) ||
          row.coverage.planned !== 1 || row.coverage.components_planned !== 3 || ![0, 1].includes(row.coverage.reviewed) ||
          ![0, 1, 2, 3].includes(row.coverage.components_reviewed)) throw new Error('Unexpected row or private payload');
      const unmeasured = baseline || (settled && !data.adoption.cohort.includes(row.id));
      if (unmeasured && (row.task_strict !== null || row.coverage.reviewed !== 0 || row.coverage.components_reviewed !== 0 || row.strict_overall.exact !== null || row.composite.exact !== null)) throw new Error('Unmeasured model acquired a research result');
      seen.add(row.id);
      for (const [key] of axes) {
        const component = row.components[key];
        if (unmeasured && (component.state !== 'not-tested' || component.value !== null || component.strict !== null)) throw new Error('Unmeasured component acquired a grade');
        if (settled && !unmeasured && !['reviewed', 'insufficient-evidence', 'delivery-failed'].includes(component.state)) throw new Error('Adopted component is still pending');
        if (!keys(component, ['state', 'value', 'strict']) || ![true,false,null].includes(component.strict) || !(component.state === 'reviewed' ? score(component.value) :
            Object.hasOwn(states, component.state) && component.value === null)) throw new Error('Unknown and zero must remain distinct');
      }
    }
    if (settled && !data.adoption.planned_cohort.every(id => seen.has(id))) throw new Error('Missing planned configuration');
    return data;
  }
  function componentCell(value) {
    if(value.state==='not-tested')return '<span class="state" data-unmeasured aria-label="未测"></span>';
    return value.state === 'reviewed' ? `<span class="value">${esc(value.value.toFixed(1))}</span>` : `<span class="state">${states[value.state]}</span>`;
  }
  function metricCell(value, label) {
    const content = value.exact === null ? `<span class="state">未知</span><span class="interval">${value.lower.toFixed(2)}–${value.upper.toFixed(2)}</span>` :
      `<span class="metric">${value.exact.toFixed(2)}</span>`;
    return `<td class="total"><span class="metric-label">${label}</span>${content}</td>`;
  }
  function render(data) {
    validate(data);
    // Deliberately preserve the supplied SMC row order; no A/T/C arithmetic or reranking here.
    const rows = data.rows.map(row => `<tr data-model="${esc(row.id)}"><td class="model"><strong>${esc(row.label)}</strong><span class="fixture-label">${row.kind === 'synthetic-fixture' ? 'FIXTURE' : '1.2.0 基准'}</span></td>` +
      `<td class="base">${typeof row.base_smc === 'number' ? row.base_smc.toFixed(2) : '未知'}</td>` + axes.map(([key, label]) =>
        `<td class="component" headers="research ${key}"><span class="subscore-label">${label}</span>${componentCell(row.components[key])}</td>`).join('') +
      `<td class="strict-cell">整题 SMC ${row.task_strict === null ? '未知' : row.task_strict}<span class="coverage">已评 ${row.coverage.components_reviewed}/3 项 · 1 题</span></td>` +
      metricCell(row.strict_overall, '严格综合') + metricCell(row.composite, '独立数值综合') + '</tr>').join('');
    return `<table aria-label="1.3.0 本地总榜布局，保留基准 SMC 顺序"><thead><tr><th class="model" rowspan="2" scope="col">配置</th>` +
      `<th class="base" rowspan="2" scope="col">基准 SMC</th><th id="research" class="research-group" colspan="3" scope="colgroup">开放研究</th>` +
      `<th rowspan="2" scope="col">整题 / 覆盖</th><th class="total" rowspan="2" scope="col">严格综合<br>1.3 预览</th>` +
      `<th class="total" rowspan="2" scope="col">独立数值综合<br>RMC 基准</th></tr><tr>` + axes.map(([key, label]) =>
        `<th id="${key}" class="component-head" scope="col">${label}</th>`).join('') + `</tr></thead><tbody>${rows}</tbody></table>`;
  }
  const api = { validate, render };
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
  root.MGResearchPreview = api;
  function decorate() {
    const mg = typeof MG !== 'undefined' ? MG : root.MG;
    if (!mg || mg.d.benchmark_version !== '1.3.0' || !mg.d.research_preview) return;
    const board = mg.d.research_preview;
    const projection = {...board};
    delete projection.weight_frame; delete projection.base_edition; delete projection.condition;
    validate(projection);
    const doc = root.document, table = doc.getElementById('ranking');
    if (!table) return;
    doc.documentElement.setAttribute('data-independent-research-preview','');
    const en = mg.state.lang === 'en';
    const referenceScope = en ? 'Reference for retained 1.2.0 answers' : '1.2.0 采用答卷参考';
    const frontierScope = en ? 'Scores, costs and timings are all from 1.2.0' : '图中成绩、成本和耗时均来自 1.2.0';
    for (const [headingId, text] of [['cost-title', referenceScope], ['timing-title', referenceScope], ['cost-frontier-title', frontierScope]]) {
      const heading = doc.getElementById(headingId);
      if (!heading) continue;
      const id = `${headingId}-baseline-scope`;
      let scope = doc.getElementById(id);
      if (!scope) {
        scope = doc.createElement('p');
        scope.id = id;
        scope.className = 'panel-desc';
        heading.insertAdjacentElement('afterend', scope);
      }
      scope.textContent = text;
    }
    const title = en ? 'Independent Open Research' : '独立开放研究';
    let note = doc.getElementById('independent-research-preview-note');
    if (!note) { note = doc.createElement('p'); note.id = 'independent-research-preview-note'; note.className = 'panel-desc independent-research-note'; doc.getElementById('leaderboard').prepend(note); }
    const progress = board.adoption ? `${board.adoption.cohort.length}/${board.adoption.planned_cohort.length}` : null;
    note.textContent = progress ? (en ? `1.3.0: Written 30 / Lean 30 / Supporting research 30 / Independent open research 10. Adopted ${progress} planned configurations after independent Sol 6.1 Max reviews. Other new-task scores remain blank; a comparison rank requires complete score coverage.` : `1.3.0：书面30／Lean30／辅助研究30／独立开放研究10。独立 Sol 6.1 Max 评审后已采用 ${progress} 个计划配置。其余新题留空，完整成绩证据齐备后才有可比较名次。`) : en ? '1.3.0: Written 30 / Lean 30 / Supporting research 30 / Independent open research 10. New tasks are unmeasured. Bars show confirmed contributions reweighted from 1.2.0, with the unmeasured ten points retained as unknown.' :
      '1.3.0：书面30／Lean30／辅助研究30／独立开放研究10。新题三项尚未实测。柱状图按新权重显示原1.2证据的已确认贡献；新增10分保留未知区间，未把已测部分归一化。';
    const rows = new Map(board.rows.map(r=>[r.id,r]));
    for (const row of doc.querySelectorAll('#ranking-body tr')) {
      const link=row.querySelector('.model-name');if(!link)continue;
      const id=new URL(link.href,doc.baseURI).pathname.match(/\/models\/([^/]+)\//)?.[1];
      const value=rows.get(id);if(!value)continue;
      const delivery=value.delivery;
      const label=(delivery.unknown?'≥':'')+delivery.normal+'/'+delivery.planned+' · '+(delivery.normal/delivery.planned*100).toFixed(1)+'%';
      const cell=row.querySelector('.delivery-cell')||row.cells[3];
      cell.textContent=label;cell.title='39项原初答＋3轮Lean自查＋3轮独立开放研究。仅首次正常final计入；原记录缺证据时保留未知。';
      const mobile=row.querySelector('.mobile-delivery');if(mobile)mobile.textContent='整体交付 '+label;
    }
    for(const link of doc.querySelectorAll('a[href]')) {
      const u=new URL(link.href,doc.baseURI);
      if(u.origin===location.origin && /\/models\/|\/method\.html$/.test(u.pathname)){u.searchParams.set('edition','1.2.0');link.href=u.href;link.dataset.fixedEdition='';}
    }
    for(const legend of doc.querySelectorAll('#leaderboard .legend-item[data-display-mode]')) {
      const labels={strict:'SMC综合',partial:'RMC综合',capability:'MC基准综合'};
      if(legend.lastChild?.nodeType===3)legend.lastChild.textContent=labels[legend.dataset.displayMode];
    }
    for(const cell of doc.querySelectorAll('#ranking thead .delivery-cell'))cell.textContent=en?'Delivery rate / 45':'整体交付率 / 45';
    const desc=doc.getElementById('leaderboard-desc'); if(desc)desc.textContent=board.adoption?(en?'1.3 settled full-scope comparisons · other confirmed contributions retained':'1.3完整范围的已结算比较 · 其他配置保留已确认贡献'):(en?'1.3 confirmed contribution · ten research points unmeasured':'1.3已确认贡献排序 · 新增10分未测，完整分仍未知');
    const anchor=doc.getElementById('category-leaderboards');
    if(anchor) {
      let panel=doc.getElementById('independent-research-leaderboards');
      if(!panel){panel=doc.createElement('section');panel.id='independent-research-leaderboards';panel.className='panel independent-research-board';anchor.insertAdjacentElement('afterend',panel);}
      const q=new URLSearchParams(location.search),selected=['overall',...axes.map(a=>a[0])].includes(q.get('independent-tab'))?q.get('independent-tab'):'overall';
      const view=q.get('view-independent')==='table'?'table':'chart';
      const choices=[['overall','总榜'],...axes];
      const field=selected==='overall'?null:selected;
      const known=r=>field?r.components[field].value:r.item.exact;
      const ordered=board.rows.map((r,index)=>({r,index})).sort((a,b)=>{const x=known(a.r),y=known(b.r);return x===null?(y===null?a.index-b.index:1):y===null?-1:y-x||a.index-b.index;});
      let rank=0,previous=null;
      const body=ordered.map(({r},index)=>{
        const v=known(r),component=field?r.components[field]:null,verdict=field?component.strict:(r.task_strict===null?null:r.task_strict===100);
        if(v!==null&&v!==previous)rank=index+1;previous=v;
        const unmeasured=Object.values(r.components).every(c=>c.state==='not-tested');
        const display=field?componentCell(component):(v===null?(unmeasured?'':'证据不足'):v.toFixed(2));
        const coverage=unmeasured?'':field?(v===null?'未知/':(field==='taste'?'3/':'1/'))+(field==='taste'?'3稿':'1题'):r.coverage.components_reviewed+'/3分项';
        return '<tr><td>'+(v===null?'':rank)+'</td><td>'+esc(r.label)+'</td><td class="numeric">'+display+'</td><td class="numeric">'+(verdict===null?'':verdict?'通过':'未通过')+'</td><td class="numeric">'+coverage+'</td></tr>';
      }).join('');
      const models=new Map(mg.d.models.map(m=>[m.id,m]));
      const chart=ordered.map(({r})=>{
        const v=known(r),m=models.get(r.id),color=m?.theme?.ink||'#445b8c';
        return '<div class="bar-group" style="--model-color:'+esc(color)+';--model-ink:'+esc(color)+'"><div class="chart-model">'+esc(r.label)+'</div><div class="metric-bars"><div class="metric-bar-row"><div class="bar-track">'+(v===null?'':'<span class="score-bar mode-partial" style="left:0;width:'+v+'%"></span>')+'</div><span class="chart-value">'+(v===null?'':v.toFixed(2))+'</span></div></div></div>';
      }).join('');
      panel.innerHTML='<div class="panel-head"><div><h2>独立开放研究排行榜</h2><p class="panel-desc">1道三轮任务 · 主榜权重10% · 未测项留空</p></div><div class="board-toolbar"><div class="board-view segmented" role="group" aria-label="图表或表格">'+['chart','table'].map(k=>'<button data-independent-view="'+k+'" aria-pressed="'+(view===k)+'">'+(k==='chart'?'图表':'表格')+'</button>').join('')+'</div></div></div><div class="segmented category-tabs" role="tablist" aria-label="独立开放研究分类">'+choices.map(([key,label])=>'<button role="tab" data-independent-tab="'+key+'" aria-selected="'+(selected===key)+'">'+label+'</button>').join('')+'</div>'+
        '<div class="score-figure"'+(view==='chart'?'':' hidden')+'><div class="horizontal-score-chart independent-research-chart"><div class="score-x-axis">'+[0,20,40,60,80,100].map(v=>'<span style="left:'+v+'%">'+v+'</span>').join('')+'</div>'+chart+'</div></div>'+
        '<div class="table-wrap"'+(view==='table'?'':' hidden')+'><table class="compact independent-research-ranking"><thead><tr><th>#</th><th>模型</th><th class="numeric">'+(field?'原始分 / 100':'题分 / 100')+'</th><th class="numeric">SMC</th><th class="numeric">覆盖</th></tr></thead><tbody>'+body+'</tbody></table></div>';
      const change=(key,val)=>{const u=new URL(location.href);u.searchParams.set(key,val);history.replaceState(null,'',u);decorate();};
      for(const button of panel.querySelectorAll('[data-independent-tab]'))button.onclick=()=>change('independent-tab',button.dataset.independentTab);
      for(const button of panel.querySelectorAll('[data-independent-view]'))button.onclick=()=>change('view-independent',button.dataset.independentView);
    }
    const category=doc.getElementById('category-tab-research');if(category)category.textContent=en?'Supporting research':'辅助研究';
    for(const key of ['written','lean','research']) {
      const label=doc.querySelector('#category-panel-'+key+' .panel-desc');if(label)label.textContent=en?'Source category score /100 · New overall weight 30%':'源分项百分制 · 新总榜权重30%';
    }
  }
  api.decorate = decorate;
  if (typeof document !== 'undefined') {
    root.addEventListener('mg:updated', decorate);
    decorate();
  }
})(globalThis);
