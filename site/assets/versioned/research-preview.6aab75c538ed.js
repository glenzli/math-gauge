(function (root) {
  'use strict';
  const axes = [['autonomy', '研究自主'], ['taste', '数学品味'], ['capacity', '研究能力']];
  const axisIds = axes.map(([id]) => id);
  const checks = {autonomy: 2, taste: 3, capacity: 5};
  const modes = ['MC', 'RMC', 'SMC'];
  const scoreOrder = ['SMC', 'RMC', 'MC'];
  const styling = {MC: 'capability', RMC: 'partial', SMC: 'strict'};
  const scoreModeSchema = 'math-gauge.research-board-preview/v2';
  const states = { 'not-tested': '未测', unreviewed: '待评', 'insufficient-evidence': '证据不足', 'delivery-failed': '未正常交付' };
  const statuses = {
    'not-tested': ['未测', 'Not tested'], 'review-pending': ['待评', 'Review pending'],
    'insufficient-evidence': ['证据不足', 'Insufficient evidence'], 'delivery-failed': ['未正常交付', 'No normal delivery'],
    unavailable: ['未提供', 'Unavailable']
  };
  const esc = value => String(value).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' })[c]);
  const keys = (obj, expected) => obj && Object.keys(obj).sort().join('|') === [...expected].sort().join('|');
  const score = value => typeof value === 'number' && Number.isFinite(value) && value >= 0 && value <= 100;
  function bounds(value) {
    return keys(value, ['exact', 'lower', 'upper']) && score(value.lower) && score(value.upper) && value.lower <= value.upper &&
      (value.exact === null || score(value.exact) && value.exact === value.lower && value.exact === value.upper);
  }
  function modeMetric(value) {
    if (!keys(value, ['lower', 'upper', 'exact', 'confirmed', 'state'])) return false;
    const {lower, upper, exact, confirmed, state} = value;
    return bounds({lower, upper, exact}) && score(confirmed) && lower <= confirmed && confirmed <= upper &&
      ['reviewed', 'not-tested', 'review-pending', 'insufficient-evidence', 'delivery-failed'].includes(state) &&
      (!['not-tested', 'review-pending'].includes(state) || exact === null);
  }
  function validateModes(row, unmeasured) {
    const {score_modes: values, criteria} = row;
    if (!keys(values, modes) || !keys(criteria, axisIds)) throw new Error('Unexpected score modes or private criteria');
    for (const mode of modes) {
      const value = values[mode];
      if (!keys(value, ['item', 'components']) || !keys(value.components, axisIds)) throw new Error('Unexpected score-mode fields');
      for (const metric of [value.item, ...Object.values(value.components)]) {
        if (!modeMetric(metric) || (unmeasured && (metric.state !== 'not-tested' || metric.confirmed !== 0))) {
          throw new Error('Invalid score-mode metric');
        }
      }
    }
    for (const axis of axisIds) {
      const count = criteria[axis];
      if (!keys(count, ['planned', 'passed', 'unknown']) || count.planned !== checks[axis] ||
          !Number.isInteger(count.passed) || !Number.isInteger(count.unknown) || count.passed < 0 || count.unknown < 0 ||
          count.passed + count.unknown > count.planned || (unmeasured && count.unknown !== count.planned)) {
        throw new Error('Unexpected public check counts');
      }
    }
  }
  function validate(data) {
    const baseline = data.kind === 'existing-model-unmeasured';
    const settled = data.kind === 'settled-selected-configurations';
    const scoreModes = data.schema === scoreModeSchema;
    const fields = ['schema', 'edition', 'kind', 'category', 'rank_eligible', 'default_order', 'weights_ratified', 'rows'];
    if (baseline || settled) fields.push('source_binding');
    if (settled) fields.push('adoption');
    if (scoreModes && Object.hasOwn(data, 'score_modes_binding')) fields.push('score_modes_binding');
    if (!keys(data, fields) ||
        (!scoreModes && data.schema !== 'math-gauge.research-board-preview/v1') || data.edition !== '1.3.0' || (!baseline && !settled && data.kind !== 'synthetic-fixture') ||
        data.rank_eligible !== false || data.weights_ratified !== false || data.default_order !== 'retained-base-SMC' ||
        !keys(data.category, ['id', 'zh', 'en']) || data.category.id !== 'open-research' || !Array.isArray(data.rows)) {
      throw new Error('Unrecognized local display projection');
    }
    if (fields.includes('score_modes_binding') && (!keys(data.score_modes_binding, ['policy_sha256', 'index_sha256', 'base_index_sha256']) ||
        !Object.values(data.score_modes_binding).every(hash => typeof hash === 'string' && /^[a-f0-9]{64}$/.test(hash)))) {
      throw new Error('Invalid score-mode source binding');
    }
    if ((baseline || settled) && (!keys(data.source_binding, ['edition', 'sha256']) || data.source_binding.edition !== '1.2.0' || !/^[a-f0-9]{64}$/.test(data.source_binding.sha256))) throw new Error('Unbound baseline');
    const uniqueIds = ids => Array.isArray(ids) && ids.length && new Set(ids).size === ids.length;
    if (settled && (!keys(data.adoption, ['batch_sha256', 'index_sha256', 'cohort', 'planned_cohort', 'human_review']) ||
        !/^[a-f0-9]{64}$/.test(data.adoption.batch_sha256) || !/^[a-f0-9]{64}$/.test(data.adoption.index_sha256) ||
        data.adoption.human_review !== 'pending' || !uniqueIds(data.adoption.cohort) || !uniqueIds(data.adoption.planned_cohort) ||
        !data.adoption.cohort.every(id => data.adoption.planned_cohort.includes(id)))) throw new Error('Unbound configuration adoption');
    const rowFields = ['id', 'label', 'kind', 'base_smc', 'components', 'task_strict', 'item', 'coverage', 'strict_overall', 'composite', 'composites', 'confirmed', 'strict_confirmed', 'delivery'];
    if (scoreModes) rowFields.push('score_modes', 'criteria');
    const seen = new Set();
    for (const row of data.rows) {
      if (!keys(row, rowFields) ||
          !((baseline || settled) ? /^[a-z0-9.-]+$/.test(row.id) : /^fixture-[a-z]+$/.test(row.id)) || seen.has(row.id) || row.kind !== data.kind || typeof row.label !== 'string' ||
          !(score(row.base_smc) || bounds(row.base_smc)) || !keys(row.components, axes.map(a => a[0])) || !bounds(row.strict_overall) || !bounds(row.composite) || !keys(row.composites, ['MC','RMC','SMC']) || !Object.values(row.composites).every(bounds) || !keys(row.confirmed,['MC','RMC','SMC']) || !Object.values(row.confirmed).every(score) || !score(row.strict_confirmed) || !keys(row.delivery,['planned','normal','unknown']) || row.delivery.planned!==45 || !Number.isInteger(row.delivery.normal) || !Number.isInteger(row.delivery.unknown) || row.delivery.normal<0 || row.delivery.unknown<0 || row.delivery.normal+row.delivery.unknown>45 || !bounds(row.item) ||
          ![0, 100, null].includes(row.task_strict) || !keys(row.coverage, ['planned', 'reviewed', 'components_planned', 'components_reviewed']) ||
          row.coverage.planned !== 1 || row.coverage.components_planned !== 3 || ![0, 1].includes(row.coverage.reviewed) ||
          ![0, 1, 2, 3].includes(row.coverage.components_reviewed)) throw new Error('Unexpected row or private payload');
      const unmeasured = baseline || (settled && !data.adoption.cohort.includes(row.id));
      if (unmeasured && (row.task_strict !== null || row.coverage.reviewed !== 0 || row.coverage.components_reviewed !== 0 || row.strict_overall.exact !== null || row.composite.exact !== null)) throw new Error('Unmeasured model acquired a research result');
      if (scoreModes) validateModes(row, unmeasured);
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
  function render(data, search = '') {
    validate(data);
    if (data.schema === scoreModeSchema) return renderResearchBoard(data, search, new Map(), false);
    // Deliberately preserve the supplied SMC row order; no A/T/C arithmetic or reranking here.
    const rows = data.rows.map(row => `<tr data-model="${esc(row.id)}"><td class="model"><strong>${esc(row.label)}</strong><span class="fixture-label">${row.kind === 'synthetic-fixture' ? 'FIXTURE' : '1.2.0 基准'}</span></td>` +
      `<td class="base">${typeof row.base_smc === 'number' ? row.base_smc.toFixed(2) : '未知'}</td>` + axes.map(([key, label]) =>
        `<td class="component" headers="research ${key}"><span class="subscore-label">${label}</span>${componentCell(row.components[key])}</td>`).join('') +
      `<td class="strict-cell">${row.task_strict === null ? '全项检查未知' : row.task_strict === 100 ? '全项通过' : '未全项通过'}<span class="coverage">已评 ${row.coverage.components_reviewed}/3 项 · 1 题</span></td>` +
      metricCell(row.strict_overall, '严格综合') + metricCell(row.composite, '独立数值综合') + '</tr>').join('');
    return `<table aria-label="1.3.0 本地总榜布局，保留基准 SMC 顺序"><thead><tr><th class="model" rowspan="2" scope="col">配置</th>` +
      `<th class="base" rowspan="2" scope="col">基准 SMC</th><th id="research" class="research-group" colspan="3" scope="colgroup">开放研究</th>` +
      `<th rowspan="2" scope="col">整题 / 覆盖</th><th class="total" rowspan="2" scope="col">严格综合<br>1.3 预览</th>` +
      `<th class="total" rowspan="2" scope="col">独立数值综合<br>RMC 基准</th></tr><tr>` + axes.map(([key, label]) =>
        `<th id="${key}" class="component-head" scope="col">${label}</th>`).join('') + `</tr></thead><tbody>${rows}</tbody></table>`;
  }
  function readBoard(search) {
    const query = new URLSearchParams(search);
    const requested = query.get('independent-tab');
    const tab = axisIds.includes(requested) ? requested : 'overall';
    const sort = query.get('sort-independent-' + tab)?.toUpperCase();
    const view = query.get('view-independent-' + tab) ?? query.get('view-independent');
    return {tab, field: tab === 'overall' ? null : tab, sort: modes.includes(sort) ? sort : 'SMC',
      view: view === 'table' ? 'table' : 'chart'};
  }
  function untested(row) {
    return Object.values(row.components).every(component => component.state === 'not-tested');
  }
  function gradeFor(row, mode, field) {
    const modeRecord = row.score_modes?.[mode];
    if (modeRecord) return field ? modeRecord.components[field] : modeRecord.item;
    // Old local boards carried continuous scores and binary diagnostics only.
    if (mode !== 'RMC') return {exact: null, state: untested(row) ? 'not-tested' : 'unavailable'};
    if (field) {
      const component = row.components[field];
      return {exact: component.value, state: component.state === 'unreviewed' ? 'review-pending' : component.state};
    }
    const state = untested(row) ? 'not-tested' : row.item.exact !== null ? 'reviewed' : 'insufficient-evidence';
    return {...row.item, state};
  }
  function rankedRows(rows, field, primary) {
    const priority = [primary, ...scoreOrder.filter(mode => mode !== primary)];
    const ordered = rows.map((row, index) => {
      const values = priority.map(mode => gradeFor(row, mode, field).exact);
      return {row, index, values: values.map(value => value === null ? null : Number(value.toFixed(2)))};
    });
    ordered.sort((a, b) => {
      for (const [i, left] of a.values.entries()) {
        const right = b.values[i];
        if (left !== right) return left === null ? 1 : right === null ? -1 : right - left;
      }
      return a.index - b.index;
    });
    let previous = null, rank = 0;
    return ordered.map(({row, values}, index) => {
      const signature = values.includes(null) ? null : values.join('/');
      if (signature === null || signature !== previous) rank = index + 1;
      previous = signature;
      return {row, rank: values[0] === null ? null : rank};
    });
  }
  function gradeLabel(grade, en) {
    if (grade.exact !== null) return grade.exact.toFixed(2);
    return (statuses[grade.state] || statuses['insufficient-evidence'])[Number(en)];
  }
  function tableGrade(grade, en) {
    if (grade.exact !== null) return gradeLabel(grade, en);
    const label = gradeLabel(grade, en);
    return grade.state === 'not-tested' ? `<span class="state" data-unmeasured aria-label="${esc(label)}"></span>` :
      `<span class="state">${esc(label)}</span>`;
  }
  function checkpointCell(row, field, en) {
    if (untested(row) || !row.criteria) return '';
    const count = axis => {
      const {passed, planned, unknown} = row.criteria[axis];
      return `${passed}/${planned}${unknown ? (en ? ` (${unknown} unknown)` : `（${unknown} 未知）`) : ''}`;
    };
    if (field) return count(field);
    return axes.map(([axis], index) => `${['A', 'T', 'C'][index]} ${count(axis)}`).join(' · ');
  }
  function allChecksCell(row, field, en) {
    if (untested(row)) return '';
    const flag = field ? row.components[field].strict : row.task_strict === null ? null : row.task_strict === 100;
    if (flag === null) return en ? 'Unknown' : '未知';
    return flag ? (en ? 'All passed' : '全项通过') : (en ? 'Not all passed' : '未全项通过');
  }
  function renderTable(rows, field, sort, en) {
    const raw = field ? [] : en ? ['Autonomy', 'Taste', 'Capacity'] : axes.map(([, label]) => label);
    const headers = modes.map(mode => `<th scope="col" class="numeric" data-independent-score="${mode}"${mode === sort ? ' aria-sort="descending"' : ''}>${mode}</th>`).join('');
    const body = rows.map(({row, rank}) => {
      const scores = modes.map(mode => `<td class="numeric" data-independent-score="${mode}">${tableGrade(gradeFor(row, mode, field), en)}</td>`).join('');
      const components = field ? '' : axisIds.map(axis => `<td class="numeric">${tableGrade(gradeFor(row, 'RMC', axis), en)}</td>`).join('');
      return `<tr data-model="${esc(row.id)}"><td class="numeric">${rank ?? ''}</td><th scope="row">${esc(row.label)}</th>${scores}${components}<td class="numeric independent-checks">${checkpointCell(row, field, en)}</td><td class="numeric">${allChecksCell(row, field, en)}</td></tr>`;
    }).join('');
    return `<div class="table-wrap"><table class="compact independent-research-ranking${field ? '' : ' overall'}" data-independent-primary="${sort}"><thead><tr><th scope="col">#</th><th scope="col">${en ? 'Model' : '模型'}</th>${headers}${raw.map(label => `<th scope="col" class="numeric">${label} RMC</th>`).join('')}<th scope="col" class="numeric">${en ? 'Checks passed' : '检查点通过'}</th><th scope="col" class="numeric">${en ? 'All checks' : '全项检查'}</th></tr></thead><tbody>${body}</tbody></table></div>`;
  }
  function renderChart(rows, field, models, en) {
    const palette = (value, fallback) => /^#[\da-f]{6}$/i.test(value) ? value : fallback;
    const chart = rows.map(({row}) => {
      const model = models.get(row.id), ink = palette(model?.theme?.ink, '#445b8c');
      const color = palette(model?.theme?.color, ink), provider = model?.logo?.label ?? '';
      const bars = modes.map(mode => {
        const grade = gradeFor(row, mode, field), value = grade.exact, label = gradeLabel(grade, en);
        const text = grade.state === 'not-tested' ? '' : esc(label);
        const bar = value === null ? '' : `<span class="score-bar mode-${styling[mode]}" aria-hidden="true" style="left:0;width:${value}%"></span>`;
        return `<div class="metric-bar-row" data-score-mode="${styling[mode]}"><div class="bar-track">${bar}</div><span class="score-readout"><small>${mode}</small><span class="chart-value" title="${esc(label)}" aria-label="${esc(`${mode} ${label}`)}">${text}</span></span></div>`;
      }).join('');
      const checks = [checkpointCell(row, field, en), allChecksCell(row, field, en)].filter(Boolean).join(' · ');
      const detail = checks ? `<small class="independent-chart-checks">${esc(checks)}</small>` : '';
      return `<div class="bar-group" data-model="${esc(row.id)}" data-provider="${esc(provider)}" role="group" aria-label="${esc(row.label)}" style="--model-color:${color};--model-ink:${ink}"><div class="chart-model"><div>${esc(row.label)}${detail}</div></div><div class="metric-bars">${bars}</div></div>`;
    }).join('');
    const ticks = [0,20,40,60,80,100].map(tick => `<span style="left:${tick}%">${tick}</span>`).join('');
    return `<div class="score-figure"><div class="horizontal-score-chart independent-research-chart"><div class="score-x-axis">${ticks}</div>${chart}</div></div>`;
  }
  function renderResearchBoard(board, search, models, en) {
    const {tab, field, sort, view} = readBoard(search);
    const labels = en ? ['Overall', 'Research autonomy', 'Mathematical taste', 'Research capacity'] : ['总榜', ...axes.map(([, label]) => label)];
    const tabs = ['overall', ...axisIds].map((key, index) => `<button type="button" role="tab" data-independent-tab="${key}" aria-selected="${tab === key}">${labels[index]}</button>`).join('');
    const sortButtons = scoreOrder.map(mode => `<button type="button" data-independent-sort="${mode}" aria-pressed="${sort === mode}">${mode}</button>`).join('');
    const viewButtons = ['chart', 'table'].map(name => `<button type="button" data-independent-view="${name}" aria-pressed="${view === name}">${en ? (name === 'chart' ? 'Chart' : 'Table') : (name === 'chart' ? '图表' : '表格')}</button>`).join('');
    const rows = rankedRows(board.rows, field, sort);
    return `<div class="panel-head"><div><h2>${en ? 'Independent Open Research' : '独立开放研究排行榜'}</h2><p class="panel-desc">${en ? 'One three-round task · 10% of the overall score' : '1 道三轮任务 · 主榜权重 10%'}</p></div><div class="board-toolbar independent-research-controls"><div class="segmented" role="group" aria-label="${en ? 'Sort by score' : '按分数排序'}">${sortButtons}</div><div class="board-view segmented" role="group" aria-label="${en ? 'Chart or table' : '图表或表格'}">${viewButtons}</div></div></div><div class="segmented category-tabs" role="tablist" aria-label="${en ? 'Independent Open Research categories' : '独立开放研究分类'}">${tabs}</div>` +
      (view === 'chart' ? renderChart(rows, field, models, en) : renderTable(rows, field, sort, en));
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
      const labels={strict:'SMC综合',partial:'RMC综合',capability:board.schema===scoreModeSchema?'MC综合':'MC基准综合'};
      if(legend.lastChild?.nodeType===3)legend.lastChild.textContent=labels[legend.dataset.displayMode];
    }
    for(const cell of doc.querySelectorAll('#ranking thead .delivery-cell'))cell.textContent=en?'Delivery rate / 45':'整体交付率 / 45';
    const desc=doc.getElementById('leaderboard-desc'); if(desc)desc.textContent=board.adoption?(en?'1.3 settled full-scope comparisons · other confirmed contributions retained':'1.3完整范围的已结算比较 · 其他配置保留已确认贡献'):(en?'1.3 confirmed contribution · ten research points unmeasured':'1.3已确认贡献排序 · 新增10分未测，完整分仍未知');
    const anchor=doc.getElementById('category-leaderboards');
    if(anchor) {
      let panel=doc.getElementById('independent-research-leaderboards');
      if(!panel){panel=doc.createElement('section');panel.id='independent-research-leaderboards';panel.className='panel independent-research-board';anchor.insertAdjacentElement('afterend',panel);}
      const models=new Map(mg.d.models.map(m=>[m.id,m]));
      const {tab}=readBoard(location.search);
      panel.innerHTML=renderResearchBoard(board,location.search,models,en);
      const bind=(control,param)=>{
        const attribute='data-independent-'+control;
        const selector=`[${attribute}]`;
        const key='independent'+control[0].toUpperCase()+control.slice(1);
        for(const button of panel.querySelectorAll(selector))button.onclick=()=>{
          const value=button.dataset[key],url=new URL(location.href);
          url.searchParams.set(param,value);
          history.replaceState(null,'',url);
          decorate();
          panel.querySelector?.(`[${attribute}="${value}"]`)?.focus?.({preventScroll:true});
        };
      };
      bind('tab','independent-tab');
      bind('view','view-independent-'+tab);
      bind('sort','sort-independent-'+tab);
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
