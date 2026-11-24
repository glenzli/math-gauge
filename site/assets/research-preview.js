(function (root) {
  'use strict';
  const axes = [['autonomy', '研究自主'], ['taste', '数学品味'], ['capacity', '研究能力']];
  const labelsEn = {autonomy:'Research autonomy', taste:'Mathematical taste', capacity:'Research capacity'};
  const initials = {autonomy:'A', taste:'T', capacity:'C'};
  const checks = {autonomy: 2, taste: 3, capacity: 5};
  const modes = ['MC', 'RMC', 'SMC'];
  const scoreOrder = ['SMC', 'RMC', 'MC'];
  const styling = {MC: 'capability', RMC: 'partial', SMC: 'strict'};
  const scoreModeSchema = 'math-gauge.research-board-preview/v2';
  const valueSchema = 'math-gauge.research-board-preview/v3';
  const strictCreditSchema = 'math-gauge.research-board-preview/v4';
  const itemWeightSchema = 'math-gauge.research-board-preview/v5';
  const externalSchema = 'math-gauge.research-board-preview/v6';
  const strictCreditBoard = board => [strictCreditSchema, itemWeightSchema, externalSchema].includes(board.schema);
  const valueBoard = board => board.schema === valueSchema || strictCreditBoard(board);
  const scoreModeBoard = board => board.schema === scoreModeSchema || valueBoard(board);
  const boardAxes = board => valueBoard(board) ? axes.slice(1) : axes;
  const states = { 'not-tested': '未测', unreviewed: '待评', 'insufficient-evidence': '证据不足', 'delivery-failed': '未正常交付' };
  const statuses = {
    'not-tested': ['未测', 'Not tested'], 'review-pending': ['待评', 'Review pending'],
    'insufficient-evidence': ['证据不足', 'Insufficient evidence'], 'delivery-failed': ['未正常交付', 'No normal delivery'],
    unavailable: ['未提供', 'Unavailable']
  };
  const esc = value => String(value).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' })[c]);
  const keys = (obj, expected) => obj && Object.keys(obj).sort().join('|') === [...expected].sort().join('|');
  const score = value => typeof value === 'number' && Number.isFinite(value) && value >= 0 && value <= 100;
  const hash = value => typeof value === 'string' && /^[a-f0-9]{64}$/.test(value);
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
  function validateModes(row, axisIds, unmeasured, strictCredit) {
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
    if (strictCredit) {
      const {SMC, RMC, MC} = values;
      const upper = view => [view.item, ...axisIds.map(axis => view.components[axis])].map(metric => metric.upper);
      const reliable = upper(RMC), positive = upper(MC);
      // Unresolved upper bounds round outward, while exact scores round to nearest.
      const exceeds = (n, limit) => n - limit > 1e-9;
      if (upper(SMC).some((n, i) => exceeds(n, reliable[i])) || reliable.some((n, i) => exceeds(n, positive[i]))) {
        throw new Error('Strict credit must stay within retained reliable and positive credit');
      }
    }
  }
  function validate(data) {
    const baseline = data.kind === 'existing-model-unmeasured';
    const settled = data.kind === 'settled-selected-configurations';
    const scoreModes = scoreModeBoard(data), revised = valueBoard(data), strictCredit = strictCreditBoard(data);
    const hasExternal = data.schema === externalSchema;
    const weighted = data.schema === itemWeightSchema || hasExternal;
    const hasNative = Object.hasOwn(data, 'native_binding');
    const displayAxes = boardAxes(data), axisIds = displayAxes.map(([id]) => id);
    const fields = ['schema', 'edition', 'kind', 'category', 'rank_eligible', 'default_order', 'weights_ratified', 'rows'];
    if (baseline || settled) fields.push('source_binding');
    if (settled) fields.push('adoption');
    if (scoreModes && Object.hasOwn(data, 'score_modes_binding')) fields.push('score_modes_binding');
    if (revised) fields.push('value_binding', 'item_weights');
    if (strictCredit) fields.push('strict_credit_binding');
    if (weighted) fields.push('item_weight_binding');
    if (hasExternal) fields.push('external_binding');
    if (hasNative) fields.push('native_binding');
    if (!keys(data, fields) ||
        (!scoreModes && data.schema !== 'math-gauge.research-board-preview/v1') || data.edition !== '1.3.0' || (!baseline && !settled && data.kind !== 'synthetic-fixture') ||
        data.rank_eligible !== false || data.weights_ratified !== false || data.default_order !== 'retained-base-SMC' ||
        !keys(data.category, ['id', 'zh', 'en']) || data.category.id !== 'open-research' || !Array.isArray(data.rows)) {
      throw new Error('Unrecognized local display projection');
    }
    if (fields.includes('score_modes_binding') && (!keys(data.score_modes_binding, ['policy_sha256', 'index_sha256', 'base_index_sha256']) ||
        !Object.values(data.score_modes_binding).every(hash))) {
      throw new Error('Invalid score-mode source binding');
    }
    if (revised) {
      const binding = data.value_binding;
      if (!keys(binding, ['policy_sha256', 'base_results_sha256', 'index_sha256']) || !hash(binding.policy_sha256) ||
          !hash(binding.base_results_sha256) || binding.index_sha256 !== null && !hash(binding.index_sha256) ||
          data.score_modes_binding && binding.base_results_sha256 !== data.score_modes_binding.index_sha256 ||
          !keys(data.item_weights, axisIds) || !Object.values(data.item_weights).every(n => Number.isInteger(n) && n > 0)) {
        throw new Error('Invalid value score source binding or item weights');
      }
    }
    if (strictCredit) {
      const binding = data.strict_credit_binding;
      if (!keys(binding, ['policy_sha256', 'value_results_sha256', 'index_sha256']) || !hash(binding.policy_sha256) ||
          !hash(binding.value_results_sha256) || binding.value_results_sha256 !== data.value_binding.index_sha256 ||
          binding.index_sha256 !== null && !hash(binding.index_sha256)) throw new Error('Invalid strict-credit source binding');
    }
    if (weighted) {
      const binding = data.item_weight_binding;
      const sources = {value_policy_sha256: data.value_binding.policy_sha256,
        value_results_sha256: data.value_binding.index_sha256,
        strict_credit_policy_sha256: data.strict_credit_binding.policy_sha256,
        strict_credit_results_sha256: data.strict_credit_binding.index_sha256};
      if (!keys(binding, ['version', 'policy_sha256', ...Object.keys(sources)]) ||
          binding.version !== '0.1.0' || !hash(binding.policy_sha256) ||
          !Object.entries(sources).every(([key, digest]) => hash(digest) && binding[key] === digest)) {
        throw new Error('Invalid item weight source binding');
      }
    }
    if ((baseline || settled) && (!keys(data.source_binding, ['edition', 'sha256']) || data.source_binding.edition !== '1.2.0' || !/^[a-f0-9]{64}$/.test(data.source_binding.sha256))) throw new Error('Unbound baseline');
    const uniqueIds = ids => Array.isArray(ids) && ids.length && new Set(ids).size === ids.length;
    if (settled && (!keys(data.adoption, ['batch_sha256', 'index_sha256', 'cohort', 'planned_cohort', 'human_review']) ||
        !/^[a-f0-9]{64}$/.test(data.adoption.batch_sha256) || !/^[a-f0-9]{64}$/.test(data.adoption.index_sha256) ||
        data.adoption.human_review !== 'pending' || !uniqueIds(data.adoption.cohort) || !uniqueIds(data.adoption.planned_cohort) ||
        !data.adoption.cohort.every(id => data.adoption.planned_cohort.includes(id)))) throw new Error('Unbound configuration adoption');
    const adoptedIds = new Set(settled ? data.adoption.cohort : []);
    if (hasExternal) {
      const binding = data.external_binding;
      if (!settled || !keys(binding, ['index_sha256', 'adoption_sha256', 'cohort', 'source_kind', 'policy_bindings', 'human_review']) ||
          !hash(binding.index_sha256) || !hash(binding.adoption_sha256) || !uniqueIds(binding.cohort) ||
          binding.human_review !== 'pending' || binding.source_kind !== 'external-handoff-operator-attestation' ||
          !keys(binding.policy_bindings, ['value', 'strict_credit', 'item_weight']) ||
          binding.policy_bindings.value !== data.value_binding.policy_sha256 ||
          binding.policy_bindings.strict_credit !== data.strict_credit_binding.policy_sha256 ||
          binding.policy_bindings.item_weight !== data.item_weight_binding.policy_sha256 ||
          binding.cohort.some(id => adoptedIds.has(id))) throw new Error('Unbound external adoption');
      binding.cohort.forEach(id => adoptedIds.add(id));
    }
    const nativeKind = 'native-agy-same-conversation-sealed-finals';
    const nativeIds = new Set();
    if (hasNative) {
      const binding = data.native_binding;
      if (!settled || !weighted || !keys(binding, ['index_sha256', 'adoption_sha256', 'cohort', 'source_kind', 'policy_bindings', 'human_review']) ||
          !hash(binding.index_sha256) || !hash(binding.adoption_sha256) || !uniqueIds(binding.cohort) ||
          binding.human_review !== 'pending' || binding.source_kind !== nativeKind ||
          !keys(binding.policy_bindings, ['value', 'strict_credit', 'item_weight']) ||
          binding.policy_bindings.value !== data.value_binding.policy_sha256 ||
          binding.policy_bindings.strict_credit !== data.strict_credit_binding.policy_sha256 ||
          binding.policy_bindings.item_weight !== data.item_weight_binding.policy_sha256 ||
          binding.cohort.some(id => adoptedIds.has(id))) throw new Error('Unbound native adoption');
      binding.cohort.forEach(id => {nativeIds.add(id);adoptedIds.add(id);});
    }
    const rowFields = ['id', 'label', 'kind', 'base_smc', 'components', 'task_strict', 'item', 'coverage', 'strict_overall', 'composite', 'composites', 'confirmed', 'strict_confirmed', 'delivery'];
    if (scoreModes) rowFields.push('score_modes', 'criteria');
    const seen = new Set();
    for (const row of data.rows) {
      if (!keys(row, rowFields) ||
          !((baseline || settled) ? /^[a-z0-9.-]+$/.test(row.id) : /^fixture-[a-z]+$/.test(row.id)) || seen.has(row.id) || row.kind !== (nativeIds.has(row.id) ? nativeKind : data.kind) || typeof row.label !== 'string' ||
          !(score(row.base_smc) || bounds(row.base_smc)) || !keys(row.components, axisIds) || !bounds(row.strict_overall) || !bounds(row.composite) || !keys(row.composites, ['MC','RMC','SMC']) || !Object.values(row.composites).every(bounds) || !keys(row.confirmed,['MC','RMC','SMC']) || !Object.values(row.confirmed).every(score) || !score(row.strict_confirmed) || !keys(row.delivery,['planned','normal','unknown']) || row.delivery.planned!==45 || !Number.isInteger(row.delivery.normal) || !Number.isInteger(row.delivery.unknown) || row.delivery.normal<0 || row.delivery.unknown<0 || row.delivery.normal+row.delivery.unknown>45 || !bounds(row.item) ||
          ![0, 100, null].includes(row.task_strict) || !keys(row.coverage, ['planned', 'reviewed', 'components_planned', 'components_reviewed']) ||
          row.coverage.planned !== 1 || row.coverage.components_planned !== axisIds.length || ![0, 1].includes(row.coverage.reviewed) ||
          !Number.isInteger(row.coverage.components_reviewed) || row.coverage.components_reviewed < 0 ||
          row.coverage.components_reviewed > axisIds.length) throw new Error('Unexpected row or private payload');
      const unmeasured = baseline || (settled && !adoptedIds.has(row.id));
      if (unmeasured && (row.task_strict !== null || row.coverage.reviewed !== 0 || row.coverage.components_reviewed !== 0 || row.strict_overall.exact !== null || row.composite.exact !== null)) throw new Error('Unmeasured model acquired a research result');
      if (scoreModes) validateModes(row, axisIds, unmeasured, strictCredit);
      seen.add(row.id);
      for (const [key] of displayAxes) {
        const component = row.components[key];
        if (!keys(component, ['state', 'value', 'strict'])) throw new Error('Unexpected component fields');
        if (unmeasured && (component.state !== 'not-tested' || component.value !== null || component.strict !== null)) throw new Error('Unmeasured component acquired a grade');
        const pendingRevision = revised && component.state === 'unreviewed';
        if (settled && !unmeasured && !pendingRevision && !['reviewed', 'insufficient-evidence', 'delivery-failed'].includes(component.state)) throw new Error('Adopted component is still pending');
        if (![true,false,null].includes(component.strict) || !(component.state === 'reviewed' ? score(component.value) :
            Object.hasOwn(states, component.state) && component.value === null)) throw new Error('Unknown and zero must remain distinct');
      }
    }
    if (settled && !data.adoption.planned_cohort.every(id => seen.has(id))) throw new Error('Missing planned configuration');
    if (hasExternal && !data.external_binding.cohort.every(id => seen.has(id))) throw new Error('Missing external configuration');
    if (hasNative && !data.native_binding.cohort.every(id => seen.has(id))) throw new Error('Missing native configuration');
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
    if (scoreModeBoard(data)) return renderResearchBoard(data, search, new Map(), false);
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
  function readBoard(search, axisIds) {
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
  function checkpointCell(row, field, en, axisIds) {
    if (untested(row) || !row.criteria) return '';
    const count = axis => {
      const {passed, planned, unknown} = row.criteria[axis];
      return `${passed}/${planned}${unknown ? (en ? ` (${unknown} unknown)` : `（${unknown} 未知）`) : ''}`;
    };
    if (field) return count(field);
    return axisIds.map(axis => `${initials[axis]} ${count(axis)}`).join(' · ');
  }
  function allChecksCell(row, field, en) {
    if (untested(row)) return '';
    const flag = field ? row.components[field].strict : row.task_strict === null ? null : row.task_strict === 100;
    if (flag === null) return en ? 'Unknown' : '未知';
    return flag ? (en ? 'All passed' : '全项通过') : (en ? 'Not all passed' : '未全项通过');
  }
  function renderTable(rows, field, sort, en, displayAxes) {
    const axisIds = displayAxes.map(([id]) => id);
    const raw = field ? [] : displayAxes.map(([id, label]) => en ? labelsEn[id] : label);
    const headers = modes.map(mode => `<th scope="col" class="numeric" data-independent-score="${mode}"${mode === sort ? ' aria-sort="descending"' : ''}>${mode}</th>`).join('');
    const body = rows.map(({row, rank}) => {
      const scores = modes.map(mode => `<td class="numeric" data-independent-score="${mode}">${tableGrade(gradeFor(row, mode, field), en)}</td>`).join('');
      const components = field ? '' : axisIds.map(axis => `<td class="numeric">${tableGrade(gradeFor(row, 'RMC', axis), en)}</td>`).join('');
      return `<tr data-model="${esc(row.id)}"><td class="numeric">${rank ?? ''}</td><th scope="row">${esc(row.label)}</th>${scores}${components}<td class="numeric independent-checks">${checkpointCell(row, field, en, axisIds)}</td><td class="numeric">${allChecksCell(row, field, en)}</td></tr>`;
    }).join('');
    return `<div class="table-wrap"><table class="compact independent-research-ranking${field ? '' : ' overall'}" data-independent-primary="${sort}"><thead><tr><th scope="col">#</th><th scope="col">${en ? 'Model' : '模型'}</th>${headers}${raw.map(label => `<th scope="col" class="numeric">${label} RMC</th>`).join('')}<th scope="col" class="numeric">${en ? 'Checks passed' : '检查点通过'}</th><th scope="col" class="numeric">${en ? 'All checks' : '全项检查'}</th></tr></thead><tbody>${body}</tbody></table></div>`;
  }
  function renderChart(rows, field, models, en, axisIds) {
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
      const checks = [checkpointCell(row, field, en, axisIds), allChecksCell(row, field, en)].filter(Boolean).join(' · ');
      const detail = checks ? `<small class="independent-chart-checks">${esc(checks)}</small>` : '';
      return `<div class="bar-group" data-model="${esc(row.id)}" data-provider="${esc(provider)}" role="group" aria-label="${esc(row.label)}" style="--model-color:${color};--model-ink:${ink}"><div class="chart-model"><div>${esc(row.label)}${detail}</div></div><div class="metric-bars">${bars}</div></div>`;
    }).join('');
    const ticks = [0,20,40,60,80,100].map(tick => `<span style="left:${tick}%">${tick}</span>`).join('');
    return `<div class="score-figure"><div class="horizontal-score-chart independent-research-chart"><div class="score-x-axis">${ticks}</div>${chart}</div></div>`;
  }
  function renderResearchBoard(board, search, models, en) {
    const displayAxes = boardAxes(board), axisIds = displayAxes.map(([id]) => id);
    const {tab, field, sort, view} = readBoard(search, axisIds);
    const labels = [en ? 'Overall' : '总榜', ...displayAxes.map(([id, label]) => en ? labelsEn[id] : label)];
    const tabs = ['overall', ...axisIds].map((key, index) => `<button type="button" role="tab" data-independent-tab="${key}" aria-selected="${tab === key}">${labels[index]}</button>`).join('');
    const sortButtons = scoreOrder.map(mode => `<button type="button" data-independent-sort="${mode}" aria-pressed="${sort === mode}">${mode}</button>`).join('');
    const viewButtons = ['chart', 'table'].map(name => `<button type="button" data-independent-view="${name}" aria-pressed="${view === name}">${en ? (name === 'chart' ? 'Chart' : 'Table') : (name === 'chart' ? '图表' : '表格')}</button>`).join('');
    const rows = rankedRows(board.rows, field, sort);
    return `<div class="panel-head"><div><h2>${en ? 'Independent Open Research' : '独立开放研究排行榜'}</h2><p class="panel-desc">${en ? 'One three-round task · 10% of the overall score' : '1 道三轮任务 · 主榜权重 10%'}</p></div><div class="board-toolbar independent-research-controls"><div class="segmented" role="group" aria-label="${en ? 'Sort by score' : '按分数排序'}">${sortButtons}</div><div class="board-view segmented" role="group" aria-label="${en ? 'Chart or table' : '图表或表格'}">${viewButtons}</div></div></div><div class="segmented category-tabs" role="tablist" aria-label="${en ? 'Independent Open Research categories' : '独立开放研究分类'}">${tabs}</div>` +
      (view === 'chart' ? renderChart(rows, field, models, en, axisIds) : renderTable(rows, field, sort, en, displayAxes));
  }
  const api = { validate, render };
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
  root.MGResearchPreview = api;
  const categoryId = 'independent_open_research';
  function categoryStatus(state, lang) {
    if (!Object.hasOwn(statuses, state)) return null;
    const label = statuses[state][lang === 'en' ? 1 : 0];
    return {text:state === 'not-tested' ? '' : label, label};
  }
  function categoryScoreLabel(board, axis, lang, weighted) {
    const en = lang === 'en';
    if (axis === 'item') return en ? 'Composite' : '综合';
    const label = en ? labelsEn[axis] : axes.find(([id]) => id === axis)[1];
    if (!weighted) return label;
    const {taste, capacity} = board.item_weights;
    const share = board.item_weights[axis]+'/'+(taste+capacity);
    return en ? label+' ('+share+')' : label+'（'+share+'）';
  }
  function categoryComponents(data) {
    const board = data.research_preview;
    if (data.benchmark_version !== '1.3.0' || !board || !valueBoard(board)) return null;
    const byModel = new Map(board.rows.map(row => [row.id, row]));
    return {
      id:categoryId, axes:boardAxes(board).map(([id]) => id),
      label:(axis, lang, weighted) => categoryScoreLabel(board, axis, lang, weighted),
      metric(id, mode, axis) {
        const view = byModel.get(id)?.score_modes[mode];
        const metric = axis === 'item' ? view?.item : view?.components[axis];
        return metric ? {...metric, value:metric.exact} : {value:null, state:'unavailable'};
      }
    };
  }
  function localizeCategoryScores(doc, board, lang, count) {
    for (const label of doc.querySelectorAll('[data-research-score-label]')) {
      const grouped = Object.hasOwn(label.dataset, 'researchScoreGroup');
      const text = categoryScoreLabel(board, label.dataset.researchScoreLabel, lang, grouped);
      if (label.textContent !== text) label.textContent = text;
      if (grouped && label.colSpan !== count) label.colSpan = count;
    }
  }
  function mountCategory(doc) {
    const template = doc.getElementById('independent-research-category-template');
    const tabs = doc.querySelector('#category-leaderboards .category-tabs');
    const supporting = doc.getElementById('category-panel-research');
    if (!template || !tabs || !supporting || doc.getElementById('category-tab-'+categoryId)) return;
    const [tab, panel] = template.content.cloneNode(true).children;
    tabs.append(tab);
    supporting.insertAdjacentElement('afterend', panel);
  }
  function decorate() {
    const mg = typeof MG !== 'undefined' ? MG : root.MG;
    if (!mg || mg.d.benchmark_version !== '1.3.0' || !mg.d.research_preview) return;
    const board = mg.d.research_preview;
    const projection = {...board};
    delete projection.weight_frame; delete projection.base_edition; delete projection.condition;
    validate(projection);
    const doc = root.document, table = doc.getElementById('ranking');
    doc.getElementById('independent-research-preview-note')?.remove();
    mountCategory(doc);
    if (!table) return;
    doc.documentElement.setAttribute('data-independent-research-preview','');
    const en = mg.state.lang === 'en';
    const costScope = en ? 'Costs for retained evaluation runs' : '采用记录的评测成本';
    const timingScope = en ? 'Shared timed tasks · excludes independent open research' : '共有计时任务 · 不含独立开放研究';
    const frontierScope = en ? 'Scores and resource use from retained evaluation records' : '采用评测记录中的成绩、成本与耗时';
    for (const [headingId, text] of [['cost-title', costScope], ['timing-title', timingScope], ['cost-frontier-title', frontierScope]]) {
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
    const rows = new Map(board.rows.map(r=>[r.id,r]));
    const strictCredit = strictCreditBoard(board);
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
      const labels={strict:'SMC综合',partial:'RMC综合',capability:scoreModeBoard(board)?'MC综合':'MC基准综合'};
      if(legend.lastChild?.nodeType===3)legend.lastChild.textContent=labels[legend.dataset.displayMode];
    }
    for(const cell of doc.querySelectorAll('#ranking thead .delivery-cell'))cell.textContent=en?'Delivery rate / 45':'整体交付率 / 45';
    const desc=doc.getElementById('leaderboard-desc'); if(desc)desc.textContent=board.adoption?(en?'1.3 settled full-scope comparisons · other confirmed contributions retained':'1.3完整范围的已结算比较 · 其他配置保留已确认贡献'):(en?'1.3 confirmed contribution · ten research points unmeasured':'1.3已确认贡献排序 · 新增10分未测，完整分仍未知');
    const explanation=doc.getElementById('score-explanation');
    if(explanation&&mg.state.score==='strict')explanation.textContent=strictCredit?
      (en?'Independent open research keeps the net credit of passed checks. The original tasks retain their acceptance rules.':'独立开放研究保留已通过检查的净信用，既有任务沿用原验收规则。'):
      (en?'Existing tasks retain whole-task and self-check acceptance; independent open research uses checkpoint-based SMC.':'既有任务按整题与自查轨迹验收；独立开放研究按检查点计 SMC。');
    const category=doc.getElementById('category-tab-research');if(category)category.textContent=en?'Supporting research':'辅助研究';
    const supportingTitle=doc.querySelector('#category-panel-research h3');
    if(supportingTitle)supportingTitle.textContent=en?'Supporting research leaderboard':'辅助研究排行榜';
    const context=doc.querySelector('#category-leaderboards .section-context');
    if (context) context.textContent=en?'Each category sorts independently':'各类独立排序';
    const tab=doc.getElementById('category-tab-'+categoryId);
    if (tab) tab.textContent=board.category[en?'en':'zh'];
    const title=doc.querySelector('#category-panel-'+categoryId+' h3');
    if (title) title.textContent=en?board.category.en+' leaderboard':board.category.zh+'排行榜';
    const categoryDesc=doc.querySelector('#category-panel-'+categoryId+' .panel-desc');
    if (categoryDesc) {
      const weight=board.weight_frame[categoryId];
      categoryDesc.textContent=en?`Category / 100 · overall weight ${weight}%`:`类内满分100 · 总榜权重${weight}%`;
    }
    if (valueBoard(board)) {
      const shown = root.MGBoards?.readBoard(location.search, categoryId).shown.length ?? modes.length;
      localizeCategoryScores(doc, board, mg.state.lang, shown);
    }
    for (const readout of doc.querySelectorAll('[data-research-category-state]')) {
      const display=categoryStatus(readout.dataset.researchCategoryState, mg.state.lang);
      if(display){readout.textContent=display.text;readout.setAttribute('aria-label',display.label)}
    }
    for(const key of ['written','lean','research']) {
      const label=doc.querySelector('#category-panel-'+key+' .panel-desc');if(label)label.textContent=en?'Source category score /100 · New overall weight 30%':'源分项百分制 · 新总榜权重30%';
    }
  }
  api.categoryStatus = categoryStatus;
  api.categoryComponents = categoryComponents;
  api.decorate = decorate;
  if (typeof document !== 'undefined') {
    root.addEventListener('mg:updated', decorate);
    decorate();
  }
})(globalThis);
