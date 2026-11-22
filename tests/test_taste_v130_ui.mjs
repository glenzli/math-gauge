// Aggregate-only UI fixture contracts; no private task or mathematical review.
import test from 'node:test';
import assert from 'node:assert/strict';
import { createRequire } from 'node:module';
const require = createRequire(import.meta.url);
const ui = require('../scripts/templates/research-preview.js');
const boards = require('../scripts/templates/board-controls.js');
require('./fixtures/research-preview-v130.js');
const fixture = globalThis.MGResearchPreviewData;

test('the authorized source retains the three independent grades for the profile', () => {
  assert.doesNotThrow(() => ui.validate(fixture));
  for (const row of fixture.rows) {
    assert.deepEqual(Object.keys(row.components).sort(), ['autonomy', 'capacity', 'taste']);
    assert.equal(row.coverage.planned, 1);
  }
});

test('zero, untested, unreviewed and insufficient evidence are distinct visible values', () => {
  const html = ui.render(fixture);
  for (const value of ['>0.0<', 'aria-label="未测"', '>待评<', '>证据不足<']) assert.ok(html.includes(value));
  assert.ok(html.includes('全项检查未知'));
  assert.ok(html.includes('未全项通过'));
});

test('subscores never rerank the retained SMC order or recompute the totals', () => {
  const data = structuredClone(fixture);
  data.rows[0].components.autonomy.value = 0;
  data.rows[1].components.autonomy.value = 100;
  data.rows[0].strict_overall = { exact: 12.34, lower: 12.34, upper: 12.34 };
  const html = ui.render(data);
  const order = [...html.matchAll(/data-model="([^"]+)"/g)].map(m => m[1]);
  assert.deepEqual(order, data.rows.map(row => row.id));
  assert.ok(html.includes('12.34'));
});

test('public projection rejects private additions at every displayed boundary', () => {
  for (const add of [
    data => { data.private_case = 'forbidden'; },
    data => { data.rows[0].manuscript = 'forbidden'; },
    data => { data.rows[0].components.autonomy.reason = 'forbidden'; },
    data => { data.rows[0].strict_overall.evidence = 'forbidden'; },
  ]) {
    const data = structuredClone(fixture); add(data);
    assert.throws(() => ui.render(data));
  }
});

test('synthetic data cannot masquerade as real model results and labels are escaped', () => {
  const data = structuredClone(fixture);
  data.kind = 'model-results';
  assert.throws(() => ui.render(data));
  data.kind = 'synthetic-fixture'; data.rows[0].label = '<script>bad()</script>';
  assert.ok(ui.render(data).includes('&lt;script&gt;bad()&lt;/script&gt;'));
  data.rows[0].components.autonomy = { state: 'not-tested', value: 0 };
  assert.throws(() => ui.render(data));
});

test('published baselines show only unmeasured new-task states, never inherited grades', () => {
  const data = structuredClone(globalThis.MGResearchBaselineData);
  const html = ui.render(data);
  assert.ok(html.includes('1.2.0 基准'));
  assert.equal((html.match(/aria-label="未测"/g) || []).length, data.rows.length * 3);
  assert.ok(!html.includes('FIXTURE'));
  data.rows[0].components.capacity = { state: 'reviewed', value: 100, strict: true };
  assert.throws(() => ui.render(data));
  data.rows[0].components.capacity = { state: 'not-tested', value: null, strict: null };
  data.rows[0].task_strict = 100;
  assert.throws(() => ui.render(data));
});

test('old editions receive no DOM mutation from the new controller', () => {
  globalThis.MG = { d: { benchmark_version: '1.2.0' } };
  ui.decorate(); // No document exists: any attempted mutation would throw.
  delete globalThis.MG;
});

test('a settled subset retains the fixed plan and keeps every unselected model unmeasured', () => {
  // Pure synthetic grades on an in-memory clone; never install a public result.
  const data = structuredClone(globalThis.MGResearchBaselineData);
  data.kind = 'settled-selected-configurations';
  const planned = data.rows.slice(0,10).map(r=>r.id);
  data.adoption = {batch_sha256:'a'.repeat(64),index_sha256:'b'.repeat(64),cohort:planned.slice(0,2),planned_cohort:planned,human_review:'pending'};
  data.rows = data.rows.map((row,index)=>index<2?{...structuredClone(fixture.rows[index]),id:row.id,label:row.label,kind:data.kind}:{...row,kind:data.kind});
  assert.doesNotThrow(()=>ui.validate(data));
  assert.match(ui.render(data),/>0.0</);
  const unselected=structuredClone(data);
  unselected.rows[2].components.autonomy={state:'reviewed',value:0,strict:false};
  assert.throws(()=>ui.validate(unselected));
  const pending=structuredClone(data);
  pending.rows[0].components.taste={state:'unreviewed',value:null,strict:null};
  assert.throws(()=>ui.validate(pending));
  const privateData=structuredClone(data);
  privateData.adoption.evidence='forbidden';
  assert.throws(()=>ui.validate(privateData));
  const changedPlan=structuredClone(data);
  changedPlan.adoption.planned_cohort.shift();
  assert.throws(()=>ui.validate(changedPlan));
});

function modeMetric(exact, state = exact === null ? 'insufficient-evidence' : 'reviewed') {
  return {lower:exact ?? 0,upper:exact ?? 100,exact,confirmed:exact ?? 0,state};
}

function scoreModeBoard(source = fixture) {
  const board = structuredClone(source);
  board.schema = 'math-gauge.research-board-preview/v2';
  for(const row of board.rows) {
    const untested = Object.values(row.components).every(grade=>grade.state==='not-tested');
    const unavailable = untested ? 'not-tested' : 'review-pending';
    row.criteria = Object.fromEntries(Object.entries({autonomy:2,taste:3,capacity:5}).map(([axis,planned])=>
      [axis,{planned,passed:0,unknown:planned}]));
    row.score_modes = {};
    for(const mode of ['MC','RMC','SMC']) {
      row.score_modes[mode] = {item:modeMetric(mode==='RMC'?row.item.exact:null, mode==='RMC'&&row.item.exact!==null?'reviewed':unavailable),
        components:Object.fromEntries(Object.entries(row.components).map(([axis,grade])=>[axis,
          mode==='RMC'&&grade.value!==null?modeMetric(grade.value):modeMetric(null,unavailable)]))};
    }
  }
  const first = board.rows[0];
  if(first?.components.capacity.state==='reviewed') {
    first.criteria.capacity = {planned:5,passed:4,unknown:0};
    first.components.capacity.strict = false;
    first.task_strict = 0;
    first.score_modes.MC.components.capacity = modeMetric(91);
    first.score_modes.SMC.components.capacity = modeMetric(80);
    first.score_modes.SMC.item = modeMetric(90);
  }
  return board;
}

function valueBoard() {
  const board = scoreModeBoard();
  board.schema = 'math-gauge.research-board-preview/v3';
  board.value_binding = {policy_sha256:'a'.repeat(64),base_results_sha256:'b'.repeat(64),index_sha256:'c'.repeat(64)};
  board.item_weights = {taste:1,capacity:2};
  const [assessed,zero,insufficient,unmeasured] = board.rows;
  board.rows = [assessed,zero,insufficient,unmeasured];
  zero.components.taste.value = 0;
  zero.score_modes.RMC.components.taste = modeMetric(0);
  insufficient.score_modes.RMC.components.taste = modeMetric(null,'insufficient-evidence');
  for (const row of board.rows) {
    delete row.components.autonomy;
    delete row.criteria.autonomy;
    for (const mode of Object.values(row.score_modes)) delete mode.components.autonomy;
    const reviewed = Object.values(row.components).filter(grade=>grade.state==='reviewed').length;
    row.coverage = {planned:1,reviewed:Number(reviewed===2),components_planned:2,components_reviewed:reviewed};
  }
  return board;
}

function strictCreditBoard(board = valueBoard()) {
  board.schema = 'math-gauge.research-board-preview/v4';
  board.strict_credit_binding = {policy_sha256:'d'.repeat(64),value_results_sha256:board.value_binding.index_sha256,
    index_sha256:'e'.repeat(64)};
  for (const row of board.rows) row.score_modes.SMC = structuredClone(row.score_modes.RMC);
  const row = board.rows[0];
  row.score_modes.SMC.components.capacity = modeMetric(73);
  return board;
}

test('current category shows only scored taste and capacity with distinct evidence states', () => {
  const board = valueBoard();
  const table = ui.render(board,'?view-independent=table&independent-tab=autonomy');
  const rows = Object.fromEntries([...table.matchAll(/<tr data-model="([^"]+)">([\s\S]*?)<\/tr>/g)]
    .map(([,id,row])=>[id,row]));
  assert.match(table,/数学品味 RMC/);
  assert.match(table,/研究能力 RMC/);
  assert.doesNotMatch(table,/data-independent-tab="autonomy"|研究自主/);
  assert.match(rows['fixture-alpha'],/>65\.00</);
  assert.match(rows['fixture-beta'],/>0\.00</);
  assert.match(rows['fixture-gamma'],/>证据不足</);
  assert.match(rows['fixture-delta'],/data-unmeasured aria-label="未测"><\/span>/);
  for (const mutate of [
    board => {board.rows[0].score_modes.SMC.components.taste.quote='private';},
    board => {board.rows[0].components.autonomy={state:'reviewed',value:100,strict:true};},
    board => {board.rows[0].extension={evidence:'private'};},
    board => {board.value_binding.path='private';},
  ]) {
    const changed = valueBoard(); mutate(changed);
    assert.throws(()=>ui.validate(changed));
  }
});

test('the category supplies whole-item scores and keeps point SMC separate from all-check status', () => {
  const data = scoreModeBoard();
  assert.doesNotThrow(()=>ui.validate(data));
  const row=data.rows[0];
  assert.deepEqual(Object.keys(row.score_modes), ['MC', 'RMC', 'SMC']);
  assert.equal(row.score_modes.SMC.item.exact, 90);
  assert.equal(row.score_modes.SMC.components.capacity.exact, 80);
  assert.equal(row.task_strict, 0);
  assert.deepEqual(row.criteria.capacity, {planned:5, passed:4, unknown:0});
});

test('strict net credit and check counts remain distinct public fields', () => {
  const board = strictCreditBoard();
  const row = board.rows[0];
  const html = ui.render(board,'?view-independent=table&independent-tab=capacity');
  const cells = html.match(/<tr data-model="fixture-alpha">([\s\S]*?)<\/tr>/)[1];
  assert.match(cells,/data-independent-score="SMC">73\.00</);
  assert.match(cells,/independent-checks">4\/5</);
  assert.match(cells,/未全项通过/);
  row.score_modes.SMC.components.capacity = modeMetric(81);
  assert.throws(()=>ui.validate(board),/retained reliable and positive credit/);
  row.score_modes.SMC.components.capacity = modeMetric(73);
  row.score_modes.RMC.item = modeMetric(87.3333333333);
  row.score_modes.SMC.item = {...modeMetric(null,'review-pending'),upper:87.3333333334};
  assert.doesNotThrow(()=>ui.validate(board),'an outward-rounded uncertain upper bound retains its exact ceiling');
  board.strict_credit_binding.reason = 'private';
  assert.throws(()=>ui.validate(board),/source binding/);
});

test('the native board controller stores the fourth category view independently', () => {
  const key='independent_open_research';
  const source='https://example.test/index.html?category='+key+'&sort-'+key+'=partial&view-lean=table';
  const url=boards.boardURL(source,key,{shown:['strict','capability'],view:'table'});
  assert.equal(url.searchParams.get('category'),key);
  assert.equal(url.searchParams.get('sort-'+key),'partial');
  assert.equal(boards.readView(url.search,key),'table');
  assert.deepEqual(boards.readBoard(url.search,key).shown,['strict','capability']);
  assert.equal(boards.readView(url.search,'lean'),'table');
});

test('v2 projections reject private nested fields, changed denominators, and unknown scores recorded as zero', () => {
  for(const mutate of [
    board=>{board.rows[0].criteria.capacity.direction_name='private';},
    board=>{board.rows[0].score_modes.MC.item.quote='private';},
    board=>{board.rows[0].criteria.capacity.planned=6;},
    board=>{board.rows[0].score_modes.MC.item=modeMetric(0,'not-tested');},
    board=>{board.score_modes_binding={policy_sha256:'d'.repeat(64),index_sha256:'a'.repeat(64),base_index_sha256:'e'.repeat(64),path:'private'};},
  ]) {
    const data = scoreModeBoard(); mutate(data);
    assert.throws(()=>ui.render(data));
  }
});

test('the homepage guide explains checkpoint SMC in 1.3 and preserves the older whole-task rule', async () => {
  const {readFileSync} = await import('node:fs');
  const vm = await import('node:vm');
  const source = readFileSync(new URL('../scripts/templates/edition-notes.js',import.meta.url),'utf8');
  const node = (tagName,textContent) => ({tagName,textContent,children:[],dataset:{},setAttribute(){},querySelector(){return null;},
    append(...items){this.children.push(...items);},replaceChildren(...items){this.children=items;},
    createTHead(){const part=node('thead');this.append(part);return part;},
    createTBody(){const part=node('tbody');this.append(part);return part;},
    insertRow(){const part=node('tr');this.append(part);return part;},
    insertCell(){const part=node('td');this.append(part);return part;}});
  const flatten = element => [element.textContent,...element.children.map(flatten)].filter(Boolean).join(' ');
  const guide = (edition,lang,researchPreview={}) => {
    const shell = node('details');
    Object.assign(shell.dataset,{tasks:'39',public:'25',private:'14',families:'35',total:'100'});
    const document={querySelector:selector=>selector==='[data-assessment-guide]'?shell:selector==='main'?{}:null,
      querySelectorAll:()=>[],getElementById:()=>null};
    const independent=edition==='1.3.0';
    const groups=['written','lean','research'].map((id,index)=>({id,weight:independent?30:index<2?35:30,children:[]}));
    if(independent)groups.push({id:'independent_open_research',weight:10,children:[]});
    const d={benchmark_version:edition,research_preview:independent?researchPreview:null,models:[],policy:{groups,subcategories:[]}};
    vm.runInNewContext(source,{document,location:new URL('https://example.test/index.html'),URL,window:{addEventListener(){}},
      MG:{d,state:{lang},node,href:value=>value}});
    const descendants=element=>[element,...element.children.flatMap(descendants)];
    const taxonomy=descendants(shell).find(element=>element.tagName==='table');
    return {text:flatten(shell),rows:taxonomy.children.find(element=>element.tagName==='tbody').children};
  };
  const current = guide('1.3.0','zh');
  assert.match(current.text,/25／25／50.*A 的2个门槛、T 的3个方面、C 的5个硬方向/);
  assert.match(current.text,/4／5时，该项 SMC 为80，状态为「未全项通过」/);
  assert.deepEqual(current.rows.map(row=>row.children[0].textContent),['书面证明','Lean','辅助研究','独立开放研究']);
  assert.equal(current.rows.reduce((sum,row)=>sum+parseFloat(row.children[2].textContent),0),100);
  assert.match(guide('1.3.0','en').text,/checkpoint.*capacity SMC of 80/);
  const revised = guide('1.3.0','zh',valueBoard());
  assert.match(revised.text,/数学品味 1 · 研究能力 2/);
  assert.match(revised.text,/自主拓展档位只折算数学画像的研究主动性/);
  assert.doesNotMatch(revised.text,/25／25／50|研究自主25%/);
  const retainedCredit = guide('1.3.0','zh',strictCreditBoard());
  assert.match(retainedCredit.text,/全部通过时保留该项实际 RMC/);
  assert.match(retainedCredit.text,/检查.*通过数单列/);
  assert.doesNotMatch(retainedCredit.text,/各自在分项内等权/);
  const older = guide('1.2.0','zh');
  assert.match(older.text,/每份交付按整题通过／不通过验收/);
  assert.doesNotMatch(older.text,/检查点/);
  assert.equal(older.rows.length,3);
});

test('the lexical MG controller installs one native category and leaves the main table intact', async () => {
  const { readFileSync } = await import('node:fs');
  const vm = await import('node:vm');
  const board = structuredClone(globalThis.MGResearchBaselineData); board.rows = board.rows.slice(0,2);
  const [first, second] = board.rows;
  board.kind = 'settled-selected-configurations';
  board.adoption = {batch_sha256:'a'.repeat(64),index_sha256:'b'.repeat(64),cohort:[first.id],
    planned_cohort:[first.id,second.id],human_review:'pending'};
  board.rows = [{...structuredClone(fixture.rows[0]),id:first.id,label:first.label,kind:board.kind},
    {...second,kind:board.kind}];
  const nodes = new Map();
  class Element {
    constructor(tag) {this.tagName=tag.toUpperCase();this.dataset={};this.children=[];this.cells=this.children;this.attrs={};this.hidden=false;this.textContent='';}
    append(node){this.children.push(node);node.parent=this;if(node.id)nodes.set(node.id,node);}
    prepend(node){this.children.unshift(node);node.parent=this;if(node.id)nodes.set(node.id,node);}
    setAttribute(key,val){this.attrs[key]=val;}
    insertBefore(node,last){this.children.splice(this.children.indexOf(last),0,node);node.parent=this;}
    remove(){if(this.parent)this.parent.children.splice(this.parent.children.indexOf(this),1);if(this.id)nodes.delete(this.id);}
    insertAdjacentElement(_,node){(this.adjacent??=[]).push(node);nodes.set(node.id,node);}
    querySelector(selector){return selector==='[data-research-checkpoints]'?this.children.find(x=>Object.hasOwn(x.dataset,'researchCheckpoints')):null;}
    insertCell(){const cell=new Element('td');this.append(cell);return cell;}
  }
  const table=new Element('table'),wrap=new Element('div'),head=new Element('tr'),body=new Element('tr');
  table.closest=()=>wrap;table.tHead={rows:[head],insertRow(){const r=new Element('tr');this.rows.push(r);return r;}};
  for(let i=0;i<8;i++)head.append(new Element('th'));
  for(let i=0;i<8;i++)body.append(new Element('td'));
  for(const [index,mode] of [[4,'strict'],[5,'partial'],[6,'capability']])head.cells[index].dataset.displayMode=mode;
  table.querySelector=()=>head.cells.find(c=>Object.hasOwn(c.dataset,'researchGroup'));
  table.querySelectorAll=()=>head.cells.filter(c=>c.dataset.displayMode);
  const link={href:'https://example.test/models/'+board.rows[0].id+'/index.html?edition=1.3.0',dataset:{}};
  body.querySelector=()=>link;
  for(const [id,node] of [['ranking',table],['leaderboard',new Element('section')],['leaderboard-desc',new Element('p')]])nodes.set(id,node);
  const banner=new Element('p');banner.id='independent-research-preview-note';
  nodes.get('leaderboard').append(banner);
  const resourceHeadings=['cost-title','timing-title','cost-frontier-title'].map(id=>{
    const heading=new Element('h2');nodes.set(id,heading);return heading;
  });
  const html=new Element('html');
  const key='independent_open_research',tabs=new Element('div'),supporting=new Element('section');
  const tab=new Element('button'),panel=new Element('section'),title=new Element('h3'),description=new Element('p');
  const supportingTab=new Element('button'),supportingTitle=new Element('h3');
  const categoryTable=new Element('table'),categoryHeader=new Element('tr'),categoryRow=new Element('tr');
  categoryTable.tHead={rows:[categoryHeader]};categoryTable.tBodies=[{rows:[categoryRow]}];
  categoryRow.querySelector=selector=>selector==='.model-name'?link:Element.prototype.querySelector.call(categoryRow,selector);
  tab.id='category-tab-'+key;panel.id='category-panel-'+key;
  nodes.set('category-panel-research',supporting);
  nodes.set('category-tab-research',supportingTab);
  nodes.set('category-ranking-'+key,categoryTable);
  nodes.set('independent-research-category-template',{content:{cloneNode:()=>({children:[tab,panel]})}});
  const scoreCells=['not-tested','insufficient-evidence','review-pending',null].map(state=>{
    const cell=new Element('span');
    if(state)cell.dataset.researchCategoryState=state;
    cell.textContent=state?'—':'0.00';return cell;
  });
  const selectors={'#category-leaderboards .category-tabs':tabs,
    '#category-panel-research h3':supportingTitle,
    ['#category-panel-'+key+' h3']:title,['#category-panel-'+key+' .panel-desc']:description};
  const document={documentElement:html,baseURI:'https://example.test/index.html?edition=1.3.0',
    getElementById:id=>nodes.get(id)||null,createElement:tag=>new Element(tag),querySelector:selector=>selectors[selector]??null,
    querySelectorAll:selector=>selector==='#ranking-body tr'?[body]:selector==='a[href]'?[link]:
      selector==='[data-research-category-state]'?scoreCells.filter(cell=>cell.dataset.researchCategoryState):[]};
  const research=scoreModeBoard(board);
  research.item_weights={taste:1,capacity:2};
  research.value_binding={policy_sha256:'a'.repeat(64),base_results_sha256:'b'.repeat(64),index_sha256:'c'.repeat(64)};
  for (const row of research.rows) {
    delete row.components.autonomy;
    delete row.criteria.autonomy;
    for (const view of Object.values(row.score_modes)) delete view.components.autonomy;
    row.coverage.components_planned=2;
    row.coverage.components_reviewed=row.coverage.reviewed*2;
  }
  strictCreditBoard(research);
  research.weight_frame={[key]:10};
  const data={benchmark_version:'1.3.0',research_preview:research,models:board.rows.map(r=>({id:r.id,label:r.label,theme:{ink:'#445b8c'}}))};
  nodes.set('category-leaderboards',new Element('section'));
  const location=new URL('https://example.test/index.html?edition=1.3.0&score=capability&profile-stage=first#assessment-guide');
  const context={document,location,URL,URLSearchParams,history:{replaceState(_a,_b,url){location.href=url}},addEventListener(){}};
  const source=readFileSync(new URL('../scripts/templates/research-preview.js',import.meta.url),'utf8');
  vm.runInNewContext('const MG='+JSON.stringify({d:data,state:{lang:'zh',score:'strict'}})+';\n'+source,context);
  assert.equal(html.attrs['data-independent-research-preview'],'');
  assert.ok(!nodes.has(banner.id),'a stale adoption banner is removed');
  assert.equal(table.tHead.rows.length,1);
  assert.equal(body.cells.length,8,'main table retains only original overall columns');
  assert.ok(body.cells.every(c=>!Object.hasOwn(c.dataset,'independentCell')));
  assert.equal(new URL(link.href).searchParams.get('edition'),'1.2.0');
  for(const heading of resourceHeadings)assert.match(heading.adjacent[0].textContent,/1\.2\.0/);
  assert.match(resourceHeadings[2].adjacent[0].textContent,/成绩、成本和耗时/);
  assert.equal(wrap.hidden,false); // fixture starts visible; controller must not force it on
  wrap.hidden=true;context.MGResearchPreview.decorate();assert.equal(wrap.hidden,true);
  assert.deepEqual(tabs.children,[tab]);
  assert.deepEqual(supporting.adjacent,[panel]);
  assert.ok(!nodes.has('independent-research-leaderboards'));
  assert.equal(description.textContent,'类内满分100 · 总榜权重10% · 单列检查通过数');
  assert.equal(categoryHeader.children[0].textContent,'检查通过数');
  assert.match(categoryRow.children[0].textContent,/C 4\/5/);
  assert.equal(supportingTab.textContent,'辅助研究');
  assert.equal(supportingTitle.textContent,'辅助研究排行榜');
  assert.deepEqual(scoreCells.map(cell=>cell.textContent),['','证据不足','待评','0.00']);
  assert.equal(scoreCells[0].attrs['aria-label'],'未测');
  assert.equal(location.searchParams.get('profile-stage'),'first');
  assert.equal(location.searchParams.get('score'),'capability');
  assert.equal(location.hash,'#assessment-guide');
  context.MGResearchPreview.decorate();
  assert.ok(!nodes.has(banner.id),'rendering never restores the adoption banner');
  assert.equal(table.tHead.rows.length,1,'rerender must not add project columns');
  assert.equal(tabs.children.length,1,'rerender keeps one fourth category tab');
  vm.runInContext("MG.state.lang = 'en'; MGResearchPreview.decorate();",context);
  for(const heading of resourceHeadings){
    assert.equal(heading.adjacent.length,1,'rerender keeps one visible resource scope per panel');
    assert.match(heading.adjacent[0].textContent,/1\.2\.0/);
  }
  assert.match(resourceHeadings[2].adjacent[0].textContent,/Scores, costs and timings/);
  assert.deepEqual(scoreCells.map(cell=>cell.textContent),['','Insufficient evidence','Review pending','0.00']);
  assert.equal(scoreCells[0].attrs['aria-label'],'Not tested');
  assert.equal(supportingTab.textContent,'Supporting research');
  assert.equal(supportingTitle.textContent,'Supporting research leaderboard');
  assert.equal(categoryHeader.children[0].textContent,'Checks passed');
  assert.equal(categoryRow.children.length,1,'re-render leaves one diagnostic column');
  vm.runInNewContext("MG.state.lang = 'zh'; MGResearchPreview.decorate();",context);
  assert.equal(supportingTitle.textContent,'辅助研究排行榜');
});
