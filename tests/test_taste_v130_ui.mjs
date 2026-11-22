// Aggregate-only UI fixture contracts; no private task or mathematical review.
import test from 'node:test';
import assert from 'node:assert/strict';
import { createRequire } from 'node:module';
const require = createRequire(import.meta.url);
const ui = require('../scripts/templates/research-preview.js');
require('./fixtures/research-preview-v130.js');
const fixture = globalThis.MGResearchPreviewData;

test('all three raw scores appear on each row, with explicit names on narrow layouts', () => {
  const html = ui.render(fixture);
  assert.match(html, /colspan="3" scope="colgroup">开放研究/);
  const rows = html.match(/<tr data-model=.*?<\/tr>/g);
  assert.equal(rows.length, fixture.rows.length);
  for (const row of rows) {
    for (const name of ['研究自主', '数学品味', '研究能力']) assert.ok(row.includes(name));
    assert.equal((row.match(/class="component"/g) || []).length, 3);
    assert.ok(row.includes('1 题'));
  }
});

test('zero, untested, unreviewed and insufficient evidence are distinct visible values', () => {
  const html = ui.render(fixture);
  for (const value of ['>0.0<', 'aria-label="未测"', '>待评<', '>证据不足<']) assert.ok(html.includes(value));
  assert.ok(html.includes('整题 SMC 未知'));
  assert.ok(html.includes('整题 SMC 0'));
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

test('the existing index table is enhanced using the original lexical MG controller', async () => {
  const { readFileSync } = await import('node:fs');
  const vm = await import('node:vm');
  const page = JSON.parse(readFileSync(new URL('../site/data/editions/1.3.0/index.json',import.meta.url),'utf8'));
  const board = structuredClone(page.data.research_preview); board.rows = board.rows.slice(0,1);
  const nodes = new Map();
  class Element {
    constructor(tag) {this.tagName=tag.toUpperCase();this.dataset={};this.children=[];this.cells=this.children;this.attrs={};this.hidden=false;this.textContent='';}
    append(node){this.children.push(node);node.parent=this;if(node.id)nodes.set(node.id,node);}
    prepend(node){this.children.unshift(node);node.parent=this;if(node.id)nodes.set(node.id,node);}
    setAttribute(key,val){this.attrs[key]=val;}
    insertBefore(node,last){this.children.splice(this.children.indexOf(last),0,node);node.parent=this;}
    remove(){if(this.parent)this.parent.children.splice(this.parent.children.indexOf(this),1);}
    querySelectorAll(selector){
      if(selector==='[data-independent-cell]')return this.cells.filter(c=>Object.hasOwn(c.dataset,'independentCell'));
      const key=selector==='[data-independent-tab]'?'independentTab':selector==='[data-independent-view]'?'independentView':null;
      if(!key)return [];
      this.cache??={};if(this.cache[selector]?.html===this.innerHTML)return this.cache[selector].buttons;
      const attr=key==='independentTab'?'data-independent-tab':'data-independent-view';
      const buttons=[...String(this.innerHTML).matchAll(new RegExp(attr+'="([^"]+)"','g'))].map(m=>({dataset:{[key]:m[1]}}));
      this.cache[selector]={html:this.innerHTML,buttons};return buttons;
    }
    insertAdjacentElement(_,node){nodes.set(node.id,node);}
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
  const html=new Element('html');
  const document={documentElement:html,baseURI:'https://example.test/index.html?edition=1.3.0',
    getElementById:id=>nodes.get(id)||null,createElement:tag=>new Element(tag),querySelector:()=>null,
    querySelectorAll:selector=>selector==='#ranking-body tr'?[body]:selector==='a[href]'?[link]:[]};
  const data={benchmark_version:'1.3.0',research_preview:board,models:board.rows.map(r=>({id:r.id,label:r.label,theme:{ink:'#445b8c'}}))};
  nodes.set('category-leaderboards',new Element('section'));
  const location=new URL('https://example.test/index.html?edition=1.3.0');
  const context={document,location,URL,URLSearchParams,history:{replaceState(_a,_b,url){location.href=url}},addEventListener(){}};
  const source=readFileSync(new URL('../scripts/templates/research-preview.js',import.meta.url),'utf8');
  vm.runInNewContext('const MG='+JSON.stringify({d:data,state:{lang:'zh',score:'strict'}})+';\n'+source,context);
  assert.equal(html.attrs['data-independent-research-preview'],'');
  assert.equal(table.tHead.rows.length,1);
  assert.equal(body.cells.length,8,'main table retains only original overall columns');
  assert.ok(body.cells.every(c=>!Object.hasOwn(c.dataset,'independentCell')));
  assert.equal(new URL(link.href).searchParams.get('edition'),'1.2.0');
  assert.equal(wrap.hidden,false); // fixture starts visible; controller must not force it on
  wrap.hidden=true;context.MGResearchPreview.decorate();assert.equal(wrap.hidden,true);
  const independent=nodes.get('independent-research-leaderboards');
  assert.ok(independent.innerHTML.includes('role="tablist"'));
  independent.querySelectorAll('[data-independent-tab]').find(b=>b.dataset.independentTab==='capacity').onclick();
  assert.equal(location.searchParams.get('independent-tab'),'capacity');
  independent.querySelectorAll('[data-independent-view]').find(b=>b.dataset.independentView==='table').onclick();
  assert.equal(location.searchParams.get('view-independent'),'table');
  assert.ok(independent.innerHTML.includes('class="score-figure" hidden'));
  assert.ok(!independent.innerHTML.includes('<td class="numeric">0</td>'));
  context.MGResearchPreview.decorate();
  assert.equal(table.tHead.rows.length,1,'rerender must not add project columns');
});
