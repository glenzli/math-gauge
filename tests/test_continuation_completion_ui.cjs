/* Saved continuation statistics and score-column mapping; no score arithmetic. */
const {test}=require('node:test');
const assert=require('node:assert/strict');
const fs=require('node:fs');
const path=require('node:path');
const vm=require('node:vm');
const source=fs.readFileSync(path.join(__dirname,'../scripts/templates/edition-notes.js'),'utf8');

function mount(models,{lang='zh',partial=[],observations=false}={}){
 const ids=new Map();
 class Element{
  constructor(tag,text='',className=''){this.tagName=tag.toUpperCase();this.textContent=text??'';this.className=className;this.children=[];this.dataset={};if(this.tagName==='DETAILS')this.open=false;}
  set id(value){this._id=value;ids.set(value,this)}get id(){return this._id}
  setAttribute(name,value){(this.attributes??={})[name]=value}
  append(...children){this.children.push(...children)}
  replaceChildren(...children){this.children=children}
  insertBefore(child){this.append(child)}
  querySelector(){return null}
  createTHead(){const head=new Element('thead');this.append(head);return head}
  createTBody(){const body=new Element('tbody');this.append(body);return body}
  insertRow(){const row=new Element('tr');this.append(row);return row}
  insertCell(){const cell=new Element('td');this.append(cell);return cell}
 }
 const main=new Element('main'),state={lang},callbacks=[];
 const diagnostics=[new Element('section'),new Element('section')];
 let observation,meta,link;
 if(observations){
  observation=new Element('details');observation.id='research-initiative';observation.hidden=true;
  meta=new Element('p');link=new Element('a');link.href='https://example.test/site/models/pending/index.html?edition=1.2.0';
  observation.querySelector=selector=>selector==='.initiative-meta'?meta:null;
  observation.querySelectorAll=()=>[link];
 }
 const document={querySelector:selector=>selector==='main'?main:null,
  querySelectorAll:selector=>selector==='#content-rates'?[diagnostics[0]]:selector==='#mathematical-profile'?[diagnostics[1]]:selector==='#content-rates,#mathematical-profile'?diagnostics:[],getElementById:id=>ids.get(id)};
 const location=new URL('https://example.test/site/index.html');
 const node=(tag,text,cls)=>new Element(tag,text,cls);
 const d={benchmark_version:'1.2.0',models,partial_models:partial};
 const MG={d,state,node,f:value=>value.toFixed(2),compareModelOrder:(a,b)=>a.id.localeCompare(b.id),result:()=>{throw new Error('Saved table values must be used')}};
 vm.runInNewContext(source,{MG,document,window:{addEventListener:(_,callback)=>callbacks.push(callback)},location,URL});
 const findAll=(element,predicate)=>[...(predicate(element)?[element]:[]),...element.children.flatMap(child=>findAll(child,predicate))];
 const table=id=>findAll(ids.get(id),element=>element.tagName==='TABLE')[0];
 const content=cell=>cell.textContent||cell.children.map(content).join('');
 const rows=id=>table(id).children[1].children.map(row=>row.children.map(content));
 const headers=id=>table(id).children[0].children[0].children.map(content);
 const fullRates=id=>findAll(ids.get(id),element=>element.className==='revision-full-rate').map(content);
 return {rows,headers,state,observation,meta,link,diagnostics,fullRates,element:id=>ids.get(id),update:()=>callbacks.forEach(callback=>callback())};
}
const summary=(selected,full)=>({selected,reviewed:selected,delivery_failed:selected-full,pending:0,settled:true,
 full_count:{lower:full,upper:full,exact:full},full_rate:{lower:full/selected,upper:full/selected,exact:full/selected}});
const model=(id,completion)=>({id,label:id,neutral_revision_completion:completion,
 neutral_revision_delta:{strict:2,partial:-1,capability:3}});

test('continuation table consumes the saved full rate and maps SMC/RMC/MC deltas',()=>{
 const f=mount([model('Full',summary(7,7)),model('Failed delivery',summary(9,8))]);
 assert.deepEqual(f.rows('revision-score-change'),[
  ['Full','7','100% (7/7)','+2.00','-1.00','+3.00'],
  ['Failed delivery','9','88.9% (8/9)','+2.00','-1.00','+3.00']]);
 f.state.lang='en';f.update();
 assert.deepEqual(f.headers('revision-score-change'),['Model','Continued tasks','Full-score rate','ΔSMC','ΔRMC','ΔMC']);
 assert.equal(f.rows('revision-score-change')[1][2],'88.9% (8/9)');
});

test('missing or unsettled summaries and an empty denominator do not invent a rate',()=>{
 const pending=summary(9,8);pending.settled=false;
 const empty={...summary(1,0),selected:0,full_rate:{lower:null,upper:null,exact:null}};
 const f=mount([model('Missing'),model('Pending',pending),model('Empty',empty)]);
 assert.deepEqual(f.rows('revision-score-change').map(row=>row.slice(1,3)),[['0','—'],['—','—'],['—','—']]);
});

test('continuation ranking prioritizes rate, fewer selected tasks, then SMC/RMC/MC gains',()=>{
 const entry=(id,selected,full,strict,partial,capability)=>({...model(id,summary(selected,full)),neutral_revision_delta:{strict,partial,capability}});
 const pending=summary(1,1);pending.settled=false;
 const f=mount([
  entry('More tasks',7,7,99,99,99),entry('RMC tie-break',6,6,2,2,0),
  entry('Lower rate',9,8,99,99,99),entry('MC tie-break',6,6,2,2,1),
  entry('Lower RMC',6,6,2,1,99),entry('Higher SMC',6,6,3,-99,-99),
  entry('Same rate more tasks',20,18,99,99,99),entry('Same rate fewer tasks',10,9,-99,-99,-99),
  entry('Known zero',2,0,0,0,0),model('Unsettled',pending)
 ]);
 assert.deepEqual(f.rows('revision-score-change').map(row=>row[0]),[
  'Higher SMC','MC tie-break','RMC tie-break','Lower RMC','More tasks',
  'Same rate fewer tasks','Same rate more tasks','Lower rate','Known zero','Unsettled'
 ]);
});

test('gains start collapsed, highlight only confirmed full rates, and retain expansion across updates',()=>{
 const pending=summary(7,7);pending.settled=false;
 const f=mount([model('Full',summary(7,7)),model('Partial',summary(9,8)),model('Pending',pending)]);
 const disclosure=f.element('revision-score-change');
 assert.equal(disclosure.tagName,'DETAILS');
 assert.equal(disclosure.open,false);
 assert.deepEqual(f.fullRates('revision-score-change'),['100% (7/7)']);
 disclosure.open=true;f.state.lang='en';f.update();
 assert.equal(f.element('revision-score-change'),disclosure);
 assert.equal(disclosure.open,true);
 assert.deepEqual(f.fullRates('revision-score-change'),['100% (7/7)']);
});

test('partial evidence keeps its scores and clickable model/archive links in SMC order',()=>{
 const f=mount([],{lang:'en',partial:[{id:'partial',label:'Partial model',score_values:{strict:1,partial:2,capability:3},answer_delivery:{active_final:21,forced_content:5,planned:39}}]});
 assert.deepEqual(f.headers('partial-tests'),['Model','SMC','RMC','MC','Normal / forced / initial','Archive']);
 assert.deepEqual(f.rows('partial-tests'),[['Partial model','1.00','2.00','3.00','21 / 5 / 39','Details →']]);
});

test('A1 observations remain visible in the revision edition and link to first-answer evidence',()=>{
 const f=mount([],{observations:true});
 assert.equal(f.observation.hidden,false);
 assert.equal(f.diagnostics[0].hidden,true,'first-answer content rates stay hidden');
 assert.notEqual(f.diagnostics[1].hidden,true,'profiles retain their independent stage control');
 assert.equal(new URL(f.link.href).searchParams.get('edition'),'1.1.0');
 assert.equal(f.link.attributes['data-fixed-edition'],'1.1.0');
 assert.match(f.meta.textContent,/仅首答A1，不含中性续答/);
 f.state.lang='en';f.update();
 assert.equal(f.observation.hidden,false);
 assert.equal(new URL(f.link.href).searchParams.get('lang'),'en');
 assert.match(f.meta.textContent,/first answers only; neutral continuations excluded/);
});
