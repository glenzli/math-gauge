#!/usr/bin/env python3
"""Render the current, source-bound user-selected result records only."""
import argparse
import hashlib
import html
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from math_gauge.records import validate_record


def build_data(source_root=ROOT):
    root = Path(source_root).resolve()
    policy = json.loads((root / "protocol/scoring-policy.json").read_bytes())
    models, sources = [], []
    for model, label in (("terra-6.1-max", "Terra 6.1 Max"),
                         ("deepseek-v4.1-flash-1017", "DeepSeek v4.1 Flash 1017"),
                         ("gemini-3.8-flash-high", "Gemini 3.8 Flash High")):
        folder = root / "results/v0.6.0" / model / "20261105"
        validate_record(folder)
        record = json.loads((folder / "record.json").read_bytes())
        public = json.loads((folder / "result.json").read_bytes())
        combined = json.loads((folder / "combined-aggregate.json").read_bytes())
        if (public.get("benchmark_version") != "0.6.0"
                or combined.get("benchmark_version") != "0.6.0"
                or public.get("human_review") != "pending"
                or combined.get("formal_comparison_eligible") is not False):
            raise ValueError("Current display identity or review status changed")
        models.append({"id": model, "label": label, "public": public,
                       "combined": combined, "trajectory": record["trajectory"],
                       "source_record": str((folder / "record.json").relative_to(root))})
        for name in ["result.json", "combined-aggregate.json", "record.json"]:
            path = folder / name
            sources.append({"path": str(path.relative_to(root)),
                            "sha256": hashlib.sha256(path.read_bytes()).hexdigest()})
    return {"schema": "math-gauge.current-results-display/v1", "benchmark_version": "0.6.0",
            "human_review": "pending", "formal_comparison_eligible": False,
            "models": models, "policy": policy, "sources": sources}


def render(data):
    # JSON embedded as data only; no remote resources or score calculation.
    payload = json.dumps(data, ensure_ascii=False).replace("<", "\\u003c").replace("&", "\\u0026")
    cards = "".join(f'<article class="card"><div class="eyebrow">{html.escape(m["label"])}</div>'
                    f'<div class="score" id="score-{m["id"]}"></div><p id="scope-{m["id"]}"></p>'
                    f'<a href="../{html.escape(m["source_record"])}">查看完整记录 ↗</a></article>'
                    for m in data["models"])
    return '''<!doctype html>
<html lang="zh-CN"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Math Gauge · 当前结果</title>
<style>
:root{color-scheme:light;font-family:Inter,-apple-system,BlinkMacSystemFont,"PingFang SC",sans-serif;color:#193247;background:#f4f7f7}*{box-sizing:border-box}body{margin:0;line-height:1.65}main{max-width:1080px;margin:auto;padding:52px 24px 64px}.eyebrow{font-size:13px;letter-spacing:.06em;color:#55717c}h1{font-size:clamp(38px,7vw,68px);line-height:1.05;letter-spacing:-.055em;margin:14px 0 22px}h2{font-size:22px;letter-spacing:-.02em;margin:0 0 16px}p{color:#526773;max-width:760px}a{color:#087c83;text-decoration:none}a:hover{text-decoration:underline}.badge{display:inline-block;background:#e0eeec;color:#276562;border-radius:100px;padding:5px 12px;font-size:12px}.bar{display:flex;gap:8px;flex-wrap:wrap;margin:30px 0 20px}button{border:1px solid #c9d9db;background:#fff;color:#24404b;border-radius:100px;padding:10px 20px;font:inherit;cursor:pointer}button[aria-pressed=true]{background:#193b4a;color:#fff;border-color:#193b4a}.cards{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:18px}.card,section{background:#fff;border:1px solid #dce6e6;border-radius:20px;padding:26px}.score{font-size:64px;font-weight:650;letter-spacing:-.05em;font-variant-numeric:tabular-nums}.card p{margin:0 0 18px;font-size:14px}section{margin-top:24px}.scroll{overflow:auto}table{border-collapse:collapse;width:100%;white-space:nowrap;text-align:left;font-size:14px}th,td{padding:12px 14px;border-bottom:1px solid #e5ecec}th{color:#637a83;font-weight:500}th:first-child,td:first-child{padding-left:0}.note{font-size:13px;color:#6a7f87}footer{margin-top:24px;font-size:13px;color:#6a7f87}@media(max-width:640px){main{padding:30px 16px}.cards{grid-template-columns:1fr}.card,section{padding:20px}.score{font-size:56px}}
</style><main><div class="eyebrow">MATH GAUGE / BENCHMARK 0.6.0</div>
<h1>数学工作，<br>能否可靠完成。</h1>
<p>当前固定留档覆盖书面论证、Lean语义审计、完整形式化与答卷审阅，并保留模型自我判断、实际修复和最后交付。</p>
<span class="badge">开发分析 · AI审核 · 人审待定</span>
<div class="bar"><button data-mode="public" aria-pressed="true">公开部分</button><button data-mode="combined" aria-pressed="false">含私有探索</button></div>
<div class="cards">''' + cards + '''</div>
<section><h2>能力方向</h2><p class="note" id="coverage"></p><div class="scroll"><table id="capabilities"></table></div></section>
<section><h2>四档 Lean：核实通过数</h2><div class="scroll"><table id="lean"></table></div><p class="note">四题统一按归档工程核验正确性与语义对齐。8/20/40项先在CH2家族内平均，再与92项CH3家族等权平均。<a href="../docs/formalization-audit.md">查看工程审核 ↗</a></p></section>
<section><h2>三轮自查后的实际状态</h2><div class="scroll"><table id="trajectory"></table></div><p class="note">自称完成、审核完成与稳定保持分别记录。固定采用最后规定轮次，保留未完成、误报和原始执行差异。</p></section>
<section><h2>计分与来源</h2><p id="weights" class="note"></p><p class="note">公私共用版本与共享评分器，采用评分方法0.4.0。部分等价测项继承旧benchmark记录。公开只提供私有聚合。</p><div id="downloads"></div></section>
<footer>三模型的原始档案、完整性证据与评分规则保存在项目中。DeepSeek两道输出预算耗尽且没有交付的题按0分计入固定分母。本次整理没有新增候选调用。</footer>
<script type="application/json" id="data">''' + payload + '''</script>
<script>
const d=JSON.parse(document.getElementById('data').textContent);let mode='public';
const el=id=>document.getElementById(id),f=v=>v==null?'未决':v.toFixed(2),titles={'proofs':'书面论证','lean-audit':'历史语义审计','lean-formalization':'大Lean形式化','answer-review':'答卷审阅','exploration':'私有探索'};
function table(id,headers,rows){const t=el(id);t.replaceChildren();const h=t.createTHead().insertRow();headers.forEach(s=>{const c=document.createElement('th');c.textContent=s;h.append(c)});const b=t.createTBody();rows.forEach(row=>{const r=b.insertRow();row.forEach(s=>{const c=r.insertCell();c.textContent=s})})}
function update(){d.models.forEach(m=>{const r=m[mode];el('score-'+m.id).textContent=f(r.metrics.overall.exact);el('scope-'+m.id).textContent=mode==='public'?'公开总分 / 100':'含私有探索总分 / 100'});const first=d.models[0][mode],c=first.coverage;el('coverage').textContent=`${c.papers_planned}份任务 · ${c.parent_families}个数学家族 · ${c.slots_planned}条标准记录`;
table('capabilities',['方向','能力内部权重',...d.models.map(m=>m.label)],first.profile.components.map(x=>[titles[x.id]||x.id,x.weight+'%',...d.models.map(m=>f(m[mode].metrics[x.id]?.exact))]));
const states={verified_complete:'核实全部完成',incomplete_stable:'仍不完整，完成数未变',incomplete_changed:'仍不完整，有实际进展',regressed:'发生回退，仍不完整',interrupted:'轮次未完成',unresolved:'审核未决'};const ids=['LCH01','LCH02','HCH02','MG-C003'];table('lean',['任务',...d.models.map(m=>m.label)],ids.map(id=>[id,...d.models.map(m=>{const x=m.public.lean_formalization_breakdown.cases.find(x=>x.case_id===id);return `${x.complete_count}/${x.total}`} )]));
table('trajectory',['记录',...d.models.map(m=>m.label)],[['最后一轮核实通过',...d.models.map(m=>`${m.trajectory.last_complete_count}/${m.trajectory.total}`)],['首次核实全部完成',...d.models.map(m=>m.trajectory.first_verified_complete_round==null?'尚未达到':'第'+m.trajectory.first_verified_complete_round+'轮')],['核实误报完整',...d.models.map(m=>m.trajectory.false_complete_claim_rounds.length+'轮')],['最后状态',...d.models.map(m=>states[m.trajectory.state]||'审核未决')]]);
const w=d.policy.overall_weights;el('weights').textContent=`能力${w.core}% · 独立复答${w.repeat}% · 中性自查${w.neutral}%（书面与Lean为1:2）· 立场压力${w.stance}%`;
el('downloads').replaceChildren(...d.models.map(m=>{const a=document.createElement('a');a.href='downloads/'+m.id+'-'+mode+'.json';a.textContent=m.label+' 机器结果 ↓';a.style.marginRight='20px';return a}));document.querySelectorAll('[data-mode]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.mode===mode)))}
document.querySelectorAll('[data-mode]').forEach(b=>b.onclick=()=>{mode=b.dataset.mode;update()});update();
</script></main></html>'''


def write_site(destination, *, source_root=ROOT):
    dest = Path(destination)
    data = build_data(source_root)
    dest.mkdir(parents=True, exist_ok=True)
    (dest / "index.html").write_text(render(data), encoding="utf-8")
    (dest / "data.json").write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n")
    (dest / "downloads").mkdir(exist_ok=True)
    for model in data["models"]:
        for scope in ["public", "combined"]:
            (dest / "downloads" / (model["id"] + "-" + scope + ".json")).write_text(
                json.dumps(model[scope], ensure_ascii=False, indent=2) + "\n")
    return data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=ROOT / "site")
    args = parser.parse_args()
    data = write_site(args.out)
    print(json.dumps({"status": "passed", "benchmark_version": data["benchmark_version"],
                      "models": len(data["models"]), "candidate_calls": 0}))


if __name__ == "__main__":
    main()
