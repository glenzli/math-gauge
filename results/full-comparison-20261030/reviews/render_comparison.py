"""Render actual shared-runner judgments; never execute a candidate or create a score."""
import json
from pathlib import Path
import sys

REPO = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO))
from math_gauge.review import compare_models

BASE = Path(__file__).resolve().parents[1]
RUNTIME = Path('/private/tmp/math-gauge-full-comparison-20261030/runtime')


def load(path):
    return json.loads(path.read_text())


def fraction(summary):
    if summary['complete']:
        return f"{summary['strict_passes']}/{summary['planned']}（{100*summary['strict_pass_rate']:.1f}%）"
    return f"待完成：{summary['resolved']}/{summary['planned']} 已定，{summary['strict_passes']} 通过"


def main():
    if not (RUNTIME / 'queue-final.json').exists():
        raise SystemExit('Queue is still active; live submissions are not final accounting.')
    freeze = load(RUNTIME / 'freeze.json')
    run_index = load(RUNTIME / 'model-runs.json')
    lean_path = BASE / 'reviews/lean-report-map.json'
    lean = load(lean_path) if lean_path.exists() else {}
    data = compare_models(freeze['cases'], run_index['model_runs'],
                          execution_receipts=run_index['execution_receipts'], lean_reports=lean)
    (BASE / 'comparison.json').write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n')
    labels = data['model_order']
    expected_labels = ['gpt-6.1-terra/max', 'gemini-3.8-flash-high/high']
    if labels != expected_labels:
        raise ValueError('Unexpected model identity or ordering for this declared comparison')
    names = dict(zip(expected_labels, ['Terra 6.1 Max', 'Gemini 3.8 Flash High']))
    lines = ['# 全习题集双模型比较', '',
             ('两模型均已完成全部 41 题的单次运行与审核。' if data['complete'] else '运行或审核仍未完成，当前不发布全题集通过率。'), '',
             '这是 AI 数学审核的暂定结果，供人工验收；题目和答卷均未标记为人工批准。纯文字题按完整论证评分，Lean 生成／修复题另须原样编译、公理检查和语义覆盖全部通过。', '',
             '| 模型 | 严格通过 | 已提交／计划 | 有效运行 | 已定／待定 |', '|---|---:|---:|---:|---:|']
    for label in labels:
        s = data['models'][label]['summary']
        count = s['mathematical_requests'] if s['mathematical_requests'] is not None else f"{s['known_mathematical_requests']} 已知，{s['unknown_request_counts']} 待核"
        lines.append(f"| {names[label]} | {fraction(s)} | {count}/{s['planned']} | {s['valid_executions']} | {s['resolved']}/{s['pending']} |")
    lines += ['', '## 分项结果', '', '| 任务 | Terra | Gemini |', '|---|---:|---:|']
    task_names = {'written': '数学论证', 'audit': 'Lean 对齐判定', 'generate': 'Lean 生成', 'repair': 'Lean 修复'}
    for kind, title in task_names.items():
        lines.append('| ' + title + ' | ' + ' | '.join(fraction(data['models'][label]['groups']['task_kind'][kind]) for label in labels) + ' |')
    lines += ['', '| 判定题子集 | Terra | Gemini |', '|---|---:|---:|']
    for value, title in [('aligned', '原 Lean 对齐（3题）'), ('misaligned', '原 Lean 失配（3题）')]:
        lines.append('| ' + title + ' | ' + ' | '.join(fraction(data['models'][label]['groups']['audit_expected'][value]) for label in labels) + ' |')
    lines += ['', '| 数学章节 | Terra | Gemini |', '|---|---:|---:|']
    sections = {'01-operators-and-dynamics': '算子、轨道与不动点', '02-analysis-and-recovery': '分析、观测与最优恢复', '03-algebra-and-compatible-lifting': '代数、商结构与相容提升', '04-topology-and-descent': '拓扑、下降与空间重构', '05-finite-covering': '有限集与定量覆盖', '06-fourier-and-regularity': 'Fourier 分析与正则性', '07-geometric-proof-mechanisms': '几何拼接与层化比较'}
    for section, title in sections.items():
        lines.append('| ' + title + ' | ' + ' | '.join(fraction(data['models'][label]['groups']['section'][section]) for label in labels) + ' |')
    lines += ['', '| 作者主目标 Lean 覆盖分层 | Terra | Gemini |', '|---|---:|---:|']
    coverage_labels = {'full-main-task': '完整覆盖（40题）', 'partial-main-task': '部分覆盖（P003，1题）'}
    for value in data['models'][labels[0]]['groups']['author_lean_coverage']:
        title = coverage_labels.get(value, value)
        lines.append('| ' + title + ' | ' + ' | '.join(fraction(data['models'][label]['groups']['author_lean_coverage'][value]) for label in labels) + ' |')
    pair = data['paired']
    lines += ['', '## 同题配对', '', f"已具备配对结果 {pair['comparable']}/41 题。双方都通过 {pair['counts']['both_pass']}；仅 Terra 通过 {pair['counts']['first_only']}；仅 Gemini 通过 {pair['counts']['second_only']}；双方都未严格通过 {pair['counts']['neither_pass']}。", '',
              '六组 Lean 母题各含两个版本，P002 与 F107/F108 另共享公开来源机制。这些题目并非相互独立的随机样本；本轮不作总体模型排名或显著性推断。完整母题配对、作者 Lean 覆盖子集和各类结果计数见 comparison.json。', '',
              '## 逐题答卷与审核', '', '| 题目 | Terra | Gemini |', '|---|---|---|']
    packets = {(r['model_label'], r['case_id']): r for r in load(BASE / 'reviews/packet-map.json')}
    outcomes = {'pass': '通过', 'fail': '未通过', 'partial': '部分完成', 'unresolved': '未决', 'candidate_lean_compile_error': '原代码编译失败', 'candidate_lean_axiom_rejected': '公理检查未通过', 'candidate_lean_format_error': '源码交付／提取待审', 'lean_infrastructure_error': 'Lean 环境故障'}
    row_lookup = {label: {r['case_id']: r for r in data['models'][label]['cases']} for label in labels}
    operational = {}
    unsupported_compilation_reports = []
    for (label, cid), packet in packets.items():
        pid = packet['packet_id']
        verdict_path = BASE / f'reviews/adjudication/{pid}.json'
        if not verdict_path.exists():
            verdict_path = BASE / f'reviews/primary/{pid}.json'
        if verdict_path.exists():
            verdict = load(verdict_path)
            if verdict.get('candidate_execution_claim_status') == 'definite-compilation-report-without-candidate-execution-evidence':
                unsupported_compilation_reports.append((label, cid))
            if verdict.get('operational_outcome') == 'terminal-filtered-no-answer':
                operational[(label, cid)] = verdict
    for item in freeze['cases']:
        cid = item['case_id']; cells = []
        for label in labels:
            row = row_lookup[label][cid]; packet = packets.get((label,cid))
            status = outcomes.get(row['outcome'], row['outcome'])
            if row['outcome'] == 'candidate_lean_format_error' and row['resolved']:
                status = '源码交付未通过（已复核）'
            if (label, cid) in operational:
                status = '过滤未作答'
            if packet:
                pid = packet['packet_id']; status += f" · [答卷](reviews/packets/{pid}/response.md)"
                if (BASE / f'reviews/primary/{pid}.json').exists():
                    status += f" · [初审](reviews/primary/{pid}.json)"
                if (BASE / f'reviews/adjudication/{pid}.json').exists():
                    status += f" · [复核](reviews/adjudication/{pid}.json)"
                if (BASE / f'answers/{pid}/lean/report.json').exists():
                    status += f" · [Lean](answers/{pid}/lean/report.json)"
            cells.append(status)
        lines.append('| ' + cid + ' | ' + ' | '.join(cells) + ' |')
    lines += ['', '## 未作答与评分边界', '',
              '严格通过率使用原定每模型 41 题的完整分母，包含服务端过滤未作答。过滤通知不属于错误数学证明，数学审核轴记为 unknown；本轮没有为它重试或改写提示。', '',
              '| 模型 | 过滤未作答 | 返回数学答卷 | 有数学答卷中的通过数 |', '|---|---:|---:|---:|']
    for label in labels:
        count = sum(key[0] == label for key in operational)
        summary = data['models'][label]['summary']
        answered = summary['valid_executions'] - count
        lines.append(f"| {names[label]} | {count} | {answered} | {summary['strict_passes']}/{answered} |")
    if unsupported_compilation_reports:
        lines += ['', '编译证据表述另记：' + '；'.join(names[label] + ' ' + cid for label, cid in unsupported_compilation_reports) + ' 给出了确定的编译／公理报告文字，但候选没有实际 Lean 执行收据。这些文字不计作候选编译证据；其对齐审计的数学完成情况依题面单独判断。']
    lines += ['', '上表的答卷子集仅作补充，不能替代全题通过率。通过表示所有必需义务已有有效证明；少数通过答卷仍有不影响主证明的附加错误，详见逐题复核。', '',
              'R005 原题未单独明示竞争函数能否取负无穷值；本轮保留原题及原分数，并在复核中记录该边界。澄清后的新版本将以独立两模型单题补测记录，不替换本轮答卷。', '',
              '## 运行与证据边界', '',
              '- 四组题集和评分材料在发送前冻结；两模型逐题消息字节相同，每题独立会话、无答题工具或现场 Lean 反馈，先 Terra 后 Gemini，每模型并发 2 题。',
              '- 请求型号为 `gpt-6.1-terra/max` 和 `gemini-3.8-flash-high/high`。当前 CLI 没有独立回显 Terra 型号／档位和 Gemini 档位；Gemini 回显了型号。请求配置、观测字段和局限分别保留。',
              '- 40 题具有完整作者主任务 Lean 证据；P003 的完整数学参考依赖精确引用的已发表几何结果，作者 Lean 为部分覆盖。作者编译证据不替代候选答案正确性。',
              '- 评审包不另附模型标签，但阶段时序及少数原始答卷中的文件路径可能暴露模型，因此不称完全盲审；原始答卷未为匿名而改写。数学失败、部分完成、争议和格式提取问题保留独立复核；没有改候选代码后回填原分数。',
              '- [事前方案](PLAN.md) · [题集质量门槛](qualification/README.md) · [完整统计](comparison.json) · [习题总目录](../../exercises/README.md)。', '']
    (BASE / 'comparison.md').write_text('\n'.join(lines))
    print(json.dumps({'complete':data['complete'], 'summaries':{label:data['models'][label]['summary'] for label in labels}},ensure_ascii=False))


if __name__ == '__main__':
    main()
