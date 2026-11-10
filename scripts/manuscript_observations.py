#!/usr/bin/env python3
"""Check or project descriptive unrequested-result observations. No model calls."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from math_gauge.manuscript_surplus import (
    ROOT_PATH, REVIEW_ROOT_PATH, check_pair, descriptor, public_projection, read_source,
    observation_result, source_context, validate_observation_policy, validate_reuse_binding, validate_sources,
)
from math_gauge.scoring import summarize_manuscript_observations


def serialized(value):
    return json.dumps(value, ensure_ascii=False, indent=2) + '\n'


def private_report(review, result):
    rows = ['# 主动额外成果 · 观察记录0.1.0', '',
            (f"模型：{review['model_id']} · 当前档：{result['record_id']} · 原审核档：{review['record_id']}"
             if result.get('reuse_binding') else f"模型：{review['model_id']} · 原档：{review['record_id']}"), '',
            '记录未受要求时主动交付、经核实的额外成果组；不表示研究能力，数量更多未必更好。', '',
            f"已核实额外成果组：{result['counts']['confirmed_groups']} · 已审手稿：{result['coverage']['reviewed']}/5", '',
            '未测／未决时全部答卷的总组数未知，不设满分、百分比或有限上限。', '',
            '保留的原数学审核按源散列引用，不改写其中的数学判定、摘录和来源；当前只读取成果组，原百分比视图已退出。', '']
    for case in review['cases']:
        rows += [f"## {case['case_id']} · {case['status']}", '', case['scope_audit'], '',
                 f"原任务完成情况：{json.dumps(case['original_task'], ensure_ascii=False)}", '']
        for c in case['candidates']:
            rows += [f"### {c['id']} · {c['title']} · {c['decision']}", '']
            for key, label in [('statement', '陈述'), ('scope_delta', '范围增量'),
                               ('proof_review', '数学核验'), ('nontrivial_step', '实质步骤'),
                               ('value_rationale', '价值'), ('reason', '结论理由')]:
                rows += [f'**{label}：** {c[key]}', '']
            for cite in c['citations']:
                source = cite['source']
                rows += [f"原答：`{source['path']}`，SHA256 `{source['sha256']}`，"
                         f"UTF-8 bytes [{cite['start_byte']}, {cite['end_byte']})。", '']
    return '\n'.join(rows)


def summary_report(summaries):
    from scripts.render_results_site import MODEL_LABELS
    rows = []
    for item in sorted(summaries, key=lambda x: (-x['counts']['confirmed_groups'], x['model'])):
        count, cov = item['counts'], item['coverage']
        marker = '*' if count['total_groups'] is None else ''
        rows.append(f"| {MODEL_LABELS.get(item['model'], 'Dot Underlying')} | {count['confirmed_groups']}{marker} | {cov['reviewed']}/5 |")
    return '''# 主动额外成果 · 观察记录

[数学研究分榜内展开](../site/index.html?category=research#research-initiative) · [观察规则](../protocol/manuscript-observations.md) · [记录索引](../results/manuscript-observations/v0.1.0/observations.json)

这里记录模型在原任务未要求的情况下，主动提出并实际交付了多少经核实的额外成果组。仅覆盖五道手稿题，复用规则选定A1；没有补跑，没有研究邀请，没有跨尝试拼接。

它描述这批答卷的主动探索行为，不表示研究能力，也不预设数量越多越好。原题完成质量、可靠性以及是否适合主动扩展范围须分别判断。没有满分、百分比、题目产出率或有限上限，不是独立benchmark，也不进入任何主分或两率。

| 模型 | 已核实额外成果组 | 已审手稿 |
|---|---:|---:|
''' + '\n'.join(rows) + '''

* 尚未测完。所列为已核实组数，全部答卷的总组数未知；不按已审覆盖放大，不推算剩余题目可能产生多少组。排列只便于浏览，不列优劣名次。0表示这批已审原答中没有核实到符合门槛的成果组，不表示能力为零。

每个成果组须正确、原题未要求且非简单重复。价值取决于具体研究本体与用途，不设统一高价值门槛。正常纠错、补必要证明、原题要求的自选扩展、直接推论和等价改写不计；一个定理及必要引理、直接推论或在原答/稿件中的重复只计一组。同题可有多组，直接合计数量。

逐项数学核验与原文绑定保持原字节。公开手稿MG-MCP003的接受/排除理由可在研究分榜的折叠观察栏查看；四道私有手稿的数学内容、标识和逐题分配留私库，公开只列合并组数、覆盖和不透明散列。原任务的错误和扣分保留，额外成果不能抵销错误。

审核方式见[统一审核说明](review-process.md)。这里核查相对给定材料和必需目标的额外成果，不认定文献首创、盲审或事前预注册。已核实组数不保证未来主动性，也不能据此将某模型认定为更好的研究者。

当前观察记录位于`results/manuscript-observations/v0.1.0/<model>/<record-id>/observation.json`。私库另留可读报告，并通过描述符引用不变的原数学审核、共同边界、原答和主成绩。旧MRS百分比派生结果和独立页面退出当前工作树。

校验：`python3 scripts/manuscript_observations.py --private-root ../math-gauge-private`。加`--write`仅从已保留数学审核重建观察记录，不调用模型。组数汇总仍由共享`scoring.py`负责，显示层不重新计数。
'''


def reuse_sources(private_root, paths):
    """Explicit registrations persist privately; every read rechecks both contexts."""
    paths = [Path(path) if Path(path).is_absolute() else private_root / path for path in paths]
    index_path = private_root / ROOT_PATH / 'observations.json'
    if index_path.is_file():
        index = json.loads(index_path.read_bytes())
        for row in index['models']:
            if row.get('reuse_binding') is not None:
                read_source(private_root, row['reuse_binding'])
                paths.append(private_root / row['reuse_binding']['path'])
    return [descriptor(path, private_root) for path in sorted(set(paths))]


def run(public_root, private_root, *, write=False, reuse_bindings=()):
    public_root, private_root = Path(public_root).resolve(), Path(private_root).resolve()
    policy_path = public_root / 'protocol/manuscript-observations-policy.json'
    policy_source = descriptor(policy_path, public_root)
    policy = validate_observation_policy(read_source(public_root, policy_source))
    private_policy_path = Path('verification/manuscript-observations/v0.1.0/policy.json')
    policy_raw = policy_path.read_bytes()
    private_policy = {'path': private_policy_path.as_posix(), 'bytes': len(policy_raw),
                      'sha256': hashlib.sha256(policy_raw).hexdigest()}
    rebound = list((private_root / REVIEW_ROOT_PATH).glob('*/*/current-review.json'))
    if rebound:
        edition = json.loads((public_root/'benchmark.json').read_bytes())
        selected = dict(edition['selected_result_record_ids'])
        native = public_root/'results/v0.6.0/dot-underlying-model-20261108/20261108/native-observation.json'
        if native.is_file():
            selected['dot-underlying-model-20261108'] = '20261108'
        reviews = []
        for model,record_id in selected.items():
            folder = private_root/REVIEW_ROOT_PATH/model/record_id
            reviews.append(folder/('current-review.json' if (folder/'current-review.json').is_file() else 'review.json'))
    else:
        reviews = sorted((private_root / REVIEW_ROOT_PATH).glob('*/*/review.json'))
    if not reviews:
        raise ValueError('No retained manuscript result reviews')
    outputs = [(private_root / private_policy_path, policy_raw)]
    public_rows, private_rows, summaries = [], [], []
    reuses = {}
    for item in ([] if rebound else reuse_sources(private_root, reuse_bindings)):
        binding = validate_reuse_binding(read_source(private_root, item), public_root, private_root)
        key = (binding['model_id'], binding['source_review_record_id'])
        if key in reuses:
            raise ValueError('Duplicate or conflicting manuscript observation reuse registration')
        reuses[key] = (binding, item)
    consumed = set()
    for path in reviews:
        review = json.loads(path.read_bytes())
        model_id, record_id = review['model_id'], review['record_id']
        expected_name = 'current-review.json' if review.get('metadata_rebind') else 'review.json'
        if path != private_root / REVIEW_ROOT_PATH / model_id / record_id / expected_name:
            raise ValueError('Review identity differs from source path')
        source_identity = model_id, record_id
        binding, binding_source = reuses.get(source_identity, (None, None))
        context = binding['source_context'] if binding else source_context(public_root, private_root, model_id, record_id)
        baseline = read_source(private_root, review['baseline'])
        source_policy = read_source(private_root, review['policy'])
        validate_sources(review, private_root, context, baseline, source_policy)
        result = summarize_manuscript_observations(review, source_policy, policy)
        result = observation_result(result, binding, binding_source)
        if binding:
            consumed.add(source_identity)
            context, record_id = binding['target_context'], binding['record_id']
        source_review = descriptor(path, private_root)
        private = {**result, 'source_review': source_review, 'policy': private_policy}
        public = public_projection(review, result, policy, public_record=context['public_record'],
            policy_source=policy_source, private_review_sha256=source_review['sha256'],
            private_baseline_sha256=review['baseline']['sha256'])
        relative = ROOT_PATH / model_id / record_id
        for root, value in ((private_root, private), (public_root, public)):
            target, raw = root / relative / 'observation.json', serialized(value).encode()
            outputs.append((target, raw))
            if root == public_root:
                item = {'path': target.relative_to(root).as_posix(), 'bytes': len(raw),
                        'sha256': hashlib.sha256(raw).hexdigest()}
                public_rows.append({'model_id': model_id, 'record_id': record_id, 'observation': item})
        private_rows.append({'model_id': model_id, 'record_id': record_id, 'source_review': source_review,
                             'observation': (relative / 'observation.json').as_posix()})
        if binding:
            private_rows[-1]['reuse_binding'] = binding_source
        outputs.append((private_root / relative / 'report.md', private_report(review, result).encode()))
        summaries.append({'model': model_id, 'counts': result['counts'], 'coverage': result['coverage']})
    if consumed != set(reuses) or len({row['model_id'] for row in public_rows}) != len(public_rows):
        raise ValueError('Observation reuse has no unique retained source review')
    common = {'schema': 'math-gauge.manuscript-observation-index/v1', 'version': policy['version'],
              'base_benchmark_version': '0.6.0', 'observation_id': policy['observation_id'],
              'kind': 'descriptive-observation', 'is_score': False, 'higher_is_better': None,
              'reviewer_kind': 'ai', 'human_review': 'pending', 'post_observation': True,
              'formal_comparison_eligible': False, 'new_candidate_calls': 0, 'main_scores_modified': False}
    outputs += [(public_root / ROOT_PATH / 'observations.json', serialized({**common, 'visibility': 'public',
                 'policy': policy_source, 'models': public_rows}).encode()),
                (private_root / ROOT_PATH / 'observations.json', serialized({**common, 'visibility': 'private',
                 'models': private_rows}).encode()),
                (public_root / 'docs/manuscript-observations.md', summary_report(summaries).encode())]
    for target, raw in outputs:
        if write:
            if not target.is_file() or target.read_bytes() != raw:
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(raw)
        elif not target.is_file() or target.read_bytes() != raw:
            raise ValueError(f'Stale or missing manuscript observation: {target}')
    for row in public_rows:
        check_pair(public_root, private_root, row['model_id'], row['record_id'])
    return summaries


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--public-root', type=Path, default=ROOT)
    parser.add_argument('--private-root', type=Path, required=True)
    parser.add_argument('--write', action='store_true', help='Rebuild descriptive counts from unchanged source reviews')
    parser.add_argument('--reuse-binding', type=Path, action='append', default=[],
                        help='Register a private same-answer binding; repeat for multiple models')
    args = parser.parse_args()
    print(serialized(run(args.public_root, args.private_root, write=args.write, reuse_bindings=args.reuse_binding)), end='')


if __name__ == '__main__':
    main()
