# 完整尝试与重试统计

[页面运行与重试记录](../site/index.html#execution-anomalies) · [匿名数据](../results/execution-attempts/v0.1.0/current.json) · [历史异常样本](execution-anomalies.md)

该统计描述已留档的任务尝试过程，独立于 MC、RMC、SMC、两率、费用及异常分类。它不产生新的候选调用，也不改写原答、原评审或已有故障排除。

首页的「运行与重试记录」跨评分版展示已留档的首答、自查与 1.2.0 续答。各批保留原始计数单位，首答数据来自完整尝试摘要和各模型公开运行摘要，续答数据来自续答资源报告。没有核实的尝试数、有效重试数或系统排除数显示为「—」。历史异常样本按原截点在同一附表内单列。

## Astra 6.2 xHigh · 2026-11-20

39道初答与三轮自查共44次物理调用：42次有效尝试全部正常交卷，1次明确容量错误与1次明确网络断流属于系统排除；没有消耗模型额度的重试。9道中性续答另有9次正常物理调用、9次有效尝试，因此本轮正式资源共53次物理调用／51次有效尝试／2次系统排除。独立canary预检为1个逻辑检查、2次物理调用，不进入39＋3＋9分母或正式资源。

两次系统故障仍保留完整原生事件与请求记录，排除其有效模型事件、用量、费用和时间，不改写旧本地结算报告。CLI外层调用次数与实际工具往返HTTP请求次数分别记录；后者未知。原生正常交卷锁定采用选择，数学错误不会产生重试资格。

The Astra 6.2 xHigh campaign retains 44 base physical invocations:42 effective attempts delivered normally, with one confirmed capacity failure and one confirmed network failure excluded as system retries. Nine neutral revisions add nine normal physical/effective attempts. Formal totals are 53 physical invocations, 51 effective attempts and two system exclusions; a separate one-slot/two-invocation canary is excluded. Unknown inner HTTP-call counts remain unknown.

## Carbon High

来源是 `20261115` 答卷绑定的完整物理请求索引。统计覆盖该索引识别的来源批次，包含早期失败批次，以及后继续跑和三轮自查。

| 范围 | 尝试记录 | 有效尝试 | 系统排除 | 正常交卷 |
|---|---:|---:|---:|---:|
| 早期失败批次 | 7 | 6 | 1 | 0 |
| 续跑与自查 | 55 | 45 | 10 | 41 |
| **全部** | **62** | **51** | **11** | **41** |

另一种分项：39道初答对应56条尝试记录（48次有效、8项系统排除、38份正常交卷）；固定三轮自查对应6条记录（3次有效、3项系统排除、3份正常交卷）。

## 如何计数

- **尝试记录**以唯一任务尝试生命周期计数，包含有原据的联网前中断；它不是服务商 HTTP、续接或辅助调用的次数。实际候选 API 请求总数保持未知。
- **有效尝试**沿用原来源及有据的排除判断。62＝51＋11；51＝41份正常交卷＋10次消耗尝试的交付失败。
- **额外尝试**以39道初答＋3轮自查的42个规定交付槽为基准：62−42＝20条。
- **额外有效重试**为51−42＝9次。系统排除另列，不占该有效尝试额度。一次正常数学答错不产生新的重试资格。
- **旧异常表的7条**是截至2026年11月15日01:12 SGT的早期已审样本。异常分类有独立的去重、归因和未知值规则；不能把62条尝试、20条额外尝试或9次有效重试当作异常运行数。

只对来源完整核对过的模型提供这份汇总；没有汇总不表示零次重试。所有统计仍保留AI审核／人工待审状态。

## 来源与公开边界

公开投影保留原请求索引及公开记录的不透明SHA256，按批次、初答及三轮给出匿名合计。原始请求、题目标识、路径和逐项排除原据仍在私库。共享的 `scripts/results_attempt_history.py` 从唯一生命周期重算并核对原索引及公开记录；严格字段白名单阻止私有来源信息进入投影。

## English

Carbon High's retained history contains **62 task-attempt records: 51 effective attempts and 11 system exclusions**, with 41 normal finals. The earlier failed batch contributes 7 records; the resumed run and self-checks contribute 55. Against 39 initial tasks plus three fixed self-checks, this is **20 additional records, including nine effective retries**.

These are lifecycle records, including pre-request interruptions, not API-call counts. Actual candidate API-call totals remain unknown. The seven reviewed runs in the earlier anomaly snapshot retain their original cutoff and attribution; they are not the campaign retry total. Scores, selected answers, original judgments and execution records remain unchanged. Source hashes are public; private case identifiers, source paths and raw evidence remain private.
