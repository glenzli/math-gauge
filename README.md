# Math Gauge

[简体中文](README.md) · [English](README.en.md)

**Measure the capability, not just the answer.**

Math Gauge 是一套面向数学工作的模型评测，涵盖书面证明、Lean 形式化和数学研究任务。当前版本为 **[1.0.0](https://github.com/glenzli/math-gauge/releases/tag/v1.0.0)**。

[在线榜单](https://glenzli.com/benchmarks/math-gauge/?lang=zh) · [完整结果](docs/results.md) · [公开题目](cases/README.md) · [运行指南](docs/harness-guide.md)

## 为什么做 Math Gauge

> 我最先想到的比喻，是把核桃浸在某种能让它软化的液体里——为什么不干脆用水呢？
>
> （引自格罗滕迪克《收获与播种》，据 Colin McLarty〈[The Rising Sea](https://www.landsburg.com/grothendieck/mclarty1.pdf)〉所引英译转译。）

我很喜欢“泡核桃”这个表述。

现在的前沿模型，数学能力已经很强。[FrontierMath](https://epoch.ai/frontiermath)、[BrokenArXiv](https://matharena.ai/?comp=overall--brokenarxiv) 等评测，也为了解它们提供了很好的参考。不过，在编写 [OET（算子演化论）](https://glenzli.com/books/oet/) 的过程中，我还是会遇到一些问题：有的推导写得流畅，仔细检查却少了条件；有的回答看似正确，实际上已经把问题换成了模型更熟悉的样子。

在我自己的数学工作中，往往是先有一个想法，再慢慢理清概念、寻找合适的表示，把推导和证明展开。有些思路未必走在模型熟悉的套路上，我会更看重它能否跟住原来的问题，认真检查每一步，守住条件和意图。它可以质疑、举反例，也可以提出别的做法，但要把理由和与原问题的关系讲清楚。

这一路，我的主力也从早期的 Gemini、Claude 逐渐换成了 GPT 系列。使用中，我慢慢摸到了不同模型的强项、盲点和风格；但模型还在不断进步，过去的经验也需要更新。我于是想做一套贴近自己数学工作的 benchmark，把日常需要的推导、审阅、背景核查和 Lean 形式化整理成题，看各个模型实际做得怎样，再决定接下来选谁做主力、怎样分工。Math Gauge 就是这样来的。

## 测什么

| 方向 | 满分 | 主要任务 |
|---|---:|---|
| 书面证明 | 35 | 书面论证、反例与边界分析，以及对已有论证的审阅。 |
| Lean | 35 | 语义审计、形式化与连续三轮自查，分别检查代码、数学对应和纠错。 |
| 数学研究 | 30 | 背景核查、命题拓展，以及把一个数学想法展开成严谨手稿。 |

完整评测有 **39 道初答题：公开 25 道、私有 14 道，共 35 个数学家族**。同一整章 Lean 题另接续三轮自查，合计 42 次规定交付；相关变体先在家族内聚合，公私题共用运行与计分规则。

想先看一道题，可以从[矩阵估计想法的手稿化任务](cases/manuscript-completion/MG-MCP003/task.md)读起。各子类的题目、权重和选题理由见[题目目录](cases/README.md)与[选题说明](docs/selection.md)。候选只接收题面和明确提供的材料，参考与判准不进入答题上下文；私有题的题面、原答和逐题评审保持私有。

## 怎么读分数

| 分数 | 含义 |
|---|---|
| **MC · Mathematical Capability** | 只计经过核实的有效数学贡献，包括未完成任务中的有效进展。 |
| **RMC · Reliable Mathematical Capability** | 在有效成果上扣除错误断言、误判等造成的损失，是默认主分。 |
| **SMC · Strict Mathematical Completion** | 整题达到全部实质要求才得分；自查按完整三轮的完成情况、诊断和无回退要求验收。 |

三种分数使用同一批规则选定答卷和固定权重，均按 **100 分**报告；未测项保留未知范围，不把已测部分放大到满分。每题采用规则内首次正常交卷；没有正常交卷时，MC 可计经核实的截止前原成果，RMC 与 SMC 为 0。具体判准见[评分规范](protocol/benchmark-scoring.md)。

## 当前结果

榜单默认按 RMC 排序。打开[在线榜单](https://glenzli.com/benchmarks/math-gauge/?lang=zh)，可以切换三种分数、查看分项，并从模型页进入公开原答与逐题评审；[完整文字结果](docs/results.md)保留成绩表、来源更正和补测说明。

2026-11-18 的 [Sol 6.2 Max](https://glenzli.com/benchmarks/math-gauge/models/sol-6.2-max/?lang=zh) 已测完并入榜：MC **93.21**、RMC **93.21**、SMC **89.17**。与 Sol 6.1 Max 的逐项变化见[完整结果](docs/results.md#sol-62-max--2026-11-18)。

[![Math Gauge 中文总榜](docs/screenshots/leaderboard-zh.jpg)](https://glenzli.com/benchmarks/math-gauge/?lang=zh)

当前结果汇集不同批次的留档答卷，部分含旧答复用和后续补测；采用 **AI 审核，另有部分人工抽审**。实际运行条件、故障与重试经过随来源保留，阅读模型差异时可一并查看[审核方式](docs/review-process.md)和[运行记录](docs/results.md#记录与复算)。

<details>
<summary>成本与耗时截图</summary>

以下两图以 RMC 为例。成本只计每题采用的一次作答及三轮固定自查，使用留档的 API 参考价或测试日费用；耗时包含工具使用与等待，受运行环境影响。两者的来源和限制分别见[成本口径](docs/cost-reference.md)与[计时口径](docs/answer-timings.md)。

[![Math Gauge 中文成本与 RMC 前沿](docs/screenshots/cost-frontier-zh.jpg)](https://glenzli.com/benchmarks/math-gauge/?lang=zh&cost-axis=cost&cost-score=partial#cost-frontier)

[![Math Gauge 中文耗时与 RMC 前沿](docs/screenshots/time-frontier-zh.jpg)](https://glenzli.com/benchmarks/math-gauge/?lang=zh&cost-axis=time&cost-score=partial#cost-frontier)

</details>

## 本地查看与运行评测

在仓库根目录启动本地服务，再打开 <http://127.0.0.1:8000/site/>：

```bash
python3 -m http.server 8000 --bind 127.0.0.1
```

要运行评测，请按[运行与交付指南](docs/harness-guide.md)准备题包和独立答题环境。所有正式题目均 **允许本地工具及预置公共依赖，禁止联网检索和工具联网**；模型服务与认证连接另行记录。题包、时间限制、封卷、隔离和重试的具体要求都在指南中。

## 继续阅读

| 想了解 | 入口 |
|---|---|
| 题目与选题 | [公开题目](cases/README.md) · [选题说明](docs/selection.md) |
| 评分与审核 | [评测协议](protocol/evaluation.md) · [评分规范](protocol/benchmark-scoring.md) · [审核方式](docs/review-process.md) |
| 辅助指标 | [内容可靠率与目标达成率](protocol/content-rates.md) · [手稿主动额外成果](docs/manuscript-observations.md) |
| 执行与留档 | [运行与交付指南](docs/harness-guide.md) · [正式记录合同](protocol/result-record.md) |
| 时间与费用 | [计时口径](docs/answer-timings.md) · [成本口径](docs/cost-reference.md) |
| 故障与补测 | [答卷来源更正](docs/harness-corrections.md) · [整章自查补充](docs/c003-sealed-continuation.md) · [尝试与重试统计](docs/execution-attempts.md) |
| 版本与证据 | [1.0.0 发行说明](releases/v1.0.0/README.md) · [历史发行](releases/) · [证据留存与恢复](docs/evidence-retention.md) |

当前 1.0.0 复用的历史答卷保留原执行版本、原答和原审核，兼容关系见发行说明。查看或复算这些结果不表示模型重新参加了测试。
