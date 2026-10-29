# Math Gauge

**Measure the capability, not just the answer.**

Math Gauge 是数学推理与 Lean 语义对齐习题及评测工具。它考察模型能否在实际给定的结构下完成证明、反例、构造或分类，保持假设、量词、定义域和结论强度，并让题面、原始答卷、审核与编译证据可以复核。

[文档导航](docs/README.md) · [项目定位](docs/project-positioning.md) · [评测方法](docs/evaluation-methods.md) · [按能力重点选题](exercises/by-focus.md) · [使用与复核](docs/usage.md) · [结果与版本](docs/results.md) · [仓库地图](docs/repository-map.md)

## 当前试卷

当前主试卷为 **43 份**。它们已准备数学参考、逐项判准、来源和 AI 复核材料，仍为 **draft / human pending**。GR001 已作[0.1.2 数学范围修订](drafts/progressive-groups-20261030/reviews/strict-amendment-0.1.2.json)，其余40组及两章保持0.1.1；确切版本以各题 `case.json` 与修订记录为准。新版没有模型答卷或通过率。新增目标的作者 Lean、真实编译和逐项独立语义复核见[作者证据账本](results/author-lean-20261030/README.md)；GP003 的剩余几何缺口单独列明，不能称为全库完整形式化。

| 题集 | 规模 | 入口 |
| --- | --- | --- |
| 递进题组 | 原 41 题逐一扩为 41 组、246 阶段 | [题组目录](drafts/progressive-groups-20261030/README.md) |
| 整章 Lean 考试 | 卷 I 第 2/3 章两份试卷，分别 34/92 项义务 | [整章目录](drafts/chapter-exams-20261030/README.md) |

一个完整题组或整章是一份相关样本，不能把阶段或义务当成独立题数。递进题组持续改变同一对象的条件、量词、域或结论方向；整章题提供含证明的完整原文，要求交付完整 Lean 工程及逐项语义对应。

下一轮的[执行协议](protocol/reliability-execution.md)计划每份试卷独立作答三次，并在[预选八题](protocol/reliability-20261030/selection.md)上开展中性、支持与怀疑三个分支的两轮定点自查。每模型 177 个槽位是计划数，实际调用为 0；共享 runner 的多轮调度及 KEEP/FULL 答卷组合仍待实现和离线验收。见[材料包及未执行状态](protocol/reliability-20261030/README.md)。

## 从哪里开始

| 目的 | 阅读路径 |
| --- | --- |
| 了解项目测什么、结论能支持到哪里 | [项目定位](docs/project-positioning.md) → [评测方法](docs/evaluation-methods.md) |
| 阅读当前题目与出题材料 | [递进题组](drafts/progressive-groups-20261030/README.md)或[整章考试](drafts/chapter-exams-20261030/README.md) → 对应题目的完整材料 |
| 按考察能力选择题目 | [能力重点索引](exercises/by-focus.md)，再读取该题完整材料 |
| 导出候选输入、接入运行器或复核结果 | [使用指南](docs/usage.md) → [基础协议](protocol/evaluation.md)及相应运行协议 |
| 查看已经实测的原版 | [原 41 题七章目录](exercises/README.md) → [结果与版本](docs/results.md) |
| 新增题目或维护代码 | [仓库地图](docs/repository-map.md) → [贡献指南](CONTRIBUTING.md) |

## 准备候选材料

需要 Python 3.10+；共享 runner 无第三方运行依赖。在仓库根目录执行：

```sh
python3 -m math_gauge validate --suite drafts/progressive-groups-20261030
python3 -m math_gauge validate --suite drafts/chapter-exams-20261030
python3 -m math_gauge prepare --suite drafts/progressive-groups-20261030 --case MG-GR001 --out runs/group-r001
python3 -m math_gauge prepare --suite drafts/chapter-exams-20261030 --case MG-C002 --out runs/chapter02
```

每次输出目录须是新的。`prepare` 不调用模型；`validate` 检查材料合同与身份，不判断数学正确性。实际消息应由 `candidate_message(request)` 构造，以完整传递白名单附件。参考、评分、来源、真假、审核及历史答卷均不进入候选输入；目录分离本身不提供闭卷访问隔离。

省略 `--suite` 仍只选择 `cases/public` 的 20 题，不自动选择全部 43 份新试卷或全部 41 道原版单题。具体命令、作者与候选 Lean 核验及离线复算见[使用指南](docs/usage.md)。

## 已有结果与证据状态

原版 41 道单题保留为历史基准。首轮完整比较有 82 次独立数学请求，AI 审核严格完成为 Terra 6.1 Max 40/41、Gemini 3.8 Flash High 27/41，题目与答卷仍待人工验收。R005 澄清版另作两次请求，双方通过，不回填首轮旧版本成绩。原始答卷、失败、过滤通知、候选源码及冻结评分完整保留，见[结果索引](docs/results.md)。

数学与语义审核、固定源码的真实编译、公理检查、人工批准是不同证据。原版 40 题有完整作者主任务 Lean 证据，P003 保留部分覆盖边界；新增题组使用[独立冻结的作者工程与审核](results/author-lean-20261030/README.md)，不继承母题覆盖结论。工程测试通过也不构成模型通过率，见[评测方法中的证据说明](docs/evaluation-methods.md)。

本轮[严格数学复核](results/strict-review-20261030/README.md)与旧版独立AI审查分别记录。GR001的0.1.2修订处理真实作用域歧义，不以编辑等价代替数学审核。

项目题材源于公开 OET 的写作与研究协作，扩展到泛函分析、代数、拓扑、范畴与几何。来源、确切版本和 AI 协作说明见 [SOURCES.md](SOURCES.md)。公开题可能已进入训练数据；本项目不声称它们对模型必然未见。

仓库采用 [MIT 许可证](LICENSE)；复用的第三方材料保留其各自的许可证、署名及来源记录。
