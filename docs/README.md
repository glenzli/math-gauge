# 文档导航

Math Gauge 的当前主试卷是 **43 份材料**：41 个递进题组，以及两份整章 Lean 考试。确切版本以逐题 `case.json` 和修订记录为准；它们仍为 draft / human pending，尚无模型成绩。[作者 Lean 证据账本](../results/author-lean-20261030/README.md)记录逐项形式化、真实编译及独立语义审核，明确保留 GP003 的未完成部分。多轮调度仍待实现验收。

已经实测的原版是另一套 **41 道单题**。其七章目录、原始答卷和冻结成绩继续保留，不能将其成绩套到新试卷上。

## 按目的阅读

| 你想做什么 | 推荐顺序 | 阅读后可确认的内容 |
| --- | --- | --- |
| 了解项目 | [首页](../README.md) → [项目定位](project-positioning.md) | 所测问题、适用范围、版本和结论边界 |
| 阅读当前试卷 | [递进题组](../drafts/progressive-groups-20261030/README.md)或[整章考试](../drafts/chapter-exams-20261030/README.md) → 完整逐题材料 | 数学目标、候选附件、参考、判准与真实审核状态 |
| 按考察能力选题 | [能力重点索引](../exercises/by-focus.md) → 对应完整题目 | 跨题型的能力分组与受测义务 |
| 研究评测设计 | [评测方法](evaluation-methods.md) → [基础协议](../protocol/evaluation.md) → [题组合同](../protocol/question-groups.md) | 实验单位、输入边界、严格完成与错误传播 |
| 准备或规划新实验 | [使用指南](usage.md) → [重复执行协议](../protocol/reliability-execution.md) → [评分标准](../protocol/reliability-scoring.md) → [材料包](../protocol/reliability-20261030/README.md) | 可用单轮入口，以及尚未实现验收的多轮部分 |
| 复核已有成绩 | [结果与版本](results.md) → 对应结果 README → 逐题答卷与审核 → [离线复算](usage.md) | 冻结版本、分母、实际运行条件及保存判断的汇总一致性 |
| 复核新增题目的作者 Lean | [作者证据账本](../results/author-lean-20261030/README.md) → 逐题 alignment、源码、编译报告与独立语义审核 | 实际命题与题面的对应、固定源码身份和未完成边界 |
| 新增题目或维护代码 | [仓库地图](repository-map.md) → [贡献指南](../CONTRIBUTING.md) | 唯一材料来源、代码职责、对应验证与保存要求 |
| 阅读原版习题 | [原 41 题七章目录](../exercises/README.md) → [任务类型](../exercises/task-types.md) → [版本历史](../exercises/history.md) | 原版题目的主题、变体相关性与历史身份 |

## 文档各自负责什么

| 文档 | 职责 |
| --- | --- |
| [项目定位](project-positioning.md) | 为什么建立这套材料、研究什么、哪些能力结论尚不能作出 |
| [评测方法](evaluation-methods.md) | 怎样冻结、执行、审核和报告，规范与实际实现如何对应 |
| [使用与复核](usage.md) | 题集选择、候选输入、运行器、两种 Lean 核验及离线复算的具体命令 |
| [结果与版本](results.md) | 已发生的完整比较、补测、历史校准与证据阅读顺序 |
| [仓库地图](repository-map.md) | 目录目的、代码所有权、测试与材料生命周期 |
| [贡献指南](../CONTRIBUTING.md) | 新题、版本修订、候选边界、验证和提交规则 |
| [protocol/](../protocol/evaluation.md) | 各轨的正式材料和执行合同；新增协议不自动代表软件已实现 |

当前 43 份试卷的逐题状态以各自 `case.json`、`review.json`、合同及散列绑定回执为准。0.1.1 的编辑等价与后续数学修订分别保留记录，不能把复用原审核称作新一次全量数学审定。[原版出题侧账本](../exercises/instructor-guide.md)继续只对应原 41 题，不自动覆盖新增目标。

GR001当前为0.1.2，其余40题组和两章为0.1.1；[局部修订回执](../drafts/progressive-groups-20261030/reviews/strict-amendment-0.1.2.json)与[本轮数学复核](../results/strict-review-20261030/README.md)分别说明作用域调整和审查范围。

## 复核一条结论

先确认 task 及显式附件的版本，再读原始答卷与响应散列绑定的审核。需要 Lean 的交付还要看候选原始源码、真实编译、公理依赖和逐项语义对应；作者参考编译不能替代候选交付。最后核对冻结、型号与工具条件、所有尝试及汇总分母。

离线复算只验证保存的判断能够重新汇总，不重新判断数学，也不调用模型或 Lean。AI 审核、内核检查和人工批准分别记录，提交或推送不改变审核状态。

题库与评审材料对项目读者公开可读，不代表可以附进候选上下文。实际投放始终使用共享 runner 的显式投影。

[返回首页](../README.md)
