# 评测材料的职责分层

当前基准只有一个case集合与一个共享runner。分层用于保持候选边界和证据归属，不产生第二套任务或评分实现。

| 层 | 内容 | 维护者所做的判断 |
| --- | --- | --- |
| 数学目标 | task及显式候选附件 | 给全实际结构、目标和交付范围，不泄露评分、真假或路线 |
| 评审合同 | reference、rubric、contract、来源与审核 | 逐义务证明、反例、允许替代解法及具体判准 |
| 分类导航 | cases/taxonomy.json、catalog.json与by-focus.md | 按真实阶段分类，不改变题目或额外增加要求 |
| 执行 | math_gauge/execution.py及薄适配器 | 冻结原始请求、响应、全部尝试与源码核验 |
| 审核和报告 | math_gauge/review.py | 绑定同一答卷与收据，区分数学、交付、服务及人审 |
| 证据 | verification/author及本地运行目录 | 保留固定源码、编译、语义覆盖与缺口的实际身份 |

全局评测原则见[evaluation.md](evaluation.md)。逐阶段相关性、整章背景和声明映射见[question-groups.md](question-groups.md)。当前可靠性材料仅规定待实现的多轮历史与答卷组合，不把准备工作计作模型考试。
