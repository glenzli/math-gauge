# 文档导航

Math Gauge 0.4.0默认公开基准含36份任务：原32份数学卷与4份真实答卷审阅；公开36份任务关联32个母题家族，合并3份私有探索后为39份任务、35个家族。另11份数学卷保留为显式后备。原43份数学卷与新增审阅的相关性继续记录。参考答案为透明复核而公开，仍不属于 solver 输入。根据目的选择入口：

| 目的 | 入口 |
| --- | --- |
| 对比 Terra / Gemini 的六方向能力、作答稳定性与自查、AR重大误判及整章交付 | [离线对比页](results/comparison-2026-11-03/index.html) · [文字表](benchmark-comparison-2026-11-03.md) · [PNG](results/comparison-2026-11-03/comparison.png) · [SVG](results/comparison-2026-11-03/comparison.svg) |
| 阅读 Gemini 3.8 Flash 当前综合重算，39份首次答卷/87份记录 | [文字报告](gemini-combined-2026-11-03.md) · [公开机器结果](results/gemini-2026-11-03/result.json) |
| 阅读 Terra 6.1 当前综合重算，39份首次答卷/87份记录 | [独立结果页](results/terra-2026-11-03/index.html) · [文字报告](terra-combined-2026-11-03.md) · [机器结果](results/terra-2026-11-03/result.json) · [组合合同](../protocol/composite-development-report.md) |
| 运行已发布0.3.0任务包并交回答卷 | [v0.3.0 包内操作说明源文件](release-consumer-README-v0.3.0.md)；中性任务包与题集均为0.3.0 |
| 理解原32份数学卷与后备11题的取舍 | [0.3.0选卷依据](selection-v0.3.0.md) |
| 单独选择备选题 | [备选目录](../cases/reserve/README.md) · [显式清单](../cases/reserve-suite.json) |
| 了解已纳入0.4.0的真实答卷审阅、60/30/10判准与同母题聚合 | [审阅题组](../cases/answer-review/README.md) · [正式说明](answer-review-pilot.md) · [评分合同](../protocol/answer-review-scoring.md) · [显式清单](../cases/answer-review-suite.json) |
| 构建、检查任务包，或查阅历史分发 | [分发合同](../protocol/release-distribution.md) · [v0.1.0 历史发布说明](release-notes-v0.1.0.md) |
| 了解测量目标、样本单位和结论边界 | [项目定位](project-positioning.md) |
| 阅读当前试卷及完整出题材料 | [试卷目录](../cases/README.md) · [按考察重点选卷](../cases/by-focus.md) |
| 理解输入、数学审核、Lean与报告 | [评测方法](evaluation-methods.md) · [基础协议](../protocol/evaluation.md) |
| 查看当前能力方向、75/5/10/10综合权重与固定分母 | [综合评分标准](../protocol/benchmark-scoring.md) · [默认权重](../protocol/benchmark-profile.json) |
| 核验模型返回信息、隔离来源与正式比较资格 | [运行证据标准](../protocol/execution-evidence.md) · [隔离流程](../protocol/isolated-cli-runs.md) |
| 导出候选材料、接入共享runner | [使用指南](usage.md) |
| 维护交换接口、统一导入返回包并复用评分 | [外部 harness 合同](../protocol/external-harness.md) · [使用指南](usage.md) |
| 检查当前编译、语义覆盖与人审状态 | [验证状态](verification.md) · [作者证据账本](../verification/author/README.md) |
| 查看重复作答与立场分支的固定设计 | [可靠性材料包](../protocol/reliability/README.md) |
| 维护题目、工具与来源 | [仓库地图](repository-map.md) · [贡献指南](../CONTRIBUTING.md) · [来源说明](../SOURCES.md) |

协议分别管理共同评测边界、逐阶段审核、候选源码与实际隔离。题面给数学目标和交付范围；评分、真假、选题理由与实验机制留在评审侧。

当前题库和任务包均为0.4.0；历史包与旧原始证据保留。AR纳入和8份既有答卷重评属于观察结果后的方法变更。

[项目首页](../README.md)
