# 文档导航

Math Gauge 默认题集含32份完整试卷，另11份保留为显式后备；两者同属43卷公开开发题库。参考答案为透明复核而公开，仍不属于 solver 输入。根据目的选择入口：

| 目的 | 入口 |
| --- | --- |
| 阅读 Terra 6.1 首次综合评测，35题/83槽、组合profile v0.2.0 | [独立结果页](results/terra-2026-11-03/index.html) · [文字报告](terra-combined-2026-11-03.md) · [机器结果](results/terra-2026-11-03/result.json) · [组合合同](../protocol/composite-development-report.md) |
| 在任意外部 harness 运行任务并交回答卷 | [v0.3.0 包内操作说明源文件](release-consumer-README-v0.3.0.md)；中性任务包与题集均为0.3.0 |
| 理解默认32题/80次与后备11题的取舍 | [0.3.0选卷依据](selection-v0.3.0.md) |
| 单独选择备选题 | [备选目录](../cases/reserve/README.md) · [显式清单](../cases/reserve-suite.json) |
| 构建、检查任务包，或查阅历史分发 | [分发合同](../protocol/release-distribution.md) · [v0.1.0 历史发布说明](release-notes-v0.1.0.md) |
| 了解测量目标、样本单位和结论边界 | [项目定位](project-positioning.md) |
| 阅读当前试卷及完整出题材料 | [试卷目录](../cases/README.md) · [按考察重点选卷](../cases/by-focus.md) |
| 理解输入、数学审核、Lean与报告 | [评测方法](evaluation-methods.md) · [基础协议](../protocol/evaluation.md) |
| 查看七个分项、加权总分、缺测规则和独立运行范围 | [综合评分标准](../protocol/benchmark-scoring.md) · [默认权重](../protocol/benchmark-profile.json) |
| 核验模型返回信息、隔离来源与正式比较资格 | [运行证据标准](../protocol/execution-evidence.md) · [隔离流程](../protocol/isolated-cli-runs.md) |
| 导出候选材料、接入共享runner | [使用指南](usage.md) |
| 维护交换接口、统一导入返回包并复用评分 | [外部 harness 合同](../protocol/external-harness.md) · [使用指南](usage.md) |
| 检查当前编译、语义覆盖与人审状态 | [验证状态](verification.md) · [作者证据账本](../verification/author/README.md) |
| 查看重复作答与立场分支的固定设计 | [可靠性材料包](../protocol/reliability/README.md) |
| 维护题目、工具与来源 | [仓库地图](repository-map.md) · [贡献指南](../CONTRIBUTING.md) · [来源说明](../SOURCES.md) |

协议分别管理共同评测边界、逐阶段审核、候选源码与实际隔离。题面给数学目标和交付范围；评分、真假、选题理由与实验机制留在评审侧。

[项目首页](../README.md)
