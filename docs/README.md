# 文档导航

Math Gauge 当前源码为本地0.5.0预览：默认30任务/21数学家族，另20份备选；合并3份私有探索后33任务/24家族。公开完整计划54记录，合并57记录；原43数学卷与3份同族加强稿共46数学卷，加4份相关AR为50条任务。旧答复用、新原生初答与观察后选题重算分别留证；参考公开仍不代表solver可读。已发布0.4.0资产和原指南不改。根据目的选择入口：

| 目的 | 入口 |
| --- | --- |
| 对比 Terra / Gemini 的六方向能力、作答稳定性与自查、AR重大误判及整章交付 | [离线对比页](results/comparison-2026-11-03/index.html) · [文字表](benchmark-comparison-2026-11-03.md) · [PNG](results/comparison-2026-11-03/comparison.png) · [SVG](results/comparison-2026-11-03/comparison.svg) |
| 阅读 Gemini 3.8 Flash 当前综合重算，33份首次答卷/57份记录 | [文字报告](gemini-combined-2026-11-03.md) · [公开机器结果](results/gemini-2026-11-03/result.json) |
| 阅读 Terra 6.1 当前综合重算，33份首次答卷/57份记录 | [独立结果页](results/terra-2026-11-03/index.html) · [文字报告](terra-combined-2026-11-03.md) · [机器结果](results/terra-2026-11-03/result.json) · [组合合同](../protocol/composite-development-report.md) |
| 查看本地0.5.0任务包预览 | [30任务/54记录操作指南](release-consumer-README-v0.5.0.md)；尚未发布，不表示已有下载资产 |
| 运行已发布0.4.0任务包 | [v0.4.0原操作指南](release-consumer-README-v0.4.0.md)；保持原36任务/84记录身份 |
| 理解当前30任务与20备选的取舍、家族计数与覆盖损失 | [0.5.0选题依据](selection-v0.5.0.md)；[0.3.0历史取舍](selection-v0.3.0.md)保留 |
| 单独选择备选题 | [备选目录](../cases/reserve/README.md) · [显式清单](../cases/reserve-suite.json) |
| 了解保留在当前默认集的真实答卷审阅、60/30/10判准与同母题聚合 | [审阅题组](../cases/answer-review/README.md) · [正式说明](answer-review-pilot.md) · [评分合同](../protocol/answer-review-scoring.md) · [显式清单](../cases/answer-review-suite.json) |
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

当前0.5.0尚为本地预览，0.3多轮合同为六题各两次独立及每分支一次后续，旧A3/R2留档不进入默认；发布状态以真实Release为准。AR纳入和8份旧答重评属于此前的观察后方法变更，本次选题重算另含三份同族书面题的新原生初答。新题15项判准没有作者Lean证据，人审待办；原43卷/372义务/470模块的作者证据范围不扩大。当前结果继续使用2026-11-03路径，精确数值以新版冻结机器结果和审核快照为准。

[项目首页](../README.md)
