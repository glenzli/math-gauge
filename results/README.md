# 当前固定结果档案

benchmark0.6.0开发草稿；三评分聚合0.8.0／MC0.2.0／Strict0.2.0。AI审核、人审待定、正式比较资格false，尚未发布release。

仅保存用户选定的Terra、DeepSeek、Gemini当前记录，路径为v0.6.0/<model>/20261105。原答、自评、原工程与具名审核保持字节；日常runs不入Git，旧版本从Git历史恢复。公私统一题池，不发布独立公有分数。

三种评分分别为数学能力MC、可靠数学能力RMC（默认）、严格数学交付Strict；每种均保存首次和允许计次非逻辑重跑视图，共六份。MC使用capability-combined-aggregate.json及capability-retry-combined-aggregate.json，RMC沿用combined-aggregate.json及retry-combined-aggregate.json，Strict沿用strict-combined-aggregate.json及strict-retry-combined-aggregate.json。私有对应capability-result.json、capability-retry-result.json、result.json、retry-result.json、strict-result.json、strict-retry-result.json。

record.json绑定六份结果、capability-scoring-policy.json、score-modes.json和原审核政策；各模型detailed-report.md报告三种贡献与完整分区间。独立无工具正式组不再留档；单独指定的邀请研究仅留必要上下文，不计分。结构复核保留原R1及新增R3审核，当前分值不因新增模式变更。

三种分数共用相同答卷、题池、家族聚合和权重：书面35、Lean35、数学研究30。当前公24／私9共33题、29个数学家族，另固定三轮Lean自查。已建90／100，研究稿完善10分待建；所有分数均为已确认贡献／100，不重新归一化。

[当前总报告](../docs/results.md) · [结果页](../site/index.html) · [留档合同](../protocol/result-record.md)
