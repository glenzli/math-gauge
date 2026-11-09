# 当前固定结果档案

benchmark0.6.0封版；三评分聚合0.8.0／MC0.2.0／Strict0.2.0。AI审核、人审待定、正式比较资格false。发布包与标签保持封存，新的模型成绩作为追加记录。

仅保存用户选定的当前快照，CLI模型和记录号由benchmark.json登记，公私同步。Dot使用独立native-observation.json，CLI使用record.json，原始执行身份与验证门槛分别保留。原答、自评、原工程与具名审核保持字节；日常runs不入Git，旧版本从Git历史恢复。公私统一题池，不发布独立公有分数。

| 模型 | 当前档案 |
|---|---|
| Claude Opus 5.5 Max · Claude Code | [20261109](v0.6.0/claude-opus-5.5-max/20261109/README.md) |
| Sol 6.1 Max · Codex CLI | [20261109](v0.6.0/sol-6.1-max/20261109/README.md) |
| Sol 6.1 xHigh · Codex CLI | [20261109](v0.6.0/sol-6.1-xhigh/20261109/README.md) |
| Terra 6.1 Max · Codex CLI | [20261105](v0.6.0/terra-6.1-max/20261105/README.md) |
| Terra 6.1 xHigh · Codex CLI | [20261108](v0.6.0/terra-6.1-xhigh/20261108/record.json) |
| Gemini 3.8 Flash High · AGY CLI | [20261105](v0.6.0/gemini-3.8-flash-high/20261105/README.md) |
| Gemini 4 Argon High · AGY CLI | [20261108](v0.6.0/gemini-4-argon/20261108/record.json) |
| DeepSeek v4.1 Flash 1017 · Codex | [20261105](v0.6.0/deepseek-v4.1-flash-1017/20261105/README.md) |
| Dot Underlying Model · Dot native harness | [20261108](v0.6.0/dot-underlying-model-20261108/20261108/README.md) |

三种评分分别为数学能力MC、可靠数学能力RMC（默认）、严格数学交付SMC（归档模式strict）；每种均保存首次和允许计次非逻辑重跑视图，共六份。实际文件名、完整原答及政策身份均以record.json或native-observation.json的精确描述符为准。

record.json绑定六份结果、capability-scoring-policy.json、score-modes.json和原审核政策；各模型README及详细报告提供三种贡献与完整分区间。内容可靠率与完整目标达成率另按共同697单元和149目标审核。独立无工具正式组不再留档；单独指定的邀请研究仅留必要上下文，不计分。结构复核保留原R1及新增R3审核，当前分值不因新增模式变更。

三种分数共用相同答卷、题池、家族聚合和权重：书面35、Lean35、数学研究30。当前公25／私14共39题、35个数学家族，另固定三轮Lean自查，共42次规定交付。已建100／100，数学想法手稿化组件0.5.0的五个等权家族（公1／私4）仍分享10分；所有分数均为已确认贡献／100，不重新归一化。

[当前总报告](../docs/results.md) · [结果页](../site/index.html) · [留档合同](../protocol/result-record.md)

PS001现替换公开GR103。各记录的written_replacement_evidence绑定新题A1；完整原生证据在私库written-replacement-inputs中。Gemini仅保留原评94，Terra新A1为100，DS未知；旧GR103原始材料是历史来源，不再计入当前分数。当前承诺审核另存带ps001后缀的具名文件，旧审核不覆盖。
