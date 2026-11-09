# 当前固定结果档案

benchmark0.6.0封版；三评分聚合0.8.0／MC0.2.0／Strict0.2.0。AI审核、人审待定、正式比较资格false。发布包与标签保持封存，新的模型成绩作为追加记录。

仅保存用户选定的当前快照，CLI模型和记录号由benchmark.json登记，公私同步。Dot使用独立native-observation.json，CLI与源绑定外部答卷使用各自schema的record.json，原始执行身份与验证门槛分别保留。原答、自评、原工程与具名审核保持字节；日常runs不入Git，旧版本从Git历史恢复。公私统一题池，不发布独立公有分数。

| 模型 | 当前档案 |
| --- | --- |
| Astra 6 (max) · Codex CLI | [20261109](v0.6.0/astra-6-max/20261109/README.md) |
| Sol 6.1 (max) · Codex CLI | [20261109](v0.6.0/sol-6.1-max/20261109/README.md) |
| Claude Opus 5.5 (max) · Claude Code | [20261109](v0.6.0/claude-opus-5.5-max/20261109/README.md) |
| Astra 6 (xhigh) · Codex CLI | [20261110](v0.6.0/astra-6-xhigh/20261110/README.md) |
| Dot Underlying · Unknown<sup>1</sup> | [20261108](v0.6.0/dot-underlying-model-20261108/20261108/README.md) |
| Sol 6.1 (xhigh) · Codex CLI | [20261109](v0.6.0/sol-6.1-xhigh/20261109/README.md) |
| Terra 6.1 (max) · Codex CLI | [20261105](v0.6.0/terra-6.1-max/20261105/README.md) |
| Terra 6.1 (xhigh) · Codex CLI | [20261108](v0.6.0/terra-6.1-xhigh/20261108/record.json) |
| Kimi 3.1 Pro (max) · Claude Code | [20261110-r3-recovery](v0.6.0/kimi-3.1-pro-max/20261110-r3-recovery/README.md) |
| DeepSeek v4.1 Flash (max) · Codex CLI<sup>2</sup> | [20261110](v0.6.0/deepseek-v4.1-flash-1017/20261110/README.md) |
| Gemini 3.8 Flash (high) · AGY CLI | [20261105](v0.6.0/gemini-3.8-flash-high/20261105/README.md) |
| Gemini 4 Argon (high) · AGY CLI | [20261108](v0.6.0/gemini-4-argon/20261108/record.json) |

每份当前快照新增独立`answer-timings.json`，绑定当次选定答卷及可核实时间。完整来源和私有逐项时间留私库，公开附件提供公开逐项时间与合并统计；缺失为null，不影响分数。见[耗时总表与计时规则](../docs/answer-timings.md)。

[主动额外成果观察](manuscript-observations/v0.1.0/observations.json)只记录规则选定A1在未被要求时交付的额外成果组数与手稿审阅覆盖，不是新增能力分或独立benchmark，不设满分或百分比，也不预设数量越多越好。原数学审核与来源散列保留，当前只读取去重成果组。公私合并组数和公开题核验可见[研究分榜内的折叠观察栏](../site/index.html?category=research#research-initiative)及[观察报告](../docs/manuscript-observations.md)，私有题数学内容与逐题分配留私库。

三种评分分别为数学能力MC、可靠数学能力RMC（默认）、严格数学交付SMC（归档模式strict）；每种均保存首次和允许计次非逻辑重跑视图，共六份。实际文件名、完整原答及政策身份均以record.json或native-observation.json的精确描述符为准。

record.json绑定六份结果、capability-scoring-policy.json、score-modes.json和原审核政策；各模型README及详细报告提供三种贡献与完整分区间。内容可靠率与完整目标达成率另按共同697单元和149目标审核。独立无工具正式组不再留档；单独指定的邀请研究仅留必要上下文，不计分。结构复核保留原R1及新增R3审核，当前分值不因新增模式变更。

三种分数共用相同答卷、题池、家族聚合和权重：书面35、Lean35、数学研究30。当前公25／私14共39题、35个数学家族，另固定三轮Lean自查，共42次规定交付。已建100／100，数学想法手稿化组件0.5.0的五个等权家族（公1／私4）仍分享10分；所有分数均为已确认贡献／100，不重新归一化。

[当前总报告](../docs/results.md) · [结果页](../site/index.html) · [留档合同](../protocol/result-record.md)

PS001现替换公开GR103。各记录的written_replacement_evidence绑定新题A1；完整原生证据在私库written-replacement-inputs中。Gemini仅保留原评94，Terra与DeepSeek本轮A1均为100；旧GR103原始材料是历史来源，不再计入当前分数。当前承诺审核另存带ps001后缀的具名文件，旧审核不覆盖。

DeepSeek最终记录按[外部答卷合同](../protocol/paper-observations.md)0.2.0验证，MC76.71／RMC65.30／SMC25.83；38份已评答卷、1项超时及旧C003三轮构成完整39＋3。原答、原评和旧失败保留；两率另待补审。

¹ Dot原生独立运行方式。

² 使用DeepSeek Harness（DSH）时，多道题因推理过程过长、耗尽最大输出预算而未能交卷，因此改用Codex CLI执行。

Kimi 3.1 Pro (max)的C003第三轮经用户断电排查补充接纳，单轮100/100，轨迹为91→91→91→92；R1/R2误报扣分保留。更新后MC75.28／RMC70.41／SMC43.67，内容可靠率91.14%、完整目标达成率68.03%。47次物理请求和原归档保留，本次没有重考。 [完整报告](v0.6.0/kimi-3.1-pro-max/20261110-r3-recovery/README.md)。
