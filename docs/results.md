# 当前完整结果

当前本地评分版为 **1.2.0**，已发布题包仍为1.0.0。新版按[中性续答规则](neutral-revision.md)采用非Lean失分题的一次续答：逐题80%首答＋20%续答，三个模式、家族权重与完整100分分母一致；Lean及三轮自查沿用。基础采用聚合 **0.9.0**／MC **0.3.0**／SMC **0.2.0**，续答组件 **0.1.0**；页面默认按SMC排序，指标顺序为SMC／RMC／MC。

## 1.2.0：已完成续答

| 模型 | SMC | RMC | MC | 续答题数 | 三项满分率 |
|---|---:|---:|---:|---:|---:|
| [Astra 6 (max)](../site/models/astra-6-max/index.html) | 91.33 | 95.01 | 95.01 | 6 | 100%（6／6） |
| [Sol 6.1 (max)](../site/models/sol-6.1-max/index.html) | 91.33 | 94.93 | 95.01 | 7 | 100%（7／7） |
| [Sol 6.2 (max)](../site/models/sol-6.2-max/index.html) | 91.33 | 94.57 | 94.57 | 6 | 100%（6／6） |
| [Astra 6.2 (max)](../site/models/astra-6.2-max/index.html) | 89.73 | 93.80 | 93.80 | 7 | 100%（7／7） |
| [Astra 6.2 (xHigh)](../site/models/astra-6.2-xhigh/index.html) | 83.90 | 91.66 | 92.66 | 9 | 88.9%（8／9） |
| [Sol 6.2 (xhigh)](../site/models/sol-6.2-xhigh/index.html) | 83.23 | 92.36 | 93.61 | 10 | 80%（8／10） |
| [Astra 6 (xhigh)](../site/models/astra-6-xhigh/index.html) | 81.33 | 91.70 | 92.70 | 6 | 100%（6／6） |
| [Sol 6.1 (xhigh)](../site/models/sol-6.1-xhigh/index.html) | 70.50 | 89.98 | 92.15 | 8 | 87.5%（7／8） |
| [Terra 6.1 (max)](../site/models/terra-6.1-max/index.html) | 68.63 | 81.38 | 83.11 | 9 | 88.9%（8／9） |
| [Terra 6.1 (xhigh)](../site/models/terra-6.1-xhigh/index.html) | 64.75 | 80.03 | 81.25 | 9 | 55.6%（5／9） |
| [Claude Opus 5.5 (max)](../site/models/claude-opus-5.5-max/index.html) | 62.48 | 92.97 | 95.11 | 15 | 53.3%（8／15） |
| [Gemini 4 Neon (xHigh)](../site/models/gemini-4-neon-xhigh/index.html) | 61.17 | 86.54 | 93.08 | 18 | 11.1%（2／18） |
| [Claude Sonnet 5.5 (max)](../site/models/claude-sonnet-5.5-max/index.html) | 58.98 | 89.49 | 93.03 | 17 | 52.9%（9／17） |
| [Claude Opus 5.5 (xHigh)](../site/models/claude-opus-5.5-xhigh/index.html) | 57.22 | 89.96 | 92.30 | 17 | 35.3%（6／17） |
| [Gemini 4 Hydrogen (xHigh)](../site/models/gemini-4-hydrogen-xhigh/index.html) | 48.25 | 78.83 | 89.82 | 17 | 0%（0／17） |
| [Kimi 3.1 Pro (max)](../site/models/kimi-3.1-pro-max/index.html) | 46.38 | 72.29 | 76.93 | 19 | 42.1%（8／19） |
| [DeepSeek v4.1 Flash (max)](../site/models/deepseek-v4.1-flash-1017/index.html) | 26.25 | 64.09 | 76.93 | 26 | 3.8%（1／26） |

共采用17个配置的206份续答，102份达到续答自身的三项满分。满分率的分母是各配置选中的全部续答题，失败交付也在分母内，首答三项全满的免测题不计入；各配置的失分集合不同，该比例不是同题排名。总分由共享评分器逐题80／20折算，仍保留首答失分和续答退步。全部采用续答已完成AI数学审核，人工数学审核仍待完成。

Gemini 4 Neon新增18份正常续答，其中2份自身三项全满。Gemini 4 Hydrogen新增17份正常续答，其中1份续答本身通过严格评审、0份三项全满；AI审核由Sol 6.1（max）完成，人工审核待完成。GLM 5.3、Gemini 3.8 Flash与Gemini 4 Argon已从1.2.0下架，不再进入本版待测、画像名单或默认导出；1.1.0及更早成绩、原答与冻结包保留。其他入选配置继续等待回交，完整历史分发和采用经过见[续答说明](neutral-revision.md)。

成本计入206份有效续答的完整费用，复用调用各计一次；确认的纯系统失败仅留重试历史。耗时比较17个已结算配置共有计时的同一12道公开非Lean题，另列整章形式化。累计作答时长与并行批次跨度分别保留，缺失时间或用量保持未知。[续答包指南](neutral-revision-harness.md) · [计时说明](answer-timings.md)

[数学画像](mathematical-profile-revision.md)对采用续答独立审核论证、忠实度、审辨、深度和闭合，再逐题80／20折算，覆盖原35个数学家族。研究主动性始终只看首答，严格完成度直接取所选阶段的正式SMC。三份首答画像的来源绑定更正仍用于两个当前视图，原件、历史1.1.0和三项主分不变。[开放研究能力](open-research.md)另看五个共同开放家族的实际研究交付，不由分数或主动性换算。 [形式化能力](formalization-profile.md)采用Lean整体SMC，包含语义审计、初答工程和三轮对齐自查，在两个阶段保持相同；当前画像共九轴。

[续答满分率来源](../results/continuation-completion/v0.1.0/current.json) · [续答资源索引](../results/continuation-resources/v0.1.0/index.json)。公有文件只含允许公开的证据及匿名合并总分，完整私有题包和评审留在私库。最新已发布题包仍为1.0.0。

## 1.1.0：首答与原三轮自查

六道TX按[研究增量尺度统一复评](theorem-extension-reassessment.md)，原题、原答、原评与旧成绩保留。下表未加入1.2.0续答贡献。

39道初答（公25／私14）、35个数学家族，另有固定三轮Lean自查。书面35／Lean35／研究30，始终按完整100分报告，未测项保留未知范围。

| 模型 | Harness | MC | RMC（主分） | SMC | 主动／强收／总题数 |
|---|---|---:|---:|---:|---:|
| [Astra 6 (max)](../site/models/astra-6-max/index.html) | Codex CLI | 93.76 | 93.76 | 89.17 | 39／0／39 |
| [Sol 6.1 (max)](../site/models/sol-6.1-max/index.html) | Codex CLI | 93.76 | 93.66 | 89.17 | 39／0／39 |
| [Sol 6.2 (max)](../site/models/sol-6.2-max/index.html) | Codex CLI | 93.21 | 93.21 | 89.17 | 39／0／39 |
| [Astra 6.2 (max)](../site/models/astra-6.2-max/index.html) | Codex CLI | 92.25 | 92.25 | 87.17 | 39／0／39 |
| [Claude Opus 5.5 (max)](../site/models/claude-opus-5.5-max/index.html) | Claude Code | 94.32 | 92.00 | 59.42 | 39／0／39 |
| [Sol 6.2 (xhigh)](../site/models/sol-6.2-xhigh/index.html) | Codex CLI | 92.04 | 90.79 | 80.17 | 39／0／39 |
| [Astra 6 (xhigh)](../site/models/astra-6-xhigh/index.html) | Codex CLI | 91.45 | 90.45 | 79.17 | 39／0／39 |
| [Astra 6.2 (xHigh)](../site/models/astra-6.2-xhigh/index.html) | Codex CLI | 90.89 | 89.89 | 81.00 | 39／0／39 |
| [Dot Underlying (2026-11-08)](../site/models/dot-underlying-model-20261108/index.html) | Unknown¹ | 91.10 | 89.68 | 78.00 | 39／0／39 |
| [Claude Opus 5.5 (xHigh)](../site/models/claude-opus-5.5-xhigh/index.html) | Claude Code | 91.36 | 88.80 | 54.92 | 39／0／39 |
| [Sol 6.1 (xhigh)](../site/models/sol-6.1-xhigh/index.html) | Codex CLI | 90.68 | 88.51 | 68.00 | 39／0／39 |
| [Claude Sonnet 5.5 (max)](../site/models/claude-sonnet-5.5-max/index.html) | Claude Code | 91.95 | 88.20 | 55.42 | 39／0／39 |
| [Gemini 4 Neon (xHigh)](../site/models/gemini-4-neon-xhigh/index.html) | AGY CLI | 91.91 | 85.42 | 60.42 | 39／0／39 |
| [Gemini 4 Carbon (medium)](../site/models/gemini-4-carbon-medium/index.html) | AGY CLI⁴ | 92.89 | 80.85 | 64.50 | 38／1／39 |
| [Terra 6.1 (max)](../site/models/terra-6.1-max/index.html) | Codex CLI | 82.07 | 80.30 | 65.67 | 39／0／39 |
| [Terra 6.1 (xhigh)](../site/models/terra-6.1-xhigh/index.html) | Codex CLI | 79.71 | 78.50 | 63.00 | 39／0／39 |
| [Gemini 4 Hydrogen (xhigh)](../site/models/gemini-4-hydrogen-xhigh/index.html) | AGY CLI⁴ | 88.36 | 77.37 | 47.92 | 39／0／39 |
| [Gemini 4 Carbon (high)](../site/models/gemini-4-carbon-high/index.html) | AGY CLI⁴ | 89.62 | 75.89 | 32.83 | 38／1／39 |
| [Gemini 4 Argon (high)](../site/models/gemini-4-argon/index.html) | AGY CLI⁴ | 86.89 | 70.80 | 37.92 | 38／1／39 |
| [Kimi 3.1 Pro (max)](../site/models/kimi-3.1-pro-max/index.html) | Claude Code | 75.28 | 70.41 | 43.67 | 38／0／39 |
| [DeepSeek v4.1 Flash (max)](../site/models/deepseek-v4.1-flash-1017/index.html) | Codex CLI² | 76.71 | 64.23 | 25.83 | 37／1／39 |
| [Gemini 3.8 Flash (high)](../site/models/gemini-3.8-flash-high/index.html) | AGY CLI⁴ | 59.39 | 39.21 | 13.75 | 38／1／39 |

总榜默认按 SMC、RMC、MC 依次比较。切到其他口径时，所选分数排第一，其余两项仍按 SMC、RMC、MC 的优先级比较。分项榜使用本项成绩独立排序。三项均已结算且公布到两位小数相同的模型共享名次，例如第 1、1、3 名。

并列行、下载目录、续答汇总和运行记录按厂商与系列归组。同系列按型号标注的版本从新到旧，同型号按已知档位由高到低。成本、耗时和其他指标图仍先看各自指标，同值时沿用模型目录顺序。初答测试时间保存在来源记录里。

主动交卷与强收有内容互斥；强收表示留有可审核数学内容，MC可以为0。三轮自查另列，执行状态与完整区间见模型档案。后续测试完成结算并选定留档后再上榜。

### 部分测试：GLM

[GLM 5.3 (max)](../site/models/glm-5.3-max/index.html)退出主榜及分项排行，保留详情和已有证据。39道初答中21份正常交卷、5份强收有内容，三轮Lean自查未执行。按1.1.0的已确认贡献为MC42.04、RMC27.90、SMC14.08／100，完整区间见模型页；这些数值不表示所有规定测项已完成。退出排行依据是测试流程尚未完成，不设数学低分剔除门槛，原有失败与未测状态不重判。

⁴ AGY CLI留档中发现较严重的回传与终态处理缺陷，可能丢失模型回复或空等至超时。此类故障允许额外重跑，实际调用次数可能超过通常3次；已核实的末尾空等从展示耗时扣除，原始记录保留。正常交卷后不因数学错误重跑。

## Gemini 4 Neon xHigh · 2026-11-22

39道初答、三轮固定Lean自查与18份中性续答均正常交卷。1.1.0首答基线为 **MC91.9094／RMC85.4178／SMC60.4167**；1.2.0为 **MC93.0801／RMC86.5376／SMC61.1667**。18份续答中2份自身三项全满，其余保留有效贡献及具体错误；满分率不是同题排名。Sol6.1Max分组审核，主聊天复核并定稿，原始评审与最终判断分别留存；人工数学审核仍待完成。

整章形式化初答及三轮自查均核实92／92，诊断准确、无回退，完整三轮轨迹通过。初答内容可靠率 **91.17%**、完整目标达成率 **84.92%**，按共同697个承诺单元和149个完整目标独立审核。数学画像另有首答与含续答阶段，两率仍只描述首答。

运行使用AGY CLI，允许本地工具及预置公共依赖，禁止外部检索和工具联网；实际分批版本随来源保留。60份有效交付之外，13次有证据的纯系统中断留在重试历史，不进入有效尝试、成本、耗时或模型异常次数。所留有效运行记录中未确认模型或原生harness异常。

API Standard参考成本合计 **$137.8559499**，基础42份为$88.9622955，18份续答为$48.8936544；不是订阅实际账单。续答资源全额计入。整章形式化初答约 **41.94分钟**，三轮自查另计；比较图仍采用12道共有计时的公开非Lean题。另有一道初答的墙钟与单调时钟证据不一致，保持耗时未知，不影响这12题和整章计时。

[模型详情](../site/models/gemini-4-neon-xhigh/index.html) · [首答与三轮记录](../results/v1.0.0/gemini-4-neon-xhigh/20261122/record.json) · [续答采用层](../results/edition-reassessments/v1.2.0/gemini-4-neon-xhigh/20261122/public.json) · [资源汇总](../results/continuation-resources/v0.1.0/gemini-4-neon-xhigh-20261122.json)。私有题文、原答、判准与完整执行来源留在私库。

Gemini 4 Neon (xHigh) delivered all 39 initial answers, three fixed Lean self-checks and 18 neutral revisions normally. Its first-answer baseline is MC91.9094 / RMC85.4178 / SMC60.4167; edition1.2.0 gives **MC93.0801 / RMC86.5376 / SMC61.1667**. Two of18 revisions are full in all modes. All four chapter deliveries verified92/92 with accurate diagnosis and no regression. First-answer content reliability is91.17% and complete-goal attainment84.92%. Effective deliveries total **$137.8559499** at the retained Standard API reference tariff, including revisions in full. Thirteen confirmed system interruptions remain in retry history only. The shared12-task timing sample and separate41.94-minute chapter measurement are known; one other first-answer duration remains unknown because its clocks disagree. Sol6.1Max group reviews and the root's final judgments retain their attribution; human mathematical review remains pending.

## DeepSeek 中性续答 · 2026-11-20

DeepSeek v4.1 Flash（1017，max）的26道中性续答已结算：24份正常交卷、1份截止原稿仅计MC、1题截止无正文。1.2.0成绩为 **MC76.93／RMC64.09／SMC26.25**，续答自身三项满分1／26。新增参考成本$8.45，连同首答及三轮自查合计$14.86。原final、补回的原始交付附件、判分与130项独立五轴判断均已绑定来源；未新增作答。[详细审核](../results/edition-reassessments/v1.2.0/deepseek-v4.1-flash-1017/20261110/REPORT.md)

首答基线为MC76.7075／RMC64.2264／SMC25.8333；续答纳入后为MC76.9323／RMC64.0853／SMC26.2500。两题截止分别只计已核实原稿的MC78/100和无正文MC0，RMC／SMC均为0。该批新增的是原失分题中性续答，原39道初答及三轮自查、Lean成绩和历史审核不改。原内容两率与主动额外成果仍只读首答。

DeepSeek v4.1 Flash (1017, max) has 26 settled neutral revisions:24 normal finals, one cutoff manuscript reviewed for MC only, and one cutoff with no deliverable content. Edition1.2.0 gives **MC76.93 / RMC64.09 / SMC26.25**, with one of26 revisions full in all modes. Revisions add $8.45 in reference cost, totaling $14.86 with the original answers and three self-checks. Native finals, recovered original delivery files, mathematical judgments and130 independent five-axis judgments remain source-bound; no candidates were called again. [Detailed review](../results/edition-reassessments/v1.2.0/deepseek-v4.1-flash-1017/20261110/REPORT.md)

## Astra 6.2 xHigh · 2026-11-20

本轮采用已完成的原答与原AI评审，不重跑候选。39道初答、三轮固定自查和9份中性续答全部正常交卷；1.1.0首答基线为SMC **81.0000**、RMC **89.8917**、MC **90.8917**，1.2.0为SMC **83.9000**、RMC **91.6633**、MC **92.6633**。9份续答中8份自身三项全满；原1.1.0判断、原始请求、首份正常交卷与封存工程保持来源绑定，该模型没有回填1.0.0成绩。

Sol6.1Max审核22份非Lean首答、8份Lean首答与三轮自查及6份命题拓展续答；主聊天审核9份论证审阅／手稿首答与3份续答，并作Lean语义抽查及最终验收。C003初答与三轮均核实92/92，三轮诊断均30/30，保留原FULL／KEEP和实际源码。全部为AI数学审核，人工数学审核仍待完成；编译证据与运行边界另行保留。

运行请求为gpt-6.2-astra/xhigh，通过OpenAI API、default服务档，使用Codex CLI0.169.1。53次数学物理调用包括51次有效尝试与2次已确认系统排除：1次容量错误、1次网络断流。独立canary预检的2次物理调用不进入正式分母或资源。42次基础交付记录580个本地命令完成事件，9份续答另有60个；允许本地工具及预置公共依赖，禁止外部检索和工具联网。后端SKU与内部HTTP调用数保持未知。

首答内容可靠率 **100.00%**、完整目标达成率 **84.28%**，按共同697个承诺单元与149个完整目标独立审核；不把忠实性缺口直接转作内容错误。五份首答手稿核实 **4组**主动额外成果，续答中的受邀拓展不计入该观察。数学画像可在首答与含续答间切换，严格完成度分别读取81.00与83.90，主动研究性两阶段相同。

51次有效尝试的完整原生用量合计46,604,269 tokens，按已留存Astra6.2 Standard短上下文费率折算为 **$77.744974**；基础42次为$63.7598564，续答9次为$13.9851176，续答资源全额计入。有效作答累计17,439.698899秒，确认系统重试的452.769696秒只留历史。初答中位数约3.26分钟，固定三轮另计；比较图仍采用原有12道共有公开非Lean题和独立整章计时，累计作答时长不当作同题速度或并行跨度。

[模型详情与公开题证据](../site/models/astra-6.2-xhigh/index.html) · [首答记录](../results/v1.0.0/astra-6.2-xhigh/20261120/record.json) · [公开原答与评审](../results/v1.0.0/astra-6.2-xhigh/20261120/report.md) · [1.2.0续答采用层](../results/edition-reassessments/v1.2.0/astra-6.2-xhigh/20261120/public.json)。私有题文、原答、逐项判准与原生来源留在私库。这批入库和页面更新仅在本地，未提交、推送或发布。

The completed Astra 6.2 xHigh answers and their original AI judgments are adopted without new candidate calls. All 39 initial tasks, three fixed self-checks and nine neutral revisions delivered normally. Its 1.1.0 baseline is SMC 81.0000 / RMC 89.8917 / MC 90.8917; edition 1.2.0 gives **SMC 83.9000 / RMC 91.6633 / MC 92.6633**, with eight of nine revisions full in all modes. Sol6.1Max and the root reviewer retain their actual review attribution; human mathematical review remains pending. Codex CLI0.169.1 used the OpenAI API's default service tier, with backend SKU and inner HTTP counts unknown. The 51 effective attempts cost **$77.744974** at the retained Standard short-context reference tariff and total 17,439.698899 seconds. Two confirmed system failures retain 452.769696 seconds in retry history only. First-answer content reliability is 100.00% and complete-goal attainment is 84.28%; four additional-result groups are verified across five first-answer manuscripts. Both remain first-answer diagnostics. The profile offers both stages, with strict completion 81.00 / 83.90 and unchanged initiative. Shared-task timing keeps the original 12-task sample and a separate chapter measurement. These changes are local.

## Claude Opus 5.5 (xHigh) · 2026-11-19

本轮为外部便携题包的首次评审：题源1.0.0，采用当前1.1.0标准。Claude Code2.1.303、Opus5.5 xHigh，允许本地工具，不联网。Sol6.1Max分三组并行全审；39道初答和三轮固定自查均正常交卷。MC **91.3606**、RMC **88.7981**、SMC **54.9167**；首次与规则重试视图相同。

C003初答及三轮均核实92/92，原FULL／KEEP与源码分别保留。R1把清单未要求的进一步加强误称为原稿缺陷，三轮诊断分别10/30、30/30、30/30；工程无回退、无虚报完成，整段SMC不通过。首个R1请求的原生畸形／截断返回经日志核实后作为纯系统故障排除，实际43次物理请求与42次采用交付分别留档，原记录字段不回写。

内容可靠率 **93.33%**、完整目标达成率 **87.12%**，按697项承诺和149个完整目标独立核查；额外成果观察为13组，只作中性参考，不抵销原题错误。42份采用交付共 **47,305,953 tokens**，原生list参考成本 **$104.18**。合计原生终态耗时470.78分钟，表示各次作答累计，不能当作并发批次的日历耗时。

[模型详情与25道公开题证据](../site/models/claude-opus-5.5-xhigh/index.html) · [完整自评与评分档案](../results/v1.0.0/claude-opus-5.5-xhigh/20261119/record.json) · [公开审核报告](../results/v1.0.0/claude-opus-5.5-xhigh/20261119/report.md) · [便携来源说明](result-record-editions.md)。私有题的原答、逐项判准、运行日志和完整来源证明留在私库。

## Astra 6.2 Max · 2026-11-19

本轮使用1.0.0题库，按1.1.0标准首次评审；39道初答和三轮自查全部正常交卷。对照 Astra 6 Max 的15份研究原答后，更正了一份私有手稿的结构忠实性判断，以及公开TX002的研究增量判断：后者已给出足够确定矩形行进的完整行列机制，按既有结构等价规则计R3。题面、原答与初评保留，未补跑。当前MC／RMC均为92.2528，SMC为87.1667。

与 Astra 6 Max 当前1.1成绩相比，MC／RMC少1.5111、SMC少2.0000。剩余差异来自一份手稿尚未完成的目标，以及两道拓展题确实少交付的局部研究成果；没有因路线或表述不同另扣分。书面与Lean贡献相同。内容可靠率100.00%、完整目标达成率90.45%；数学画像另按原答独立审核，人工审核仍待完成。

五份手稿核实4组主动额外成果。随后对旧模型的完整原答复核中，旧Astra 6 Max当前核实4组；此前观察与审核保留，新裁决经具名补充选入当前版。这些组数不进入主分或两率，1.0.0页面保持不变。

请求gpt-6.2-astra/max，使用Codex CLI0.169.0-alpha.11.1；后端型号和effort未独立回显。45次物理请求含3次有证据的纯系统中断，42次选定交付均为首次有效作答，共记录666个本地命令完成事件。允许本地工具及预置公共依赖，禁止联网检索与工具联网。39份初答原生执行耗时中位数约8.12分钟；整批跨度约5小时10分，包含并行、暂停与恢复。三轮自查另计。42份采用交付按[官方Astra 6.2 Standard短上下文价格](https://developers.openai.com/api/docs/models/gpt-6.2-astra)折算的API参考成本约$77.46；它不是订阅扣费，也不声称已还原逐次请求的长上下文计价，详见[成本口径](cost-reference.md)。这批答案没有1.0.0成绩，旧版不回填。

## Sol 6.2 xHigh · 2026-11-19

本轮使用1.0.0题库，按1.1.0标准首次评审；39道初答和三轮自查均正常交卷并完成AI审核。MC为92.0378，RMC为90.7878，SMC为80.1667。十二个书面证明家族及全部Lean任务、自查均获满分；论证审阅仍有遗漏和一处错误指认。研究部分的主要差异在命题拓展的增量与手稿的任务完成、结构忠实度。分项和公开逐题依据见[模型详情](../site/models/sol-6.2-xhigh/index.html)。这批答案没有1.0.0评分，旧版页面不回填它的成绩。

内容可靠率99.73%、完整目标达成率87.57%；五份手稿经全文复核后核实8组主动额外成果，该观察不计入主分或两率。数学画像独立审核，原答、评审依据与未知后端信息均保留；人工审核仍待完成。

请求gpt-6.2-sol/xhigh，使用Codex CLI0.169.0-alpha.11.1；后端型号与effort未回显。42次规定交付均为首次有效作答，无模型重试或纯系统排除，实际执行406个本地命令。允许本地工具及预置公共依赖，禁止联网检索与工具联网。39份初答原生耗时中位数约3.93分钟；整批跨度约2小时9分，包含并行，不能当作串行推理时间。三轮自查另计；42份交付按同一Sol 6.2 Standard单价折算的API参考成本约$14.93，不表示订阅实际扣费。

## Sol 6.2 Max · 2026-11-18

本轮为1.0.0题库的全新测试，39份正常初答及三轮正常自查均已审核。按1.1尺度，MC/RMC为93.2083，SMC为89.1667。相较Sol 6.1 Max，MC下降0.5556、RMC下降0.4556、SMC持平；主要差异是公开命题拓展TX001保留正确基础证明，但未完成上一版答卷中已有的尖锐性拓展。另有一份私有手稿消除了旧答独立附带错误的扣分。其余37题及整段自查的评分一致，不能据这两题推断普遍提升或下滑。1.0原判的差值保存在原档，1.1将旧TX001单锐性例从R2归为R1。

2026-11-19再次对照两代未满分项的原答，六道拓展题及唯一非研究低分题AR003均未发现漏分或尺度不一。AR003两代同为95/100、SMC不通过，均未核查映射空间底集与拓扑的宇宙小性；TX001的新旧差异来自旧答明确交付的二次多项式尖锐性例，而非评审偏好。当前成绩保持不变。

内容可靠率100.00%、完整目标达成率90.92%；五份手稿的主动额外成果已按共同边界审核，观察结果不计入主分。实际43次物理请求含1次已证实的控制器误拦截；该次不占有效模型次数，选定42次交付均为首次有效作答。请求gpt-6.2-sol/max，CLI版本0.169.0-alpha.11.1，后端标签未回显。全部允许本地工具，禁止联网检索和工具联网。

39份初答的原生执行耗时中位数约8.19分钟，三轮自查另计；实际批次跨度约4小时47分，包含并行、暂停与控制器恢复，不作为模型纯推理速度。原生用量完整保留；按已核实的Sol 6.2 Standard公开单价折算，采用42份答卷的API参考成本约$17.35，沿用原榜口径，不表示实际订阅扣费。AI审核、编译证据与人工批准继续分开。

## 本次方法调整

每题采用首次正常交卷，随后停止，不为数学错误重跑。有正常交卷时，三种评分只审核实际交付的正文及明确提交的工程；未随答复交付的更大封存工程不补入。

没有正常交卷时，MC可以审核本条件内最后一次有效尝试在截止前已存在的原始数学正文或完整工程文件。来源、截止与数学内容须分别核实；不能修补源码、拼尝试、把数值脚本当作证明或从思考日志拼出答案。RMC与SMC为0。未测研究题继续保留潜在得分和扣分范围。

既有初答按已有原件完成提交分类和来源复核；另有具名C003补充测试，三轮来源单独登记。原0.8.0政策、原记录和六视图按散列另存；原答、原评与题目保留原字节。规则见[提交来源规范](../protocol/submission-scoring.md)。

## 来源复核要点

- Terra Max按实际正常答卷采用C003初答18/92及三轮0→0→33；诊断分仍独立审核。旧74/92等额外封存工程不补入正常交卷。
- Gemini 3.8的HCH02正常返回原模块未通过内核，按0/40；错误核验保证另行扣罚。其C003无正常交卷轮次的截止原工程仅可计MC，正常轮次只审实际返回。
- DeepSeek的GR023截止正文保留有效MC；没有正常交卷，RMC与SMC为0。
- GLM的39份初答来源审核完成，三项末次缺档已由2026-11-11补充材料复核销项，原分数不变；三轮自查未执行，继续保留未知。[补充复核记录](../results/v0.6.0/glm-5.3-max/20261110/review-completion.json)。
- Argon采用20261111完整记录：37份原CLI正常交卷，另接纳1份因harness回传故障而恢复的HCH02原答；C003仍无正常交卷；另从新订阅封卷工程完成C003固定三轮补充自查，以正常最终回复及完整工程交付。首答和规则重试条件各绑定自身实际尝试，不交叉借用工程。

## 内容可靠率与完整目标

两率使用共同697个承诺单元与149个完整成果目标。内容可靠率检查实际断言的正确性和论证支持；目标达成率验收完整独立成果，保留类别、家族和变体权重。正常答卷来源发生更正时另行复核，原审核仍保留。定义、目标和权重没有增加。

| 模型 | 已审内容可靠率 | 已确认目标达成率 |
|---|---:|---:|
| [Astra 6 (max)](../site/models/astra-6-max/index.html) | 100.00% | 90.92% |
| [Sol 6.1 (max)](../site/models/sol-6.1-max/index.html) | 99.90% | 90.92% |
| [Sol 6.2 (max)](../site/models/sol-6.2-max/index.html) | 100.00% | 90.92% |
| [Astra 6.2 (max)](../site/models/astra-6.2-max/index.html) | 100.00% | 90.45% |
| [Astra 6.2 (xHigh)](../site/models/astra-6.2-xhigh/index.html) | 100.00% | 84.28% |
| [Claude Opus 5.5 (max)](../site/models/claude-opus-5.5-max/index.html) | 94.22% | 85.84% |
| [Sol 6.2 (xhigh)](../site/models/sol-6.2-xhigh/index.html) | 99.73% | 87.57% |
| [Astra 6 (xhigh)](../site/models/astra-6-xhigh/index.html) | 98.68% | 87.36% |
| [Dot Underlying (2026-11-08)](../site/models/dot-underlying-model-20261108/index.html) | 99.65% | 85.29% |
| [Claude Sonnet 5.5 (max)](../site/models/claude-sonnet-5.5-max/index.html) | 90.83% | 83.38% |
| [Sol 6.1 (xhigh)](../site/models/sol-6.1-xhigh/index.html) | 98.93% | 82.61% |
| [Terra 6.1 (max)](../site/models/terra-6.1-max/index.html) | 97.93% | 72.51% |
| [Gemini 4 Carbon (medium)](../site/models/gemini-4-carbon-medium/index.html) | 93.59% | 83.60% |
| [Terra 6.1 (xhigh)](../site/models/terra-6.1-xhigh/index.html) | 99.80% | 69.67% |
| [Gemini 4 Neon (xHigh)](../site/models/gemini-4-neon-xhigh/index.html) | 91.17% | 84.92% |
| [Gemini 4 Hydrogen (xhigh)](../site/models/gemini-4-hydrogen-xhigh/index.html) | 90.53% | 78.42% |
| [Gemini 4 Carbon (high)](../site/models/gemini-4-carbon-high/index.html) | 88.92% | 84.24% |
| [Kimi 3.1 Pro (max)](../site/models/kimi-3.1-pro-max/index.html) | 91.14% | 68.03% |
| [Gemini 4 Argon (high)](../site/models/gemini-4-argon/index.html) | 83.13% | 69.78% |
| [DeepSeek v4.1 Flash (max)](../site/models/deepseek-v4.1-flash-1017/index.html) | 76.64% | 57.36% |
| [Gemini 3.8 Flash (high)](../site/models/gemini-3.8-flash-high/index.html) | 65.28% | 38.79% |
| [GLM 5.3 (max)](../site/models/glm-5.3-max/index.html) | 69.48% | 32.44% |

Carbon Medium内容可靠率93.5938864629%、完整目标达成率83.60%；697项断言与149项完整目标均已判定。本次只更新最后强收手稿的来源与相应成果判断，其余38题及固定三轮自查不改判，断言／目标契约与权重不变。

[两率规则](../protocol/content-rates.md) · [主动额外成果观察](manuscript-observations.md)。旧19个模型的五道手稿已按完整原答、原先绑定的交付附件和共同边界重新核实；额外成果由51组更正为112组。最新Astra 6.2 Max的4组及Opus 5.5 xHigh的13组未重审。计组不使用高价值门槛，同一机制的定理、引理及直接推论合并；原任务本身的完成步骤不计额外。当前21模型覆盖100／105个已交付可审手稿槽，另5槽未正常交付；原观察、主分、两率及1.0.0数据保留。数学画像另经[统一核心复核](mathematical-profile-recheck.md)：现行0.4.0覆盖全部21模型，论证按原题核心成立验收，严格完成度直接取正式SMC；当前工作树只保留现行画像。

## 记录与复算

模型详情展示大类、子类、公开逐题结果、固定自查轨迹、完整原答和来源。所有图表读取共享评分器，排序和指标显示设置只影响页面。耗时表位于能力榜单底部，解释见[时间记录](answer-timings.md)。

所有正式任务允许本地工具及预置公共依赖，禁止联网检索与工具联网；实际工具使用和harness版本按来源批次记录。纯系统故障凭证据排除；最大输出耗尽消耗有效尝试；正常数学错误不再重试。

当前结果采用AI审核，并有部分人工抽审。既有全审记录由Sol 6.1 Max完成，Astra 6 Max／Dot抽审核对；Carbon保留本轮AI审核来源。[审核说明](review-process.md)。

[当前排行榜](../site/index.html) · [评分规范](../protocol/benchmark-scoring.md) · [完整档案](../results/README.md)

1.0.0通过[源绑定兼容记录](../releases/v1.0.0/compatibility.json)复用既有答卷及当前判分。原答、原评、六种成绩视图和实际运行版本保持不变；新版本不代表重新运行。评分组件的独立版本号沿用原值。

HCH02恢复原答的更正于2026-11-13按用户确认计入，原判分标准和benchmark1.0.0不变。该原答代码块原样编译失败，核验承诺按Flash同题标准扣罚；C003补测前的总分为MC77.00／RMC60.91／SMC37.92。原始ERROR、原记录及旧成绩保留，见[更正说明](harness-corrections.md)。

Gemini 4 Hydrogen（xhigh）使用AGY CLI1.5.7订阅完成39道初答与三轮固定自查。整章形式化首答及三轮均核实92/92；R1、R2诊断不准确，自查SMC不通过。三大类RMC贡献为书面25.30/35、Lean33.33/35、研究18.18/30；所有评分使用同一批规则选定答卷。本次没有新增人工数学批准。

Argon于2026-11-14通过AGY CLI1.5.9订阅完成三轮整章工程补充自查。初答封卷与三轮工程均核实92／92，无回退；R2虚述未提供的全空间接口，R3大量声明与章节定位失实。按原70／30规则，三轮100／95／85，自查计9.33／10，整段SMC不通过；当前总分MC86.33／RMC70.24／SMC37.92。原39个初答、HCH02更正及正常交卷38／39保持不变。见[补充条件与统一准入](c003-sealed-continuation.md)。

Flash于2026-11-15（新加坡时间）通过AGY CLI1.5.9订阅完整补跑三轮。父工程与三轮均核实74／92，新增修复与回退均为0；R1只整理已有定理别名、映射和未导入草稿，R2／R3的Lean源码及对齐表相同。编译与公理检查通过，但18项语义缺口仍在。三轮均诊断0／30并误报完整，各扣20分，自查分项MC0／RMC−2／SMC0（满分10），当前总分MC59.94／RMC39.77／SMC13.75。原39份初答与旧报告保持，详见[三轮结果](../results/v0.6.0/gemini-3.8-flash-high/20261105/supplements/c003-20261114/README.md)。


## Carbon整轮运行与来源说明

一项私有手稿题在三次有效尝试后仍无正常交卷，现仅按最后一次截止时封存的完整原稿评审MC，RMC／SMC为0。三项总分为91.78／79.74／64.50；未改规则、未合并前轮内容。 原采用尝试与旧评审保留，新增审核单独绑定原稿及截止记录。

[Carbon Medium模型详情](../site/models/gemini-4-carbon-medium/index.html)与[公开来源选择说明](../results/v0.6.0/gemini-4-carbon-medium/20261115/source-selection-disclosure.json)保留采用边界。当前MC91.78／RMC79.74／SMC64.50，38份正常交卷、1项强收有内容，无空白初答。2026-11-15新加坡时间01:00后额外补测C003，累计物理第7次／有效第6次正常交卷；实际初答及三轮KEEP均AI核验92／92，诊断准确、无回退，整条轨迹Strict通过。此前五次有效失败及物理第6次原ERROR均保留；物理第6次已证明是本地控制器误拒原生上下文压缩，单独排除，不计模型尝试。初答用时116分23.8秒，三轮合计34分30.1秒；首次口径及其余38题保持。

包含High、Medium与环境排查的旧批次及排查从2026-11-11 17:01:45 UTC延续至2026-11-14约14:30 UTC，随后本次C003补测于2026-11-14约21:17 UTC结束，跨越两天以上；旧Medium批次窗口约47小时40分，此后另行补测C003。两者表示不同范围的经过时间，均包含等待与运行中断。AGY/GCP期间频繁断流、超时与HTTP429；这些记录影响未交卷的归因。Argon与Carbon的已审复杂题同时暴露出严重推理错误及完成问题。最初的High批次未形成可用的成套答卷；2026-11-15续跑已完成结算。

本次来源采用包含用户观察后明确接纳的额外补试；原物理次数、有效次数与此前失败均保留，第4／5次没有改写成通常三次以内的重试资格。正常交卷锁定来源，不因数学错误重跑，不挑最高分、不跨尝试拼卷。AI评审、人工待审与原比较资格分别保留；用户接纳来源不构成人工数学批准。

当前API参考总额为$56.9869815：唯一无回执的内部请求经Infra Sentinel核对后，按用户确认以0补记费用；安全审核辅助调用不计入。原生用量缺失状态保持，原答卷保留题源版本0.6.0身份，通过独立的来源兼容记录接入当前benchmark1.0.0；本次整理与接入不再调用候选模型。


Carbon High 的 2026-11-15 续跑现已结算：39道初答中38份正常交卷、1项强收有内容、0项无可审核正文；MC／RMC／SMC为88.51/74.78/32.83。先测非Lean题，再测Lean题，最后接续C003及固定三轮自查；成功试跑直接留作正式答卷。AGY1.5.9后继原生请求的HIGH／MEDIUM档位按原请求保留；已确证的本地控制或认证TLS故障单独留证，不消耗有效尝试；无法确证为纯系统故障的断流保留原计次，作答超时和输出耗尽计次。逐题数学判断、三轮状态及实际条件见[模型详情](../site/models/gemini-4-carbon-high/index.html)和[来源说明](../results/v0.6.0/gemini-4-carbon-high/20261115/source-selection-disclosure.json)。

Carbon High 的完整历史补充见[尝试与重试统计](execution-attempts.md)：共62条任务尝试记录，其中51次有效、11项系统排除；42个规定槽外额外20条，包含9次有效重试。旧异常表的7条为早期时间截点的部分样本，保留原值和原归因。该补充不改变答卷来源、任何分数或原生执行记录。

本批High保留共同697项断言和149项完整目标合同；三种分数、两率、时间与费用均绑定同一批规则选定来源。采用尝试API参考$73.52，42份采用交付的原生用量均已对齐；其他重试与安全审核辅助调用另存，不计入该参考总额。
