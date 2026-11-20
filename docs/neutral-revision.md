# 1.2.0：中性续答

1.2.0增加一次完善自己原答的机会，只运行非Lean未满分题。候选拿到原题、自己的完整首答、通用标准和中性研究邀请，不拿外部旧等级、具体失分点或参考答案。已经满分的整题免测，Lean初答与三轮自查沿用原有结果。

每道入选题仍按原权重计算：**80%首答＋20%续答**，MC、RMC、SMC使用同一份续答分别折算。首答80、续答100的题得到84；首答0、续答100得到20。续答退步也会反映在这20%中。首答和续答的严格通过判断分别保存，因此最终分数既承认改善，也保留首次作答的差距。完整规则见[评分与执行协议](../protocol/neutral-revision.md)。

当前本地已采用15个配置的171份续答。原9个GPT配置共68份，包括首批19次新调用及3份观察后采用的旧中性试答，以及随后6个配置的46题。本次外部回交增加Claude Opus 5.5 Max／xHigh、Sonnet 5.5 Max和Kimi 3.1 Pro Max的68份正常交卷；分组审核并统一复核，逐题保留实际AI评审归属。题面、首答、各次初审与原研究记录不改写，另加入Astra 6.2 xHigh的9份正常续答，其中8份自身三项全满；只复用已完成答卷及原评，没有新增候选调用。人工数学审核仍待完成。

| 模型 | 续答题数 | 三项满分 | 满分率 |
|---|---:|---:|---:|
| Claude Opus 5.5 (max) | 15 | 8 | 53.3% |
| Claude Opus 5.5 (xHigh) | 17 | 6 | 35.3% |
| Claude Sonnet 5.5 (max) | 17 | 9 | 52.9% |
| Kimi 3.1 Pro (max) | 19 | 8 | 42.1% |
| Astra 6.2 (max) | 7 | 7 | 100% |
| Astra 6.2 (xHigh) | 9 | 8 | 88.9% |
| Astra 6 (max) | 6 | 6 | 100% |
| Astra 6 (xhigh) | 6 | 6 | 100% |
| Sol 6.2 (max) | 6 | 6 | 100% |
| Sol 6.2 (xhigh) | 10 | 8 | 80% |
| Sol 6.1 (max) | 7 | 7 | 100% |
| Sol 6.1 (xhigh) | 8 | 7 | 87.5% |
| Terra 6.1 (max) | 9 | 8 | 88.9% |
| Terra 6.1 (xhigh) | 9 | 5 | 55.6% |

三项满分指续答自身的未舍入MC、RMC和SMC均满；分母包含全部入选题，交付失败也计入，首答三项全满的免测题不计入。各配置的失分集合不同，这些比例不是同题排名。171份中100份三项满分；其余保留已核实的数学贡献、具体错误或任务对应缺口，不以改进幅度代替完整性判断。

完整100分中的新版成绩由共享评分器生成。本轮46道续答对应47次实际请求。Astra 6 Max一次请求遇到容量错误后到达截止，经用户观察后授权，以相同输入与配置恢复，得到首份正常交卷。两次请求及原截止都留档。用户随后确认故障归为系统重试，只有恢复计入有效资源。[结果页](results.md)

原外部分发包含11个配置的200题；已回交5个配置的94题，包括Claude三个配置、Kimi与DeepSeek。92份正常交卷，另有2题截止未交卷并按原成果边界结算；余下6个配置的106题待回交，GLM跳过。包内保留原题、配置自己的原答及交付文件、统一候选提示和回交工具；候选材料与评审材料分开。尚未回交项保持未知，不提前赋予提升。[续答包指南](neutral-revision-harness.md)

底层资源记录保留基础测试、采纳续答与合计。172次来源执行请求中，171次有效尝试全额进入续答资源统计，含3次各计一次的旧中性试答。20%权重只用于数学计分。已确认的容量和网络系统故障单列重试。首页成本参考显示合计成本，耗时参考采用12道共有计时的公开题并单列整章形式化。缺失时间或用量保持未知，累计候选执行时间和并行批次跨度分别保留。原内容两率与额外成果观察属于首答诊断，数学画像可独立切换首答与含续答阶段。[计时说明](answer-timings.md)

本次68份外部答卷与导出父答和实际提示逐字对应，原生最终事件与保存的正文一致。两次本地封卷恢复复用同一原生成功答卷，没有新增候选调用或重答。Kimi原生金额标记为未知口径，未作为实际计费；按已留存Kimi Standard费率对完整用量重算API参考成本，原始金额和核算依据另存。[成本口径](cost-reference.md)

GLM移入“部分测试”区域，保留已有成绩、来源和未测状态，退出排行。初答已完成来源核查，39题中21份正常交卷、5份强收有内容，三轮Lean自查未执行；该展示调整不删除或重判答卷。

## 1.2.0中性续答采用层

中性续答0.1.0使用单独的来源绑定记录，不将外部回交伪装为原CLI或native记录。每个续答绑定实际父答、完整题文／附件、通用提示、新原答与明确交付文件、执行收据及逐项评审。原A1、旧评、实际旧执行版本和当时非计分研究的声明保持原字节；观察后采用另记，不倒写预注册。

采用层保存首答与续答各自的三模式题分和严格二值判定，再由共享评分器逐题80／20折算。仅主条件父答相同的记录可复用，不能移植给不同原答。已完成、交付失败、未执行、来源不足和待评分别记录。外部导入只收存来源，不能在未审核时生成有效数学分。

公有投影只暴露允许的公有逐题材料与匿名合并总分、数量和不透明散列。私有题号、题文、原答、评审及执行源路径保持私有。候选包与操作者规则包分开，候选不接收旧等级或失分提示。[续答协议](../protocol/neutral-revision.md) · [回交指南](neutral-revision-harness.md)

DeepSeek本次26题由Codex coordinator按完整交卷及补回的原文件复核：1题续答自身三项全满，24题正常final；1题截止原稿仅评MC，另1题无正文计0。补件未产生新候选调用，原生final和已有原附件均保持原字节。新增判断的实际AI归属与五轴引文单独留存。[本批报告](../results/edition-reassessments/v1.2.0/deepseek-v4.1-flash-1017/20261110/REPORT.md)

## English

Edition1.2.0 adds one neutral revision for each non-Lean task with a confirmed loss in any of MC, RMC or SMC. The candidate receives the original task, its own complete first answer, generic standards and a neutral invitation, with no external grade, case-specific review or reference. Tasks already full in all three modes are exempt. Lean results remain unchanged.

Each selected task uses **80% of its first score plus20% of its revision score** in all three modes, retaining the original family weights and fixed100-point frame. Regressions count. Strict judgments for both deliveries remain binary and separate; their weighted contribution can be0,0.2,0.8 or1. A revision cannot erase the first-answer deficit.

The local edition includes 171 revisions across 15 configurations, with 100 full in all three unrounded modes. The original nine GPT configurations retain their 68 revisions and source history, including three reused neutral pilots and one confirmed capacity retry. The68 normally delivered external answers from three Claude configurations and Kimi remain adopted. Astra6.2 xHigh adds nine retained, normally delivered revisions, eight full in all modes, without new candidate calls. Their actual native finals, parent answers and prompts are authenticated; two local sealing recoveries did not call candidates again. Mathematical and profile judgments retain their actual AI reviewer attribution, with human review pending.

Of the original200 tasks packaged across11 external configurations,94 have returned from five configurations:three Claude configurations, Kimi and DeepSeek. They comprise92 normal finals and two settled cutoff deliveries. The remaining106 tasks across six configurations await returns; GLM is skipped. All171 effective adopted continuations across172 source execution requests enter resource accounting in full, with each reused pilot counted once. Confirmed system failures remain in retry history. The homepage compares15 configurations on the same12 shared public tasks, with the chapter run separate. Kimi uses the retained Standard reference rather than its native unknown-basis amount; DeepSeek uses the unchanged archived peak tariff and inclusive-cache receipt normalization. Original content rates and surplus observations remain first-answer diagnostics. The published task suite remains1.0.0; this adoption is local.
