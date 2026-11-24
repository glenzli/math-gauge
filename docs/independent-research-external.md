# 1.3 外部答卷评审 · 2026-11-24

本轮采用 Claude Opus 5.5 Max／xHigh、Claude Sonnet 5.5 Max、Kimi 3.1 Pro Max 和 DeepSeek v4.1 Flash Max 的独立开放研究答卷。每个配置均保留三轮正常交付、原生证据、明确交付的附件及独立数学评审。Sol 6.1 Max 按题组并行审核，归档与采用不产生新的候选调用；当前为 AI 审核，人工数学审核待完成。

下表为新增研究题的百分制成绩。数学品味 T 与研究能力 C 按 `Q=(2T+C)/3` 汇合，Q 占整体榜单 10%；三种口径分别计算。其余部分使用同一份 1.2 来源答卷，按 30／30／30 保留到 1.3。

| 配置 | 新题 MC | 新题 RMC | 新题 SMC | 1.3 总榜 RMC | 新增候选参考费（USD） |
|---|---:|---:|---:|---:|---:|
| Kimi 3.1 Pro Max | 75.67 | 75.67 | 72.00 | 72.14 | 2.5847068 |
| Claude Opus 5.5 xHigh | 78.67 | 71.67 | 71.67 | 87.83 | 14.4660992 |
| Claude Opus 5.5 Max | 75.00 | 63.00 | 47.00 | 89.68 | 11.2651446 |
| Claude Sonnet 5.5 Max | 76.67 | 59.00 | 44.67 | 86.09 | 6.9469012 |
| DeepSeek v4.1 Flash Max | 68.00 | 59.67 | 40.67 | 63.26 | 0.249565896 |

同日，Kimi 经新建 Sol 6.1 Max 先盲复核、再对照旧评校准，按用户选择采用完整复评。数学品味 T 的 MC／RMC／SMC 为 87／87／87，研究能力 C 为 53／53／42。此次纠正一项研究覆盖验收，并收紧研究深度的连续评分；旧新题三分均为 80.67，现为上表数值。1.3 总榜 MC／RMC／SMC 相应更新为 76.34／72.14／48.29。原答、旧评和先前聚合快照保持原字节，新采用由具名更正记录绑定，不重新作答，候选用量与费用不变。

严格信用采用通过检查项所保留的实际净分；通过全部检查也不会把原本 86 分的成果自动变成 100 分。三轮有效成果、后续修正、反例和未闭合依赖按既定轨迹标准判断，重复内容不重复得分。五个配置的额外自主拓展均评为 E0；它不取消题内已经成立的研究成果，也不另扣主榜分。

成本计入三轮完整有效用量，合计新增 **$35.512417696**，沿用每个配置在 1.2 中的冻结 API 参考费率。Claude/Kimi 使用最终 session 累计值及逐轮差分，不能把三次累计快照相加。Kimi 原生费用的计价依据不明，使用可核对的用量重新计价。Sonnet 的累计值含两次内层重试；对应完整逐请求响应不齐，保留这一证据边界。评审费用未知，另列。独立研究不进入共有题耗时比较。

配置名与 effort 是实际可观察的请求标签，不表示已独立认证后台 SKU。Sonnet 与 Kimi 的原生请求均为 Max；DeepSeek 后两轮记录为只读工具权限，保留实际条件。DeepSeek 仅计确认有效的三轮，已确认的基础设施故障不计正式尝试和资源。原始容器、旧操作审计与后续操作者确认分别保留在私有归档。

外部采用使用[独立聚合来源](../protocol/mathematical-taste/v1.3.0/external-results.json)及[独立资源来源](../protocol/mathematical-taste/v1.3.0/external-resources.json)，不改写原十个 GPT 配置的冻结计划或成绩。页面由同一个评分投影驱动，更新总榜、T/C 分项、数学画像、交付覆盖、成本及下载。1.0／1.1／1.2 的答卷、评审和页面数据保持原字节。私有题文、研究方向、原答和逐项理由不进入公开输出。

## English summary

Five externally collected configurations were reviewed by Sol 6.1 Max and admitted locally to the 1.3 edition. Each has three original normal-final deliveries, including explicitly delivered attachments. The review is AI-only with human mathematical review pending. Item MC/RMC/SMC uses the existing 2:1 taste/capacity projection and contributes 10% of the overall score. Strict credit retains actual net credit rather than converting checkpoint coverage into a score.

A fresh Sol 6.1 Max re-audit of Kimi was completed before consulting its earlier grade, then calibrated against the retained evidence. The user selected the complete reassessment: taste is 87/87/87 and capacity is 53/53/42, giving item MC/RMC/SMC of 75.67/75.67/72.00 and overall scores of 76.34/72.14/48.29. The correction addresses one coverage judgment and research-depth calibration. Original answers, reviews and the prior aggregate snapshot remain unchanged; a named source-bound amendment selects the new review. No candidate rerun or candidate-cost change is involved.

The full effective candidate resource increment is **$35.512417696**, using the retained 1.2 API reference tariffs. Session cumulative receipts are counted once; reasoning and cached tokens are not charged twice. Evaluator overhead remains unknown. Independent research is excluded from shared-task timing comparisons. External sources have separate adoption and resource bindings; the original ten-configuration plan, scores and historical editions remain unchanged. Request labels do not authenticate backend identities.
