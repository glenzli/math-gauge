# 评价版 1.1.0 · TX 研究增量

1.1.0 是在已发布 1.0.0 题库上新增的评审层。39 道初答、35 个数学家族、三轮 C003 自查、35／35／30 权重和全部原始题面保持不变。

本轮只修订六道命题拓展题的 R0／R1／R2／R3 尺度，再统一复评当前选定的历史答卷。其他题的数学判定、TX 的 B 基础判定、原有错误扣罚、交付来源与尝试选择均不变。没有新增求解器调用，没有更换答卷，也不合并多次尝试的数学内容。

## 研究增量与 SMC

| 等级 | 验收内容 |
|---|---|
| R0 | 没有经过核实的超题面研究增量。B2／R0 表示可见原题已正确证明。 |
| R1 | 有用的局部细化、定量信息、锐性或边界结果。 |
| R2 | 在具有实质范围的自然对象族上，完整解决一项新问题。 |
| R3 | 深入且完整的研究增量：自然范围、显著推进与关键论证闭合，并有足够的解释或系统处理能力。 |

这是开放的成果等级。参考给出充分锚点，不能成为唯一正确答案清单；强结论写在原证明内部也按相同尺度计分。不以篇幅、定理数、方法是否熟悉或是否单列“推广”评分。实际范围和证明必须由答卷交付，评审不能代补关键构造、量词、条件或桥梁。

MC、RMC 保留原来的分档算术和错误处理。没有其他罚时，MC 为 R／3，RMC 为 (R−D(B))／3；基础罚与普通罚仍按原 max 和根因去重规则组合，不直接重复累加。六家族等权分享 10 分，没有单题扣负截断。

**TX 的 SMC 保持二值：B2 且 R3 的成果完整成立，同时满足原有严格错误与正常交付规则。** 它表示充分研究增量是否完成，不改成另一种连续研究分。原题正确但没有拓展，不能描述为证明失败。

完整的通用标准、两道公开题的逐档锚点及边界见[冻结标准](theorem-extension-calibration.md)；另外四题的具体标准及全部逐题新评留在私库。政策绑定见[校准政策](theorem-extension-calibration.json)。

## 来源与复算

原 1.0.0 发布资产、兼容清单、任务与原始结果记录继续保持原字节。原答保留实际 0.6.0 或 1.0.0 执行身份；旧评分报告中沿用的 0.6.0 政策身份另列，不冒称这些模型在 1.1.0 重新参加测试。

新的 `results/edition-reassessments/v1.1.0/` 绑定完整的 1.0 来源快照、旧有效六视图、新量规、具名新评与当前六视图。HCH02 来源更正和 C003 补充自查先按其原身份接入，再应用 TX 复评。`scoring.py` 负责全部算术；公开只投影公开题与匿名合并成绩，私有标准、题号、原答及新评不外投。

内容可靠率、完整目标达成率、手稿额外成果观察、成本与耗时保留各自原有来源；R 改变不自动产生新的真假断言或完整目标判定。

本轮是允许参考既有答卷的**后验量规修订与统一复评**，并非盲测或预注册。通用准则由当前协调窗口、Astra 6 与 Sol 6.2 Max 商议，在正式新评分之前冻结。逐答审核注明实际 AI 评审者，人工数学审核仍待完成；三方讨论不等于每份答卷都经过三份独立审核。

英文说明 / English: Edition1.1 adds a post-observation, source-bound assessment layer for the six TX tasks. It retains the published1.0 task suite, all original answers and judgments, execution identities, fixed weights and delivery rules. R tiers measure the mathematical research increment actually delivered, accepting equivalent routes and proof-internal results. TX SMC remains binary: a correct baseline and a complete R3 contribution, subject to the original reliability and normal-delivery gates. There are no new candidate calls. Original score views remain unchanged; current scores are recomputed by the shared scorer. Private evidence remains private, and AI review is distinct from human mathematical approval.
