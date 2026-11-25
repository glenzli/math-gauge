# TX 研究增量复评 · 1.1.0

评分版本 **1.1.0** 校准了六道 TX 的 R1／R2／R3，统一复评已采用的 18 个配置。共核对 **216 个条件槽**（两种尝试条件），去重后为 **113 个答卷／无交付状态**；14 份答卷的 R 档改变。没有重新测试模型，只对原答卷按调整后的标准重新评价；SMC 判定与全部模型的 SMC 总分均不变。

这次调整区分“完成原证明”与“实际研究推进”，也纠正了同等内容因放在证明内外而给分不同的情况。单个锐性例通常是 R1；在自然对象族上完整解决新问题可达 R2；一项深入且完整的研究增量即可 R3，不要求照参考答案凑齐一套定理。经典方法、短证明与证明内部出现，都不是自动降分的理由；普通背景引理也不会仅因单列而自动升档。

TX 的 SMC 仍是二值：原题 B2 且完整达到 R3，并符合原有错误与交付规则。B2／R0 是原题正确、没有研究增量，不能描述为原题失败。具体判准见[冻结标准](../protocol/theorem-extension-calibration.md)和[1.1评审层](../protocol/evaluation-1.1.md)。另外四题的详细锚点和完整新评只在私库保存。

## 当前总分与变化

采用规则重试条件 `nonlogical_retry_3`，单位为完整100分中的已确认贡献。所有数值读取共享评分器的留档报告，未按已测比例重新归一化；未知范围继续留在模型页。原版本列指本次修订前已采用的有效来源视图，含当时已经接纳的来源更正和 C003 补充。

| 模型 | 原 RMC | 1.1 RMC | 变化 | 1.1 MC | SMC |
|---|---:|---:|---:|---:|---:|
| Astra 6 (max) | 94.32 | 93.76 | -0.5556 | 93.76 | 89.17 |
| Sol 6.1 (max) | 94.22 | 93.66 | -0.5556 | 93.76 | 89.17 |
| Sol 6.2 (max) | 93.21 | 93.21 | +0.0000 | 93.21 | 89.17 |
| Claude Opus 5.5 (max) | 91.44 | 92.00 | +0.5556 | 94.32 | 59.42 |
| Astra 6 (xhigh) | 90.45 | 90.45 | +0.0000 | 91.45 | 79.17 |
| Dot (261108) | 90.23 | 89.68 | -0.5556 | 91.10 | 78.00 |
| Sol 6.1 (xhigh) | 87.96 | 88.51 | +0.5556 | 90.68 | 68.00 |
| Claude Sonnet 5.5 (max) | 88.20 | 88.20 | +0.0000 | 91.95 | 55.42 |
| Gemini 4 Carbon (medium) | 79.74 | 80.85 | +1.1111 | 92.89 | 64.50 |
| Terra 6.1 (max) | 80.85 | 80.30 | -0.5556 | 82.07 | 65.67 |
| Terra 6.1 (xhigh) | 78.50 | 78.50 | +0.0000 | 79.71 | 63.00 |
| Gemini 4 Hydrogen (xhigh) | 76.81 | 77.37 | +0.5556 | 88.36 | 47.92 |
| Gemini 4 Carbon (high) | 74.78 | 75.89 | +1.1111 | 89.62 | 32.83 |
| Gemini 4 Argon (high) | 70.24 | 70.80 | +0.5556 | 86.89 | 37.92 |
| Kimi 3.1 Pro (max) | 70.41 | 70.41 | +0.0000 | 75.28 | 43.67 |
| DeepSeek v4.1 Flash (max) | 64.23 | 64.23 | +0.0000 | 76.71 | 25.83 |
| Gemini 3.8 Flash (high) | 39.77 | 39.21 | -0.5556 | 59.39 | 13.75 |
| GLM 5.3 (max) | 27.34 | 27.90 | +0.5556 | 42.04 | 14.08 |

## 审核与版本边界

通用准则与六题锚点由当前协调窗口、Astra 6、Sol 6.2 Max 商议；允许现有答卷作为尺度设计参考，在正式复评之前固定政策散列。逐答审核由实际承担该题的 AI 评审者完成，并对边界与变化交叉核对；不声称每份答卷都做了三份独立审核，也不把三方一致写成人工数学批准。

本轮是后验量规修订，不是盲测、预注册或新一轮求解器测试。新评绑定实际选定原答、旧评、新标准和有效旧报告的散列；旧 B、旧 R 和改判理由均保留。相同原文字节复用数学复评，但不同条件的选择与原评来源分别绑定，不跨尝试取并集或择优。

1.0.0 已发布题包、标签、资产与兼容清单保持不变。原0.6.0／1.0.0执行身份与旧六视图不改，1.1在独立[评审目录](../results/edition-reassessments/v1.1.0/transition.json)上叠加。聚合0.9.0／MC0.3.0／SMC0.2.0的算术、固定权重与分母不变；其余题的判定、错误扣罚、提交状态、两率、手稿观察、成本和耗时继续使用原证据。

公开题的模型页同时列出当前 R、复评理由和原答／原评链接；私有题仅进入匿名合并成绩。

## English

Scoring edition **1.1.0** calibrates R tiers for all six theorem-extension tasks and uniformly reassesses 18 retained configurations: 216 condition slots, or113 distinct answer/nondelivery states. Fourteen answer tiers change; all SMC decisions and overall SMC scores remain unchanged. The original answers were re-evaluated under the revised standards; no candidate was retested.

R1 recognizes useful local progress; R2 a complete substantive extension on a natural family; R3 a deep, complete research increment. Equivalent routes and results inside a proof count equally. A reference is an open anchor, not a required checklist. TX SMC remains binary: B2 plus a complete R3 contribution and the original reliability/delivery gates. B2/R0 means the visible proof is correct.

This is an explicitly post-observation rubric revision. The coordinator, Astra6 and Sol6.2Max agreed on standards before formal reassessment; actual case reviewers and boundary cross-checks are attributed separately. AI consensus is not human mathematical approval. All original source bytes, execution versions, reviews, old scores and1.0 release assets remain intact. Other mathematical judgments, weights, error penalties, rates, costs and timings are unchanged. The table above compares retained RMC before/after on the fixed100-point frame; SMC is shown in the final column.

核验范围及结果见[本地核验摘要](../results/edition-reassessments/v1.1.0/validation.json)。
