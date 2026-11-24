# 研究主动性：统一机会复核

本轮只调整 1.3.0 数学画像里的“研究主动性”。它衡量模型在没有被要求时，实际追问并验证了多少有价值的数学问题；不表示开放研究能力的上限，也不以发散越多越好。主榜 MC、RMC、SMC、其他画像轴、原答和历史版本均保持原样。本轮复用已有答卷，没有重新考试。

## 机会与分数

先按原题要求固定共同机会集，再按同一标准读各模型的实际交付。原题采用 12 个书面论证、6 个命题拓展、4 个背景核查和 5 个手稿家族，共 27 个机会。任务本身限定较紧的论证审阅和 Lean 不进入分母。独立开放研究的三稿整体提供另外 1 个域外拓展机会，不按稿件数重复计入。

每个机会独立评 0–4 档，28 个机会等权，分数为各档的平均值乘 25。新题最多贡献 `100/28 ≈ 3.57` 分，替代此前占 20% 的混合。新旧题使用同一行为标准，原 E 档作为来源判断保留，不直接换算。

| 档位 | 实际做到了什么 |
|---|---|
| 0 | 完成原要求或使用常规工具，没有可核实的额外探究 |
| 1 | 实际检查一个有意义的额外边界、例子或锐性问题 |
| 2 | 对非平凡的自选问题交出实质构造、机制、条件或障碍 |
| 3 | 系统推进额外问题，取得关键进展或建立精确阻碍 |
| 4 | 完成一个独立有用、证明和范围明确的强研究单元；严肃负结果同样可以 |

必做的分类、纠错、条件检查和必要引理不能重复记为主动性。一个更强结果即使也用于原题证明，只要确实超出全部要求、独立有用且不是例行工具，仍可计入。4 档不要求文献首创，也不要求解决包含该结果的整个更大问题；例如明确限于非临界范围的完整定理，不因另一个端点尚未解决而自动降档。

100 分意味着每个机会都达到了 4 档，并非主动性的及格线。低分可能来自大部分首答克制地完成原题；研究能力应结合“开放研究能力”、数学深度与严格完成度一起看。更主动的行为也应结合问题忠实度判断是否适合实际工作。

经证据确认的空白交付或未进行额外探索记 0。真正未测或缺少可采用证据的机会保持未知，保留固定区间，不把已知部分重新归一化为满分。[完整标准](../protocol/research-initiative.md) · [机器可读参数](../protocol/research-initiative.json)

## 统一复核结果

审核范围为 20 个保留配置，每个配置固定 28 个机会。其中 17 个配置已有可采用的完整三轮独立研究；其余 3 个配置的新题机会保持未知。所有可用原答及明确交付附件均已按同一标准审阅。下表中的旧口径与新口径不是同一量尺，分数变化不代表模型能力退步或进步。

<!-- initiative-results:start -->

| 配置 | 旧展示口径 | 新主动性 | 已结算机会 |
|---|---:|---:|---:|
| Gemini 4 Neon (xhigh) | 33.24 | 43.75 | 28/28 |
| Claude Opus 5.5 (max) | 23.43 | 41.96 | 28/28 |
| Claude Opus 5.5 (xHigh) | 21.14 | 34.82 | 28/28 |
| Claude Sonnet 5.5 (max) | 19.43 | 33.93 | 28/28 |
| Gemini 4 Hydrogen (xhigh) | 18.14 | 33.04 | 28/28 |
| gemini-4-carbon-high | — | 28.57–32.14 | 27/28 |
| Astra 6 (max) | 12.57 | 23.21 | 28/28 |
| Sol 6.1 (max) | 19.86 | 22.32 | 28/28 |
| gemini-4-carbon-medium | — | 21.43–25.00 | 27/28 |
| Terra 6.1 (max) | 14.29 | 20.54 | 28/28 |
| Sol 6.1 (xhigh) | 9.71 | 19.64 | 28/28 |
| Sol 6.2 (max) | 17.00 | 18.75 | 28/28 |
| Sol 6.2 (xhigh) | 30.29 | 18.75 | 28/28 |
| Astra 6 (xhigh) | 14.29 | 17.86 | 28/28 |
| Astra 6.2 (max) | 9.71 | 16.07 | 28/28 |
| Astra 6.2 (xHigh) | 9.14 | 12.50 | 28/28 |
| dot-underlying-model-20261108 | — | 10.71–14.29 | 27/28 |
| DeepSeek v4.1 Flash (max) | 5.14 | 8.04 | 28/28 |
| Terra 6.1 (xhigh) | 9.71 | 7.14 | 28/28 |
| Kimi 3.1 Pro (max) | 6.29 | 3.57 | 28/28 |

<!-- initiative-results:end -->

当前 1.3 页面只展示该版本已采用的模型，不因这次补审扩大榜单名单。雷达图、按轴排名、表格和单模型下载共同读取新评审；覆盖单位单列为“拓展机会”，与其他轴的家族、Lean 子类及品味检查数分开。

## 证据与审核边界

四个新建 Sol 6.1 Max 审核上下文分别负责书面论证、命题拓展与背景核查、手稿、独立研究三稿，逐份阅读实际原文。协调者复核判断和任务边界，并对疑难证明进行交叉校准；初判、具名校准、引文和来源限制分别保留。采用的是规则选定首答、明确交付的附件及已接纳的同次截止内容，不加入中性续答、隐藏思考、其他尝试或未提交工作区。

这是已知旧总体表现之后设计的方法调整，机会集先于本轮逐答审核固定，并非盲测。原 E 及旧数学评审不覆盖；公开数据只提供合计、覆盖和不透明来源散列。私有逐答理由与引文保持私有。当前状态为 AI 复核，人工数学审核待完成。

## English

The current 1.3 research-initiative axis uses 28 equal, task-based opportunities: 27 original mathematical-development families and one extra-scope opportunity across the adopted three research manuscripts. Every opportunity is independently assessed on the same 0–4 behavioral scale. The new task can contribute at most 3.57 points, replacing its former 20% share; original E judgments remain unchanged and are not converted into the new grades.

Required proofs, corrections and routine tools do not count as unsolicited research. Verified further questions, sharp conditions, constructions and rigorous barriers do. One complete, independently useful unit can earn the highest grade without literature novelty or solving a larger problem. A score of 100 requires that level on every opportunity; it is not a passing threshold or a capability ceiling. Read initiative alongside open-research capability, fidelity and strict completion.

The reassessment covers 20 retained configurations. All 27 original opportunities are settled for each; 17 configurations have adopted three-manuscript evidence, while three retain an unknown new-task opportunity. Genuine unknowns keep their fixed interval instead of rescaling observed work. Fresh Sol 6.1 Max reviewers read the original deliveries and explicit companions, with attributed cross-review and coordinator calibration. This is post-observation AI review with human mathematical review pending. No candidate calls, main scores, other axes or historical editions are changed.
