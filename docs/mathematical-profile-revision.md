# 数学画像的两个阶段

评分版1.2.0提供“首答／含续答”切换。首答以原0.4.0画像和另列的证据一致性更正为基线；含续答使用已经采用的中性续答及逐题独立复评。当前页面另加入独立评审的[开放研究能力](open-research.md)，形成八轴；原有七轴和主榜权重不因此变化。现有五轴续答评审覆盖15个配置的171份既有续答，其他配置的续答画像保持待测，没有重新答题。

| 维度 | 首答 | 含续答 |
|---|---|---|
| 论证能力、问题忠实度、数学审辨力、数学深度、成果闭合度 | 原题及实际首答的独立数学判断，含明确采用的基线更正 | 入选题各自按80%首答等级＋20%续答等级合成，再按原家族权重聚合 |
| 严格完成度 | 正式1.1.0 SMC | 正式1.2.0 SMC，直接读取、不再折算一次 |
| 开放研究能力 | 五个共同开放手稿家族的独立0–4档判断 | 已采用手稿续答单独评审，逐题80／20合成；未选中家族保持首答 |
| 研究主动性（最后一轴） | 原题之外、未经邀请的自主推进，描述行为而非能力上限 | 沿用首答，不把统一研究邀请后的成果计入主动性 |

原有五个能力评审轴和研究主动性仍覆盖原35个数学家族；开放研究能力使用五个共同开放家族，两种覆盖分别显示。没有入选续答的题和全部Lean及原三轮自查沿用原证据。某题首答主分全满而免测，不意味着它的深度等画像维度自动满档。实际续答退步也保留，不挑两次中的高分。

原有独立评审轴使用全卷中适用的数学内容，包括书面论证、答卷审阅、Lean审计及形式化、背景核查、手稿完成和定理拓展；关联变体先在家族内合并，三轮自查沿用原分配。新开放研究轴只看明确要求发展数学想法的五个家族，完整做好原题即可获得最高档；固定证明和核查做完后停止不算能力失败。严格完成度则使用正式总分的权重，各轴保留各自的评价范围。

## 复评看什么

复评读取原题、提供材料、完整新答、明确交付附件与已采用的数学审核，分别给五轴的0至4档判断及原文证据。依据是[原画像标准](../protocol/mathematical-profile.md)，不是将MC、RMC、SMC或B/R等级换算成画像分数。

例如，补齐缺失的证明可以提高论证和闭合；证明更广泛的统一机制可以提高深度；准确发现自己的误判可以提高审辨。把一个替代模型研究得更加完整，若仍缺少回到原目标的必要对应，并不能提高忠实度。闭合的独立数学成果仍可在深度和闭合轴保留相应评价。

“含续答”呈现完整评测流程的折算表现；各模型再答的是自身失分集合，不是相同的第二套全卷。已有续答题数、补满率和分数变化作为旁列信息，不新增主分，也不据此声称统一条件下的学习或纠错能力。首答全满而免测的模型没有续答样本时，该率保持不适用。

## 证据与状态

首答画像原件、原政策和各次评审均保留；新画像由独立来源绑定记录组合。未测、原件不足和未完成画像评审保持未知，已结算的交付失败按实际交付规则评估。不能以首答值填作已评续答，也不能在未审核时用正常交卷或编译通过替代数学判断。

公开只提供各轴合并值、覆盖、阶段及不透明散列；私有题号、原答、逐题理由与引文保持私有。复评采用Sol 6.1 Max分组审核及协调者独立评审、统一复核，逐题保留实际评审归属；AI审核、实际形式验证与人工批准分别记录，人工数学审核仍待完成。新增候选调用为0。

原9个配置的340项判断保留，Claude／Kimi四个配置的340项判断继续采用；Astra 6.2 xHigh另有45项，DeepSeek另有130项独立五轴判断，合计855项。另经独立复核，三份旧首答画像的论证、忠实度和审辨等级与其自身引用的原评审证据不一致，分别由4档更正为2档；其余维度不变。这九项更正采用独立的来源绑定记录，在当前1.2.0的首答与含续答两种视图中使用同一基线。它们不计作续答退步，不更改MC／RMC／SMC；原0.4.0文件与历史1.1.0视图保留。更正仍为AI审核、人工待审。

Astra 6.2 xHigh在两套阶段均可单独选中比较；严格完成度直接使用首答SMC81.00与含续答SMC83.90。研究主动性始终沿用同一首答判断；首答两率和4组主动额外成果另列，不作为画像等级的换算输入。

新开放研究轴已独立审核22个配置的110份首答及32份已采用手稿续答，逐份记录建模、机制、条件边界和证明闭合的依据，共568项判断。核心缺口不能用其他成果抵补，附带错误只有通过明确的删除依赖检查后才可与已成立核心分开；原错误及SMC判决仍保留。完整标准、全部模型对照和来源索引见[开放研究说明](open-research.md)。

[完整方法](../protocol/mathematical-profile-revision.md) · [首答画像说明](mathematical-profile-recheck.md) · [续答规则](neutral-revision.md)

## English

Assessment 1.2.0 offers first-answer and revision-inclusive views. The current eight-axis profile separately adds [open research capability](open-research.md) while preserving the seven source axes and all main scores. Five original capability axes retain the 35-family weights and blend selected task grades as 80% first answer plus 20% adopted revision. Research initiative remains first-answer-only and is shown last as a behavioral trait. Strict completion reads official SMC for the chosen stage, without another blend. The new axis uses five common explicitly open manuscript families, with separate coverage and independent judgments of 110 first answers and 32 adopted manuscript continuations across 22 configurations.

The current review covers 171 existing revisions across 15 configurations and 855 independent axis judgments, with no new candidate calls. Exempt tasks and all Lean evidence stay unchanged. Regressions count; missing revision judgments stay unknown. A full main score cannot substitute for a profile judgment. Revision task counts, full-score rates and score deltas are supplementary observations over each model's own loss set, not a common second examination or a new score. Source answers and original judgments are retained; private mathematical evidence remains private. Reviews are AI assessments with human mathematical review pending.

A separate source-bound correction resolves three old first-answer profiles whose proof, fidelity and discernment grades contradicted their own cited evidence: those nine grades change from4 to2, with all other axes retained. Both current1.2.0 views use the same corrected baseline. This is not a revision regression and does not change MC, RMC or SMC. Original0.4.0 files and archived1.1.0 views remain unchanged. The axes cover applicable work across the full35-family suite, rather than only the theorem-extension tasks.

Astra 6.2 xHigh is selectable in both profile stages. Its strict completion reads the official first-answer 81.00 or revision-inclusive 83.90 directly; initiative retains the same first-answer judgment. First-answer content rates and the four surplus groups remain separate observations.
