# 研究主动性：共同拓展机会 0.1.0

本标准只更新 **1.3.0 的研究主动性画像**。它观察模型在原要求之外实际做了哪些有数学依据的推进，不改变 MC、RMC、SMC、开放研究能力或其他画像轴。原答、原评、旧 E 档和历史版本保留；本轮不重新调用被测模型。方法是在已知既有总体表现后调整的，机会集在本轮逐答复核前按题面固定，不是盲测设计。当前为 AI 复核，人工数学审核待完成。

## 共同机会集

原题中纳入 27 个数学家族：书面论证 12、命题拓展 6、背景核查 4、手稿 5。它们都直接要求开展数学工作，并允许在同一问题附近进一步检查条件、范围、结构或障碍。每题分别保留全部必做目标和额外研究的边界。附列方向只是例子，其他有依据的自然问题也可接受。

四个限定论证审阅家族、四个 Lean 家族不进入这个分母。这些题的原指令要求限定范围的检查或已有义务的形式化，准确完成后停止是合适的行为。它们的原答和额外观察仍保留，论证、审辨、形式化及完成情况照原规则评估。

另加入独立开放研究题三轮中的一个**额外自主推进机会**，共 28 个机会，全部等权。三轮只计一个机会，不按稿数增加权重。它最多贡献 \(100/28\approx3.57\) 分，与一个旧题机会相同。旧题使用原首答；新题来自既有三轮研究环境，两种实际条件在来源中分别保留。中性续答不回填旧题的主动性。

机会集由题目要求决定，所有模型相同；不按某个模型探索了几题、旧分高低或已知覆盖重新选择分母。

## 统一 0–4 档

| 档 | 实际需要的数学行为 |
|---|---|
| 0 | 仅完成原要求、使用例行工具或重述结论；没有可核实的额外探究。空泛建议和无依据的附加断言也在此档。 |
| 1 | 自行检查一个有意义的额外边界、特例或锐性问题，并给出有效计算、例子或论证。 |
| 2 | 自行提出一个非平凡问题，交出实质探索，例如额外机制、构造、条件或具体障碍；可以尚未解决整个问题。 |
| 3 | 系统推进一个自然的额外范围或条件问题，取得已核实的关键进展，或建立精确的阻碍；问题、方法和范围清楚。 |
| 4 | 至少完成一个独立有用的研究单元：自行选择的问题、实质方法，以及成立的结果或严格障碍，连同依赖、适用范围和限制。一个强单元即可，不要求堆叠定理或文献首创。 |

负结果可以体现高主动性：例如严肃检验一个自然推广后，给出完整反例或证明所选路线的必要操作无法成立。仅提出猜想、表示打算研究，不能代替实际数学工作。例行特例或直接重排不能因写得很长而进入高档。

某个更强结果也用于原题证明，并不自动排除其额外价值；若它超出全部必做目标、具有独立用途且不是例行工具，仍可计入。反过来，必要引理、原题已要求的推广、修复和边界分类，不能重复记为主动性。数学内容决定边界，不要求答卷出现“主动研究”标题或问号。

原任务未完成，不自动抹去另一项独立成立的额外探究；原来的错误、跑偏和未交卷后果仍保留在主分、忠实度与完成度中。额外条件必须在原文中明示，不能由审核者事后补进原命题。未经证明的附加结论不计为成立成果，审核者也不能补写缺失机制。

## 新题额外推进与旧 E 档

新机会只看已交三稿中超出原登记研究范围的实质推进。原题的五个研究方向、所需基础与必要桥梁属于本题研究能力，不重复算额外主动性。

本次按上述同一 0–4 行为尺度独立复核三稿。**旧 E0–E3 评审及其数值原样保留，不直接转换新档。** 因而，一个在旧成果价值尺度下仅获较低 E 档的严肃负结果，仍须按它实际体现的探究过程判断。新主动性判断不改写旧 E、品味、研究能力或题分。

## 聚合、未知与证据

令 \(g_i\in\{0,1,2,3,4\}\) 是第 \(i\) 个机会的主动性档位，完整覆盖时

\[
I=\frac{100}{28}\sum_{i=1}^{28}\frac{g_i}{4}.
\]

机会未探索记 0；经证据确认的空白交付也记 0。真正未运行或缺少可采用原证据则保持未知，每个未知机会保留 \(100/28\) 分的区间，不按已知部分重新归一化。覆盖与得分分别展示，全部机会已审不等于满分。

每个判断绑定规则选定原答、同次明确交付的附件，以及已经接纳的同次截止成果；不引入隐藏思考、未交工作区、其他尝试或后来续答。正档须指出实际的额外问题、数学检查、非必做边界及原文字节引据。零档也须审阅完整可用交付，不由关键词检索或旧分自动生成。原始新评、协调者的具名校准及旧评分开保留。

公库只提供共同标准、合并指标、覆盖数及不透明来源散列；私有任务清单、逐答评审、理由和引文留在私库。`research_initiative.py` 负责机会与证据合同，聚合调用共享评分函数；`assess_research_initiative.py` 负责准备、采用和重放核验。所有步骤均不调用候选模型。

## English

The current 1.3 research-initiative profile uses 28 equal opportunities: 27 original mathematical-development tasks (12 written arguments, six theorem-extension tasks, four background checks and five manuscripts), plus one extra-scope opportunity from the retained three-round independent research task. Four bounded argument-review families and four Lean families are excluded. Accurate completion of a scoped review or supplied formalization does not require additional research. The selection follows original task requests, not observed model success.

All opportunities use independent 0–4 behavioral judgments: no supported extra inquiry; an actually checked local probe; substantive exploration of a nontrivial independent question; systematic progress or a precise barrier; and a coherent independently useful research unit with verified outcomes or a rigorous obstruction. One strong unit suffices. Literature novelty, many theorems and a solved open problem are not required. Required work, routine helpers, empty suggestions, unsupported claims and silent replacement of the original problem do not create initiative credit. A stronger independently useful result is not excluded merely because it also proves the requested claim.

The new extra-scope opportunity uses the same scale and weighs 1/28, rather than 20%. Its original E judgments remain unchanged source diagnostics and are not converted into the new grade. Required foundations and registered capacity directions are excluded. Original A1 behavior and the three-round research setting retain their actual, different conditions. Neutral continuations do not backfill legacy initiative.

Complete coverage is the equal mean of the 28 grades, scaled by 25. Settled blank deliveries are zero; genuine missing evidence retains fixed uncertainty instead of rescaling observed work. Reviews bind exact original deliveries, explicitly delivered companions and already admitted cutoff evidence. Original answers/reviews, historical editions, main scores and other axes remain unchanged. This is a post-observation AI reassessment with human mathematical review pending; no new candidate calls are made. Private task inventory, reasons and quotations remain private.
