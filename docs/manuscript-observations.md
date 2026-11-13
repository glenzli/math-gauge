# 主动额外成果 · 观察记录

[数学研究分榜内展开](../site/index.html?category=research#research-initiative) · [观察规则](../protocol/manuscript-observations.md) · [记录索引](../results/manuscript-observations/v0.1.0/observations.json)

这里记录模型在原任务未要求的情况下，主动提出并实际交付了多少经核实的额外成果组。仅覆盖五道手稿题，复用规则选定A1；没有补跑，没有研究邀请，没有跨尝试拼接。

它描述这批答卷的主动探索行为，不表示研究能力，也不预设数量越多越好。原题完成质量、可靠性以及是否适合主动扩展范围须分别判断。没有满分、百分比、题目产出率或有限上限，不是独立benchmark，也不进入任何主分或两率。

| 模型 | 已核实额外成果组 | 已审手稿 |
|---|---:|---:|
| Gemini Hydrogen (xhigh) | 11 | 5/5 |
| Claude Opus 5.5 (max) | 6 | 5/5 |
| Claude Sonnet 5.5 (max) | 6 | 5/5 |
| Sol 6.1 (max) | 2 | 5/5 |
| Astra 6 (xhigh) | 1 | 5/5 |
| Sol 6.1 (xhigh) | 1 | 5/5 |
| Terra 6.1 (max) | 1 | 5/5 |
| Astra 6 (max) | 0 | 5/5 |
| DeepSeek v4.1 Flash (max) | 0 | 5/5 |
| Dot Underlying (2026-11-08) | 0 | 5/5 |
| Gemini 3.8 Flash (high) | 0 | 5/5 |
| Gemini 4 Argon (high) | 0 | 5/5 |
| GLM 5.3 (max) | 0 | 2/5 |
| Kimi 3.1 Pro (max) | 0 | 5/5 |
| Terra 6.1 (xhigh) | 0 | 5/5 |

* 尚未测完。所列为已核实组数，全部答卷的总组数未知；不按已审覆盖放大，不推算剩余题目可能产生多少组。排列只便于浏览，不列优劣名次。0表示这批已审原答中没有核实到符合门槛的成果组，不表示能力为零。

每个成果组须正确、原题未要求且非简单重复。价值取决于具体研究本体与用途，不设统一高价值门槛。正常纠错、补必要证明、原题要求的自选扩展、直接推论和等价改写不计；一个定理及必要引理、直接推论或在原答/稿件中的重复只计一组。同题可有多组，直接合计数量。

逐项数学核验与原文绑定保持原字节。公开手稿MG-MCP003的接受/排除理由可在研究分榜的折叠观察栏查看；四道私有手稿的数学内容、标识和逐题分配留私库，公开只列合并组数、覆盖和不透明散列。原任务的错误和扣分保留，额外成果不能抵销错误。

审核方式见[统一审核说明](review-process.md)。这里核查相对给定材料和必需目标的额外成果，不认定文献首创、盲审或事前预注册。已核实组数不保证未来主动性，也不能据此将某模型认定为更好的研究者。

当前观察记录位于`results/manuscript-observations/v0.1.0/<model>/<record-id>/observation.json`。私库另留可读报告，并通过描述符引用不变的原数学审核、共同边界、原答和主成绩。旧MRS百分比派生结果和独立页面退出当前工作树。

校验：`python3 scripts/manuscript_observations.py --private-root ../math-gauge-private`。加`--write`仅从已保留数学审核重建观察记录，不调用模型。组数汇总仍由共享`scoring.py`负责，显示层不重新计数。
