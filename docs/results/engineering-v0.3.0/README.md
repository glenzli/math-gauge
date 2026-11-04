# 工程答卷成绩 · 权重0.3.0

| 模型 | 公开总分 | 含私有题总分 | Lean自查净分 |
|---|---:|---:|---:|
| Terra 6.1 Max | 91.6211151369 | 91.9635064412 | 37.6296296296 |
| Gemini 3.8 Flash High | 67.4419021739 | 62.8430434783 | −20 |

总分为能力70%、独立复答5%、书面中性自查5%、Lean对齐自查10%、立场压力10%。书面论证占公开总分28%、含私有题总分24.5%；Lean相关三项分别合计45%与38%。

沿用0.2.0的工程来源、逐项正确性判断和三轮自查判准，只调整聚合权重。MG-C003首答两者均通过74/92；自查后Terra为84/92、Gemini为74/92。误报完整的额外20个专项分不变，其总分影响随自查权重翻倍。

- [Terra公开成绩](terra-public.json)与[含私有题聚合](terra-combined.json)
- [Gemini公开成绩](gemini-public.json)与[含私有题聚合](gemini-combined.json)
- [Terra自查评审绑定](terra-review.json)与[Gemini自查评审绑定](gemini-review.json)
- [新权重与评分规则](../../../protocol/lean-alignment/engineering-scoring-v0.3.0.md) · [成绩报告](../../benchmark-comparison-v0.6.0.md)
- [0.2.0原权重成绩](../engineering-v0.2.0/README.md)

结果由共享评分器从完整冻结计划、原逐槽证据及评审重算，未新增模型调用。新评审文件只变更版本与政策绑定，全部数学判断不变。私有题只公开聚合结果；部分等价测试继承已有作答记录。当前为AI审核，人工复核待完成。
