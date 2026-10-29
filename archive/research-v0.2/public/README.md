# 公开研究题集 · 初版十题

这些题目检验模型在多步构造中能否保留实际条件，并准确区分可实现的记录与更强的整体结论。题面只提供对象、条件和主要目标；答案可能是证明、反例或范围明确的替代构造。

本页、参考证明、评分依据、审核记录及形式化文件供出题与评审使用。正式作答只投影选中题目的 task.md，不把这些材料或题目真假交给候选模型。

| 题号 | 题面 | 领域 | 评审材料 |
| --- | --- | --- | --- |
| MG-R001 | [递归算子系统的闭合](MG-R001/task.md) | recursive operators | [参考](MG-R001/reference.md) · [评分](MG-R001/rubric.json) · [审核](MG-R001/review.json) |
| MG-R002 | [兼容线性记录的整体实现](MG-R002/task.md) | functional analysis / bidual observations | [参考](MG-R002/reference.md) · [评分](MG-R002/rubric.json) · [审核](MG-R002/review.json) |
| MG-R003 | [双重平均与不变记录](MG-R003/task.md) | functional analysis / ergodic averages | [参考](MG-R003/reference.md) · [评分](MG-R003/rubric.json) · [审核](MG-R003/review.json) |
| MG-R004 | [复形记录的稳定消元](MG-R004/task.md) | functional analysis / Hilbert complexes | [参考](MG-R004/reference.md) · [评分](MG-R004/rubric.json) · [审核](MG-R004/review.json) |
| MG-R005 | [有限观测下的凸成本恢复](MG-R005/task.md) | functional analysis / convex duality | [参考](MG-R005/reference.md) · [评分](MG-R005/rubric.json) · [审核](MG-R005/review.json) |
| MG-R006 | [逐层可解系统的兼容提升](MG-R006/task.md) | category theory / inverse limits | [参考](MG-R006/reference.md) · [评分](MG-R006/rubric.json) · [审核](MG-R006/review.json) |
| MG-R007 | [对称作用下的提升障碍](MG-R007/task.md) | representation theory / group cohomology | [参考](MG-R007/reference.md) · [评分](MG-R007/rubric.json) · [审核](MG-R007/review.json) |
| MG-R008 | [逐层记录的统一承载对象](MG-R008/task.md) | category theory / filtered colimits and pro-objects | [参考](MG-R008/reference.md) · [评分](MG-R008/rubric.json) · [审核](MG-R008/review.json) |
| MG-R009 | [局部记录的有效下降商](MG-R009/task.md) | condensed sets / effective descent | [参考](MG-R009/reference.md) · [评分](MG-R009/rubric.json) · [审核](MG-R009/review.json) |
| MG-R010 | [由紧全不连通探针重构空间](MG-R010/task.md) | general topology / compact generation and condensed comparison | [参考](MG-R010/reference.md) · [评分](MG-R010/rubric.json) · [审核](MG-R010/review.json) |

## 审核与使用状态

全部题目保持 draft、human pending。数学作者与独立审核者使用 Astra Max；工程流程使用 Sol 6.1 Max。逐题的 AI 审核、人工审核、形式化和模型试跑状态分别写入 review.json，并在[整体验证记录](../../results/ten-case-validation/README.md)汇总。

MG-R001 保持原隔离实验的题面字节。它已有一次 Terra 6.1 Max 和一次 Gemini 3.8 Flash High 闭卷对照；其 12 个参考 Lean 模块、81 条定理按相同源文件散列复用核验证据。其余九题尚未运行候选模型，也未完成 Lean 形式化。本轮不声称十题已通过难度校准。

## 出题侧布局

五个强目标在实际条件下不能成立：MG-R001、MG-R002、MG-R004、MG-R006、MG-R008。五个主目标可以成立，但所得对象或保证较弱：MG-R003、MG-R005、MG-R007、MG-R009、MG-R010。这些分类不进入候选输入，也不能代替逐题证明。

对于不成立的目标，一个满足全部前提的有效反例足以否定该目标；额外构造贡献另记。对于成立的目标，评分要求完成题面实际目标，不要求抄齐参考稿的所有边界、条件升级或反例。模型若给出意外结果，审核其证明后单独记录。

[设计标准](../../protocol/research-case-design.md) · [评测协议](../../protocol/evaluation.md) · [来源](../../SOURCES.md) · [旧题归档](../../archive/legacy-v0/README.md)
