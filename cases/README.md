# 当前试卷

0.5.0默认题集 `cases/suite.json` 含30份相关任务，关联21个母题家族。另20份后备数学卷由 `cases/reserve-suite.json` 显式选择。完整题库含46份数学卷与4份真实答卷审阅，共372项阶段或章节义务，另有15项书面证明评审判准。相关任务、判准及审阅维度不构成独立数学家族。

材料具参考、判准、来源及AI审核记录，题目与当前答卷仍为 **human pending**。已有数学答卷及8份候选审阅答卷；AR纳入、评分与统一重评属于观察结果后的方法变更，详见[审阅说明](../docs/answer-review-pilot.md)与[当前结果](../docs/benchmark-comparison-2026-11-03.md)。已发布资产保持原样。

题面与附件由共享runner按 `case.json` 显式投影；本目录、分类、参考、评分和审核记录均为出题侧材料。参考与既有历史继续公开以供透明复核，不进入 solver 题包，也不构成未公开留出集。

[按考察重点选卷](by-focus.md) · [机器目录](catalog.json) · [分类定义与逐项依据](taxonomy.json) · [来源](../SOURCES.md) · [验证状态](../docs/verification.md)

## 书面证明、反例与构造 · 14份

| 试卷 | 任务 | 必答规模 | 完整材料 |
| --- | --- | ---: | --- |
| [MG-GP001 · 局部单形、锥附着与整体同伦型](proofs/MG-GP001/task.md) | written | 6阶段 | [合同](proofs/MG-GP001/contract.json) · [参考](proofs/MG-GP001/reference.md) · [评分](proofs/MG-GP001/rubric.json) · [题包复核](proofs/MG-GP001/review.json) · [作者Lean](proofs/MG-GP001/formal/COVERAGE.md) |
| [MG-GP002 · Fourier 逆、截断误差与参数边界](proofs/MG-GP002/task.md) | written | 6阶段 | [合同](proofs/MG-GP002/contract.json) · [参考](proofs/MG-GP002/reference.md) · [评分](proofs/MG-GP002/rubric.json) · [题包复核](proofs/MG-GP002/review.json) · [作者Lean](proofs/MG-GP002/formal/COVERAGE.md) |
| [MG-GP003 · 半局部邻域、下降与层化的依赖比较](proofs/MG-GP003/task.md) | written | 6阶段 | [合同](proofs/MG-GP003/contract.json) · [参考](proofs/MG-GP003/reference.md) · [评分](proofs/MG-GP003/rubric.json) · [题包复核](proofs/MG-GP003/review.json) · [作者Lean](proofs/MG-GP003/formal/COVERAGE.md) |
| [MG-GR002 · 线性记录、有限观测与原空间恢复](proofs/MG-GR002/task.md) | written | 6阶段 | [合同](proofs/MG-GR002/contract.json) · [参考](proofs/MG-GR002/reference.md) · [评分](proofs/MG-GR002/rubric.json) · [题包复核](proofs/MG-GR002/review.json) · [作者Lean](proofs/MG-GR002/formal/COVERAGE.md) |
| [MG-GR005 · 凸成本记录、紧性与闭上图恢复](proofs/MG-GR005/task.md) | written | 6阶段 | [合同](proofs/MG-GR005/contract.json) · [参考](proofs/MG-GR005/reference.md) · [评分](proofs/MG-GR005/rubric.json) · [题包复核](proofs/MG-GR005/review.json) · [作者Lean](proofs/MG-GR005/formal/COVERAGE.md) |
| [MG-GR008 · 塔记录的表示、有限层延拓与自然变换](proofs/MG-GR008/task.md) | written | 6阶段 | [合同](proofs/MG-GR008/contract.json) · [参考](proofs/MG-GR008/reference.md) · [评分](proofs/MG-GR008/rubric.json) · [题包复核](proofs/MG-GR008/review.json) · [作者Lean](proofs/MG-GR008/formal/COVERAGE.md) |
| [MG-GR009 · 群作用下降、稳定子与基底检验](proofs/MG-GR009/task.md) | written | 6阶段 | [合同](proofs/MG-GR009/contract.json) · [参考](proofs/MG-GR009/reference.md) · [评分](proofs/MG-GR009/rubric.json) · [题包复核](proofs/MG-GR009/review.json) · [作者Lean](proofs/MG-GR009/formal/COVERAGE.md) |
| [MG-GR010 · 探针映射空间与连续性层级](proofs/MG-GR010/task.md) | written | 6阶段 | [合同](proofs/MG-GR010/contract.json) · [参考](proofs/MG-GR010/reference.md) · [评分](proofs/MG-GR010/rubric.json) · [题包复核](proofs/MG-GR010/review.json) · [作者Lean](proofs/MG-GR010/formal/COVERAGE.md) |
| [MG-GR014 · 线性关系、坐标纤维与无限赋值](proofs/MG-GR014/task.md) | written | 6阶段 | [合同](proofs/MG-GR014/contract.json) · [参考](proofs/MG-GR014/reference.md) · [评分](proofs/MG-GR014/rubric.json) · [题包复核](proofs/MG-GR014/review.json) · [作者Lean](proofs/MG-GR014/formal/COVERAGE.md) |
| [MG-GR021 · 同时分块与二次扩张上的下降](proofs/MG-GR021/task.md) | written | 5评审判准 | [合同](proofs/MG-GR021/contract.json) · [参考](proofs/MG-GR021/reference.md) · [评分](proofs/MG-GR021/rubric.json) · [题包复核](proofs/MG-GR021/review.json) |
| [MG-GR022 · 对角呈示的完成与商拓扑](proofs/MG-GR022/task.md) | written | 5评审判准 | [合同](proofs/MG-GR022/contract.json) · [参考](proofs/MG-GR022/reference.md) · [评分](proofs/MG-GR022/rubric.json) · [题包复核](proofs/MG-GR022/review.json) |
| [MG-GR023 · 有限测试记录与群作用](proofs/MG-GR023/task.md) | written | 5评审判准 | [合同](proofs/MG-GR023/contract.json) · [参考](proofs/MG-GR023/reference.md) · [评分](proofs/MG-GR023/rubric.json) · [题包复核](proofs/MG-GR023/review.json) |
| [MG-GR103 · 参数最小不动点、消元与近似传递](proofs/MG-GR103/task.md) | written | 6阶段 | [合同](proofs/MG-GR103/contract.json) · [参考](proofs/MG-GR103/reference.md) · [评分](proofs/MG-GR103/rubric.json) · [题包复核](proofs/MG-GR103/review.json) · [作者Lean](proofs/MG-GR103/formal/COVERAGE.md) |
| [MG-GR104 · 幂等元提升、逆极限与环分解](proofs/MG-GR104/task.md) | written | 6阶段 | [合同](proofs/MG-GR104/contract.json) · [参考](proofs/MG-GR104/reference.md) · [评分](proofs/MG-GR104/rubric.json) · [题包复核](proofs/MG-GR104/review.json) · [作者Lean](proofs/MG-GR104/formal/COVERAGE.md) |

## Lean 语义审计 · 5份

| 试卷 | 任务 | 必答规模 | 完整材料 |
| --- | --- | ---: | --- |
| [MG-GF101 · 商环塔、幂零性与分离条件](lean-audit/MG-GF101/task.md) | audit | 6阶段 | [合同](lean-audit/MG-GF101/contract.json) · [参考](lean-audit/MG-GF101/reference.md) · [评分](lean-audit/MG-GF101/rubric.json) · [题包复核](lean-audit/MG-GF101/review.json) · [作者Lean](lean-audit/MG-GF101/formal/COVERAGE.md) |
| [MG-GF103 · 初始拓扑的比较与测试空间](lean-audit/MG-GF103/task.md) | audit | 6阶段 | [合同](lean-audit/MG-GF103/contract.json) · [参考](lean-audit/MG-GF103/reference.md) · [评分](lean-audit/MG-GF103/rubric.json) · [题包复核](lean-audit/MG-GF103/review.json) · [作者Lean](lean-audit/MG-GF103/formal/COVERAGE.md) |
| [MG-GF105 · 陪集切片、最小覆盖与空切片](lean-audit/MG-GF105/task.md) | audit | 6阶段 | [合同](lean-audit/MG-GF105/contract.json) · [参考](lean-audit/MG-GF105/reference.md) · [评分](lean-audit/MG-GF105/rubric.json) · [题包复核](lean-audit/MG-GF105/review.json) · [作者Lean](lean-audit/MG-GF105/formal/COVERAGE.md) |
| [MG-GF107 · 加权逆算子、支撑界与量词交换](lean-audit/MG-GF107/task.md) | audit | 6阶段 | [合同](lean-audit/MG-GF107/contract.json) · [参考](lean-audit/MG-GF107/reference.md) · [评分](lean-audit/MG-GF107/rubric.json) · [题包复核](lean-audit/MG-GF107/review.json) · [作者Lean](lean-audit/MG-GF107/formal/COVERAGE.md) |
| [MG-GF111 · 扩展非负界、有限子域与统一常数](lean-audit/MG-GF111/task.md) | audit | 6阶段 | [合同](lean-audit/MG-GF111/contract.json) · [参考](lean-audit/MG-GF111/reference.md) · [评分](lean-audit/MG-GF111/rubric.json) · [题包复核](lean-audit/MG-GF111/review.json) · [作者Lean](lean-audit/MG-GF111/formal/COVERAGE.md) |

## Lean 生成与修复 · 5份

| 试卷 | 任务 | 必答规模 | 完整材料 |
| --- | --- | ---: | --- |
| [MG-GF102 · 商环塔的稳定、比较与自然性](lean-construction/MG-GF102/task.md) | generate | 6阶段 | [合同](lean-construction/MG-GF102/contract.json) · [参考](lean-construction/MG-GF102/reference.md) · [评分](lean-construction/MG-GF102/rubric.json) · [题包复核](lean-construction/MG-GF102/review.json) · [作者Lean](lean-construction/MG-GF102/formal/COVERAGE.md) |
| [MG-GF104 · 初始拓扑、子空间与分离性修复](lean-construction/MG-GF104/task.md) | repair | 6阶段 | [合同](lean-construction/MG-GF104/contract.json) · [参考](lean-construction/MG-GF104/reference.md) · [评分](lean-construction/MG-GF104/rubric.json) · [题包复核](lean-construction/MG-GF104/review.json) · [作者Lean](lean-construction/MG-GF104/formal/COVERAGE.md) |
| [MG-GF106 · 陪集覆盖、商群计数与子群改变](lean-construction/MG-GF106/task.md) | generate | 6阶段 | [合同](lean-construction/MG-GF106/contract.json) · [参考](lean-construction/MG-GF106/reference.md) · [评分](lean-construction/MG-GF106/rubric.json) · [题包复核](lean-construction/MG-GF106/review.json) · [作者Lean](lean-construction/MG-GF106/formal/COVERAGE.md) |
| [MG-GF108 · 加权逆算子的正性边界与接口修复](lean-construction/MG-GF108/task.md) | repair | 6阶段 | [合同](lean-construction/MG-GF108/contract.json) · [参考](lean-construction/MG-GF108/reference.md) · [评分](lean-construction/MG-GF108/rubric.json) · [题包复核](lean-construction/MG-GF108/review.json) · [作者Lean](lean-construction/MG-GF108/formal/COVERAGE.md) |
| [MG-GF112 · 扩展非负最优界的取得与系统组合](lean-construction/MG-GF112/task.md) | generate | 6阶段 | [合同](lean-construction/MG-GF112/contract.json) · [参考](lean-construction/MG-GF112/reference.md) · [评分](lean-construction/MG-GF112/rubric.json) · [题包复核](lean-construction/MG-GF112/review.json) · [作者Lean](lean-construction/MG-GF112/formal/COVERAGE.md) |

## 整章形式化 · 2份

| 试卷 | 任务 | 必答规模 | 完整材料 |
| --- | --- | ---: | --- |
| [MG-C002 · OET卷1第2章整章形式化](chapters/MG-C002/candidate/task.md) | generate | 34义务 | [合同](chapters/MG-C002/contract.json) · [参考](chapters/MG-C002/reference.md) · [评分](chapters/MG-C002/rubric.json) · [题包复核](chapters/MG-C002/review.json) · [作者Lean](chapters/MG-C002/formal/COVERAGE.md) |
| [MG-C003 · OET卷1第3章整章形式化](chapters/MG-C003/candidate/task.md) | generate | 92义务 | [合同](chapters/MG-C003/contract.json) · [参考](chapters/MG-C003/reference.md) · [评分](chapters/MG-C003/rubric.json) · [题包复核](chapters/MG-C003/review.json) · [作者Lean](chapters/MG-C003/formal/COVERAGE.md) |

## 真实答卷审阅 · 4份

| 试卷 | 任务 | 必答规模 | 完整材料 |
| --- | --- | ---: | --- |
| [MG-AR001 · 真实答卷审阅 001：幂等元提升、逆极限与环分解](answer-review/MG-AR001/task.md) | answer_review | 3审阅维度 | [合同](answer-review/MG-AR001/group-contract.json) · [参考](answer-review/MG-AR001/reference.md) · [评分](answer-review/MG-AR001/rubric.json) · [题包复核](answer-review/MG-AR001/review.json) |
| [MG-AR002 · 真实答卷审阅 002：线性关系、坐标纤维与无限赋值](answer-review/MG-AR002/task.md) | answer_review | 3审阅维度 | [合同](answer-review/MG-AR002/group-contract.json) · [参考](answer-review/MG-AR002/reference.md) · [评分](answer-review/MG-AR002/rubric.json) · [题包复核](answer-review/MG-AR002/review.json) |
| [MG-AR003 · 真实答卷审阅 003：探针映射空间与连续性层级](answer-review/MG-AR003/task.md) | answer_review | 3审阅维度 | [合同](answer-review/MG-AR003/group-contract.json) · [参考](answer-review/MG-AR003/reference.md) · [评分](answer-review/MG-AR003/rubric.json) · [题包复核](answer-review/MG-AR003/review.json) |
| [MG-AR004 · 真实答卷审阅 004：半局部邻域、下降与层化的依赖比较](answer-review/MG-AR004/task.md) | answer_review | 3审阅维度 | [合同](answer-review/MG-AR004/group-contract.json) · [参考](answer-review/MG-AR004/reference.md) · [评分](answer-review/MG-AR004/rubric.json) · [题包复核](answer-review/MG-AR004/review.json) |

## 备选卷 · 20份

[备选目录、主题分类与完整材料](reserve/README.md)集中列出20份书面卷，由显式清单选择。审阅另可用[独立清单](answer-review-suite.json)选择，样本相关性与评分见[审阅说明](../docs/answer-review-pilot.md)。

所有路径和候选输入散列由 `python3 scripts/catalog.py` 从当前合同生成；`--check` 只读核验。
