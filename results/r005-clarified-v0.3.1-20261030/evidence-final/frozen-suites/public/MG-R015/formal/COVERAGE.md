# MG-R015：实际对象与 Lean 覆盖

Lean 4.29.1；Mathlib revision `5e932f97dd25535344f80f9dd8da3aab83df0fe6`。本题只编译 `CompletionFailure.lean` 及公共 Mathlib 依赖。没有依赖旧题或 OET 项目库。

声明位于 `MathGauge.CompletionFailure`。题面与代码均采用所有自然数层 $n\ge0$；`powerSub t M n` 是乘以 $t^n$ 的真实线性映射的像，故正是 $t^nM$。`completion` 是实际商模积中的相容族子模。

| 原文义务或新结论 | 实际定义／声明 |
|---|---|
| $t^nM$、商模和全部自然约化 | `powerSub`, `mem_powerSub`, `powerSub_anti`, `Level`, `reduce`, `reduce_mk` |
| 题面采用的真实完备化模 | `completion`；量词是所有 `n ≤ m` 的约化相容性 |
| 原线性映射的逐层商映射及交换式 | `levelMap`, `levelMap_mk`, `reduce_natural` |
| 原线性映射诱导的完成映射 | `completionMap` |
| 两个实际可数秩自由 $k[X]$ 模 | `Free k = ℕ →₀ Polynomial k`；`counterexample` 显式给出自然数基 `Finsupp.basisSingleOne` |
| $f_i\mapsto X^i e_i$ 的实际线性映射与单射 | `diagonal`, `diagonal_apply`, `diagonal_injective` |
| 实际商 $C$ 及原行短正合 | `Cokernel`, `quotientMap`, `quotient_surjective`, `row_exact` |
| 每层有限部分和及逐坐标公式 | `partialSum`, `partialSum_apply` |
| 每个部分和位于原映射像中 | `partialSum_in_range` |
| 所有层之间的约化相容性 | `partialSum_difference`, `witness` |
| 真实完成商映射的核中元素 | `witness_in_kernel` |
| $X^r$ 倍数在低于 $r$ 次的系数为零 | `low_coefficient_zero` |
| 任意相容原像会使第一层有限支撑代表的每个常数项都为一 | `witness_not_in_range`，使用实际商代表、商相等和原相容性 |
| 完成后的实际序列在中间不正合 | `completion_not_exact` |
| 全部题设与失败结论汇总 | `counterexample` |

形式化保留任意域 $k$，未固定特殊特征，也没有把完备化替换为逐坐标无限积或张量积。本例的完整反驳已覆盖原全称任务；没有声称额外证明完成映射的单射性、右端满射性或所有完成模的完整分类。参考没有提出这些额外结论。

源码散列和导入闭包由 `manifest.json` 绑定。`CurrentAudit.lean` 动态检查全部本题 `MathGauge` 声明及其递归公理依赖，仅允许 `propext`、`Classical.choice`、`Quot.sound`。human pending。
