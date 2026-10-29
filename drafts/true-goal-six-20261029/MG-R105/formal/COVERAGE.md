# MG-R105 Lean 覆盖说明

主文件为 `ObservationRecovery.lean`，命名空间 `MathGauge.R105`。依赖固定为 Lean 4.29.1、Mathlib `5e932f97dd25535344f80f9dd8da3aab83df0fe6`。本表是作者对照记录，独立语义审查与统一公理审计由整合阶段另行记录；human pending。

| 题面义务 | 实际 Lean 对象和声明 | 范围说明 |
|---|---|---|
| 代数商及观测范数 | `ObservationQuotient`, `quotient_range`, 拉回的 `NormedAddCommGroup` 与 `NormedSpace` 实例, `quotient_map`, `norm_quotient_map` | `ObservationQuotient A` 真正定义为 `E ⧸ A.ker`；范数由实际核商同构到 `A.range` 拉回。未给 E 范数，故没有借用原范数的商范数。 |
| 完备化和等距线性实现 | `completion_equiv`, `realization`, `completion_equiv_mk`, `realization_range` | `UniformSpace.Completion` 是实际度量完备化；构造到 `A.range.topologicalClosure` 的线性等距同构，再嵌入 H。没有把该同构当成假设。 |
| 实现的唯一性 | `realization_unique` | 更强地证明任何连续实现若对每个原向量满足同一延拓等式，必与构造相同。使用实际商映射满射性和完备化密度。 |
| 最优恢复的实际构造 | `recovered`, `predicted`, `recovery_observation` | `recovered` 是一个实际连续线性映射，定义为闭像正交投影与已构造等距同构逆的复合。 |
| 唯一极小点 | `residual_decomposition`, `completed_residual_decomposition`, `completed_minimal`, `completed_minimizer_unique` | 在实际闭像中证明正交平方分解，再用等距性转移到完成态；最小性和唯一性分别证明。 |
| 线性和 1-Lipschitz 性 | `recovered` 的 `ContinuousLinearMap` 类型，`recovery_lipschitz` | 线性来自构造而非额外 certificate；完整 H 上的共同常数为 1，不假设原像存在。 |
| 与原问题下确界相等 | `original_infimum`, `original_iInf` | 同时覆盖集合距离和题面实数下确界 `⨅ x : E, ‖y-Ax‖`，不是把最小值存在性假设进来。E 的零向量保证下确界集合非空。 |
| 原空间取到及全部解 | `original_minimizer_iff`, `original_attainment_iff`, `original_fiber`, `original_infimum_attained_iff`, `original_solution_set` | `original_infimum_attained_iff` 使用题面的“值等于下确界”定义；`original_solution_set` 给出所有点恰为 `x-x₀∈ker(A)`。比较式极小点定义也单独连接到同一观测等式。 |

假设为实际的实向量空间 E、实 Hilbert 空间 H 和线性映射 A。Lean 没有加入 E 的拓扑、有限维、A 的单射/满射、原像闭性或原像选择证书。H 的完备性用在闭子空间的投影与完成态实现；核商范数和稠密性等辅助结果中的多余 `CompleteSpace H` 仅为已有题设，不改变主目标范围。

参考中的四个错误路径见证未逐一编码；它们是评审侧的独立数学证据，不是候选必答义务。参考附带的 `R(y)∈ι(Q)` 等价表述由主线等距性直接得出，未设单独 Lean 定理。没有声称全部说明文字逐句形式化，也没有候选答卷形式化或人工批准。
