# Lean 对应表

| 数学义务 | 输入/参考实际声明 |
|---|---|
| 真实序列与逐点控制、快速衰减 | Core.Seq、Control、Rapid |
| 双侧逆与唯一性 | Multiplier.transport_solve、solve_transport、solution_unique |
| 加法与数乘线性 | Multiplier.solve_add、solve_smul |
| 两阶输入下的估计（输入只到这里） | Multiplier.control_solve_buffered、Candidate.InputControl、candidate |
| 快速衰减保持 | Multiplier.rapid_solve、Candidate.candidate_rapid |
| 原目标的一阶输入估计与完整结果 | Reference.weighted_identity、control_solve、complete、complete_rapid |
| 额外前提的分离见证 | Reference.witness_input、witness_extra_fails、witness_output |
| 可选零阶不可能 | Reference.no_uniform_zero_loss |

Candidate 是有意保留的可编译失配输入，不得把 Reference 内容投给候选。所有声明位于 MathGauge.F107 命名空间。编译不判定语义对齐，human pending；这不是原 PDE 的形式化。
