# MG-R011 精确形式化覆盖

所有本题模块都仅依赖固定 Mathlib 及本题前序模块，没有使用 OET、旧题模块或外部证书。命名空间为 `MathGauge.FiniteConstraints`。所有正文主目标及参考中的新增数学断言均有以下实际对象实现；人工语义审核仍待定。

| 自然语言义务 | 实际 Lean 对应 |
|---|---|
| 非空闭凸集的真实投影存在 | `project` 直接从 Mathlib `exists_norm_eq_iInf_of_complete_convex` 取出点；`project_spec` 记录成员及实际距离下确界 |
| 投影最小性、变分不等式、能量差不等式 | `project_min`, `project_variation`, `project_energy`；变分等价的背景定理为 `norm_eq_iInf_iff_real_inner_le_zero` |
| 唯一性及 firm / 非扩张估计 | `project_unique`, `project_firm`, `project_nonexpansive` |
| 有限交的闭凸性、空有限集、包含反向 | `finite_meet`, `finite_meet_closed`, `finite_meet_convex`, `finite_meet_antitone`, `finite_empty` |
| 有限投影由实际有界可行点构造 | `finite_project`, `finite_project_mem`, `finite_project_min`, `finite_project_bound` |
| 能量随约束单调、实数统一上界及嵌套误差 | `energy_mono`, `energy_bdd`, `finite_nested_energy` |
| 整个有限子集网为 Cauchy 网 | `finite_project_cauchy`; `CauchySeq` 的指标明确为 `Finset I`，滤子为 `atTop`，并非自然数序列 |
| 全交中真实极限点及全局最小性 | `exists_global_limit`, `global_nonempty`；逐个约束使用最终包含单点集及其闭性 |
| 唯一全局投影与完整网强收敛 | `global_project`, `global_mem`, `global_unique`, `finite_project_tendsto` |
| 全局最优值等于有限值上确界 | `global_energy_eq_sup` |
| 精确误差界及稳定性 | `global_energy_error`, `global_nonexpansive` |
| 空指标集退化情形 | `global_empty`；零空间由全部泛型声明直接包含 |

`B≥0` 在自然语言中保留；Lean 的实际有界可行点条件已在空有限集处蕴含它，因此定理无需额外使用该冗余假设。Lean 没有预设全交非空、极限、投影网收敛、全局解或任何主目标作为结构字段。

源文件和题面、参考、rubric 的精确 SHA256 由 `manifest.json` 绑定。最终共同验证器逐题使用新输出目录、固定 Lean 4.29.1 / Mathlib revision `5e932f97dd25535344f80f9dd8da3aab83df0fe6`，并遍历所有本题 MathGauge 声明的公理依赖。允许的公理仅为 `Classical.choice`, `Quot.sound`, `propext`。编译证据、语义复核和人工审定是分别记录的证据。
