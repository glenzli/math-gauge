# MG-R012：任意实拓扑向量空间上的实际凸势

`CyclicPotential.lean` 以实向量空间 `H`、任意拓扑、连续加法及连续标量乘法为基础，记录的第二坐标是实际连续线性泛函 `H →L[ℝ] ℝ`。没有范数、内积、分离性、局部凸性或完备性实例。

Lean 的 `IsTopologicalAddGroup` 同时记录连续加法和连续取负；题面的连续标量乘法在标量 −1 处给出连续取负，因而这不是额外数学条件。每个连续泛函分别作用于 `H`，未在对偶空间上补入拓扑或假定配对联合连续。

| 原文内容 | `MathGauge.CyclicPotential` 中的声明 |
| --- | --- |
| 任意合法有限记录及循环闭合不等式 | `path_value`、`ValidPath`、`CyclicMonotone`；列表只编码题面任意有限长度记录，空列表对应零长度路径 |
| 拼接、仿射性及连续性 | `path_append`、`path_affine`、`path_continuous` |
| 实际路径上确界 | `potential`，使用 `EReal` 的真实 `iSup` |
| 不出现负无穷、基点值为零、图上有限 | `potential_ne_bot`、`potential_base`、`potential_upper_on_graph`、`potential_finite_on_graph` |
| 凸性、闭上图及下半连续性 | `real_epigraph`、`potential_epigraph_convex`、`potential_epigraph_closed`、`potential_lsc` |
| 图包含于次梯度图 | `Subgradient`、`potential_subgradient` |
| 任意规范化支持势的比较及最小性 | `path_le_supporting`、`potential_minimal` |
| 全部主目标及严格唯一性 | `main`、`least_unique` |
| 包含不必成为图相等的真实反例 | `singleton_graph`、`singleton_cyclic`、`singleton_potential_zero`、`singleton_strict_extension`，系数空间为实数、记录泛函为零泛函 |

`EReal` 包含额外的负无穷元素，但 `main` 对每一点证明结果不为负无穷，并在基点证明值为零。因此实际输出正是题面的实值加正无穷函数。`Subgradient` 要求基点有一个真实实数值，再对全部测试点写支持不等式；不会对未定义的无穷差作运算。

最小性证明允许更广的竞争函数，只使用规范化和所给记录的次梯度条件；构造本身同时证明下半连续和凸，因而完成原竞争类中的最小性。没有把凸势、优化点、图包含或最小性包装成构造输入。

正文与 Lean 使用同一有限路径证明。无额外候选可见材料；参考中的严格扩张反例是已核验旁支，不增加最低答题义务。独立构建、公理审计和语义审核分别记录，人工审核仍为 pending。
