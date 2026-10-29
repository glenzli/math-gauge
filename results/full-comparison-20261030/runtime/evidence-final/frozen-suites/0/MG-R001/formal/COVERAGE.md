# 题面、参考论证与 Lean 对应

对象是 `task.md` 的固定版本，SHA-256 为 `779bf275a6184fb848a12f3d72089a21d4704513512e10323aa48d4ee462cecd`。核验的是原强目标的反驳，以及原条件下成立的正向结论；不是把原目标补条件后证明。

本工程直接依赖 Mathlib，没有 OET 工程导入。Lean 4.29.1，Mathlib 提交 `5e932f97dd25535344f80f9dd8da3aab83df0fe6`。本轮补齐此前披露的路径、分割搬运、谱重编号、完整目标、终止边界与 Cauchy 旁支；`FullAudit.lean` 动态枚举命名空间内全部声明（含定义、实例、自动生成辅助声明），打印公理依赖，仅有 Lean/Mathlib 常用的 `propext`、`Classical.choice`、`Quot.sound`，无占位证明和新增公理。

## 对象翻译

- `Gauge Y I` 是非吸收部分上的扩展伪度量族；没有分离性、完备性、有限距离或坐标结构字段。`Option Y` 加入吸收元，`lift_*` 验证伪度量和无限隔离。ENNReal 使用 `0 * ∞ = 0`。
- `System.Input v` 是输入子集的类型化表达。对原题可以直接取 `{x // x ∈ U_v}`；一般正向证明不使用其嵌入，因此对任意输入类型也成立。这是放宽适用范围，不是增加题面条件。
- `step v x` 由给定分割和映射唯一确定，值为终止输出或边与后继输入；`step_src` 仅验证选中的边来自本节点。它不保存整体解、终止证书、有限残差或极限。
- `ret` 是返回算子在非吸收部分的限制；`Option.map ret` 是其保持吸收元的扩展。`transform_some` 验证全定义与偏定义展开一致。
- `delta` 是实际算子族的输入上确界；`coeff` 是实际局域矩阵的块和，`gainAction_matrix` 完成桥接。谱半径按同一实矩阵的复数延拓定义。
- 主反例的输入用整数编码，`inputEmbedding_injective` 与 `actualInputEquiv` 将其对应到 `U = {(n,0) : n ∈ ℤ}`。两节点/分量非空、输入非空；步骤的分支就是原稿的整数正负分割。
- 两个单点输入的辅助反例用 `Unit` 编码，分别嵌入 `(0,∞)` 的 `1` 和 `Bool` 的 `false`。本轮 InputTransport 与 FullTarget 进一步形式化整个输入重编码后的系统及无固定点结论；原文到 Lean 的语义对应仍需人工审核，编译不能代替它。

## 主要结论

| 参考稿内容 | Lean 定理（共同前缀 `MathGauge.RecursiveClosure`） |
| --- | --- |
| 原始伪度量与吸收元合法 | `lift_self`, `lift_symm`, `lift_triangle`, `lift_bottom_isolated` |
| 实际调用返回顺序与有限终止后的稳定 | `System.calls_unfold`, `System.calls_then_stop`, `System.finite_stop_stable` |
| 真正算子空间上的单步与矩阵幂界 | `System.delta_transform`, `System.gainAction_matrix`, `System.delta_matrix_iterate` |
| 谱条件产生正权重；未预设收缩范数 | `spectral_powers_decay`, `positive_weights_of_spectral`, `System.spectral_weighted_contraction` |
| 加权迭代、残差几何界 | `System.weighted_iterate`, `System.residual_finite_sum`, `System.residual_geometric_bound` |
| 有限距离固定族只有零距结论 | `System.fixed_weighted_zero`, `System.fixed_pointwise_zero` |
| 最小偏定义固定族及其精确终止域 | `System.least_fixed`, `System.least_le_fixed`, `System.least_domain` |
| 二维反例的分离性、完备性与规范一致 | `Counterexample.gauge_separates`, `output_complete`, `metric_matches_gauge` |
| 局域 Lip 界、真正块和与谱半径 `1/2` | `Counterexample.ret_lip`, `M_is_aggregate`, `matrix_spectral_eq_half` |
| 无穷多个固定族，异参数固定族距离无穷 | `Counterexample.solution_fixed`, `solution_injective`, `fixed_families_infinite`, `different_fixed_distance_top` |
| 展开公式及每层统一误差为无穷 | `Counterexample.unfold_formulas`, `even_second_zero`, `error_top_every_depth` |
| 每个固定输入仍收敛到零解 | `Counterexample.pointwise_unfold_limit` |
| 返回复合恢复分量依赖 | `Counterexample.component_restoration` |
| 正半轴和零伪度量交换两种无解障碍 | `Obstructions.positive_no_fixed`, `swap_no_fixed`, `single_loop_spectral_lt_one` |
| 零伪度量的完备性与单点分离商 | `Obstructions.zero_pseudo_complete`, `zero_pseudo_matches`, `zero_quotient_subsingleton` |

`residual_geometric_bound` 给出扩展值不等式；只有参考稿明确要求的 `R < ∞` 且 `q < 1` 时才是有限的 Cauchy 界。未推出原空间极限存在。偏定义解明确以 `Option Y` 为值域，未冒充题面中的全定义解。全体指标的 `iSup` 在有限非空指标下即题面中的 `max`。

## 本轮补全的实际桥接

| 先前未编码项 | 新机器证明 |
|---|---|
| 完整集合分割及实际展开的两个子句 | PartitionData.system / step_stop / step_call / transform_clauses；调用片互斥只在同源边间要求 |
| 吸收元与原有带底空间的同载体搬运 | AbsorbingTransport 的等价及距离保持；原来的 Option 构造不要求额外空间结构 |
| 真正调用路径的局域矩阵乘积 | System.path_lipschitz / call_path_matrix_bound，独立于聚合 M^n 界 |
| 输入重编码后的整体函数族、展开和距离 | System.familyTransport / fixed_transport / delta_transport，Counterexample.subsetSystem |
| Fin 4 与实际块指标的谱半径桥接 | Counterexample.actual_spectral_eq_half |
| 原合取目标的准确谓词和否定 | System.StrongClosure / Counterexample.full_target_false / full_subset_target_false / spectral_does_not_imply_full_target |
| 任意有限常数无法控制指定初值误差 | Counterexample.no_finite_geometric_error |
| 两个单点输入辅助反例的完整搬运 | Obstructions.positiveSubset / swapSubset / positive_subset_no_fixed / swap_subset_no_fixed |
| 有限残差给真正 Cauchy 界 | System.WeightedCauchy / finite_residual_cauchy；没有声称原空间极限存在 |
| 所有输入各自终止仍无统一深度 | TerminationBoundary.all_inputs_halt / no_uniform_depth；有限单环且真实谱半径为 0 |

以上包括完整题面目标的否定及参考中的正向结论与边界见证。正半轴辅助反例和伪度量空间不擅自完备化；全定义、偏定义、零距离和点值相等在 Lean 中仍不同。

本轮验证以实际源 SHA-256、依赖版本、逐模块重新编译结果及全声明公理审计为准。题面保持冻结字节，不向候选提供这份覆盖表。人工审定待定。
