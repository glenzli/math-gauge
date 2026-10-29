# 题面、参考论证与 Lean 对应

对象是 `task.md` 的固定版本，SHA-256 为 `779bf275a6184fb848a12f3d72089a21d4704513512e10323aa48d4ee462cecd`。核验的是原强目标的反驳，以及原条件下成立的正向结论；不是把原目标补条件后证明。

本工程直接依赖 Mathlib，没有 OET 工程导入。Lean 4.29.1，Mathlib 提交 `5e932f97dd25535344f80f9dd8da3aab83df0fe6`。12 个模块、81 条定理；`Audit.lean` 对清单中的每条定理打印公理依赖，仅有 Lean/Mathlib 常用的 `propext`、`Classical.choice`、`Quot.sound`，无占位证明和新增公理。

## 对象翻译

- `Gauge Y I` 是非吸收部分上的扩展伪度量族；没有分离性、完备性、有限距离或坐标结构字段。`Option Y` 加入吸收元，`lift_*` 验证伪度量和无限隔离。ENNReal 使用 `0 * ∞ = 0`。
- `System.Input v` 是输入子集的类型化表达。对原题可以直接取 `{x // x ∈ U_v}`；一般正向证明不使用其嵌入，因此对任意输入类型也成立。这是放宽适用范围，不是增加题面条件。
- `step v x` 由给定分割和映射唯一确定，值为终止输出或边与后继输入；`step_src` 仅验证选中的边来自本节点。它不保存整体解、终止证书、有限残差或极限。
- `ret` 是返回算子在非吸收部分的限制；`Option.map ret` 是其保持吸收元的扩展。`transform_some` 验证全定义与偏定义展开一致。
- `delta` 是实际算子族的输入上确界；`coeff` 是实际局域矩阵的块和，`gainAction_matrix` 完成桥接。谱半径按同一实矩阵的复数延拓定义。
- 主反例的输入用整数编码，`inputEmbedding_injective` 与 `actualInputEquiv` 将其对应到 `U = {(n,0) : n ∈ ℤ}`。两节点/分量非空、输入非空；步骤的分支就是原稿的整数正负分割。
- 两个单点输入的辅助反例用 `Unit` 编码，分别嵌入 `(0,∞)` 的 `1` 和 `Bool` 的 `false`。这些简单的集合重编码以及原文到 Lean 的对应仍需人工语义审核；编译不能代替它。

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

## 复核方式

全新依赖环境：

```sh
lake update
lake exe cache get
python3 verify.py
```

已有**同一版本** Mathlib 依赖缓存时：

```sh
python3 verify.py --dependency-project /absolute/path/to/pinned/mathlib/project
```

脚本核对 Lean/Mathlib 版本，重新编译本目录全部模块，保存 `.verification/report.json` 与每模块日志，并核对全部公理依赖。共享的是已编译的 Mathlib 依赖，没有共享答案模块的旧编译结果。仓库内的 `verification-report.json` 和 `axiom-audit.log` 保存的是 2026-10-29 资格复核所引用的历史编译与公理审计记录；本轮优化未重新编译。

## 审核边界

Lean 确认形式化陈述及证明的有效性；正文与类型化陈述的语义对应是本次 AI 审核结论，人工审核仍待进行。题面在先前聊天展示中曾漏写 `V ≠ ∅`，磁盘正式题面已包含；本次以正式文件为准，未改变候选提示。


## 尚未编码的旁支与搬运边界

下列界限依据 [2026-10-29 的逐项语义审核](../../../../results/ten-case-qualification/lean-findings.json) 明列。本次只补充覆盖披露，没有新增定理或重新编译；12 个 Lean 源模块及构建输入保持原字节。既有编译记录仅可复用于源散列一致的实际编码结论。

- `Calls`、`calls_unfold` 和 `calls_then_stop` 编码了实际返回函数的复合次序；逐路径的局域矩阵乘积 $L_{e_0}\cdots L_{e_{n-1}}$ 上界尚无独立 Lean 定理。`delta_matrix_iterate` 编码的是聚合矩阵 $M^n$ 对算子族上确界距离的界，二者不能视为同一覆盖项。
- `least_domain` 与 `finite_stop_stable` 编码了逐个输入的有限终止及其展开稳定；“每个输入都有限终止不推出全输入统一深度”尚未另给形式反例。
- 一般集合分割到 `System.step` 的构造及整个系统的搬运仍由语义审核连接。主反例已有整数输入到真实子集的单射和等价，但未单独装配整个系统的等价；两个辅助反例从 `Unit` 到单点输入子集的搬运也未单独封装。
- 主反例已有 `ix_bijective`、`M_is_aggregate` 与 `matrix_spectral_eq_half`；从 `Fin 4` 到 `Bool × Fin 2` 重编号下的谱半径不变性尚未另写成独立定理。
- `not_unique_fixed`、`positive_no_fixed` 和 `swap_no_fixed` 分别给出足以反驳原合取目标的核心结论；完整题面数据及“存在、点值唯一、任意初值的有限常数几何逼近”尚未打包为一个原目标总谓词并完成其最终否定装配。
- `residual_geometric_bound` 是扩展值不等式。有限残差与 $q<1$ 下的 Cauchy 解释由正文作条件化推导，未另立一般 Cauchy 谓词或原空间极限存在定理。

以上未编码项仍有相应的正文数学论证或明确语义对应；它们不因核心模块通过编译而自动获得机器证明。当前支持的说法是“主要编码结论有既有 Lean 核验证据，并有独立语义审核”，不能表述为“参考稿全文已经端到端形式化”。
