# MG-R004：实际 Hilbert 复形、反例与完整闭值域判据

本题原强目标被一个真实复 Hilbert ℓ² 复形反驳。所有正向构造仍明确带有额外闭值域假设。没有将有限长度解释为有限维，没有将 Laplacian 的单射写成可逆。

| 题面或参考断言 | Lean 对应 |
|---|---|
| 实际复 ℓ²、对角 1/(n+1) 连续线性算子 | HilbertComplex.H / weight / diagonal_linear / d |
| 范数 1、单射、稠密非闭且非满射像 | d_norm_eq_one / d_injective / d_dense_range / range_not_closed / not_surjective |
| 两个端点约化记录均为零 | reduced_exactness：实际 ker d=⊥ 与 closure(range d)=⊤；零商的等价核/像表达 |
| 没有有界链收缩或两侧有界逆 | no_chain_contraction / no_bounded_left_inverse / no_bounded_right_inverse |
| 实际伴随与两层 Laplacian | d_self_adjoint / L₀ / L₁ / laplacians_eq / laplacians_injective / no_laplacian_right_inverse |
| 任意实际度上的能量等式、约化无环推出 ker L=0 | HilbertCriteria.laplacian_energy / laplacian_injective_of_reduced_exactness |
| 因单射，右逆必为双侧逆 | right_inverse_is_inverse |
| 链收缩使闭包成为实际像 | range_eq_kernel_of_contraction / contraction_implies_closed_range |
| 实际限制 A:ker(A)⊥→range(A)，双射由正交分解证明 | reducedMap / reducedMap_bijective |
| 闭值域后用 Banach 逆定理造部分逆 | reducedEquiv / partialInverse；不把逆作为输入 |
| 两侧复合是实际正交投影 | partialInverse_left / partialInverse_right |
| 闭值域与约化无环给真正链收缩 | closed_reduced_exact / closed_range_contraction |
| M=max(1,‖s‖,‖t‖) 的能量下界 M⁻² | degreeBound / degreeBound_pos / degree_coercive |
| 下界给闭像、稠密像与真实连续线性逆 | coercive_bijective / coerciveEquiv / laplacianEquiv |
| 逆范数≤M² | coercive_inverse_bound / laplacian_inverse_bound |
| d L=L d 与 d G=G d，由实际复合为零推出 | laplacian_commutes / inverse_commutes |
| s=d†G 的链收缩公式 | adjoint_inverse_contraction，包含零端映射的情况 |
| 真正有限长度的存在、端点、双侧逆和稳定控制 | finite_closed_range_target |
| 有限长度的三项充要判据 | finite_criteria；仅要求 0..r 范围的复形/约化正合及 0..r+1 的闭像，不对未使用尾部加条件 |
| 有限层统一有限范数常数 | finite_stability（显式使用有限和给出可用的共同上界） |
| 有限维情形作为附加条件的充分分支 | finite_dimensional_ranges |

有限链的编码把原 H_j 记为 H(j+1)，H(0) 与 H(r+2) 是题面已有的零端空间。底层族用自然数索引便于相邻映射类型，有限主定理不对范围外的空间或映射施加数学假设。端点 Subsingleton 表达零向量空间，允许所有中间层也是零空间。库的零空间与闭子空间处理无需非平凡性。

反例的非满射性通过有界逆定理及明确的单位向量障碍推得；这是原参考直接使用 (1/n) 序列的等价证明，不宣称该特定非像向量也已单独编码。数学结论不改变。

R004Audit 动态检查全部 MathGauge.HilbertComplex 与 MathGauge.HilbertCriteria 声明（含辅助声明和实例），只允许 propext、Classical.choice、Quot.sound。题面、参考、rubric 的冻结字节不变；形式证明与原文的对应属于 AI 语义审核，人工审定仍待进行。
