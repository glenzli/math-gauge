# MG-R013 精确形式化覆盖

仅依赖固定 Mathlib 与本题前序模块，不导入 OET、旧题或其他题输出。命名空间为 `MathGauge.SpectralApproximation`。空间 `E=C₀(ℕ,ℂ)` 是实际复 Banach 空间；连续线性算子、算子范数及谱均使用真实 Mathlib 对象。

| 自然语言义务 | 实际 Lean 对应 |
|---|---|
| c₀实际空间、坐标范数和消失于无穷远 | `E`, `norm_le_of_coords`, `coord_le`, `zero_limit`; 完备性为 Mathlib `ZeroAtInftyContinuousMap.instCompleteSpace` |
| 右移与有限截断的实际定义、线性和有界性 | `shift_value`, `shift`, `truncated_value`, `truncated`; `shift_norm_le`, `truncated_norm_le` |
| 强收敛 | `truncated_strong`，以实际 c₀ 尾坐标逐点证明范数收敛 |
| 全部幂的坐标公式与幂零性 | `shift_pow_apply`, `truncated_pow_succ`, `truncated_nilpotent` |
| 像空间有限维 | `truncated_finite_rank`，真实像通过有限坐标线性单射进入 `Fin n→ℂ` |
| 非零空间及零谱点 | `basis_vector`, `basis_ne_zero`, `truncated_basis_kernel`, `truncated_zero_spectral` |
| 非零参数的实际有界逆存在及全部有限模型谱 | `finite_resolvent`, `finite_resolvent_two_sided` 直接证明参考中有限几何逆的双侧恒等式；`truncated_nonzero_resolvent`, `truncated_spectrum` 给出全部谱 |
| 1属于极限谱 | `shift_one_spectral`：实际解 `(I-S)x=e₀` 将强迫所有坐标为1，和消失于无穷远矛盾 |
| 任意有限复系数多项式及常数项 | `poly`, `coeff_norm`; 数学的次数上界 d 对应 `range(d+1)`，零幂为整个 E 上的恒等算子 |
| 所有多项式的范数上界 | `poly_norm_upper` |
| 相位测试向量的实际定义及单位球界 | `phase`, `phase_norm`, `mul_phase`, `phase_vector`, `phase_vector_bound` |
| 测试坐标与全部多项式的精确范数 | `poly_apply_coordinate`, `poly_phase_coordinate`, `coeff_norm_le_poly`, `shift_poly_norm`, `truncated_poly_norm` |
| 每个多项式最终范数相等及收敛 | `polynomial_norm_eventually_equal`, `polynomial_norm_tendsto` |
| 谱恢复失败及完整合法见证 | `no_spectral_approximation`, `counterexample` |

没有计算或声称形式化整个移位谱；主反例只需实际谱点1和所有有限模型的谱 `{0}`。没有预设多项式范数公式、强极限、幂零性、有限维像或谱失败作为结构字段。所有这些性质都从上述 c₀ 算子定义推出。

题面与参考、rubric、源码及覆盖表由 `manifest.json` 的精确 SHA256 绑定。共同验证器逐题在新输出目录编译，限定为固定 Lean 标准库和固定 Mathlib 包缓存，不使用 ambient LEAN_PATH、OET项目构建或其他题输出。核审计允许公理仅 `Classical.choice`, `Quot.sound`, `propext`。人审状态 pending；没有候选模型运行。
