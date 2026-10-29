# 形式化覆盖

本表区分作者数学义务、输入附件及参考扩充；编译通过不自动表示题意对齐，人工审核仍 pending。

| 数学义务 | 声明 | 范围 |
|---|---|---|
| 逐层下降与有限稳定界 | `layers_decreasing`, `layers_stabilize` | 任意 Y，仅 B 有限 |
| 稳定终层的成员判据 | `terminal_mem` | 真实递推终层，不输入稳定证书 |
| 无停顿精确桥接 | `exact_realization` | 依赖 Realizes；强于题面停顿条件 |
| 无停顿条件下最大性 | `maximal_invariant` | 对任意实际前向不变 S |
| 原条件下实际安全集的最大性 | `safe_subset`, `safe_step`, `safe_maximal` | 无需停顿条件 |
| 原停顿条件下安全充分性 | `terminal_sound_for_stuttering` | 未要求停止发生的时间界 |
| 原等式的完整反例 | `stuttering_counterexample` | Bool 实际模型，四项共同核验 |

前三个模块是输入实现；`Reference.lean` 只供评审，包含原假设下可证方向与分离反例。
