# MG-R006：逐项 Lean 对应

题面和参考稿保持运行前冻结版本。Lean 以 n=0 编码原文 n=1，各层使用原阿贝尔群，不附加有限生成、核转移满射或提升存在假设。一般障碍理论对任意阿贝尔群塔成立；题面的有限 C_n 在具体反例中由 ZMod 的 Fintype 实例核验。

| 原文义务 | 实际声明（省略 MathGauge 前缀） |
|---|---|
| 产品差分、真实逆极限、逐层映射诱导 | AbelianTower.delta / limit / productMap / limitMap |
| 左端单射与中间正合 | limitMap_injective / limit_kernel |
| 逐层缺陷存在、选择改变为实际 coboundary | defect_exists / defect_change |
| coker Delta 的实际商、选择无关与加法 | ObstructionGroup / defect_class_independent / obstructionHom |
| 障碍消失 iff 存在原群中的兼容提升 | obstruction_zero_iff / lift_iff_coboundary |
| beta 满射推出 Delta_B 与障碍同态满射 | delta_surjective / obstruction_surjective |
| 精确核自由度，无首选原点 | lift_freedom（唯一兼容核元素） |
| 整塔态射的自然性 | delta_natural / obstructionMap / obstruction_natural |
| 全体记录可提升 iff 障碍群零 | obstruction_trivial_iff |
| 明示附加 alpha 满射的充分修复 | surjective_limit_of_kernel_surjective |
| 实际有限模幂、两类满射、行正合与交换 | AdicCounterexample.C / pi_surjective / gamma_surjective / rows_exact / diagram_commutes |
| 3 的逆元、唯一性、兼容与有限前缀提升 | record_equation / record_unique / record_compatible / finite_prefix_lift |
| 不存在全局整数提升 | no_compatible_lift / inverse_limit_not_surjective |
| lim A=0、lim B=Z、障碍群实际非零 | kernel_limit_zero / integerLimitEquiv / actual_obstruction_nontrivial |

全部声明在 R006Audit.lean 动态枚举（含实例、定义、辅助声明），只允许 propext、Classical.choice、Quot.sound。没有把结论放入结构字段。本目录用类型宇宙表达普通集合族；不涉及更强的大小约束。编译验证形式命题，原文对应是 AI 语义审核，人工审定仍待进行。
