# 形式化覆盖

本表区分作者数学义务、输入附件及参考扩充；编译通过不自动表示题意对齐，人工审核仍 pending。

| 数学义务 | 声明 | 范围 |
|---|---|---|
| 有限正源值比值与逐点界 | `ratio_le_iff` | 任意集合，允许空索引 |
| 全部扩展系数可行性 | `bound_iff` | 处理 0、有限正值与∞源值 |
| 有限可行系数存在 | `finite_bound_exists_iff` | 无需 H |
| 任意最小有限系数的值 | `least_coefficient_eq` | 非循环，用中间系数反证 |
| 最小有限系数存在判据 | `least_finite_exists_iff` | 零比值时保留无穷源值条件 |
| 单点非取到实例 | `boundary_ratio`, `boundary_feasible`, `boundary_not_attained` | 实际 d=∞, e=1 |

数值数据不假定是度量；构造原算子、矩阵最优与算法可计算性不属于题目。
