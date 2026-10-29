# MG-R020：原题与实际对象 Lean 对齐

本题是全称构造失败题；完整形式化目标是构造满足全部题设的实际数据，并证明所要求的比较不存在。没有把局部失败替代原题，也没有把存在性作为结构字段。

全部本地数学声明位于 `MathGauge.PadicOrthogonal`。

| 原文内容 | Lean 对应 |
| --- | --- |
| 系数环是特征零的完备离散赋值环 | `R = PadicInt 2`；`coefficient_dvr`、`coefficient_characteristic_zero`、`coefficient_complete` |
| 极大理想是由 2 生成的理想 | `coefficient_maximal_ideal` |
| 5 可逆及其真实倒数 | `five_is_unit`、`fifth`、`five_fifth`、`fifth_five` |
| 两个实际对称幂等矩阵 | `p`、`q`、`p_symmetric`、`q_symmetric`、`p_idempotent`、`q_idempotent` |
| 全部正交关系及和为恒等 | `IsSymmetricDecomposition`、`complementary_valid` |
| 给定相似的实际逆、同余和两项交织 | `v`、`w`、`v_w`、`w_v`、`v_unit`、`v_congr_identity`、`q_v`、`counterexample.intertwines` |
| 一般题设与目标 | `ComparisonData`、`HasIsometricComparison`；前者只存给定相似及题设，后者才要求等距比较 |
| 任何正交交织矩阵的第一列所受约束 | `q_fixed_vector`、`no_orthogonal_intertwiner` |
| 实际模 8 平方障碍 | `squares_mod_eight`、`no_square_mod_eight`、`no_normalized_five_square`，使用 `PadicInt.toZModPow 3` |
| 全部数据合法且无所求比较 | `counterexample`、`counterexample_has_no_isometric_comparison`、`universal_target_false` |
| 给定相似的 Gram 矩阵 | `v_gram` |

`counterexample` 的维数与分解项数均为 2，满足正整数范围；一般原目标只需一个合法实例即可被否定。无解定理直接排除所有矩阵，未仅排除标量归一化，也未假定其可逆或同余恒等。

`ComparisonData` 中 `source_valid`、`target_valid`、`near_identity` 和 `intertwines` 都是题设本身；具体反例逐项构造了这些证明。没有包含待证等距比较或平方根的字段。

Mathlib 背景是实际已证明的 p-adic 环结构和矩阵运算。没有新公理、占位证明或外部未证书边界。当前文件只是作者的对应说明；独立构建与公理审核结果另行绑定源散列，人工审核仍为 pending。
