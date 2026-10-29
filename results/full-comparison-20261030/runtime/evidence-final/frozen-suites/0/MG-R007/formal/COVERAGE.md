# MG-R007：逐项 Lean 对应

冻结题目中的任意特征域、给定等变局部分裂、有限维与可数塔保持原意。主定理实际允许任意 monoid G，因此有限群题面是特例；没有群平均，没有要求转移满射。起始下标由 1 改为 0 是重编号。

| 原文义务 | 实际声明（MathGauge 命名空间） |
|---|---|
| 任意线性塔的真实复合与稳定像 | LinearTower.down / down_comp / ranges_stabilize / stable |
| 有限维线性塔内非空仿射纤维的相容点 | LinearTower.coherent_fiber；稳定由有限维 Artinian 性导出，不把 ML 作为假设 |
| 原等变 Hom 空间上相容分裂存在 | RepresentationTower.coherent_sections，实例化 IntertwiningMap 的有限维结构 |
| 实际坐标极限与逐坐标表示 | limit / limitRep / record / record_coordinate / assemble |
| 给定 i_infinity 单射、中间正合 | mapLimit / mapLimit_injective / mapLimit_exact |
| 所要求 G 表示直和及包含/投影相容 | full_split / SplitRepresentation.splitEquiv / split_inclusion / split_projection |
| 唯一等变核因子、全体分裂挠子 | kernel_factor / sections_classified / all_limit_sections |
| 坐标相容族与极限 Hom 对应 | assemble_coordinates（配合 assemble 的逐坐标定义） |
| 所有具有规定包含/投影的同构来自分裂 | SplitRepresentation.decomposition_classified |
| 整塔同构下全部解空间双射 | SectionTransport.coherentSectionsEquiv / inverse_record / inverse_diagram |
| 平移空间运输与恒等、复合 | transport_translation / transport_difference / transport_identity / transport_composition |
| 非满射转移的实际 split 行 | TowerBoundaries.product_row / collapse_diagram / collapse_section / collapse_not_surjective |
| 模特征下不能删去局部分裂 | primeRep / prime_row / no_prime_section，对任意素数 p 与任意特征 p 域；另有 ZMod 2 明确特例 |
| 无限维多项式反例及真实行图表 | polynomialTransition / polynomial_diagram / polynomial_row_split / no_coherent_polynomial_sections |
| 无自然首选 | shear / shear_diagram / shear_section / no_shear_fixed_section |
| 零商或零核的退化边界 | section_zero_quotient / section_zero_kernel |

证明直接使用真实线性映射和实际 IntertwiningMap，不存入相容选择或分解证书。R007Audit 动态审计所有命名空间声明，含自动辅助声明与实例；只允许 Lean/Mathlib 常用三项公理。人工审定仍待进行。
