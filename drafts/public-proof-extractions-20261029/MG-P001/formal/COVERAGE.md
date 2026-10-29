# 形式化覆盖：第二轮

状态：**full-task-kernel-verified**。本题的三项必答目标——全部合法三元组的同伦型分类、全部类型的实际实现构造、有限局部整数矩阵充要判据——均有实际对象上的 Lean 证明。21 个模块使用本题独立的固定 Lean 4.36.0-rc1／TauCeti profile；共享验证记录见 `evidence/round2-lean436-20261030/MG-P001/report.json`。这不是人类审定，也没有候选模型试跑。

题面、参考解、rubric 与版本 0.1.0 保持原字节。第一轮作者记录及其“未形式化”陈述属于当时状态；被更新的旧文件保存在 `../history/round1/`，原 `review.json` 保留。此前已经通过的 Lean 4.29.1 几何分类阶段保存在 `../history/round2-lean4.29/` 和 `evidence/round2-20261029/`，不再作为当前完整判据的工具链证据。

## 对象、量词和原假设

`VertexDeletion.lean` 使用 Mathlib 的 `PreAbstractSimplicialComplex V`，其中 `V : Type*` 有有限类型实例。它记录非空面；补回通常约定中的空面不改变几何实现。有限复形可取自己的有限顶点集，额外未用顶点也允许。`carrier K` 是 `V → ℝ` 中非负、总和为 1、支集包含于实际单形的重心坐标集合，`Realization K` 取通常子空间拓扑。

`deletion`、`vertex_link`、`closed_star` 均由真实面集定义。`Punctured K v` 的条件 `x v < 1` 经 `punctured_iff_ne_vertex` 和 `punctured_complement_homeomorph` 证明就是删去实际顶点的空间。`ContractibleSpace` 包含非空性。`B ≤ K` 是子复形关系，`e.toFun = punctured_inclusion_map B v` 指定原包含映射本身为同伦等价，未换成两空间间某个任意等价。

`original_suspension_classification` 保留任意有限 K、v、B 及全部原前提，得出 K 的实际几何实现同伦等价于 link 实现的非约化悬挂。`all_suspensions_realized` 对每个有顶点的有限 L，用两个新顶点构造 K、单边 B，同时给出所有原假设及悬挂同胚。

TauCeti 的同调端点使用 `Type`，本题没有据此缩小原量词。`coordinateReindexHomeomorph` 和 `smallCoordinateHomeomorph` 证明任意有限 `Type*` 的真实坐标实现与 `Fin (card V)` 重标号实现同胚。`usedComplex` 再限制到实际出现的顶点；没有为 link 添加额外孤立点。实际 CW 结构通过 `coordinateTauHomeomorph` 从 TauCeti 的真实单纯实现转移，不是一个假设目标成立的证书。

## 逐项覆盖

| 原题／证明义务 | 主要实际声明 | 状态 |
|---|---|---|
| 有限面、通常重心实现、删除、link、闭星形 | `carrier`, `Realization`, `deletion`, `vertex_link`, `closed_star` | 已编码 |
| 删除与闭星形的并、交及坐标刻画 | `deletion_union_star`, `deletion_inter_star`, `mem_carrier_deletion_iff` | 已证明 |
| 穿孔实现到删除实现的径向强变形收缩 | `radial_homotopy`, `radial_homotopy_fixes_deletion`, `punctured_deletion_equiv` | 已证明；在每个原单形内且不经过 v |
| 原包含等价排除空 link | `edge_of_punctured_inclusion_equiv`, `vertex_link_has_vertex` | 已证明；从实际同伦和中间值性质得到边 |
| 通常非约化悬挂的商空间及拓扑 | `Susp`, `Susp.mk`, `Susp.lift` | 有许可证复用并适配 |
| 有限几何实现紧性、锥的实际拼接商 | `compact_realization`, `deletion_cone_surjective`, `deletion_cone_quotient`, `timed_deletion_cone_quotient` | 已证明 |
| 全部合法三元组的同伦型 | `original_suspension_classification` | **完整原前提下已证明** |
| 分类的两个实际复合同伦 | `deletion_collapse_return_homotopy`, `suspension_retime_homotopy`, `collapse_return_eq_retime` | 已证明；不要求删除收缩固定 link |
| 每个非空有限 L 的两锥及单边实现 | `realizing_original_hypotheses`, `all_suspensions_realized` | **全部实现已证明** |
| 两锥实现与通常悬挂的同胚 | `suspension_realization_homeomorph` | 已证明 |
| 实际两可缩开集覆盖及交与 L 的等价 | `pole_open_cover`, `pole_open_contractible`, `equatorial_equiv` | 已证明 |
| 未用顶点剔除、弱实现和坐标实现同胚、实际 CW-type | `usedCoordinateHomeomorph`, `coordinateTauHomeomorph`, `coordinateRealization_cwType` | 已证明 |
| 约化整数 H0 和正维同调的 Mayer–Vietoris、van Kampen、Hurewicz、Whitehead 应用 | `contractible_iff_model_reducedIntegralHomology_isZero`, `realizing_contractible_iff_reduced` | 已证明；不把任意无环空间当作可缩空间 |
| ordered 单纯链到实际奇异同调，含零次增广相容性 | `cellularToOrdered_comp_augmentation`, `orderedAugmentation_quasiIso_iff` | 已证明；系数实际为 ℤ |
| 原前提下整数增广链无环判据 | `original_contractible_iff_finiteOrderedAcyclic` | 已证明，无新增同调前提 |
| 有限度数截断与元素级整数正合性 | `no_cells_above_vertex_bound`, `chains_zero_above_vertex_bound`, `finiteAugmentedExact_iff_quasiIso` | 已证明 |
| 实际整数边界矩阵、删面符号和非关联零项 | `boundaryMatrix_mulVec`, `boundaryMatrix_face`, `boundaryMatrix_zero_of_not_face`, `augmentation_coordinates` | 已证明 |
| 矩阵正合性与实际增广链正合性等价 | `finiteMatrixExact_iff_augmented` | 已证明 |
| 原题的有限局部矩阵充要判据 | `original_contractible_iff_finiteLocalMatrixCriterion` | **完整原前提下已证明** |
| 判据只依赖包含 v 的单形 | `vertex_link_eq_of_incident_faces`, `finiteLocalMatrixCriterion_eq_of_incident_faces` | 已证明 |

分类的 Lean 证明直接构造同伦等价，不另行重复参考解中的 CW 商映射路线。锥高度 t 和同伦时间 s 使用 `(1+s)t-s`，非负部分留在原锥，负部分沿删除复形的收缩，拼接边界处已证明相容和连续。数学目标与结论不变。

## 有限判据的精确含义

对 link 的实际已用顶点数 N，链群是各维真实面上的有限自由 ℤ 模。边界矩阵的列恰为交错删面：相应面上的系数为 `(-1)^j`，其他项为 0；零次增广是所有坐标之和。`FiniteMatrixExact` 要求：

1. 总和为零的 0-链是 1-边界；
2. 对 `n : Fin N`，`D_n z = 0` 当且仅有对应的上一级边界可表示 z，即 `ker D_n ⊆ im D_(n+1)`；反向包含由实际链复形的边界平方为零保证。

高于顶点界的面集为空，链群为零，所以有限检查已经涵盖所有度数。这些是整数模正合性，包含约化零维信息和全部整数挠信息；没有改用有理秩或欧拉示性数。最终定理的唯一几何前提仍是原题前提。

Lean 验证了该有限矩阵判据的正确性、矩阵与真实面关联的公式、有限截断以及完整拓扑桥。**具体 Smith 标准形求解程序未实现。** 参考解中以整数标准形有限检验正合性的标准算法说明保持原样；这里没有将非计算性的矩阵存在定理标作已实现的通用矩形矩阵算法，也没有把实现一个求解器增加为题目新义务。

作者可选的球族与无环非可缩 link 见证不是 rubric 的必答目标，本轮不宣称已将这些附加例子逐一形式化。也不提供任意有限悬挂之间同伦等价的判定算法。

## 固定环境、来源与审计

当前 `manifest.json` 使用固定 profile `lean-4.36.0-rc1-tauceti`：

- Lean `leanprover/lean4:v4.36.0-rc1`；
- Mathlib `2cabef97b63d3275776b8b060d802de6a6fa1055`；
- TauCeti `ab0153c648bc0f1364ea268fc806793beb01473a`。

默认题集的 Lean 4.29.1 profile 未改变。当前审计由共享 `render_audit` 产生，重编译全部21模块，并检查全部加载的 `MathGauge` 常量，包含私有辅助及完整公理依赖。仅允许 `propext`、`Classical.choice`、`Quot.sound`。声明数不等于完成度；本表按实际声明与原题逐项对齐。原输入、源码、覆盖文档、审计器及日志均以 SHA-256 绑定。

悬挂源码来自 [Vilin97/homotopy-groups-lean 固定提交 c6652353](https://github.com/Vilin97/homotopy-groups-lean/tree/c66523531ff172d7f41913d94e56921e790a1b47)，保留原作者 Vasily Ilin、Apache-2.0、LICENSE、NOTICE 和原字节；见 `vendor/PROVENANCE.json`。适配仅涉及命名空间和商映射 API 拼写。

[固定 TauCeti](https://github.com/TauCetiProject/TauCeti/tree/ab0153c648bc0f1364ea268fc806793beb01473a) 的216个原始依赖模块在独立原生环境编译，6547个实际模块声明的完整公理闭包仅有上述三项。原始源码 ZIP、逐文件 Git blob 与 SHA-256、许可证、构建和审计日志保存在 `../../validation/round2-external-tauceti/`；本题 `tauceti-dependency-audit.json` 绑定该报告。之前核验过的另一145模块外部库仍保留为来源调查记录，完整判据使用这里的 TauCeti 实际接口。

自然语言数学复审、作者工作、独立 AI 语义审核、内核验证和待完成人类审定分别记于 `../round2-review.json`。`../reference.md` 的最后状态段保留第一轮历史，不作为当前形式化状态。
