# MG-P001：库检索、已补桥梁与实现边界

检查时间：2026-10-29 至 2026-10-30。此清单保留实际检索过程，**不是宣称不存在其他外部形式化**。此前4.29.1阶段的几何分类缺口已借助固定TauCeti和本题实际桥梁全部补齐；当前完整21模块的证据见 `COVERAGE.md` 与 `evidence/round2-lean436-20261030/`。

## 原默认4.29.1 Mathlib的实际检索结果

在固定提交 `5e932f97dd25535344f80f9dd8da3aab83df0fe6` 的完整 `Mathlib/` 源码中检索文件名及 `Hurewicz theorem`、`Whitehead theorem`、`Mayer.Vietoris`、`van.Kampen`、`unreduced suspension`、`Suspension`、`homotopy extension property` 等术语；另详细读取以下实际目录与文件：

- `AlgebraicTopology/SimplicialComplex/Basic.lean`：真实 `PreAbstractSimplicialComplex`／`AbstractSimplicialComplex`，但没有完成本题的顶点删除与几何实现主链。
- `Analysis/Convex/SimplicialComplex/Basic.lean`：几何单纯复形及 `Geometry.SimplicialComplex.space`；不能直接替代从本题抽象复形到 CW 商的证明。
- `AlgebraicTopology/SingularSet.lean`、`SimplicialSet/TopAdj.lean`：真实 simplicial-set 几何实现、标准单形与区间的比较。
- `Topology/Homotopy/Basic.lean`、`Equiv.lean`、`Contractible.lean`、`HomotopyGroup.lean`：真实连续同伦、同伦等价、可缩性、同伦群；前半段证明已实际复用。
- `Topology/CWComplex/{Abstract,Classical}/`：两种 CW 定义及有限性。`Abstract/Basic.lean` 的 TODO 明确还没有与 classical 定义之间的转换，不能把同名对象当成已接通接口。
- `AlgebraicTopology/SingularHomology/`：`Basic.lean`、`HomotopyInvariance.lean`、`HomotopyInvarianceTopCat.lean`。本提交没有所需的奇异同调 Mayer–Vietoris 与 Hurewicz 整条证明。
- `AlgebraicTopology/FundamentalGroupoid/`：基本群胚、基本群、单连通性等；未找到拓扑 van Kampen 主定理。
- `LinearAlgebra/FreeModule/PID.lean`：有非计算性的 Smith normal form 基础；这不自动给出本题局部链复形的构造及可执行判定证明。

全库的 `Topology/Sheaves/MayerVietoris.lean`、`CategoryTheory/Sites/SheafCohomology/MayerVietoris.lean` 是层上同调对象；`CategoryTheory/Limits/VanKampen.lean` 是范畴 van Kampen colimit；`AlgebraicTopology/ModelCategory/Homotopy.lean` 的 Whitehead 版本在抽象模型范畴。没有把这些命中当成本题所需的拓扑结论。

## 核实后的外部候选

外部仓库 [Vilin97/homotopy-groups-lean](https://github.com/Vilin97/homotopy-groups-lean/tree/c66523531ff172d7f41913d94e56921e790a1b47) 固定为 `c66523531ff172d7f41913d94e56921e790a1b47`。下列路径均相对 `examples/submissions/sphere_lower_homotopy_subsingleton/`：

| 外部入口 | 已核实的实际声明／对象 | 本次接入状态 |
|---|---|---|
| `Submission/Model/Suspension.lean` | 商空间 `Susp X = (I × X)/~`，两个端点分别压缩；商映射、泛性质、紧性、Hausdorff 性、函子性 | 已保留许可移植；固定工具链编译通过 |
| `Submission/WhiteheadTheorem/Basic.lean` | `WhiteheadTheorem (X Y : CWComplex) (f : X ⟶ Y) : IsWeakHomotopyEquiv f.hom → IsHomotopyEquiv f.hom` | 完整原始闭包已在独立原生4.32.2环境编译并内核审计；未接本题同调判据 |
| `Submission/Hurewicz/AbsoluteIsomorphism.lean` | `IsNConnected.absoluteHurewiczAddEquiv` 把 `(n+1)`-connected 空间的 `Additive (π_(n+2) X x)` 同构到实际整数奇异同调 `Hgrp (n+2) X` | 完整原始闭包已独立编译和内核审计；未接本题 |
| `Submission/Homology/MayerVietorisIso.lean` | 对 `interior A ∪ interior B = univ` 的真实覆盖，四个同调群为零时连接映射为同构；两个可缩子空间时有正维移位 | 完整原始闭包已独立编译和内核审计；本题具体应用仍待接入 |

Whitehead 的 CW 对象不是一个任意的“满足 Whitehead 的证书”：外部源码实际把骨架建成依次附着圆盘的 pushout 序列及其 colimit。正因为它是具体对象，本题的 `Realization K` 尚须构造到该对象的 CW 结构／同胚，不能仅凭两个文件都使用“CW”一词就套用定理。

`external-dependency-audit.json` 保存三个定理入口的完整 145 模块闭包、每个 Git blob、SHA-256、imports 和扫描结果。文件名 `VanishingSorries.lean` 仍存在，但其本次固定字节在去注释后没有未证占位符；没有因文件名而误判。静态无占位符不能代替外部工具链的编译及 `#print axioms` 闭包审计。

外部构建文件固定 Lean 4.32.2／Mathlib `905b95818eb32af7874a58b427f50c1711a5e96c`。以下八个路径在当前 4.29.1 Mathlib 源码与对应缓存中不存在：

- `Mathlib.Algebra.Exact.Basic`
- `Mathlib.Algebra.Order.Archimedean.Real.Basic`
- `Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic`
- `Mathlib.AlgebraicTopology.SimplicialSet.Nonempty`
- `Mathlib.AlgebraicTopology.SingularHomology.HomologyZero`
- `Mathlib.CategoryTheory.Limits.Preserves.SigmaConst`
- `Mathlib.Geometry.Convex.ConvexSpace.Defs`
- `Mathlib.Geometry.Convex.ConvexSpace.Module`

这些是实际接口差异，不能仅按路径缺失断定相应数学完全不存在。原样叶模块探测的结果是：`Submission.WhiteheadTheorem.Shapes.UnitInterval` 通过，`Submission.Homology.Basic` 在缺失 `HomologyZero.olean` 的第一个 import 即失败。之后已在独立 Lean 4.32.2 环境完成全部145个原始模块编译及5858个声明的公理闭包审计。全部原始源码散列与本题清单逐项一致，只有 propext、Classical.choice、Quot.sound。证据在 ../../validation/round2-external-p001/report.json；本题默认锁文件未升级。已移植的 Susp 模块只需把 `IsQuotientMap.isCoinducing.isOpen_preimage` 改为本提交的 `IsQuotientMap.isOpen_preimage`，这项变动已经实际编译核验。

## 4.29.1阶段已完成的几何工作

本题固定4.29.1环境已经编译11个实际对象模块，并由共享CurrentAudit检查390个MathGauge声明（含私有），公理闭包仅为三项基础公理。`GeneralSuspensionClassification.original_suspension_classification` 从原题全部假设推出一般K的实际同伦等价；`SuspensionRealization.all_suspensions_realized` 完成任意有限非空L的全部实现构造。这里使用紧的D与link圆柱到K的连续满射及显式分段同伦，绕过CW商定理但没有改变结论。

`TwoConeOpenCover` 进一步证明实际两锥几何实现的两极删除开集都可缩、覆盖全空间，其实际交通过归一化base坐标同伦等价于 `Realization L`。这些不是待输入的覆盖证书。

## 当前已接通的固定 TauCeti 通用桥

[固定提交 ab0153c6](https://github.com/TauCetiProject/TauCeti/tree/ab0153c648bc0f1364ea268fc806793beb01473a) 使用 Lean4.36.0-rc1 / Mathlib2cabef97b63d3275776b8b060d802de6a6fa1055。已经实际读取的关键声明如下，不能仅因旧Mathlib没有接口就认定外部实现不存在：

- `AlgebraicTopology/SimplicialComplex/Realization/Finite.lean`：`AbstractSimplicialComplex.realizationHomeomorphRange` 把有限复形的弱实现同胚到真实重心坐标像。
- `Realization/Coordinates.lean`、`Realization/CWComplex/Basic.lean`：坐标刻画和通过实际单形球参数建立的 classical CW 结构。`AbstractSimplicialComplex` 强制所有单点都是面，必须先限制到实际使用的顶点；不能给link添加无用的孤立顶点。
- `Realization/CWComplex/OrderedChainComplex.lean`：`TauCeti.orderedSimplicialHomologyIsoSingularHomology` 将实际ordered单纯链同调同构到Mathlib的奇异同调，系数可取整数。
- `AlgebraicTopology/SimplicialComplex/ChainComplex.lean`：有限面上的自由模、实际交错删面边界与增广映射。
- `AlgebraicTopology/Singular/MayerVietoris/Reduced.lean`：真实两可缩开集覆盖的 `TopCat.isIso_reducedMayerVietorisδ_of_contractible`，包括度数零的约化同调。
- `AlgebraicTopology/Singular/Reduced.lean`：约化同调的同伦不变性，以及非空空间约化H0为零推出道路连通。
- `AlgebraicTopology/FundamentalGroup/VanKampen/Basic.lean`：`TauCeti.simplyConnectedSpace_of_interior_union`。
- `AlgebraicTopology/Homotopy/Hurewicz/Comparison.lean`、`Homotopy/Whitehead.lean`：奇异整数同调消失、单连通与真实CW-type假设下的同伦群消失和可缩性。

这些较新端点的216个原始依赖模块已在4.36.0-rc1原生环境完整编译，6547个实际模块声明的公理闭包仅有propext、Classical.choice、Quot.sound；原始源码、Git blob、SHA-256、许可证和日志见 `../../validation/round2-external-tauceti/`。本题当前manifest使用专门的4.36固定profile，原4.29.1 manifest保留于历史。以下桥梁均是新增实际证明，不以外部库存在本身替代语义对齐。

## 已完成的本题接口

1. `CoordinateCore` 先限制到实际出现的顶点，证明限制与补零互逆且连续；`CoordinateCWBridge` 经有限弱实现与重心坐标像的同胚获得真实CW-type。没有向link添加孤立顶点。
2. `CoordinateReindex` 证明任意有限 `Type*` 顶点类型与 `Fin (card V)` 的坐标重标号同胚，因此TauCeti中Type0端点不缩小原题范围。
3. `TwoOpenContractibility` 与 `OriginalCriterion` 把已经证明的两可缩开集及交的同伦等价实际代入约化Mayer–Vietoris、零维道路连通性、van Kampen、Hurewicz和Whitehead。单连通性是从整数约化H0推出的结论，不是新增前提。
4. `OrderedAcyclicity` 证明cellular-to-ordered链同构保持零次增广（orientation scale在0次是1），再接到实际奇异同调的增广。没有只证明正维比较而遗漏约化H0。
5. `FiniteLocalChains` 证明有限面基上的整数kernel=image条件与上述增广quasi-isomorphism等价，以及高于实际顶点界的链群为零。
6. `FiniteBoundaryMatrix`、`FiniteMatrixCriterion` 给出真实有限面索引的整数矩阵，证明其mulVec就是上述实际边界，并证明有限矩阵条件与实际链正合性双向等价。
7. `FiniteLocalCriterion.original_contractible_iff_finiteLocalMatrixCriterion` 保留全部原几何前提和原量词，得到最终充要条件；`finiteLocalMatrixCriterion_eq_of_incident_faces` 证明它只依赖包含v的单形。

当前原题三个必答目标都已覆盖，不再保留未证的CW、Hurewicz、同调或有限截断前提。完整逐项映射和固定字节编译证据见 `COVERAGE.md`、`manifest.json`、`verification-report.json`。

## 实现边界

本题验证的是有限矩阵判据的正确性，具体Smith标准形求解器未实现。固定外部库里检查过的 `TauCeti/LinearAlgebra/Matrix/SmithNormalForm.lean` 是非奇异方阵的存在／唯一性结果，不能冒称已经提供通用矩形矩阵的可执行算法。题面要求给出并证明有限数据可检验的充要条件，没有要求提交求解程序；参考解中标准整数线性代数算法的说明保留原字节。

作者可选的无环非可缩link见证和所有球族不属于rubric必答义务，没有计入完整任务覆盖。人类审定仍待完成，候选模型试跑仍为零。
