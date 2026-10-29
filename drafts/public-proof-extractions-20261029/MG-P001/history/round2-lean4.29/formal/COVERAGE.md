# 形式化覆盖：第二轮

状态：**partial-actual-object**。原题的同伦型分类与全部实现构造已经在实际有限复形上完成；整数局部充要判据仍未完成，所以整题不能标记为完整形式化。题面、参考解、rubric 与版本 0.1.0 保持原字节。第一轮覆盖说明保存在 `../history/round1/formal/COVERAGE.md`；原 `review.json` 保留为第一轮作者证据。

## 对象与量词

`VertexDeletion.lean` 使用 Mathlib 的 `PreAbstractSimplicialComplex V` 和有限顶点类型 `V`。非空面约定与通常包含空面的约定只差空面，不改变几何实现；有限复形可取它的有限顶点集为 `V`，额外无用顶点也允许。`carrier K` 是 `V → ℝ` 中非负、总和为 1、支集包含于某个实际单形的坐标集合，`Realization K` 取通常子空间拓扑。

`deletion`、`vertex_link`、`closed_star` 都由实际有限面定义。`Punctured K v` 的坐标条件 `x v < 1`，通过 `punctured_iff_ne_vertex` 与 `punctured_complement_homeomorph` 证明等于删去实际顶点的空间。Lean 的 `ContractibleSpace` 已包含非空性。`B ≤ K` 是实际子复形关系；`e.toFun = punctured_inclusion_map B v` 要求原包含映射本身是同伦等价，没有替换成任意两空间存在某个等价。

`original_suspension_classification` 保留任意有限 K、v、B 及两条原前提，证明 `Nonempty (Realization K ≃ₕ Susp (Realization (vertex_link K v)))`。`all_suspensions_realized` 对任意有顶点的有限 L 构造两个新顶点的 K 与单边 B，同时给出全部原前提和 `Realization K ≃ₜ Susp (Realization L)`。没有使用目标结论证书、未证结构字段或新增公理。

## 逐项覆盖

| 原题／证明义务 | 实际 Lean 声明 | 状态 |
|---|---|---|
| 有限复形、实际重心几何实现、删点、link、闭星形 | `carrier`, `Realization`, `deletion`, `vertex_link`, `closed_star`, `vertex` | 已编码 |
| 删除与闭星形并为 K、交为 link；删除实现的坐标刻画 | `deletion_union_star`, `deletion_inter_star`, `mem_carrier_deletion_iff` | 已证明 |
| 穿孔到删除的径向强变形收缩，保留实际单形且不穿过 v | `radial_homotopy`, `radial_homotopy_fixes_deletion`, `punctured_deletion_equiv`, `deletion_contractible` | 已证明 |
| 包含 B 的原假设排除空 link | `edge_of_punctured_inclusion_equiv`, `vertex_link_has_vertex` | 已证明；使用真实同伦路径与中间值定理 |
| 非约化悬挂的商空间、商拓扑、泛性质、紧性、Hausdorff 性 | `VendoredSuspension.lean` 的 `Susp`, `Susp.mk`, `Susp.lift` 等 | 有许可证移植并编译 |
| 每个有限真实几何实现的紧性 | `compact_realization`, `isCompact_carrier` | 已证明 |
| 一般 K 的闭删除与 link 锥的连续拼接 | `link_cone_point`, `radial_link`, `deletion_cone_surjective`, `deletion_cone_quotient`, `timed_deletion_cone_quotient` | 已证明；实际紧空间连续满射保证商拓扑 |
| 一般 K 的完整同伦型分类 | `general_suspension_equiv_of_contraction`, `original_suspension_classification` | **已证明完整原几何前提下的分类** |
| 悬挂的两个复合同伦 | `deletion_collapse_return_homotopy`, `suspension_retime_homotopy`, `collapse_return_eq_retime` | 已证明；不要求删除的收缩固定 link |
| 对任意有限非空 L 的两锥 K 和单边 B，满足全部原前提 | `realizing_original_hypotheses`, `edge_inclusion_is_homotopy_equivalence`, `all_suspensions_realized` | **已证明全部实现** |
| 两锥复形的实际实现等于通常悬挂 | `suspension_realization_homeomorph` | 已证明真实同胚 |
| 两锥空间的两个可缩开集与实际交 | `pole_open_cover`, `isOpen_pole_open`, `pole_open_contractible` | 已证明 |
| 两开集的交同伦等价于原 L | `equatorial_equiv`, `equatorial_homotopy`, `equatorial_nonempty` | 已证明真实归一化和直线同伦 |
| 整数约化同调消失与 X 可缩的双向结论 | 尚未完成外部同调／CW 接口与上述对象的组合 | **未证明** |
| 只由局部有限关联数据形成增广整数链复形，并证明有限正合性判定等价 | 尚缺单纯／奇异同调比较的本题实例及有限决策正确性 | **未证明** |
| 作者可选无环非可缩 link 例子 | 本轮没有将矩阵检查当成拓扑证明 | 未形式化；非必答目标 |

形式证明直接构造分类的同伦等价，不必沿参考解的 CW 商映射路线另证 `K → K/D`。参考解本身没有因此改写。显式锥同伦在时间 s、锥高度 t 使用 `(1+s)t-s`：非负部分仍在原锥，负部分沿删除复形的收缩；在共同底面与顶点处的相容性及连续性均已核验。

## 固定环境与证据

当前 11 模块 manifest 固定 Lean **4.29.1**、Mathlib **5e932f97dd25535344f80f9dd8da3aab83df0fe6**。`CurrentAudit.lean` 逐字复用仓库共享生成器，检查全部加载的 `MathGauge` 常量（包括私有辅助）及完整公理依赖，只允许 `propext`、`Classical.choice`、`Quot.sound`。共享验证器的逐模块日志、文件散列与声明审计保存在 `evidence/round2-20261029/`。声明数不代表完成原题的比例。

悬挂对象取自 [Vilin97/homotopy-groups-lean 的固定提交 c6652353](https://github.com/Vilin97/homotopy-groups-lean/tree/c66523531ff172d7f41913d94e56921e790a1b47)，作者 Vasily Ilin，Apache-2.0。原文件、许可证、原 NOTICE、移植记录分别为 `vendor/Suspension.lean.original`、`vendor/LICENSE`、`vendor/NOTICE`、`vendor/PROVENANCE.json`。修改仅是命名空间、适配旧 Mathlib 的商映射 API 拼写及来源头，没有改变数学定义或结论。

外部 Whitehead、Hurewicz、奇异 Mayer–Vietoris 三个入口的 **145 个原始模块**已经在独立 Lean **4.32.2**／Mathlib **905b95818eb32af7874a58b427f50c1711a5e96c** 环境全部编译，并审计其实际模块来源的 **5858 个声明**，公理闭包仅有上述三项。报告为 `../../validation/round2-external-p001/report.json`；本题 `external-dependency-audit.json` 已逐项对齐其 145 个源码散列。外部基础库核验不是本题第三项目标的完成证据。

另外已定位 TauCeti 固定提交 `ab0153c648bc0f1364ea268fc806793beb01473a` 的实际有限弱实现／坐标实现同胚、CW 构造及 ordered 单纯同调到奇异同调比较；所需新版环境和本题接口属于后续独立证据，当前 manifest 不把它们计为已经接通。精确检查路径、版本差异与剩余工作见 `LIBRARY-GAPS.md`。

本轮为 AI 数学复审及形式化工作；人类审阅仍待完成，候选试跑为零。自然语言论证复审与 Lean 覆盖界限分别记录于 `../round2-review.json`。
