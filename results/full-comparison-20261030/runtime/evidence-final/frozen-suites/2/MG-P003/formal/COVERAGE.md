# MG-P003：第二轮 Lean 覆盖账本

状态：**实质辅助模块已形式化；完整题面尚未形式化。** 编译与公理闭包通过也不能将本状态改为完整覆盖。题面、参考与评分标准保持原字节，manifest 固定其 SHA256。命名空间为 `MathGauge.PublicProof.Semilocal`。

环境固定为 Lean 4.29.1、Mathlib `5e932f97dd25535344f80f9dd8da3aab83df0fe6`。只使用公开 Mathlib 与 Lean 标准库；依赖项目自身的数学库不进入导入路径。代码未采用 `sorry`、`admit` 或额外公理，也没有把 G1–G3 包装成已证明证书。

## 已有对应

| 原文步骤 | 实际 Lean 对象与声明 | 覆盖边界 |
| --- | --- | --- |
| 有限素理想并之补与半局部化 | `outside_primes`、`disjoint_outside_primes_iff`、`finite_prime_localization` | 使用真正 `CommRing`、`Ideal`、`PrimeSpectrum`、`Localization`；比题面环论范围更一般，没有要求点在环境中闭。 |
| 局部化的点与闭点 | `localization_spectrum_image_iff`、`localization_maximal_contracts_to_selected`、`maximal_map_selected_iff`、`finite_localization_closed_points`、`nonempty_localization_closed_points` | 局部化谱的像是选定点的一般化之并；闭点对应按包含极大的选定素理想。没有把所有选定点都误当作闭点。 |
| 真正的仿射概形 S | `finite_point_scheme` 及三个定理 | `AlgebraicGeometry.Spec` 构造真实概形及结构层；已证闭点有限非空和含全部闭点的开集等于全空间。尚未构造其与光滑拟射影环境的完整关系。 |
| 分离闭点的邻域系统 | `Separates`、`separates_inter`、`exists_separating_refinement`、`separates_cover`、`separates_shrink` | 真正谱拓扑开集；证明共同细化、删去相反闭点的余终性和保持覆盖的收缩仍保留指定点。 |
| 在成功阶段上取极限 | `exists_successful_separating_refinement`、`direct_limit_exact_of_cofinal_exact` | 前者对显式任意谓词 P 和收缩前提证明索引事实；后者使用 Mathlib 真正商构造 `DirectLimit` 与 `Function.Exact`。没有声称 P 已由动机几何实现。 |
| 滤过极限中的单射、满射 | `direct_limit_map_injective`、`direct_limit_map_surjective` | 自然阿贝尔群系统的实际同态；不是未定义的“极限”符号。 |
| 真实邻域余极限与层化单位 | `SetNeighborhoods`、`neighborhood_index_filtered`、`neighborhood_value`、`neighborhood_value_map`、`finite_neighborhood_sheafification_comparison` | 对任意拓扑空间上的真实阿贝尔群预层，值是 `CategoryTheory.Limits.colimit`；箭头由真实 `CategoryTheory.toSheafify` 诱导。并证明代表元公式及分量单射诱导极限单射。 |
| 单点基例 | `singleton_neighborhood_comparison_isIso`、`singleton_neighborhood_value_comparison_isIso` | 使用真实茎和真实小位点层化单位；单点邻域范畴与 Mathlib 茎索引范畴的顺序同构明确给出。尚未证明题面光滑大位点层化限制到小位点的比较。 |
| 最后的同构论证 | `comparison_bijective` | 真实阿贝尔群交换图：上行中间正合、下行复形、首箭头单射、中间竖箭头双射、右竖箭头单射推出左竖箭头双射。没有额外要求下行末端满射。 |

`FilteredExactness.lean` 中的具体商极限与 `NeighborhoodValues.lean` 中的范畴极限是两种真实构造；本组代码尚未建立这两种构造在具体邻域系统上的自然同构，也没有凭命名把它们视作已经连接。范畴邻域极限保持单射已直接使用 Mathlib 的滤过阿贝尔群极限证明。

## 未覆盖的原题内容

完整终点必须量化任意域、实际光滑分离有限型概形的有限对应范畴、实际同伦不变带转移预层、光滑拟射影 X 上任意有限非空点集，并证明题面邻域余极限的**典范**层化同态为同构。当前没有这一完整类型的 Lean 定理。

主要缺口为：实际有限对应与转移结构在固定依赖中的集成；拟射影有限点仿射邻域及各次局部化/交叠的极限比较；G1 的半局部泛点单射；G2 的 Zariski 分离商之转移及同伦不变性；G3 的有限点收缩正合性（包括有限底域）；光滑大位点与小 Zariski 位点层化比较；将所有自然映射与闭点数归纳组装到完整目标。精确命题见 [GAPS.md](GAPS.md)。

上表的点集/环论范围没有替换题面的领域；它们是原证明中的辅助结果。`finite_neighborhood_sheafification_comparison` 是实际目标箭头的小位点部分定义，**不是**一般有限点情形的同构定理。

## 外部证明复用审查

已审查公开 `kangxyz/motivic` 固定提交 `a6805c4a87cdfd7717dd7a94039246a167f15380`。源码中确有实际有限对应范畴、带转移预层、转移保持的 Nisnevich 层化以及任意域上的 HI 保持定理；因此不能声称公开 Lean 生态没有这些结构。其 Lean 4.34.1、Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`、Aglib `2c34f185fa859e862661f939cd216b07bcccfb26` 与本题固定环境不同，许可证为 Apache-2.0。

本轮检查了真实声明及若干关键证明，不只读取说明文档。定向检索和所读端点尚未找到本题任意有限点半局部单位满射/比较定理：已见的 Nis 局部可提升、单点局部消失、分离预层稠密开检测均不足以替代该有限点命题。未在新版独立环境重放该库完整编译和公理闭包，未导入或移植该库源码。审查记录和源码 blob 身份见 [external-library-review.json](external-library-review.json)。这些限制不是全互联网不存在相应证明的断言。

## 证据分层

`CurrentAudit.lean` 由仓库共用模板生成，审计本清单所有 `MathGauge` 声明及私有辅助声明的完整公理依赖闭包。声明数不是定理数。共用验证器的 `passed` 仅对应本清单源码、冻结输入和受限公理闭包；不证明本表未覆盖的几何事实。第二轮 AI 数学审查记录在 `../round2-review.md` 与 `../round2-review.json`；人工审定仍待进行，真实候选校准未运行。
