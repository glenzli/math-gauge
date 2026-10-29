# MG-R005：当前 Lean 覆盖

本页对应冻结的 0.3.1 题面、参考与评分依据；实际数学声明在同目录 Lean 源码中。源码、编译顺序、原始输入及本页散列由 [manifest.json](manifest.json) 绑定。当前逐题构建与全声明审计见 [current-formal.json](current-formal.json)；复核方法见 [共用验证器](../../../../scripts/formal/README.md)。

作者联合交付与旧审计保存于 results/full-lean-terra/formal-history，属于阶段记录。下面保留该题的逐事实数学映射；不把其他题的声明或作者联合编译计数算成本题独立证明。AI 语义审核、Lean 核验与人工审定分别记录，人工仍待定。

本题在真正的实局部凸拓扑向量空间上使用 `ℝ≥0∞` 表示 `[0,+∞]`；凸性包含零权重和无穷端点，`convexCost_iff_jensen` 证明它与真实上图凸性等价。有限观测空间是实际连续对偶子空间的代数对偶，带弱评价拓扑；其有限维、Hausdorff 和拓扑向量空间结构已经建立，因此是题面指定的有限维拓扑。

## MG-R005

All names in this table have prefix `MathGauge.ConvexCost.`.

| Mathematical assertion | Formal evidence | Status |
|---|---|---|
| Correct extended-valued convexity, including zero coefficients | `convexCost_iff_jensen` | Proved |
| Lower semicontinuity gives closed real epigraph | `closed_epigraph` | Proved |
| Continuous real affine minorants define the relaxation | `affineHull`, `plainAffineHull`, `plain_affine_sup`, `clipped_minorant_iff` | Constructed and equivalence proved; affine minorants are not required to be nonnegative |
| Relaxation is lower semicontinuous, convex, and below the cost | `affineHull_lowerSemicontinuous`, `affineHull_convex`, `affineHull_le` | Proved |
| General locally convex strict affine separation, including horizontal separators | `exists_affine_minorant_gt_of_not_mem_closure` | Proved using Hahn–Banach and a strictly positive perturbation of the vertical coefficient |
| Closed epigraph equals closure of the original epigraph | `epigraph_affineHull_eq_closure` | Proved for convex proper cost |
| Nonempty vertical fibers are real rays; empty fibers correspond to infinity | `closed_epigraph_vertical_section` | Proved |
| Uniqueness of the function determined by the closed epigraph | `epigraph_injective`, `relaxation_unique` | Proved |
| Maximal lower semicontinuous convex minorant | `affineHull_maximal` | Proved |
| Competitors have the full EReal range, including both infinities, with the task’s closed real-height epigraph convention | `reconstruct_maximal_ereal_of_isClosed_real_epigraph`; existing `reconstruct_maximal_ereal` corollary | Proved for every closed-real-epigraph minorant of convex proper f; the wrapper does not require competitor convexity or properness |
| Relaxing twice has no further effect | `affineHull_idempotent` | Proved |
| Raw records are actual fiber infima; empty fiber gives infinity | `fiberInf`, `fiberInf_empty`, `record` | Constructed / proved |
| Fiber infima preserve convexity without attainment | `fiberInf_jensen`, `fiberInf_convex` | Proved by infimum arithmetic, preserving infinite/zero cases |
| Records have a finite point when the cost does | `fiberInf_proper` | Proved |
| q_F is continuous linear and has the exact evaluation formula | `observationMap`, `observationMap_apply` | Constructed / proved |
| Restriction maps and q_F=r_KF q_K | `restriction`, `restriction_observationMap` | Constructed / proved |
| Raw projection formula (1) | `fiberInf_comp`, `record_restriction` | Proved, including empty fibers |
| Relaxed projection monotonicity (3) | `relaxed_record_mono` | Proved |
| Finite observations form a directed family; reconstructed values are directed | `finite_observations_directed`, `reconstruct_directed` | Proved |
| Reconstruct from all finite records by formula (2) | `reconstruct` | Defined exactly by this supremum |
| One-dimensional observations suffice to dominate every affine minorant | proof of `reconstruct_eq_affineHull` | Actual span of each functional and evaluation functional are instantiated |
| Reconstruction equals the full relaxation | `reconstruct_eq_affineHull` | Proved |
| Main theorem: lsc, convex, minorant, proper, maximal, convex records | `finite_observation_reconstruction` | Proved under the original hypotheses |
| G=f iff f is already lower semicontinuous | `reconstruct_eq_iff_lowerSemicontinuous` | Proved |
| Optional double-relaxed projection formula (4) | `relaxed_record_projection` | Proved with the final relaxation retained |
| Indicator relaxation is indicator of closure | `hull_indicator` | Proved for nonempty convex sets |
| Open-halfline boundary is not recovered | `open_halfline_reconstruction`, `boundary_not_recovered` | Proved |
| Exponential example is continuous, convex, positive, has infimum zero and no minimizer | `exponential_continuous`, `exponential_convex`, `exponential_positive`, `exponential_inf_zero`, `exponential_zero_observation_unattained` | Proved |
| Hyperbola region is the stated set, closed, convex, nonempty | `hyperbolaRegion_description`, `hyperbolaRegion_closed`, `hyperbolaRegion_convex`, `hyperbolaRegion_nonempty` | Proved by an algebraic argument, without derivative calculations |
| A closed convex cost can have a nonclosed projection, so final relaxation is necessary | `hyperbola_projection`, `projected_closed_cost_requires_relaxation` | Proved with the actual first-coordinate map; values at zero are infinity before relaxation and zero afterward |

R005 boundaries: the hyperbola example is expressed directly through the first-coordinate projection of ℝ², rather than additionally identifying chosen bases of `F*` and `K*` with ℝ and ℝ². The exponential no-minimizer example uses the constant zero observation, rather than an explicit isomorphism from the dual of the zero subspace to the zero vector space. These are coordinate presentations of the same counterexamples; no counterexample conclusion is missing. Separate prose steps about convex-set closure and uniqueness of finite-dimensional vector-space topology use standard mathlib facts rather than new named project theorems.

0.3.1 对应说明：新包装定理直接接收题面给定的实高度上图闭性；原有 `LowerSemicontinuous` 接口作为推论保留。`ConvexCost f` 是真实上图凸性，`convexCost_iff_jensen` 保留等价接口。代码中非负成本上图的 `0 ≤ t` 条件不可删去。最大性在重构值为 `⊤` 时由序关系处理，在有限值时使用其上图中的实高度点；没有对取 `−∞` 的竞争函数调用仅适用于正规函数的表示定理。当前审计须绑定新题面、参考、rubric 与此源码，不沿用旧版本的编译收据作为新源码通过证据。
