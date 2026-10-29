# MG-R008：当前 Lean 覆盖

本页对应冻结的 0.3.0 题面、参考与评分依据；源码、明确编译顺序、原始输入及本页散列由 [manifest.json](manifest.json) 绑定。当前逐题构建与全声明审计见 [current-formal.json](current-formal.json)，复核方法见 [共用验证器](../../../../scripts/formal/README.md)。作者联合核心交付和后续扩展均保留在 results/full-lean-terra/formal-history，历史未覆盖措辞由本页接续。人工审定仍待定。

原任务主要求和参考稿的四项附加结论均已完成：有限层幂等判据、任意塔保有限极限、乘二塔、秩二投影塔。不同完整证明路线不被声称逐句同构；具体边界如下。

使用真正的 `ModuleCat.{u} ℤ` 表示原宇宙内的阿贝尔群与所有群同态，塔仅有有限自由阶段及相邻映射。所有复合过渡递归构造；记录采用真实 `Module.DirectLimit`。自然变换保留所有 U 小对象和态射的量词，`recordNatEquivInLargerUniverse.{u,v}` 明确运输到任意更大的环境宇宙。单位测试用 `ULift.{u} ℤ`，并以 `ULift.moduleEquiv` 连接普通整数，不改变测试群。标准范畴极限由真实 Cone、IsLimit 和典范比较构造。

## MG-R008

Tower names have prefix `MathGauge.Tower.FreeTower.`; tensor/limit lemmas have prefix `MathGauge.TensorClassification.`.

| Mathematical assertion | Formal evidence | Status |
|---|---|---|
| Arbitrary adjacent finite-free inverse tower | `MathGauge.Tower.FreeTower` | Actual structure, with only original data and finite/free hypotheses |
| Composite transition identities | `transition_self`, `transition_succ`, `transition_comp` | Proved from recursion |
| Precomposition defines a directed Hom system | `homTransition`, `homDirectedSystem` | Constructed and laws proved |
| Records have representatives | `record_exists` | Proved |
| Record equality is exactly eventual equality at a common stage | `record_eq_iff` | Proved in both directions |
| Addition and scalar multiplication exist on records; inclusions are linear | `Record`, `recordOf` | Inherited from the actual constructed module direct limit |
| Postcomposition is well-defined and functorial | `recordMap`, `recordMap_of`, `recordMap_id`, `recordMap_comp`, `recordFunctor` | Constructed and proved |
| M is the actual direct limit of finite duals | `Invariant` | Definition `Record R` |
| M is countable | `dualCountable`, `invariantCountable` | Proved using finite bases and a surjection from the sigma of stages |
| M is torsion free even with noninjective transitions | `invariantTorsionFree` | Proved using eventual vanishing in the direct limit |
| Finite-dual tensor–Hom stage formula | `tensorRecordEquiv_of_tmul` with mathlib `dualTensorHomEquiv` | Proved, with actual finite-free stages instantiated |
| Tensor commutes with this direct limit | construction of `tensorRecordEquiv` uses `TensorProduct.directLimitLeft` | Actual equivalence instantiated |
| Record functor is naturally M tensor - | `tensorRecordEquiv`, `tensorRecordEquiv_natural`, `tensorRecordNatIso` | Constructed and proved |
| Countable product comparison has the intended coordinate formula | `countableProductMap_tmul`, `recordProductMap`, `recordProduct_tensor` | Proved for canonical maps |
| Product comparison surjectivity is unchanged by the tensor model | `recordProduct_surjective_iff` | Proved |
| Each tensor has coordinates in one finitely generated subgroup | `tensor_coordinates_finitely_generated` | Proved by tensor induction |
| Countable product surjectivity forces finite generation | `finite_of_countableProduct_surjective` | Proved using an actual surjective enumeration; countability is explicit |
| Ordinary representability implies canonical product surjectivity | `representable_countableProduct_surjective` | Proved directly by naturality and an actual product of Hom maps |
| Finite generated torsion free integer modules are finite free | `finite_iff_finite_free`, uses mathlib `Module.free_of_finite_type_torsion_free'` | Instantiated on the actual invariant |
| Finite-free tensor is represented by its dual | `finiteDualEquiv`, `finiteDualEquiv_tmul`, `finiteDualRepresentation` | Actual linear equivalences and natural isomorphism constructed |
| Representable functors preserve canonical compatible limits | `ModuleDiagram.representation_comparison_bijective` | Proved with explicit inverse and injectivity |
| Compatible-family model is an actual category limit | `categoryDiagram`, `categoryCone`, `categoryLift`, `categoryConeIsLimit` | Actual Cone and IsLimit constructed |
| Canonical comparison bijective implies standard categorical preservation | `categoryTensorConeIsLimit`, `compatible_comparison_implies_preservesLimit`, `representation_preservesLimit` | Proved |
| Preserving countable category limits forces product surjectivity | `categorical_countable_limits_implies_product_surjective` | Proved using the discrete countable scalar diagram and its actual limit cone |
| Five-way main classification | `classification`, `representable_iff_finite`, `countable_limits_iff_finite`, `product_surjective_iff_finite`, `finite_iff_finite_free` | Proved |
| Under the criterion, all U-small limits are preserved | `finite_preserves_all_limits` | Proved for arbitrary U-small category and diagram, not only countable ones |
| Construct a representing object | `canonicalRepresentation` | Actual natural isomorphism with Hom(M*, -) |
| All representing objects, up to isomorphism | `all_record_representing_objects`, `representingObjectEquiv` | Proved with direct covariant Yoneda; direction checked |
| All tensor-functor natural transformations come from one module homomorphism | `nat_tmul`, `tensorNatEquiv` | Proved for actual category natural transformations |
| All record-functor natural transformations | `recordToTensorNatEquiv`, `recordNatEquiv` | Actual equivalence constructed |
| Identity and composition laws | `recordNatEquiv_id`, `recordNatEquiv_comp` | Proved |
| Natural isomorphism iff invariant groups are isomorphic | `record_natIso_iff` | Proved |
| Arbitrarily larger ambient universe V | `recordNatEquivInLargerUniverse` | Explicitly lifted equivalence; original U-object quantifiers unchanged |

## Exact correspondence

| Reference conclusion | Actual compiled declaration | Coverage |
|---|---|---|
| Finitely many records admit one common stage | `MathGauge.Tower.FreeTower.finite_records_common_stage` | Proved for dependent arbitrary target modules |
| Finitely many record equalities admit one common later witness | `MathGauge.Tower.FreeTower.finite_equalities_common_stage` | Proved, including empty finite families |
| A map from a finite free module to a record module lifts to a finite stage | `MathGauge.Tower.FreeTower.finite_free_map_lifts` | Actual lift constructed on a chosen finite basis |
| Equality of maps from a finite free module can be witnessed at one stage | `MathGauge.Tower.FreeTower.finite_free_maps_eventually_equal` | Proved from the common-witness lemma and basis extensionality |
| Finite generation of M iff some stage dual surjects onto M | `MathGauge.Tower.FreeTower.finite_invariant_iff_stage_surjective` | Proved in both directions |
| Exact reference criterion on the original P_n: existence of n and d²=d, and for every m≥n existence of u_m and r≥m with u_m d=u_m, ρ_nm u_m=d, u_mρ_nr=ρ_mr | `MathGauge.Tower.FreeTower.FiniteStageCriterion` | Exact quantified definition; no coherence of the separately selected u_m is imposed |
| The original-stage criterion is equivalent to its dual formulation | `MathGauge.Tower.FreeTower.finiteStage_iff_dualStage` | Proved by actual finite-free bidual equivalences; `transposeDual` is constructed, with pairing and composition formulas |
| M finite generated implies the criterion | `MathGauge.Tower.FreeTower.finite_invariant_implies_dualStage` and `finiteStage_iff_dualStage` | The stage, splitting j, idempotent, retractions and later witnesses are constructed; no certificate assumption |
| Criterion implies M finite generated | `MathGauge.Tower.FreeTower.dualStage_implies_finite_invariant` | Proved by surjectivity of the finite stage. This is a complete alternative to the reference's image-isomorphism proof |
| Finite-stage criterion iff finite generation, hence iff representability | `MathGauge.Tower.FreeTower.finiteStage_iff_finite_invariant`, `finiteStage_iff_representable` | Proved under the original tower hypotheses |
| Every tower preserves finite limits | `MathGauge.Tower.FreeTower.preserves_every_finite_limit` | Standard `CategoryTheory.Limits.PreservesLimit`, for every U-small category with finitely many objects and total arrows, with no finite-generation assumption on M |
| This is the canonical finite-limit comparison | `recordComparison`, `recordComparison_injective`, `recordComparison_surjective`, `finiteRecordConeIsLimit` | The map is induced by actual limit projections; its inverse is constructed by moving representatives and compatibility equations to common stages. Empty diagrams included |
| The rank-two tower has step (a,b)↦(a,0) | `MathGauge.Tower.Examples.projectionTower` | Concrete constant ℤ×ℤ stages and the actual projection map |
| This tower satisfies the finite-stage criterion | `MathGauge.Tower.Examples.projection_finite_stage_criterion` | Explicit witness n=0, d=projection, u_m=projection, r=m+1 |
| Its invariant is ℤ and its record functor is represented by ℤ | `MathGauge.Tower.Examples.projectionInvariantEquiv`, `projectionRepresentation` | Actual linear equivalence and actual natural isomorphism with Hom(ℤ,-) |
| No step is an isomorphism, so eventual isomorphisms are not necessary | `MathGauge.Tower.Examples.projection_step_not_injective`, `projection_never_eventually_isomorphisms` | Proved using the nonzero second-coordinate kernel |
| The multiplier-two tower | `MathGauge.Tower.Examples.doublingTower` | Concrete ℤ stages and multiplication by two |
| Its invariant is ℤ[1/2] | `MathGauge.Tower.Examples.doublingInvariantEquivDyadic` | Actual linear equivalence with `dyadicIntegers`, the submodule `{q : ℚ | ∃ n : ℕ, ∃ z : ℤ, q = z / 2^n}` |
| The direct-limit-to-fraction map is legitimate and injective | `dyadicStageMap_compatible`, `doublingToRat`, `doublingToRat_injective`, `doublingToDyadic_bijective` | All transition compatibility, injectivity, range and surjectivity proved |
| Finite denominators do not generate all dyadic integers | `doubling_stage_not_surjective`, `doubling_invariant_not_finite`, `dyadicIntegers_not_finitely_generated` | The next denominator is excluded from every stage image; the finite-stage-surjectivity criterion then rules out finite generation |
| The multiplier-two record functor is not representable and fails countable-limit preservation | `doubling_not_representable`, `doubling_not_preserves_countable_limits` | Deduced from the previously compiled main classification on this concrete tower |

There is no remaining unencoded conclusion among these requested reference extensions. Alternate intermediate proof routes (for example the reference's explicit isomorphism `im e ≅ M`) are not claimed as separately encoded; their stated final conclusions are proved by the complete alternatives above. No benchmark statement or reference was changed.


## 覆盖边界

以上覆盖本题主任务及参考的全部结果性结论；参考中个别中间表达（如有限层幂等像与 M 的显式同构）被完整替代证明取代，不另称该中间声明已经编码。候选答卷另外提出的 ML 与稳定秩判据、自身塔单图表测试、逆极限表示模型和所有可数无挠群的实现，已另经数学审核通过；这些候选附加发现不自动计为本组 Lean 证明。

统一审计按 manifest 加载本题完整导入闭包，核对全部 MathGauge 声明及递归公理依赖；作者的联合审计计数不是本题的当前声明计数。当前只允许 propext、Classical.choice、Quot.sound。
