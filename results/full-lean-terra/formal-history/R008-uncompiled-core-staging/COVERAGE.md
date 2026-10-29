# MG-R005 / MG-R008 Lean coverage

This directory is an isolated formalization artifact. Canonical benchmark files were read only. No candidate model was run, and no commit or push was made.

The **requested main conclusions of both cases are proved on actual objects**. The ledger below distinguishes these from additional reference examples and alternate criteria. A compiled definition is not reported as a proof of an unencoded assertion. All mathematical hypotheses remain those of the cases; several lemmas prove stronger statements.

## Foundations and scope

- Lean 4.29.1; mathlib `5e932f97dd25535344f80f9dd8da3aab83df0fe6`. See `MANIFEST.json` for exact source identities and `Audit.compile.log` for the dynamic audit.
- R005 uses `ℝ≥0∞` for `[0,+∞]` with its actual order topology. `JensenConvex` includes all nonnegative coefficients summing to one, including zero coefficients and infinite endpoint values. `convexCost_iff_jensen` proves its equivalence with convexity of the real epigraph. Competitors with negative or minus-infinite values are covered separately in `reconstruct_maximal_ereal`.
- The observation dual is the **algebraic dual of the actual continuous-dual subspace** with its weak evaluation topology. It has explicit Hausdorff topological-vector-space and locally convex instances, and is finite dimensional for each finite observation. In finite dimension this is the usual finite-dimensional topology. The observation map and restriction map are explicitly built from evaluation; neither is assumed.
- R008 uses `ModuleCat.{u} ℤ`, the standard presentation of abelian groups as integer modules. Objects are all types in `Type u`; morphisms are all integer-linear maps, equivalently all additive group homomorphisms. No injectivity, surjectivity, rank bound, or eventual stabilization hypothesis is placed on the tower maps.
- A tower contains only finite free stage modules and adjacent maps. All longer transitions are recursively constructed with `Nat.leRecOn`. `Record` is the genuine mathlib `Module.DirectLimit`, not an uninterpreted quotient interface.
- `CategoryLimits.lean` constructs a genuine `Cone` and `IsLimit` for each category diagram, and derives the standard `CategoryTheory.Limits.PreservesLimit` from the **canonical** tensor comparison. Countability means countably many objects and total arrows. The intermediate graph-compatible-family construction is instantiated on every arrow of every actual functor.
- `recordNatEquiv` quantifies over all components on all `ModuleCat.{u} ℤ` objects and all their morphisms. Lean places this family in `Type (u+1)`, its minimal ambient universe. `recordNatEquivInLargerUniverse.{u,v}` explicitly transports the classification into `Type (max u v + 1)`, so there is no restriction to a particular larger ambient universe. The same fixed U-small domain of objects is retained.
- The universe-lifted integer module `ULift.{u} ℤ` is used for evaluation at the unit and its countable product. `ULift.moduleEquiv` is part of each identification with ordinary integers; this is a size device, not a change of testing group.

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
| Competitors may take negative extended-real values | `reconstruct_maximal_ereal` | Proved, in fact for every lower semicontinuous extended-real minorant of convex proper f |
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

R008 boundaries, **not claimed as Lean-covered**: the reference's optional finite-stage idempotent/retraction criterion; the additional theorem that every tower preserves finite limits even when the main criterion fails; identification of the multiplier-two invariant with ℤ[1/2]; and the projection-on-first-coordinate rank-two example. These are additional mathematical conclusions, not used as unproved assumptions in any theorem above. Likewise the candidate response's extra Mittag–Leffler/bounded-stable-rank criterion, its own-tower single-diagram test, the inverse-limit model of the representing object, and essential surjectivity onto all countable torsion-free groups have been independently reviewed as mathematics, but are not claimed as encoded by the present Lean files. See `R008_RESPONSE_REVIEW.md`.

## Reproduction and dependency order

From this directory run `python3 check.py` followed by these names in order:

1. `ConvexCost.lean`
2. `FiniteObservation.lean`
3. `ConvexCostExtras.lean`
4. `ProjectionExample.lean`
5. `RelaxationGeometry.lean`
6. `SequentialTower.lean`
7. `TensorNatural.lean`
8. `TensorRepresentability.lean`
9. `TensorLimits.lean`
10. `CategoryLimits.lean`
11. `TowerClassification.lean`
12. `Audit.lean`

The helper derives LEAN_PATH from the pinned existing dependency project, prepends this directory, uses the fixed toolchain binary, writes each `.olean` here, and records each compiler output in its sibling `.compile.log`. No umbrella `Mathlib` import or shared-cache write is used.

`Audit.lean` dynamically enumerates **all compiled MathGauge declarations, including private generated declarations**, computes their recursive axiom dependencies, rejects project axioms, and rejects every dependency except `propext`, `Classical.choice`, and `Quot.sound`. The final `AUDIT_OK` count and exact theorem signatures are in `Audit.compile.log`. Warnings are limited to unused section variables and simplification suggestions; they are not proof gaps.
