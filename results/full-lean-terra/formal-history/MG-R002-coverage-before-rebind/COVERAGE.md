# Math Gauge R002 / R003 / R004 coverage ledger

This is an isolated formalization under `/private/tmp/math-gauge-full-lean-20261029/analysis`. Canonical task, reference and rubric files under `/Users/g4i/lab/math-gauge/cases/public` are read-only and frozen; their SHA-256 values are in `source_hashes.json`. No case text was changed. No candidate-model run, commit or push was performed.

Only compiled declarations count as proof coverage. The final compiler evidence and exact source/olean/log hashes are in `verification_receipt.json`. The compiler is Lean 4.29.1 and the Mathlib revision is `5e932f97dd25535344f80f9dd8da3aab83df0fe6`. `verify.py` recompiles in the explicit order at the end, with output confined to this directory. All namespace names below have prefix `MathGauge.`.

## R002 — original task completely refuted, general boundary theory proved

| Original mathematical fact | Declarations / module | Exact semantic connection |
| --- | --- | --- |
| Real Banach original space | `CompatibleRecords.E`, `original_space_complete` | Actual `C₀(ℕ,ℝ)` on discrete ℕ, with its sup norm and completeness instance. |
| Construct a bounded global functional, not assume one | `convergent`, `seq_limit`, `limit_linear`, `seq_limit_bound`, `exists_extended_limit` | Scalar limit is constructed on the actual subspace of convergent bounded sequences; real Hahn–Banach gives an extension with proved norm ≤ 1. |
| Actual finite test vectors and their bounds | `partial_ones`, `partial_ones_norm`, `test_sequence_linear`, `test_sequence_bound` | Finite initial blocks of ones in c₀; every dual functional gives an actual bounded sequence of these evaluations. |
| Every original finite-dimensional record | `z`, `record` | A bundled real linear map on each actual submodule of the continuous dual. Defined for all submodules, hence includes every finite-dimensional one. |
| Inclusion compatibility | `record_compatible` | The original restriction along actual submodule inclusion. |
| One uniform constant C = 1 | `z_bound`, `record_bound` | Absolute values are bounded in the actual dual operator norm. |
| Nonexistence of an E-valued representative | `coordinate`, `z_coordinate`, `no_original_realization` | Original finite-dimensional singleton spans force every coordinate of x to be 1, contradicting x's actual limit 0. |
| Complete legal counterexample | `CompatibleRecords.counterexample` | Includes completeness, compatibility, bound and nonexistence with all original finite-dimensional quantifiers. |
| Arbitrary legal record data | `RecordBidual.FinitePart`, `Record` | The index type consists of all actual finite-dimensional submodules of the actual continuous dual. The structure contains only original local linear maps, inclusion compatibility and existence of a finite uniform bound. It does not contain a global functional or a realization. |
| Independence of finite observation space | `Record.eval_eq` | Evaluation via the singleton span agrees with the supplied value on every finite-dimensional subspace containing that functional. |
| Global linearity from local compatibility | `pairPart`, `Record.eval_add`, `Record.eval_smul`, `Record.linear` | Addition is proved inside the actual sum of two singleton spans; scalar compatibility inside the singleton span. |
| Actual bounded bidual element | `Record.eval_bound`, `Record.toBidual`, `Record.toBidual_norm`; `bidual_norm_le_given_bound` | Constructs a continuous functional on E′ with norm ≤ the supplied C; no continuity or boundedness certificate is assumed. |
| Bidual restriction and gluing are mutually inverse | `restrict`, `toBidual_restrict`, `restrict_toBidual`, `recordEquiv` | Both operations use all original finite-dimensional restrictions. |
| Exact original record distance | `recordDistance`, `recordDistance_eq_norm` in `RecordRealization.lean` | The supremum is over all ‖φ‖ ≤ 1 of the difference of singleton-span record values, exactly as in the task; proved equal to ‖z_r−z_s‖. |
| Canonical J is an isometric injection | `J`, `J_norm`, `J_injective` | Actual continuous double-dual evaluation map, using Mathlib's proved Hahn–Banach isometry. |
| A specified family is realizable iff its bidual belongs to J(E) | `Represents`, `represents_iff`, `realization_exists_iff` | `Represents` quantifies over every actual finite-dimensional F and φ∈F, with original evaluations φ(x). |
| Unique realization, exact norm and stability | `realization_unique`, `realization_norm`, `realization_given_bound`, `exact_stability` | Includes original supplied-C bound and ‖x_r−x_s‖ = d(r,s). |
| Original operator transform T′F is finite-dimensional | `transpose`, `imagePart`, `imagePoint` in `RecordTransform.lean` | T′ is actual composition φ∘T; imagePart is the actual submodule image and has a proved finite-dimensional instance. |
| Transform obeys original formula and bound C‖T‖ | `transform`, `transform_formula`, `transform_bound` | Formula is r_{T′F}(T′φ); compatibility and linearity follow from constructed restrictions. |
| Bidual transform and canonical naturality | `transform_toBidual`, `canonical_naturality` | Actual T″z and T″Jx = JTx. |
| E-valued recovery on exactly the realizable records | `RealizableRecord`, `recover`, `recover_represents`, `recover_unique`, `recover_exact_stability`, `recover_covariant` | Existence is restricted to the already characterized J(E) boundary. This is not presented as a recovery on every legal record. |
| Every record realizable iff E is reflexive | `all_realizable_iff_surjective` | Exact condition is surjectivity of the canonical map J:E→E″, the reference's definition of reflexivity; no reflexivity hypothesis is added to the counterexample. |
| General theory instantiated on the real counterexample | `RecordInstantiation.c0Record`, `c0Record_no_realization`, `c0Record_bidual_norm`, `c0_bidual_outside_original` | The earlier actual c₀ family inhabits the general original-data record structure. Its constructed bidual has norm ≤ 1 and lies outside J(E). |

**Proof-route substitution, explicitly not claimed as encoded:** the reference constructs the same c₀ obstruction through the isometric identification c₀′ ≃ ℓ¹. This directory instead proves a complete Hahn–Banach/finite-block construction on the actual c₀ dual. The standalone c₀′ ≃ ℓ¹ isomorphism, finite-sign-vector derivation and series representation of each c₀ functional are not encoded here. This does not leave the original task refutation or its general existence/stability/covariance boundary unproved. The parent explicitly accepted this equivalent route during handoff.

## R003 — original task and structural reference conclusions proved

| Original mathematical fact | Declarations / module | Exact semantic connection |
| --- | --- | --- |
| Actual rectangular averages | `ErgodicOperators.avg`, `rectangle`, `rectangle_formula` | Exactly the task's double sum. Lean indices n,m represent positive lengths N=n+1, M=m+1. |
| Actual iteration R | `iteration`, `iteration_eq_lazy` | Exactly `(1/4) • ((1+T)*(1+S))`, equivalently the product of the two lazy operators. |
| Original assumptions | All principal theorems | Real normed space; actual bounded linear T,S; actual commutation; uniform bounds `∀n, ‖T^n‖≤KT`, `∀n, ‖S^n‖≤KS`. These express the task's finite power suprema as upper bounds. No reflexivity, compactness or closed-range hypothesis appears. Completeness is used only where the reference needs closed recovery subspaces. |
| Average bounds and telescoping | `avg_bound`, `avg_difference`, `rectangle_bound`; `rectangle_telescope_T/S`, `rectangle_defect_sharp_T/S` in `ErgodicConsequences.lean` | Includes exact reference defect bounds `(1+KT)KS/N` and `KT(1+KS)/M`, as well as the coarser bounds used in the convergence proof. |
| Binomial coefficients and nonnegativity | `BinomialSmoothing.p`, `p_nonneg`, `p_sum`, `p_last_zero` | Actual natural binomial coefficients divided by 2ⁿ, with actual finite support endpoint and total mass 1. |
| Unimodality, maximum and total variation | `p_increasing`, `p_decreasing`, `p_le_b`, `variation` | Actual coefficients increase to their middle maximum bₙ and decrease afterwards; total variation including the two exterior zeros is exactly 2bₙ. |
| Central binomial product and decay | `c_recurrence`, `c_product`, `c_square_bound`, `b_even`, `b_odd_le`, `b_sqrt_bound`, `b_tendsto_zero` | Proves the reference's explicit bound `bₙ≤1/√(⌊n/2⌋+1)` and convergence to zero. Uses direct induction on the square estimate, not logarithms/harmonic sums. |
| Actual polynomial expansion and difference | `lazy_expansion`, `polynomial_difference` | Equality in a genuine normed real algebra, subsequently applied to the actual bounded-operator algebra. |
| Crucial smoothing of the actual single-operator iteration | `lazy_power_bound`, `smoothing_bound`, `smoothing_tendsto_zero` | Proves `‖Bⁿ(I−U)‖≤2K_U bₙ` directly; no smoothing conclusion is assumed. |
| Actual two-operator iteration estimates | `lazy_commute`, `iteration_power`, `iteration_bound`, `iteration_difference_T/S_bound` | Proves Rⁿ=B_TⁿB_Sⁿ, norm bound KTKS and both 2KTKS bₙ defect bounds using commutation. |
| Actual closed difference subspace Y | `ErgodicRecovery.differences`, `differences_closed` | Norm closure of the sum of the two actual ranges (I−T)E and (I−S)E. |
| Decay extends from ranges to their norm closure | `vanishing`, `vanishing_closed`, `differences_vanish` | Epsilon approximation plus a proved uniform operator norm bound; not assumed closed-range equality. |
| Limits must lie in actual Z | `fixed`, `mem_fixed_iff`, `limit_is_fixed`; `rectangle_commute_T/S`, `iteration_commute_T/S`, `rectangle_defects`, `iteration_defects` | Z is the intersection of the two actual kernels. Each generic fact is instantiated for both actual task processes. |
| Both processes preserve the actual quotient record | `quotient_T`, `quotient_S`, `rectangle_record`, `iteration_record` | Proves x−Fᵢx∈Y using the actual quotient map and its algebra, hence qFᵢx=qx. |
| Both processes act identically on Z | `rectangle_fixed`, `iteration_fixed` | Actual operators, not an abstract hypothesis. |
| Full comparison and common limit | `comparison`, `equal_convergence_and_limits` in `ErgodicComparison.lean` | Each process converges to z iff z∈Z and x−z∈Y; therefore norm-convergence existence and limit agree. Product atTop is the coordinatewise divergent rectangular-net filter, equivalent to min(N,M)→∞. |
| Exact full convergence domain | `domain`, `domain_decomposition`, `full_convergence_domain`, `full_iteration_convergence_domain`, `direct_sum` | D=Z+Y and Z∩Y=0, with both directions of the convergence criterion. |
| Bounded linear recovery map | `recovered`, `recovered_limit`, `recovery_linear`, `recovery`, `recovery_norm`, `recovery_stable` | Actual P:D→L Z constructed from a decomposition whose uniqueness follows from actual limits; norm ≤ KTKS. |
| Range, kernel and identity restriction | `recovery_on_fixed`, `recovery_surjective`, `recovery_eq_zero_iff` | Range is all of Z; kernel consists exactly of domain points belonging to Y; P|Z=id. |
| Recovery depends only on qx | `recovery_depends_only_on_record` | Actual quotient equality implies equality of recovered vectors. |
| Exactly recoverable quotient records | `quotient_map`, `quotient_fixed`, `domain_iff_record_recoverable` | q(D)=q(Z); quotient is the actual normed quotient E/Y. |
| Bounded record recovery with both Lipschitz inequalities | `fixed_norm_le_representative`, `fixed_quotient_bound`, `quotient_equiv`, `record_recovery`, `record_recovery_two_sided` | Actual q(Z)→Z inverse; `‖a−b‖≤‖P̂a−P̂b‖≤KTKS‖a−b‖`. Quotient-infimum estimates do not assume a minimum is attained. |
| Original-domain and quotient recovery agree | `quotient_recovery_agrees` | P̂(qx)=Px for every x∈D, with the actual maps constructed above. |
| Closed recovery record space and input space | `record_range_closed`, `recovery_domain_closed` | Under the task's Banach completeness, q(Z) and D are closed. Uses proved two-sided bounds and actual complete fixed subspace. |
| Legitimate strengthening counterexample | `ErgodicCounterexample.E`, `shift_linear`, `shift`, `shift_power_norm_one`, `identity_power_norm_one` | Actual real ℓ¹, right shift T and S=I, with all power norms exactly 1. |
| Actual fixed-space obstruction and nonzero record | `shift_fixed_zero`, `mass`, `mass_shift`, `differences_in_mass_kernel`, `mass_e₀`, `e₀_not_zero_record` | Z=0; total mass annihilates actual Y and equals 1 on e₀, so its actual quotient record is nonzero. |
| Both actual processes fail to recover e₀ | `no_recovery_e₀`, `rectangle_e₀_norm`, `iteration_e₀_norm` | Both have no norm limit and both keep ℓ¹ norm exactly 1. |
| Exact coordinate behavior in the counterexample | `shift_power_e₀`, `iteration_shift`; `iteration_coordinate`, `iteration_coordinate_nonneg`, `iteration_coordinate_decay`, `rectangle_coordinate`, `rectangle_coordinate_decay` in `ErgodicCoordinates.lean` | Iteration coordinates are the genuine binomial probabilities; rectangular averages have uniform mass on the first N coordinates; each fixed coordinate tends to zero. |

**Proof-route substitutions / scope limits:** the decay bound is proved by the direct algebraic induction `c_square_bound`, so the reference's logarithm inequality and harmonic-sum proof route are not separately encoded. The exact odd-index scalar recurrence is not a standalone declaration; its needed inequality and the stated final decay estimate are proved. The successor-index convention and coordinatewise product filter are standard equivalent representations, explicitly stated here; a separate theorem about the function `min` is not included. No universal error rate, convergence on all E, or operator-norm convergence theorem is claimed. The actual ℓ¹ counterexample disproves recovery on all E. No extra nontrivial-space assumption was used, so the zero-space case remains included.

## R004 — complete original counterexample; deeper criterion handed to parent

| Original mathematical fact | Declarations / module | Exact semantic connection |
| --- | --- | --- |
| Actual complex Hilbert layers | `HilbertComplex.H` | Actual `lp (fun _:ℕ => ℂ) 2`; length one, with true inner product and completeness. |
| Actual reference differential and norm | `weight`, `diagonal_linear`, `d`, `d_apply`, `d_norm_eq_one` | Multiplies coordinate n by 1/(n+1), the positive-index reference shifted by one; norm exactly 1. |
| Both reduced endpoint records vanish | `d_injective`, `d_ker`, `single_mem_range`, `d_dense_range`, `d_range_closure`, `reduced_exactness` | Actual ker d=⊥ and actual closure(range d)=⊤, the equivalent submodule identities for the two reduced quotient spaces. Standalone quotient Subsingleton instances are not defined here. |
| No bounded chain contraction | `no_bounded_left_inverse`, `no_chain_contraction`, `no_bounded_right_inverse` | Actual unit-vector tests contradict boundedness; both endpoint equations are represented. |
| True adjoint and actual Laplacians | `d_self_adjoint`, `L₀`, `L₁`, `laplacians_eq` | Both equal the actual composite d∘d, using the true Hilbert adjoint. |
| Both Laplacians injective but lack bounded linear right inverses | `laplacians_injective`, `no_laplacian_right_inverse` | Actual operator statements, without finite-dimensional assumptions. |
| Range dense, neither closed nor surjective | `not_surjective`, `range_not_closed` | Proved with the Banach inverse theorem and the actual inverse-norm obstruction. The author's explicit y=(1/n) witness is not encoded separately. |
| Full task counterexample | `HilbertComplex.counterexample` | Bundles norm, both reduced endpoint identities, no contraction and no bounded right inverse. |
| Reference direction contraction⇒closed ranges | `HilbertCriteria.range_eq_kernel_of_contraction`, `contraction_implies_closed_range` | General actual neighboring bounded maps A:E→F and B:F→G with BA=0 and actual local chain-contraction identity. |
| Actual energy and reduced exactness⇒injectivity | `laplacian`, `laplacian_energy`, `laplacian_injective_of_reduced_exactness` | Actual A A*+B*B and actual closure(range A)=ker B. |
| Right inverse is two-sided under reduced exactness | `right_inverse_is_inverse` | Follows from the just-proved actual Laplacian injectivity. |

The parent is implementing the remaining closed-range⇒contraction/inverse, uniform s=d*G formula, finite-family norm maxima and finite-dimensional branches in separate files. **Those additions are not claimed by this directory's audit or ledger.** The two Hilbert modules here are frozen for parent reuse.

## Axiom audit and delivery boundary

`Audit.lean` dynamically enumerates every loaded constant whose name starts with `MathGauge.`, including definitions, theorem statements/proofs, structure projections and generated helpers. It traverses their transitive axiom dependencies and rejects any axiom other than `propext`, `Classical.choice`, and `Quot.sound`. The exact count and output are recorded by the final verification receipt. The delivery sources contain no sorry/admit/new axiom/unsafe declaration.

R005 was reassigned to the parent and is not represented by any declarations in this directory. Canonical R005 hashes are retained only as frozen source provenance from the original reading assignment.

## Exact compile order and file inventory

1. `CompatibleRecords.lean`
2. `RecordBidual.lean`
3. `RecordRealization.lean`
4. `RecordTransform.lean`
5. `RecordInstantiation.lean`
6. `HilbertComplex.lean`
7. `HilbertCriteria.lean`
8. `BinomialSmoothing.lean`
9. `ErgodicOperators.lean`
10. `ErgodicRecoveryCore.lean`
11. `ErgodicComparison.lean`
12. `ErgodicRecoveryMap.lean`
13. `ErgodicQuotient.lean`
14. `ErgodicConsequences.lean`
15. `ErgodicCounterexample.lean`
16. `ErgodicCoordinates.lean`
17. `Audit.lean`

Each module has its matching `.olean` and `.compile.log`. Supporting deliverables: `verify.py`, `check.py`, `source_hashes.json`, `verification_receipt.json`, `delivery_manifest.json`, `COVERAGE.md`, and `SEMANTIC_REVIEW.md`. `Probe.lean` and any matching scratch outputs are explicitly excluded from delivery and import closure. No module imports Probe.
