# MG-R003：当前 Lean 覆盖

本页对应冻结的 0.3.0 题面、参考与评分依据；实际数学声明在同目录 Lean 源码中。源码、编译顺序、原始输入及本页散列由 [manifest.json](manifest.json) 绑定。当前逐题构建与全声明审计见 [current-formal.json](current-formal.json)；复核方法见 [共用验证器](../../../../scripts/formal/README.md)。

作者联合交付与旧审计保存于 results/full-lean-terra/formal-history，属于阶段记录。下面保留该题的逐事实数学映射；不把其他题的声明或作者联合编译计数算成本题独立证明。AI 语义审核、Lean 核验与人工审定分别记录，人工仍待定。

所有项目名以下述完整 `MathGauge.` 命名空间为准。

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
