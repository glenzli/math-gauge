import formal_oet.vol_03.ch_12_residuals_and_substitution.structural_priors
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace formal_oet.vol_03.ch_12_residuals_and_substitution

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open formal_oet.vol_01.ch_04_operator_chain_calculus
open formal_oet.vol_02.ch_07_fitting_foundations

open scoped BigOperators

variable {X I : Type} {bot : X} [Fintype I]

/--
OET anchor: h-67ea98399b9a982d
**定义（分量经验保证域）**
The component empirical guarantee domain at threshold `tau`.
-/
def empirical_component_guarantee_domain
    (d : I → X → X → ENNReal)
    (A : I → I → ENNReal) (U sample : Set X)
    (j : I) (eps tau : ENNReal) : Set X :=
  anchor_gap_sublevel d A j U sample eps tau

/--
OET anchor: h-67ea98399b9a982d
**定义（联合经验保证域）**
The joint empirical guarantee domain over a component set `J`.
-/
def empirical_joint_guarantee_domain
    (d : I → X → X → ENNReal)
    (A : I → I → ENNReal) (U : Set X)
    (sample : I → Set X) (J : Set I)
    (eps tau : I → ENNReal) : Set X :=
  {x | x ∈ U ∧
    ∀ j : I, j ∈ J →
      weighted_anchor_distance d A j x (sample j) + eps j ≤ tau j}

/--
OET anchor: h-51e4f3855df2b936
**命题（经验保证域的基本性质）**
A sampled anchor has zero common-anchor distance to its own component sample
set.
-/
theorem weighted_anchor_distance_self_eq_zero
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (A : I → I → ENNReal) (j : I) {sample : Set X} {x : X}
    (hx : x ∈ sample) :
    weighted_anchor_distance d A j x sample = 0 := by
  apply le_antisymm
  · unfold weighted_anchor_distance
    have hzero :
        matrix_vector_bound A (fun i => d i x x) j = 0 := by
      unfold matrix_vector_bound
      apply Finset.sum_eq_zero
      intro i _
      simp [(hd i).dist_self x]
    exact le_trans
      (iInf_le
        (fun y : {y // y ∈ sample} =>
          matrix_vector_bound A (fun i => d i x y.1) j)
        ⟨x, hx⟩)
      (le_of_eq hzero)
  · exact zero_le _

/--
OET anchor: h-51e4f3855df2b936
**命题（经验保证域的基本性质，采样点）**
A sampled point lies in the component guarantee domain whenever the threshold
dominates the empirical residual bound.
-/
theorem sample_point_mem_empirical_component_guarantee_domain
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (A : I → I → ENNReal) (U sample : Set X)
    (j : I) (eps tau : ENNReal) {x : X}
    (hsampleU : sample ⊆ U)
    (hx : x ∈ sample)
    (htau : eps ≤ tau) :
    x ∈ empirical_component_guarantee_domain d A U sample j eps tau := by
  refine ⟨hsampleU hx, ?_⟩
  rw [weighted_anchor_distance_self_eq_zero d hd A j hx, zero_add]
  exact htau

/--
OET anchor: h-51e4f3855df2b936
**命题（经验保证域的基本性质，采样点有限阈值版本）**
Text-faithful wrapper retaining the finite threshold condition.
-/
theorem sample_point_mem_empirical_component_guarantee_domain_text
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (A : I → I → ENNReal) (U sample : Set X)
    (j : I) (eps tau : ENNReal) {x : X}
    (htau_finite : finite_ennreal tau)
    (hsampleU : sample ⊆ U)
    (hx : x ∈ sample)
    (htau : eps ≤ tau) :
    x ∈ empirical_component_guarantee_domain d A U sample j eps tau := by
  have _ := htau_finite
  exact sample_point_mem_empirical_component_guarantee_domain d hd A U sample
    j eps tau hsampleU hx htau

/--
OET anchor: h-51e4f3855df2b936
**命题（经验保证域的基本性质，联合采样点）**
A point sampled in every resolved component belongs to the joint empirical
guarantee domain when every threshold dominates its residual bound.
-/
theorem sample_point_mem_empirical_joint_guarantee_domain
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (A : I → I → ENNReal) (U : Set X)
    (sample : I → Set X) (J : Set I)
    (eps tau : I → ENNReal) {x : X}
    (hxU : x ∈ U)
    (hxsample : ∀ j : I, j ∈ J → x ∈ sample j)
    (htau : ∀ j : I, j ∈ J → eps j ≤ tau j) :
    x ∈ empirical_joint_guarantee_domain d A U sample J eps tau := by
  refine ⟨hxU, ?_⟩
  intro j hj
  rw [weighted_anchor_distance_self_eq_zero d hd A j (hxsample j hj), zero_add]
  exact htau j hj

/--
OET anchor: h-51e4f3855df2b936
**命题（经验保证域的基本性质，联合采样点分量形式）**
If the resolved component set is nonempty and every component sample lies in
`U`, then a point sampled in every resolved component lies in the joint
empirical guarantee domain whenever the thresholds dominate the residual
bounds.
-/
theorem sample_point_mem_empirical_joint_guarantee_domain_of_component_samples
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (A : I → I → ENNReal) (U : Set X)
    (sample : I → Set X) (J : Set I)
    (eps tau : I → ENNReal) {x : X}
    (hJne : J.Nonempty)
    (hsampleU : ∀ j : I, j ∈ J → sample j ⊆ U)
    (hxsample : ∀ j : I, j ∈ J → x ∈ sample j)
    (htau : ∀ j : I, j ∈ J → eps j ≤ tau j) :
    x ∈ empirical_joint_guarantee_domain d A U sample J eps tau := by
  rcases hJne with ⟨j₀, hj₀⟩
  exact sample_point_mem_empirical_joint_guarantee_domain d hd A U sample J eps tau
    (hsampleU j₀ hj₀ (hxsample j₀ hj₀)) hxsample htau

/--
OET anchor: h-51e4f3855df2b936
**命题（经验保证域的基本性质，联合采样点有限阈值版本）**
Text-faithful wrapper retaining finite thresholds for every resolved
component.
-/
theorem sample_point_mem_empirical_joint_guarantee_domain_text
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (A : I → I → ENNReal) (U : Set X)
    (sample : I → Set X) (J : Set I)
    (eps tau : I → ENNReal) {x : X}
    (hJne : J.Nonempty)
    (htau_finite : ∀ j : I, j ∈ J → finite_ennreal (tau j))
    (hsampleU : ∀ j : I, j ∈ J → sample j ⊆ U)
    (hxsample : ∀ j : I, j ∈ J → x ∈ sample j)
    (htau : ∀ j : I, j ∈ J → eps j ≤ tau j) :
    x ∈ empirical_joint_guarantee_domain d A U sample J eps tau := by
  have _ := htau_finite
  exact sample_point_mem_empirical_joint_guarantee_domain_of_component_samples
    d hd A U sample J eps tau hJne hsampleU hxsample htau

/--
OET anchor: h-51e4f3855df2b936
**命题（经验保证域的基本性质，分量误差）**
Membership in the component guarantee domain converts the empirical upper
certificate into the requested component tolerance.
-/
theorem empirical_component_guarantee_error_bound
    (d : I → X → X → ENNReal)
    (A : I → I → ENNReal) (U sample : Set X)
    (target proxy : Operator X bot)
    (j : I) (eps tau : ENNReal)
    (hupper :
      ∀ x ∈ U,
        d j (proxy.func x) (target.func x) ≤
          weighted_anchor_distance d A j x sample + eps)
    {x : X}
    (hx : x ∈ empirical_component_guarantee_domain d A U sample j eps tau) :
    d j (proxy.func x) (target.func x) ≤ tau :=
  le_trans (hupper x hx.1) hx.2

/--
OET anchor: h-51e4f3855df2b936
**命题（经验保证域的基本性质，联合误差）**
Membership in the joint empirical guarantee domain gives all component
tolerance bounds on `J`.
-/
theorem empirical_joint_guarantee_error_bound
    (d : I → X → X → ENNReal)
    (A : I → I → ENNReal) (U : Set X)
    (sample : I → Set X) (J : Set I)
    (target proxy : Operator X bot)
    (eps tau : I → ENNReal)
    (hupper :
      ∀ x ∈ U, ∀ j : I, j ∈ J →
        d j (proxy.func x) (target.func x) ≤
          weighted_anchor_distance d A j x (sample j) + eps j)
    {x : X}
    (hx : x ∈ empirical_joint_guarantee_domain d A U sample J eps tau) :
    ∀ j : I, j ∈ J → d j (proxy.func x) (target.func x) ≤ tau j := by
  intro j hj
  exact le_trans (hupper x hx.1 j hj) (hx.2 j hj)

/--
OET anchor: h-51e4f3855df2b936
**命题（经验保证域的基本性质，阈值单调性）**
Increasing the tolerance vector enlarges the joint empirical guarantee domain.
-/
theorem empirical_joint_guarantee_domain_mono_tau
    (d : I → X → X → ENNReal)
    (A : I → I → ENNReal) (U : Set X)
    (sample : I → Set X) (J : Set I)
    (eps tau tau' : I → ENNReal)
    (htau : ∀ j : I, j ∈ J → tau j ≤ tau' j) :
    empirical_joint_guarantee_domain d A U sample J eps tau ⊆
      empirical_joint_guarantee_domain d A U sample J eps tau' := by
  intro x hx
  exact ⟨hx.1, fun j hj => le_trans (hx.2 j hj) (htau j hj)⟩

/--
OET anchor: h-51e4f3855df2b936
**命题（经验保证域的基本性质，阈值单调性有限版本）**
Text-faithful wrapper retaining finite threshold-vector assumptions.
-/
theorem empirical_joint_guarantee_domain_mono_tau_text
    (d : I → X → X → ENNReal)
    (A : I → I → ENNReal) (U : Set X)
    (sample : I → Set X) (J : Set I)
    (eps tau tau' : I → ENNReal)
    (htau_finite : ∀ j : I, j ∈ J → finite_ennreal (tau j))
    (htau'_finite : ∀ j : I, j ∈ J → finite_ennreal (tau' j))
    (htau : ∀ j : I, j ∈ J → tau j ≤ tau' j) :
    empirical_joint_guarantee_domain d A U sample J eps tau ⊆
      empirical_joint_guarantee_domain d A U sample J eps tau' := by
  have _ := htau_finite
  have _ := htau'_finite
  exact empirical_joint_guarantee_domain_mono_tau d A U sample J eps tau tau' htau

/--
OET anchor: h-51e4f3855df2b936
**命题（经验保证域的基本性质，采样缩小）**
If the sample set is restricted while the same residual bound is kept, the
component guarantee domain can only shrink.
-/
theorem empirical_component_guarantee_domain_mono_sample_restriction
    (d : I → X → X → ENNReal)
    (A : I → I → ENNReal) (U : Set X)
    (j : I) (eps tau : ENNReal)
    {Ssmall Slarge : Set X} (hsub : Ssmall ⊆ Slarge) :
    empirical_component_guarantee_domain d A U Ssmall j eps tau ⊆
      empirical_component_guarantee_domain d A U Slarge j eps tau := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  exact le_trans
    (add_le_add (weighted_anchor_distance_mono_of_subset d A j x hsub) le_rfl)
    hx.2

/--
OET anchor: h-51e4f3855df2b936
**命题（经验保证域的基本性质，采样缩小正文前提版本）**
Text-faithful wrapper retaining nonempty restricted sample and finite threshold
assumptions.
-/
theorem empirical_component_guarantee_domain_mono_sample_restriction_text
    (d : I → X → X → ENNReal)
    (A : I → I → ENNReal) (U : Set X)
    (j : I) (eps tau : ENNReal)
    {Ssmall Slarge : Set X}
    (hsmall_nonempty : Ssmall.Nonempty)
    (htau_finite : finite_ennreal tau)
    (hsub : Ssmall ⊆ Slarge) :
    empirical_component_guarantee_domain d A U Ssmall j eps tau ⊆
      empirical_component_guarantee_domain d A U Slarge j eps tau := by
  have _ := hsmall_nonempty
  have _ := htau_finite
  exact empirical_component_guarantee_domain_mono_sample_restriction
    d A U j eps tau hsub

/--
OET anchor: h-67ea98399b9a982d
**定义（共同锚点内插域）**
The points in `U` that have one common anchor within the componentwise radius
vector `r`.
-/
def common_anchor_interpolation_domain
    (d : I → X → X → ENNReal)
    (U sample : Set X) (r : I → ENNReal) : Set X :=
  {x | x ∈ U ∧ ∃ xs ∈ sample, ∀ i : I, d i x xs ≤ r i}

/--
OET anchor: h-67ea98399b9a982d
**定义（共同锚点外插域）**
The complement in `U` of the common-anchor interpolation domain.
-/
def common_anchor_extrapolation_domain
    (d : I → X → X → ENNReal)
    (U sample : Set X) (r : I → ENNReal) : Set X :=
  U \ common_anchor_interpolation_domain d U sample r

/--
OET anchor: h-a0d7c8d3d3aaaa3d
**命题（共同锚点内插界，锚点距离形式）**
Inside the common-anchor interpolation domain, the anchor distance is bounded
by the matrix-vector action on the radius vector.
-/
theorem common_anchor_interpolation_distance_bound
    (d : I → X → X → ENNReal)
    (A : I → I → ENNReal) (U sample : Set X)
    (r : I → ENNReal) (j : I) {x : X}
    (hx : x ∈ common_anchor_interpolation_domain d U sample r) :
    weighted_anchor_distance d A j x sample ≤ matrix_vector_bound A r j := by
  rcases hx.2 with ⟨xs, hxs, hdist⟩
  exact le_trans
    (iInf_le
      (fun y : {y // y ∈ sample} =>
        matrix_vector_bound A (fun i => d i x y.1) j)
      ⟨xs, hxs⟩)
    (matrix_vector_bound_mono A hdist j)

/--
OET anchor: h-a0d7c8d3d3aaaa3d
**命题（共同锚点内插界）**
The empirical upper certificate specializes on the interpolation domain to the
radius-vector bound.
-/
theorem common_anchor_interpolation_error_bound
    (d : I → X → X → ENNReal)
    (A : I → I → ENNReal) (U sample : Set X)
    (target proxy : Operator X bot)
    (r : I → ENNReal) (eps : ENNReal) (j : I)
    (hupper :
      ∀ x ∈ U,
        d j (proxy.func x) (target.func x) ≤
          weighted_anchor_distance d A j x sample + eps)
    {x : X}
    (hx : x ∈ common_anchor_interpolation_domain d U sample r) :
    d j (proxy.func x) (target.func x) ≤
      matrix_vector_bound A r j + eps := by
  exact le_trans (hupper x hx.1)
    (add_le_add
      (common_anchor_interpolation_distance_bound d A U sample r j hx)
      le_rfl)

/--
OET anchor: h-a0d7c8d3d3aaaa3d
**命题（共同锚点内插界，可评估分量版本）**
The interpolation bound specialized to an evaluable component sample and a
componentwise upper certificate.
-/
theorem common_anchor_interpolation_error_bound_evaluable_component
    (d : I → X → X → ENNReal)
    (A : I → I → ENNReal) (U : Set X)
    (sample : I → Set X) (J : Set I)
    (target proxy : Operator X bot)
    (r : I → ENNReal) (eps : I → ENNReal) (j : I)
    (hj : j ∈ J)
    (hupper :
      ∀ x ∈ U, ∀ j : I, j ∈ J →
        d j (proxy.func x) (target.func x) ≤
          weighted_anchor_distance d A j x (sample j) + eps j)
    {x : X}
    (hx : x ∈ common_anchor_interpolation_domain d U (sample j) r) :
    d j (proxy.func x) (target.func x) ≤
      matrix_vector_bound A r j + eps j := by
  exact common_anchor_interpolation_error_bound d A U (sample j) target proxy
    r (eps j) j (fun x hxU => hupper x hxU j hj) hx

/--
OET anchor: h-a0d7c8d3d3aaaa3d
**命题（共同锚点内插界，外插边界）**
Membership in the extrapolation domain records only that the interpolation
certificate is not available.
-/
theorem common_anchor_extrapolation_records_nonmembership
    (d : I → X → X → ENNReal)
    (U sample : Set X) (r : I → ENNReal) {x : X}
    (hx : x ∈ common_anchor_extrapolation_domain d U sample r) :
    x ∈ U ∧ x ∉ common_anchor_interpolation_domain d U sample r :=
  hx

/--
OET anchor: h-a0d7c8d3d3aaaa3d
**命题（共同锚点内插界，外插不蕴含正偏差）**
Extrapolation-domain membership alone cannot force a positive true-deviation
lower bound: taking the target and proxy to be the same operator leaves the
true deviation equal to zero.
-/
theorem common_anchor_extrapolation_does_not_force_positive_error
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (phi : Operator X bot)
    (U sample : Set X) (r : I → ENNReal)
    (j : I) (tau : ENNReal) {x : X}
    (hUdom : U ⊆ dom phi)
    (hx : x ∈ common_anchor_extrapolation_domain d U sample r) :
    x ∈ dom phi ∧ ¬ tau < d j (phi.func x) (phi.func x) := by
  refine ⟨hUdom hx.1, ?_⟩
  rw [(hd j).dist_self]
  exact not_lt_of_ge (zero_le tau)

end formal_oet.vol_03.ch_12_residuals_and_substitution
