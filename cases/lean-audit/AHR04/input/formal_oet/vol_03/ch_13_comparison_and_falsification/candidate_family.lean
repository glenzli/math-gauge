import formal_oet.vol_03.ch_12_residuals_and_substitution
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace formal_oet.vol_03.ch_13_comparison_and_falsification

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open formal_oet.vol_01.ch_04_operator_chain_calculus
open formal_oet.vol_02.ch_07_fitting_foundations
open formal_oet.vol_03.ch_12_residuals_and_substitution

open scoped BigOperators

variable {X I Aidx : Type} {bot : X} [Fintype I]

/--
OET anchor: h-7fe1ddd2b091e405
**定义（候选代理族）**
A candidate proxy family is represented by a finite nonempty index type and a
proxy operator at each index.
-/
structure CandidateProxyFamily (X : Type) (bot : X) (Aidx : Type)
    [Fintype Aidx] [Nonempty Aidx] where
  proxy : Aidx → Operator X bot

/--
OET anchor: h-7fe1ddd2b091e405
**定义（一致性轮廓）**
The componentwise candidate-family consistency profile.
-/
noncomputable def consistency_profile
    (d : I → X → X → ENNReal)
    (proxy : Aidx → Operator X bot) (j : I) (x : X) : ENNReal :=
  ⨆ alpha : Aidx, ⨆ beta : Aidx,
    d j ((proxy alpha).func x) ((proxy beta).func x)

/--
OET anchor: h-7fe1ddd2b091e405
**定义（一致性轮廓，单点候选族）**
For a singleton candidate family, the consistency profile is identically zero.
-/
theorem consistency_profile_eq_zero_of_subsingleton
    [Subsingleton Aidx]
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (proxy : Aidx → Operator X bot) (j : I) (x : X) :
    consistency_profile d proxy j x = 0 := by
  apply le_antisymm
  · unfold consistency_profile
    apply iSup_le
    intro alpha
    apply iSup_le
    intro beta
    have hbeta : beta = alpha := Subsingleton.elim beta alpha
    subst beta
    exact le_of_eq ((hd j).dist_self ((proxy alpha).func x))
  · exact zero_le _

/--
OET anchor: h-0d1d36e9b079b4af
**命题（一致性轮廓的目标证书上界）**
If every candidate fits the same target on `U` over `J`, candidate disagreement
is bounded by the supremum of the pairwise tolerance sums.
-/
theorem consistency_profile_target_certificate_upper
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target : Operator X bot) (proxy : Aidx → Operator X bot)
    (U : Set X) (J : Set I) (tau : Aidx → I → ENNReal)
    (hfit : ∀ alpha : Aidx, InFittingBall d target (proxy alpha) U J (tau alpha)) :
    ∀ x ∈ U, ∀ j : I, j ∈ J →
      consistency_profile d proxy j x ≤
        ⨆ alpha : Aidx, ⨆ beta : Aidx, tau alpha j + tau beta j := by
  intro x hx j hj
  unfold consistency_profile
  apply iSup_le
  intro alpha
  apply iSup_le
  intro beta
  have htri :=
    (hd j).triangle ((proxy alpha).func x) (target.func x) ((proxy beta).func x)
  have halpha :
      d j ((proxy alpha).func x) (target.func x) ≤ tau alpha j := by
    simpa [(hd j).symm ((proxy alpha).func x) (target.func x)]
      using (hfit alpha).error x hx j hj
  have hbeta :
      d j (target.func x) ((proxy beta).func x) ≤ tau beta j :=
    (hfit beta).error x hx j hj
  have hpair :
      d j ((proxy alpha).func x) ((proxy beta).func x) ≤
        tau alpha j + tau beta j :=
    le_trans htri (add_le_add halpha hbeta)
  exact le_trans hpair
      (le_trans
        (le_iSup (fun beta : Aidx => tau alpha j + tau beta j) beta)
      (le_iSup (fun alpha : Aidx => ⨆ beta : Aidx, tau alpha j + tau beta j) alpha))

/--
OET anchor: h-0d1d36e9b079b4af
**命题（一致性轮廓的目标证书上界，正文前提版本）**
Text-faithful wrapper retaining the finite nonempty candidate family, nonempty
component set, and finite tolerance assumptions.
-/
theorem consistency_profile_target_certificate_upper_text
    [Fintype Aidx] [Nonempty Aidx]
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target : Operator X bot) (family : CandidateProxyFamily X bot Aidx)
    (U : Set X) (J : Set I) (tau : Aidx → I → ENNReal)
    (hJne : J.Nonempty)
    (htau_finite : ∀ alpha : Aidx, ∀ j : I, j ∈ J → finite_ennreal (tau alpha j))
    (hfit : ∀ alpha : Aidx, InFittingBall d target (family.proxy alpha) U J (tau alpha)) :
    ∀ x ∈ U, ∀ j : I, j ∈ J →
      consistency_profile d family.proxy j x ≤
        ⨆ alpha : Aidx, ⨆ beta : Aidx, tau alpha j + tau beta j := by
  have _ := hJne
  have _ := htau_finite
  exact consistency_profile_target_certificate_upper d hd target family.proxy U J tau hfit

/--
OET anchor: h-0d1d36e9b079b4af
**命题（一致性轮廓的目标证书上界，统一阈值版本）**
If all candidate tolerances are bounded by one vector, the consistency profile
is bounded by twice that vector component.
-/
theorem consistency_profile_uniform_target_certificate_upper
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target : Operator X bot) (proxy : Aidx → Operator X bot)
    (U : Set X) (J : Set I) (tau : Aidx → I → ENNReal)
    (tau₀ : I → ENNReal)
    (hfit : ∀ alpha : Aidx, InFittingBall d target (proxy alpha) U J (tau alpha))
    (htau : ∀ alpha : Aidx, ∀ j : I, j ∈ J → tau alpha j ≤ tau₀ j) :
    ∀ x ∈ U, ∀ j : I, j ∈ J →
      consistency_profile d proxy j x ≤ tau₀ j + tau₀ j := by
  intro x hx j hj
  unfold consistency_profile
  apply iSup_le
  intro alpha
  apply iSup_le
  intro beta
  have htri :=
    (hd j).triangle ((proxy alpha).func x) (target.func x) ((proxy beta).func x)
  have halpha :
      d j ((proxy alpha).func x) (target.func x) ≤ tau alpha j := by
    simpa [(hd j).symm ((proxy alpha).func x) (target.func x)]
      using (hfit alpha).error x hx j hj
  have hbeta :
      d j (target.func x) ((proxy beta).func x) ≤ tau beta j :=
    (hfit beta).error x hx j hj
  exact le_trans (le_trans htri (add_le_add halpha hbeta))
    (add_le_add (htau alpha j hj) (htau beta j hj))

/--
OET anchor: h-4c09ebab1364ae8a
**命题（证书上界子水平集的比较，矩阵向量单调性）**
The finite matrix-vector action is monotone in the matrix argument.
-/
theorem matrix_vector_bound_mono_matrix
    (A B : I → I → ENNReal) (v : I → ENNReal)
    (hAB : ∀ i j : I, A i j ≤ B i j) :
    ∀ j : I, matrix_vector_bound A v j ≤ matrix_vector_bound B v j := by
  intro j
  unfold matrix_vector_bound
  exact Finset.sum_le_sum fun i _ => by
    exact mul_le_mul_left (hAB i j) (v i)

/--
OET anchor: h-4c09ebab1364ae8a
**命题（证书上界子水平集的比较，共同锚点距离单调性）**
Pointwise matrix dominance implies dominance of the common-anchor distance.
-/
theorem weighted_anchor_distance_mono_matrix
    (d : I → X → X → ENNReal)
    (A B : I → I → ENNReal) (j : I) (x : X) (sample : Set X)
    (hAB : ∀ i j : I, A i j ≤ B i j) :
    weighted_anchor_distance d A j x sample ≤
      weighted_anchor_distance d B j x sample := by
  unfold weighted_anchor_distance
  apply le_iInf
  intro y
  exact le_trans
    (iInf_le
      (fun z : {z // z ∈ sample} =>
        matrix_vector_bound A (fun i => d i x z.1) j)
      y)
    (matrix_vector_bound_mono_matrix A B (fun i => d i x y.1) hAB j)

/--
OET anchor: h-4c09ebab1364ae8a
**命题（证书上界子水平集的比较，逐点证书上界）**
The scalar certificate upper bound obtained by adding a weighted common-anchor
term and a residual level.
-/
noncomputable def point_certificate_bound
    (d : I → X → X → ENNReal)
    (A : I → I → ENNReal) (sample : Set X)
    (eps : ENNReal) (j : I) (x : X) : ENNReal :=
  weighted_anchor_distance d A j x sample + eps

/--
OET anchor: h-4c09ebab1364ae8a
**命题（证书上界子水平集的比较，逐点证书界）**
If one proxy has no larger common-anchor term and no larger empirical residual,
then its pointwise certificate upper bound is no larger.
-/
theorem point_certificate_bound_le_of_matrix_and_residual_le
    (d : I → X → X → ENNReal)
    (A B : I → I → ENNReal) (sample : I → Set X)
    (epsA epsB : I → ENNReal)
    (hAB : ∀ i j : I, A i j ≤ B i j)
    (heps : ∀ j : I, epsA j ≤ epsB j) :
    ∀ x : X, ∀ j : I,
      weighted_anchor_distance d A j x (sample j) + epsA j ≤
        weighted_anchor_distance d B j x (sample j) + epsB j := by
  intro x j
  exact add_le_add (weighted_anchor_distance_mono_matrix d A B j x (sample j) hAB)
    (heps j)

/--
OET anchor: h-4c09ebab1364ae8a
**命题（证书上界子水平集的比较）**
Pointwise comparison of certificate upper bounds gives reverse inclusion of
the corresponding guarantee domains.
-/
theorem empirical_guarantee_domain_subset_of_certificate_bound_le
    (d : I → X → X → ENNReal)
    (Abetter Aworse : I → I → ENNReal) (U : Set X)
    (sample : I → Set X) (J : Set I)
    (eps_better eps_worse tau : I → ENNReal)
    (hbound :
      ∀ x ∈ U, ∀ j : I, j ∈ J →
        weighted_anchor_distance d Abetter j x (sample j) + eps_better j ≤
          weighted_anchor_distance d Aworse j x (sample j) + eps_worse j) :
    empirical_joint_guarantee_domain d Aworse U sample J eps_worse tau ⊆
      empirical_joint_guarantee_domain d Abetter U sample J eps_better tau := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  intro j hj
  exact le_trans (hbound x hx.1 j hj) (hx.2 j hj)

/--
OET anchor: h-4c09ebab1364ae8a
**命题（证书上界子水平集的比较，正文前提版本）**
The text-level statement retains the nonempty evaluable component family and
finite threshold vector.
-/
theorem empirical_guarantee_domain_subset_of_certificate_bound_le_text
    (d : I → X → X → ENNReal)
    (Abetter Aworse : I → I → ENNReal) (U : Set X)
    (sample : I → Set X) (J : Set I)
    (eps_better eps_worse tau : I → ENNReal)
    (hJ_nonempty : J.Nonempty)
    (hJ_evaluable : J ⊆ evaluable_components sample)
    (htau_finite : ∀ j : I, j ∈ J → finite_ennreal (tau j))
    (hbound :
      ∀ x ∈ U, ∀ j : I, j ∈ J →
        weighted_anchor_distance d Abetter j x (sample j) + eps_better j ≤
          weighted_anchor_distance d Aworse j x (sample j) + eps_worse j) :
    empirical_joint_guarantee_domain d Aworse U sample J eps_worse tau ⊆
      empirical_joint_guarantee_domain d Abetter U sample J eps_better tau := by
  have _ := hJ_nonempty
  have _ := hJ_evaluable
  have _ := htau_finite
  exact empirical_guarantee_domain_subset_of_certificate_bound_le
    d Abetter Aworse U sample J eps_better eps_worse tau hbound

/--
OET anchor: h-4c09ebab1364ae8a
**命题（证书上界子水平集的比较，矩阵与残差特例）**
Pointwise matrix and residual dominance imply the text-level sublevel-set
inclusion.
-/
theorem empirical_guarantee_domain_subset_of_matrix_and_residual_le_text
    (d : I → X → X → ENNReal)
    (Abetter Aworse : I → I → ENNReal) (U : Set X)
    (sample : I → Set X) (J : Set I)
    (eps_better eps_worse tau : I → ENNReal)
    (hJ_nonempty : J.Nonempty)
    (hJ_evaluable : J ⊆ evaluable_components sample)
    (htau_finite : ∀ j : I, j ∈ J → finite_ennreal (tau j))
    (hA : ∀ i j : I, Abetter i j ≤ Aworse i j)
    (heps : ∀ j : I, j ∈ J → eps_better j ≤ eps_worse j) :
    empirical_joint_guarantee_domain d Aworse U sample J eps_worse tau ⊆
      empirical_joint_guarantee_domain d Abetter U sample J eps_better tau := by
  refine empirical_guarantee_domain_subset_of_certificate_bound_le_text
    d Abetter Aworse U sample J eps_better eps_worse tau
    hJ_nonempty hJ_evaluable htau_finite ?_
  intro x _hx j hj
  exact add_le_add
    (weighted_anchor_distance_mono_matrix d Abetter Aworse j x (sample j) hA)
    (heps j hj)

/--
OET anchor: h-4c09ebab1364ae8a
**命题（证书上界子水平集的比较，单点阈值分离）**
A threshold between two pointwise certificate bounds puts a point in one
sublevel set and outside the other.
-/
theorem point_certificate_threshold_separates_domains
    (d : I → X → X → ENNReal)
    (Abetter Aworse : I → I → ENNReal) (U sample : Set X)
    (eps_better eps_worse tau : ENNReal) (j : I) {x : X}
    (hxU : x ∈ U)
    (hbetter :
      point_certificate_bound d Abetter sample eps_better j x ≤ tau)
    (hworse :
      tau < point_certificate_bound d Aworse sample eps_worse j x) :
    x ∈ empirical_component_guarantee_domain d Abetter U sample j eps_better tau ∧
      x ∉ empirical_component_guarantee_domain d Aworse U sample j eps_worse tau := by
  constructor
  · exact ⟨hxU, hbetter⟩
  · intro hx
    exact not_lt_of_ge hx.2 hworse

/--
OET anchor: h-02d097fade9a1b7a
**定义（选择规则与选择稳定性证书）**
A selection-stability certificate records that the selected proxies at two data
states are both defined on `U` and are componentwise close there.
-/
structure SelectionStabilityCertificate
    {D : Type}
    (d : I → X → X → ENNReal)
    (selector : D → Operator X bot)
    (U : Set X) (J : Set I) (sigma : I → ENNReal)
    (data₁ data₂ : D) : Prop where
  tolerance_finite : ∀ j : I, j ∈ J → finite_ennreal (sigma j)
  left_dom : U ⊆ dom (selector data₁)
  right_dom : U ⊆ dom (selector data₂)
  bound :
    ∀ x ∈ U, ∀ j : I, j ∈ J →
      d j ((selector data₁).func x) ((selector data₂).func x) ≤ sigma j

/--
OET anchor: h-02d097fade9a1b7a
**命题（选择稳定性的拟合传递）**
If the selected proxy at one data state fits the target, and the selection rule
is stable between two data states, then the selected proxy at the second data
state fits with the sum tolerance.
-/
theorem selection_stability_transfers_fitting
    {D : Type}
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (selector : D → Operator X bot)
    (target : Operator X bot) (U : Set X) (J : Set I)
    (tau sigma : I → ENNReal) (data₁ data₂ : D)
    (hfit : InFittingBall d target (selector data₁) U J tau)
    (hstable :
      SelectionStabilityCertificate d selector U J sigma data₁ data₂) :
    InFittingBall d target (selector data₂) U J (fun j => tau j + sigma j) := by
  refine ⟨?_, hfit.target_dom, hstable.right_dom, ?_⟩
  · intro j hj
    exact ENNReal.add_ne_top.mpr
      ⟨hfit.tolerance_finite j hj, hstable.tolerance_finite j hj⟩
  intro x hx j hj
  have htri :=
    (hd j).triangle (target.func x) ((selector data₁).func x) ((selector data₂).func x)
  exact le_trans htri
    (add_le_add (hfit.error x hx j hj) (hstable.bound x hx j hj))

/--
OET anchor: h-02d097fade9a1b7a
**命题（选择稳定性的拟合传递，正文前提版本）**
The text-level statement retains the nonempty component family.
-/
theorem selection_stability_transfers_fitting_text
    {D : Type}
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (selector : D → Operator X bot)
    (target : Operator X bot) (U : Set X) (J : Set I)
    (tau sigma : I → ENNReal) (data₁ data₂ : D)
    (hJ_nonempty : J.Nonempty)
    (hfit : InFittingBall d target (selector data₁) U J tau)
    (hstable :
      SelectionStabilityCertificate d selector U J sigma data₁ data₂) :
    InFittingBall d target (selector data₂) U J (fun j => tau j + sigma j) := by
  have _ := hJ_nonempty
  exact selection_stability_transfers_fitting d hd selector target U J
    tau sigma data₁ data₂ hfit hstable

end formal_oet.vol_03.ch_13_comparison_and_falsification
