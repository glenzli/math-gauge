import formal_oet.vol_02.ch_07_fitting_foundations.fitting_ball
import formal_oet.vol_03.ch_13_comparison_and_falsification.compatibility_identifiability
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

variable {X I : Type} {bot : X} [Fintype I]

/--
OET anchor: h-9b65ffd51c5a2abc
**定义（加权锚点覆盖数，覆盖集合）**
A finite nonempty subset of `U` whose common-anchor distance covers every point
of `U` at level `eps`.
-/
def weighted_covering_set
    (d : I → X → X → ENNReal)
    (A : I → I → ENNReal) (j : I) (eps : ENNReal)
    (U E : Set X) : Prop :=
  E ⊆ U ∧ E.Nonempty ∧ E.Finite ∧
    ∀ x ∈ U, weighted_anchor_distance d A j x E ≤ eps

/--
OET anchor: h-9b65ffd51c5a2abc
**定义（加权锚点覆盖数）**
The weighted covering number, with value `0` on the empty set and `⊤` when no
finite cover exists.
-/
noncomputable def weighted_cover_number
    (d : I → X → X → ENNReal)
    (A : I → I → ENNReal) (j : I) (eps : ENNReal)
    (U : Set X) : ENNReal :=
  if U = ∅ then 0
  else
    ⨅ E : {E : Set X // weighted_covering_set d A j eps U E},
      (E.1.ncard : ENNReal)

/--
OET anchor: h-9b65ffd51c5a2abc
**定义（加权锚点覆盖数，空集）**
The weighted covering number of the empty set is zero.
-/
theorem weighted_cover_number_empty
    (d : I → X → X → ENNReal)
    (A : I → I → ENNReal) (j : I) (eps : ENNReal) :
    weighted_cover_number d A j eps (∅ : Set X) = 0 := by
  simp [weighted_cover_number]

/--
OET anchor: h-9b65ffd51c5a2abc
**定义（加权锚点覆盖数，覆盖见证）**
Any finite weighted cover gives an upper bound for the covering number.
-/
theorem weighted_cover_number_le_of_cover
    (d : I → X → X → ENNReal)
    (A : I → I → ENNReal) (j : I) (eps : ENNReal)
    (U E : Set X)
    (hcover : weighted_covering_set d A j eps U E) :
    weighted_cover_number d A j eps U ≤ (E.ncard : ENNReal) := by
  by_cases hU : U = ∅
  · simp [weighted_cover_number, hU]
  · simpa [weighted_cover_number, hU] using
      (iInf_le
        (fun E : {E : Set X // weighted_covering_set d A j eps U E} =>
          (E.1.ncard : ENNReal))
        ⟨E, hcover⟩)

/--
OET anchor: h-346bbadd3afdf12a
**命题（加权覆盖的保证域判据）**
A common-anchor cover turns the empirical upper certificate into a uniform
component-distance-vector bound.
-/
theorem weighted_cover_guarantee_bound
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (A : I → I → ENNReal) (U sample : Set X)
    (target proxy : Operator X bot) (j : I)
    (eps eta : ENNReal)
    (heps_finite : finite_ennreal eps)
    (hcover : ∀ x ∈ U, weighted_anchor_distance d A j x sample ≤ eps)
    (hupper :
      ∀ x ∈ U,
        d j (proxy.func x) (target.func x) ≤
          weighted_anchor_distance d A j x sample + eta) :
    component_error_vector d target proxy U j ≤ eps + eta := by
  have _ := heps_finite
  unfold component_error_vector
  apply iSup_le
  intro x
  have hsymm :
      d j (target.func x.1) (proxy.func x.1) ≤
        weighted_anchor_distance d A j x.1 sample + eta := by
    simpa [(hd j).symm (target.func x.1) (proxy.func x.1)]
      using hupper x.1 x.2
  exact le_trans hsymm (add_le_add (hcover x.1 x.2) le_rfl)

/--
OET anchor: h-346bbadd3afdf12a
**命题（加权覆盖的保证域判据，覆盖数反面）**
If a finite sample is smaller than the weighted covering number, then it fails
to cover at least one point of `U`.
-/
theorem exists_anchor_gap_of_card_lt_weighted_cover_number
    (d : I → X → X → ENNReal)
    (A : I → I → ENNReal) (j : I) (eps : ENNReal)
    (U sample : Set X)
    (heps_finite : finite_ennreal eps)
    (hsample_subset : sample ⊆ U)
    (hsample_nonempty : sample.Nonempty)
    (hsample_finite : sample.Finite)
    (hlt : (sample.ncard : ENNReal) < weighted_cover_number d A j eps U) :
    ∃ x ∈ U, eps < weighted_anchor_distance d A j x sample := by
  have _ := heps_finite
  by_contra hno
  have hcover_all :
      ∀ x ∈ U, weighted_anchor_distance d A j x sample ≤ eps := by
    intro x hx
    exact le_of_not_gt (by
      intro hgt
      exact hno ⟨x, hx, hgt⟩)
  have hcover : weighted_covering_set d A j eps U sample :=
    ⟨hsample_subset, hsample_nonempty, hsample_finite, hcover_all⟩
  have hNle := weighted_cover_number_le_of_cover d A j eps U sample hcover
  exact not_lt_of_ge hNle hlt

/--
OET anchor: h-346bbadd3afdf12a
**命题（加权覆盖的保证域判据，覆盖数正文版本）**
The text-level covering-number statement retains membership in the active
component family.
-/
theorem exists_anchor_gap_of_card_lt_weighted_cover_number_text
    (d : I → X → X → ENNReal)
    (A : I → I → ENNReal) (J : Set I) (j : I) (eps : ENNReal)
    (U sample : Set X)
    (hj : j ∈ J)
    (heps_finite : finite_ennreal eps)
    (hsample_subset : sample ⊆ U)
    (hsample_nonempty : sample.Nonempty)
    (hsample_finite : sample.Finite)
    (hlt : (sample.ncard : ENNReal) < weighted_cover_number d A j eps U) :
    ∃ x ∈ U, eps < weighted_anchor_distance d A j x sample := by
  have _ := hj
  exact exists_anchor_gap_of_card_lt_weighted_cover_number
    d A j eps U sample heps_finite hsample_subset hsample_nonempty
    hsample_finite hlt

/--
OET anchor: h-346bbadd3afdf12a
**命题（加权覆盖的保证域判据，经验上界证书版本）**
The empirical upper certificate at `h-f16da76e4331b725` and a weighted cover
together give the
uniform component-distance-vector bound.
-/
theorem weighted_cover_guarantee_bound_from_residual_certificate
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U V : Set X)
    (sample : I → Set X)
    (Lp Lstar : I → I → ENNReal) (eps_res : I → ENNReal)
    (cover_eps : ENNReal) (j : I)
    (hcover_eps_finite : finite_ennreal cover_eps)
    (hU : U ⊆ V)
    (hsample : sample j ⊆ U)
    (hLp : IsLipMatrix d proxy U Lp)
    (hLstar : TargetLipEnvelopeCertificate d target V Lstar)
    (hres : EmpiricalResidualBound d target proxy sample eps_res)
    (hj : j ∈ evaluable_components sample)
    (hcover :
      ∀ x ∈ U,
        weighted_anchor_distance d (fun i j => Lp i j + Lstar i j)
          j x (sample j) ≤ cover_eps) :
    component_error_vector d target proxy U j ≤ cover_eps + eps_res j := by
  refine weighted_cover_guarantee_bound d hd
    (fun i j => Lp i j + Lstar i j) U (sample j) target proxy j
    cover_eps (eps_res j) hcover_eps_finite hcover ?_
  intro x hx
  exact empirical_target_perturbation_upper_point_from_residual_certificate
    d hd target proxy U V sample Lp Lstar eps_res j hU hsample hLp hLstar hres hj x hx

/--
OET anchor: h-346bbadd3afdf12a
**命题（加权覆盖的保证域判据，证书失效不蕴含真实下界）**
A threshold smaller than the available upper-certificate budget is only a
failure of that certificate.  It cannot force a true-error lower bound, as
shown by taking the target and proxy to be the same operator.
-/
theorem anchor_certificate_failure_does_not_force_true_error
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (A : I → I → ENNReal) (U sample : Set X)
    (phi : Operator X bot) (j : I)
    (eps_res tau : ENNReal) {x : X}
    (hUdom : U ⊆ dom phi)
    (hxU : x ∈ U)
    (hcertificate_failure :
      tau < weighted_anchor_distance d A j x sample + eps_res) :
    x ∈ dom phi ∧ ¬ tau < d j (phi.func x) (phi.func x) := by
  have _ := hcertificate_failure
  refine ⟨hUdom hxU, ?_⟩
  rw [(hd j).dist_self]
  exact not_lt_of_ge (zero_le tau)

/--
OET anchor: h-beb567f1812b2bf2
**推论（采样增广的证书非单调性）**
A witness satisfying the two certificate inequalities refutes inclusion of the
two guarantee sublevel sets.
-/
theorem guarantee_domain_not_subset_of_witness
    (d : I → X → X → ENNReal)
    (A : I → I → ENNReal) (j : I) (U : Set X)
    (S T : Set X) (etaS etaT tau : ENNReal) {x : X}
    (hxU : x ∈ U)
    (hS : weighted_anchor_distance d A j x S + etaS ≤ tau)
    (hT : tau < weighted_anchor_distance d A j x T + etaT) :
    ¬ anchor_gap_sublevel d A j U S etaS tau ⊆
      anchor_gap_sublevel d A j U T etaT tau := by
  intro hsub
  have hxS : x ∈ anchor_gap_sublevel d A j U S etaS tau := ⟨hxU, hS⟩
  have hxT := hsub hxS
  exact not_lt_of_ge hxT.2 hT

/--
OET anchor: h-beb567f1812b2bf2
**推论（采样增广的证书非单调性，正文前提版本）**
Text-faithful wrapper retaining sample inclusion, nonempty original sample and
finite threshold assumptions.
-/
theorem guarantee_domain_not_subset_of_witness_text
    (d : I → X → X → ENNReal)
    (A : I → I → ENNReal) (J : Set I) (j : I) (U : Set X)
    (S T : Set X) (etaS etaT tau : ENNReal) {x : X}
    (hj : j ∈ J)
    (hS_nonempty : S.Nonempty)
    (htau_finite : finite_ennreal tau)
    (hST : S ⊆ T)
    (hxU : x ∈ U)
    (hS : weighted_anchor_distance d A j x S + etaS ≤ tau)
    (hT : tau < weighted_anchor_distance d A j x T + etaT) :
    ¬ anchor_gap_sublevel d A j U S etaS tau ⊆
      anchor_gap_sublevel d A j U T etaT tau := by
  have _ := hj
  have _ := hS_nonempty
  have _ := htau_finite
  have _ := hST
  exact guarantee_domain_not_subset_of_witness d A j U S T etaS etaT tau
    hxU hS hT

/--
OET anchor: h-beb567f1812b2bf2
**推论（采样增广的证书非单调性，锚点特例）**
If the residual level increases past the threshold, a sampled anchor can leave
the guarantee domain after sample augmentation.
-/
theorem guarantee_domain_nonmonotone_at_anchor
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (A : I → I → ENNReal) (J : Set I) (j : I) (U : Set X)
    {S T : Set X} {etaS etaT tau : ENNReal} {xs : X}
    (hj : j ∈ J)
    (hST : S ⊆ T)
    (hxsU : xs ∈ U)
    (hxs : xs ∈ S)
    (htau_finite : finite_ennreal tau)
    (hetaS : etaS ≤ tau)
    (hetaT : tau < etaT) :
    xs ∈ anchor_gap_sublevel d A j U S etaS tau ∧
      xs ∉ anchor_gap_sublevel d A j U T etaT tau := by
  have _ := hj
  have _ := htau_finite
  have hxsT : xs ∈ T := hST hxs
  constructor
  · refine ⟨hxsU, ?_⟩
    rw [weighted_anchor_distance_self_eq_zero d hd A j hxs, zero_add]
    exact hetaS
  · intro hxT
    have hineq := hxT.2
    rw [weighted_anchor_distance_self_eq_zero d hd A j hxsT, zero_add] at hineq
    exact not_lt_of_ge hineq hetaT

/--
OET anchor: h-d2b8bdbba2123b66
**命题（残差次序不决定总证书上界）**
Finite scalar certificate data can have ordered residuals but oppositely
ordered total certificate bounds.
-/
theorem residual_order_not_total_certificate_order_example :
    ∃ qA qB epsA epsB tau : ENNReal,
      epsA ≤ epsB ∧ qB + epsB ≤ tau ∧ tau < qA + epsA := by
  refine ⟨2, 0, 0, 1, 1, ?_⟩
  norm_num

/--
OET anchor: h-d2b8bdbba2123b66
**命题（残差次序不决定总证书上界，标量子水平集）**
The sublevel set of a scalar certificate bound on an arbitrary point type.
-/
def scalar_certificate_sublevel {Y : Type}
    (bound : Y → ENNReal) (tau : ENNReal) : Set Y :=
  {y | bound y ≤ tau}

/--
OET anchor: h-d2b8bdbba2123b66
**命题（残差次序不决定总证书上界，单点子水平集）**
The same scalar data give a singleton witness to failure of the corresponding
sublevel-set inclusion.
-/
theorem residual_order_not_total_certificate_order_singleton_sublevel_example :
    ∃ qA qB epsA epsB tau : ENNReal,
      epsA ≤ epsB ∧
        ¬ scalar_certificate_sublevel (fun _ : Unit => qB + epsB) tau ⊆
          scalar_certificate_sublevel (fun _ : Unit => qA + epsA) tau := by
  refine ⟨2, 0, 0, 1, 1, ?_⟩
  constructor
  · norm_num
  · intro hsub
    have hunit :
        () ∈ scalar_certificate_sublevel
          (fun _ : Unit => (0 : ENNReal) + 1) 1 := by
      simp [scalar_certificate_sublevel]
    have := hsub hunit
    simp [scalar_certificate_sublevel] at this

/--
OET anchor: h-3e5f85a33b1d1e28
**命题（纤维压缩的采样证伪）**
If two sampled points are collapsed by the proxy in component `j`, two
componentwise fitting bounds force the target outputs to be within twice that
tolerance.
-/
theorem fiber_compression_sample_falsification_bound
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (eta : ENNReal) (j : I)
    {x y : X}
    (hcollapse : d j (proxy.func x) (proxy.func y) = 0)
    (hxfit : d j (proxy.func x) (target.func x) ≤ eta)
    (hyfit : d j (proxy.func y) (target.func y) ≤ eta) :
    d j (target.func x) (target.func y) ≤ eta + eta := by
  have htri₁ :=
    (hd j).triangle (target.func x) (proxy.func x) (target.func y)
  have htri₂ :=
    (hd j).triangle (proxy.func x) (proxy.func y) (target.func y)
  have hxfit_symm : d j (target.func x) (proxy.func x) ≤ eta := by
    simpa [(hd j).symm (target.func x) (proxy.func x)] using hxfit
  calc
    d j (target.func x) (target.func y)
        ≤ d j (target.func x) (proxy.func x) +
            d j (proxy.func x) (target.func y) := htri₁
    _ ≤ eta + d j (proxy.func x) (target.func y) :=
        add_le_add hxfit_symm le_rfl
    _ ≤ eta + (d j (proxy.func x) (proxy.func y) +
          d j (proxy.func y) (target.func y)) :=
        add_le_add le_rfl htri₂
    _ ≤ eta + (0 + eta) := by
        exact add_le_add le_rfl (add_le_add (le_of_eq hcollapse) hyfit)
    _ = eta + eta := by
        simp

/--
OET anchor: h-3e5f85a33b1d1e28
**命题（纤维压缩的采样证伪，反证形式）**
Target separation above twice the tolerance rules out simultaneous fitting on
the two collapsed sample points.
-/
theorem fiber_compression_sample_falsification
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (eta : ENNReal) (j : I)
    {x y : X}
    (hcollapse : d j (proxy.func x) (proxy.func y) = 0)
    (hsep : eta + eta < d j (target.func x) (target.func y)) :
    ¬ (d j (proxy.func x) (target.func x) ≤ eta ∧
        d j (proxy.func y) (target.func y) ≤ eta) := by
  intro hfit
  exact not_lt_of_ge
    (fiber_compression_sample_falsification_bound d hd target proxy eta j
      hcollapse hfit.1 hfit.2)
    hsep

/--
OET anchor: h-3e5f85a33b1d1e28
**命题（纤维压缩的采样证伪，正文前提版本）**
Text-faithful wrapper retaining that both points belong to the component sample.
-/
theorem fiber_compression_sample_falsification_text
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (sample : Set X)
    (eta : ENNReal) (J : Set I) (j : I)
    {x y : X}
    (hj : j ∈ J)
    (hsample : sample ⊆ dom proxy ∩ dom target)
    (heta_finite : finite_ennreal eta)
    (hx : x ∈ sample) (hy : y ∈ sample)
    (hcollapse : d j (proxy.func x) (proxy.func y) = 0)
    (hsep : eta + eta < d j (target.func x) (target.func y)) :
    ¬ (d j (proxy.func x) (target.func x) ≤ eta ∧
        d j (proxy.func y) (target.func y) ≤ eta) := by
  have _ := hj
  have _ := hsample hx
  have _ := hsample hy
  have _ := heta_finite
  exact fiber_compression_sample_falsification d hd target proxy eta j
    hcollapse hsep

end formal_oet.vol_03.ch_13_comparison_and_falsification
