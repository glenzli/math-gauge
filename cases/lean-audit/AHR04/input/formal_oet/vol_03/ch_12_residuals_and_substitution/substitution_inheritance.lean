import formal_oet.vol_03.ch_12_residuals_and_substitution.guarantee_domains
import formal_oet.vol_02.ch_07_fitting_foundations.chain_recurrence
import formal_oet.vol_02.ch_09_family_fitting.joint_fitting
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace formal_oet.vol_03.ch_12_residuals_and_substitution

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open formal_oet.vol_01.ch_04_operator_chain_calculus
open formal_oet.vol_02.ch_07_fitting_foundations
open formal_oet.vol_02.ch_09_family_fitting

open scoped BigOperators

variable {X I : Type} {bot : X} [Fintype I]

/--
OET anchor: h-811f6faa2a21c74d
**引理（经验拟合球继承）**
On any subdomain of the empirical guarantee domain, the empirical upper
certificate gives the corresponding component fitting ball.
-/
theorem empirical_fitting_ball_inheritance
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (A : I → I → ENNReal) (U U₀ : Set X)
    (sample : I → Set X) (J : Set I)
    (target proxy : Operator X bot)
    (eps tau : I → ENNReal)
    (htau_finite : ∀ j : I, j ∈ J → finite_ennreal (tau j))
    (htarget_dom : U₀ ⊆ dom target)
    (hproxy_dom : U₀ ⊆ dom proxy)
    (hU₀ :
      U₀ ⊆ empirical_joint_guarantee_domain d A U sample J eps tau)
    (hupper :
      ∀ x ∈ U, ∀ j : I, j ∈ J →
        d j (proxy.func x) (target.func x) ≤
          weighted_anchor_distance d A j x (sample j) + eps j) :
    InFittingBall d target proxy U₀ J tau := by
  refine ⟨htau_finite, htarget_dom, hproxy_dom, ?_⟩
  intro x hx j hj
  have hbound :=
    empirical_joint_guarantee_error_bound d A U sample J target proxy eps tau
      hupper (hU₀ hx) j hj
  simpa [(hd j).symm (target.func x) (proxy.func x)] using hbound

/--
OET anchor: h-f0c32a1e279a067f
**推论（经验代理传递）**
Fitting a proxy to an empirically certified proxy adds the two component
tolerance vectors on the same component set.
-/
theorem empirical_proxy_transfer
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy psi : Operator X bot) (U : Set X) (J : Set I)
    (tau sigma : I → ENNReal)
    (hproxy :
      InFittingBall d target proxy U J tau)
    (hpsi :
      InFittingBall d proxy psi U J sigma) :
    InFittingBall d target psi U J (fun j => tau j + sigma j) := by
  refine ⟨?_, hproxy.target_dom, hpsi.proxy_dom, ?_⟩
  · intro j hj
    exact ENNReal.add_ne_top.mpr
      ⟨hproxy.tolerance_finite j hj, hpsi.tolerance_finite j hj⟩
  intro x hx j hj
  have htri :=
    (hd j).triangle (target.func x) (proxy.func x) (psi.func x)
  exact le_trans htri
    (add_le_add (hproxy.error x hx j hj) (hpsi.error x hx j hj))

/--
OET anchor: h-f0c32a1e279a067f
**推论（经验代理传递，保证域正文形式）**
On a nonempty evaluable component family, a subdomain of the empirical
guarantee domain first yields the target-to-proxy fitting certificate; fitting
a second proxy to that proxy then gives the summed tolerance certificate.
-/
theorem empirical_proxy_transfer_from_guarantee_domain_text
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (A : I → I → ENNReal) (U U₀ : Set X)
    (sample : I → Set X) (J : Set I)
    (target proxy psi : Operator X bot)
    (eps tau sigma : I → ENNReal)
    (hJ_nonempty : J.Nonempty)
    (hJ_evaluable : J ⊆ evaluable_components sample)
    (htau_finite : ∀ j : I, j ∈ J → finite_ennreal (tau j))
    (htarget_dom : U₀ ⊆ dom target)
    (hproxy_dom : U₀ ⊆ dom proxy)
    (hU₀ :
      U₀ ⊆ empirical_joint_guarantee_domain d A U sample J eps tau)
    (hupper :
      ∀ x ∈ U, ∀ j : I, j ∈ J →
        d j (proxy.func x) (target.func x) ≤
          weighted_anchor_distance d A j x (sample j) + eps j)
    (hpsi : InFittingBall d proxy psi U₀ J sigma) :
    InFittingBall d target psi U₀ J (fun j => tau j + sigma j) := by
  have _ := hJ_nonempty
  have _ := hJ_evaluable
  have hproxy :
      InFittingBall d target proxy U₀ J tau :=
    empirical_fitting_ball_inheritance d hd A U U₀ sample J target proxy
      eps tau htau_finite htarget_dom hproxy_dom hU₀ hupper
  exact empirical_proxy_transfer d hd target proxy psi U₀ J tau sigma
    hproxy hpsi

/--
OET anchor: h-55e5b701cc5268a8
**推论（活跃目标散度证书下的经验继承）**
A divergence certificate from one reference target to every active target
transfers the empirical bound pointwise on the same component family.
-/
theorem active_target_divergence_empirical_inheritance
    {β : Type} [Fintype β] [Nonempty β]
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target : β → Operator X bot) (beta₀ : β)
    (proxy : Operator X bot) (U : Set X) (J : Set I)
    (tau Delta : I → ENNReal)
    (hDelta_finite : ∀ j : I, j ∈ J → finite_ennreal (Delta j))
    (hfit :
      InFittingBall d (target beta₀) proxy U J tau)
    (hdiv :
      ∀ x ∈ U, ∀ beta : β, beta ∈ active_indices target U x →
        ∀ j : I, j ∈ J →
          d j ((target beta₀).func x) ((target beta).func x) ≤ Delta j) :
    ∀ x ∈ U, ∀ beta : β, beta ∈ active_indices target U x →
      ∀ j : I, j ∈ J →
        d j ((target beta).func x) (proxy.func x) ≤ tau j + Delta j := by
  intro x hx beta hbeta j hj
  have _ := hDelta_finite j hj
  have htri :=
    (hd j).triangle ((target beta).func x) ((target beta₀).func x) (proxy.func x)
  have hdiv_symm :
      d j ((target beta).func x) ((target beta₀).func x) ≤ Delta j := by
    simpa [(hd j).symm ((target beta).func x) ((target beta₀).func x)]
      using hdiv x hx beta hbeta j hj
  calc
    d j ((target beta).func x) (proxy.func x)
        ≤ d j ((target beta).func x) ((target beta₀).func x) +
            d j ((target beta₀).func x) (proxy.func x) := htri
    _ ≤ Delta j + tau j :=
        add_le_add hdiv_symm (hfit.error x hx j hj)
    _ = tau j + Delta j := by
        rw [add_comm]

/--
OET anchor: h-55e5b701cc5268a8
**推论（活跃目标散度证书下的经验继承，正文前提形式）**
Text-faithful form retaining that the selected component family is nonempty.
-/
theorem active_target_divergence_empirical_inheritance_text
    {β : Type} [Fintype β] [Nonempty β]
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target : β → Operator X bot) (beta₀ : β)
    (proxy : Operator X bot) (U : Set X) (J : Set I)
    (tau Delta : I → ENNReal)
    (hJ_nonempty : J.Nonempty)
    (hDelta_finite : ∀ j : I, j ∈ J → finite_ennreal (Delta j))
    (hfit :
      InFittingBall d (target beta₀) proxy U J tau)
    (hdiv :
      ∀ x ∈ U, ∀ beta : β, beta ∈ active_indices target U x →
        ∀ j : I, j ∈ J →
          d j ((target beta₀).func x) ((target beta).func x) ≤ Delta j) :
    ∀ x ∈ U, ∀ beta : β, beta ∈ active_indices target U x →
      ∀ j : I, j ∈ J →
        d j ((target beta).func x) (proxy.func x) ≤ tau j + Delta j := by
  have _ := hJ_nonempty
  exact active_target_divergence_empirical_inheritance
    d hd target beta₀ proxy U J tau Delta hDelta_finite hfit hdiv

/--
OET anchor: h-55e5b701cc5268a8
**推论（活跃目标散度证书下的经验继承，全分量形式）**
When every component is controlled, the active-target pointwise bounds are
exactly a joint fitting certificate for the target family.
-/
theorem active_target_divergence_empirical_joint_fitting
    {β : Type} [Fintype β] [Nonempty β] [Nonempty I]
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target : β → Operator X bot) (beta₀ : β)
    (proxy : Operator X bot) (U : Set X)
    (tau Delta : I → ENNReal)
    (hDelta_finite : ∀ j : I, finite_ennreal (Delta j))
    (hfit : InFullFittingBall d (target beta₀) proxy U tau)
    (hdiv :
      ∀ x ∈ U, ∀ beta : β, beta ∈ active_indices target U x →
        ∀ j : I,
          d j ((target beta₀).func x) ((target beta).func x) ≤ Delta j) :
    JointFitting d target proxy U (fun j => tau j + Delta j) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    exact ENNReal.add_ne_top.mpr
      ⟨hfit.tolerance_finite j (Set.mem_univ j), hDelta_finite j⟩
  · intro x hx
    exact hfit.proxy_dom hx.1
  · intro x hx beta hbeta j
    exact active_target_divergence_empirical_inheritance
      d hd target beta₀ proxy U Set.univ tau Delta
      (fun q _ => hDelta_finite q) hfit
      (fun x hx beta hbeta j _ => hdiv x hx beta hbeta j)
      x hx.1 beta hbeta j (Set.mem_univ j)

/--
OET anchor: h-d58fb36d7b840be1
**命题（有限采样的补域分歧见证，采样并集）**
The union of all resolved component sample sets.
-/
def sample_union (sample : I → Set X) (J : Set I) : Set X :=
  {x | ∃ j : I, j ∈ J ∧ x ∈ sample j}

/--
OET anchor: h-d58fb36d7b840be1
**命题（有限采样的补域分歧见证，零容限相容目标类）**
Target candidates compatible with the current samples at zero tolerance on
the resolved component set.
-/
def zero_tolerance_sample_compatible
    (d : I → X → X → ENNReal)
    (target psi : Operator X bot) (sample : I → Set X) (J : Set I) : Prop :=
  ∀ j : I, j ∈ J → ∀ x ∈ sample j,
    d j (psi.func x) (target.func x) = 0

/--
OET anchor: h-d58fb36d7b840be1
**命题（有限采样的补域分歧见证，补域改写算子）**
An operator that agrees with the target on the sample union, assigns a chosen
value at one unsampled point, and sends all other points to `bot`.
-/
noncomputable def sample_complement_override
    (target : Operator X bot) (Sbullet : Set X)
    (x₀ value : X) (hx₀_ne_bot : x₀ ≠ bot) : Operator X bot := by
  classical
  refine
    { func := fun x =>
        if x ∈ Sbullet then target.func x else if x = x₀ then value else bot
      preserves_bot := ?_ }
  by_cases hbotS : bot ∈ Sbullet
  · simp [hbotS, target.preserves_bot]
  · have hbot_ne_x₀ : bot ≠ x₀ := by
      intro h
      exact hx₀_ne_bot h.symm
    simp [hbotS, hbot_ne_x₀]

/--
OET anchor: h-d58fb36d7b840be1
**命题（有限采样的补域分歧见证，采样上一致）**
The complement override agrees with the target on the sample union.
-/
theorem sample_complement_override_eq_on_sample
    (target : Operator X bot) (Sbullet : Set X)
    (x₀ value : X) (hx₀_ne_bot : x₀ ≠ bot)
    {x : X} (hx : x ∈ Sbullet) :
    (sample_complement_override target Sbullet x₀ value hx₀_ne_bot).func x =
      target.func x := by
  classical
  simp [sample_complement_override, hx]

/--
OET anchor: h-d58fb36d7b840be1
**命题（有限采样的补域分歧见证，补域点取值）**
At the selected unsampled point, the complement override takes the chosen
value.
-/
theorem sample_complement_override_value_at
    (target : Operator X bot) (Sbullet : Set X)
    (x₀ value : X) (hx₀_ne_bot : x₀ ≠ bot)
    (hx₀_not_sample : x₀ ∉ Sbullet) :
    (sample_complement_override target Sbullet x₀ value hx₀_ne_bot).func x₀ =
      value := by
  classical
  simp [sample_complement_override, hx₀_not_sample]

/--
OET anchor: h-d58fb36d7b840be1
**命题（有限采样的补域分歧见证）**
If there is an unsampled non-bottom point and a distinguishable output pair,
then two sample-compatible targets can still differ at that point.
-/
theorem finite_sample_complement_underdetermined
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target : Operator X bot) (sample : I → Set X) (J : Set I)
    (U : Set X)
    {x₀ a b : X} {ell : I}
    (hx₀U : x₀ ∈ U)
    (hx₀_not_sample : x₀ ∉ sample_union sample J)
    (hx₀_ne_bot : x₀ ≠ bot)
    (hsep : 0 < d ell a b) :
    ∃ psi_a psi_b : Operator X bot,
      zero_tolerance_sample_compatible d target psi_a sample J ∧
      zero_tolerance_sample_compatible d target psi_b sample J ∧
      0 < d ell (psi_a.func x₀) (psi_b.func x₀) := by
  have _ := hx₀U
  let psi_a := sample_complement_override target (sample_union sample J) x₀ a hx₀_ne_bot
  let psi_b := sample_complement_override target (sample_union sample J) x₀ b hx₀_ne_bot
  refine ⟨psi_a, psi_b, ?_, ?_, ?_⟩
  · intro j hj x hx
    have hx_union : x ∈ sample_union sample J := ⟨j, hj, hx⟩
    rw [show psi_a.func x = target.func x from
      sample_complement_override_eq_on_sample target (sample_union sample J)
        x₀ a hx₀_ne_bot hx_union]
    exact (hd j).dist_self (target.func x)
  · intro j hj x hx
    have hx_union : x ∈ sample_union sample J := ⟨j, hj, hx⟩
    rw [show psi_b.func x = target.func x from
      sample_complement_override_eq_on_sample target (sample_union sample J)
        x₀ b hx₀_ne_bot hx_union]
    exact (hd j).dist_self (target.func x)
  · rw [show psi_a.func x₀ = a from
        sample_complement_override_value_at target (sample_union sample J)
          x₀ a hx₀_ne_bot hx₀_not_sample,
      show psi_b.func x₀ = b from
        sample_complement_override_value_at target (sample_union sample J)
          x₀ b hx₀_ne_bot hx₀_not_sample]
    exact hsep

/--
OET anchor: h-c9dea98a2f95fb0c
**推论（经验链的域内累积上界）**
Layerwise empirical fitting balls satisfy the same terminal accumulation bound
as the deterministic in-domain chain recurrence.
-/
theorem empirical_chain_in_domain_accumulation
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Nat → Operator X bot)
    (U : Nat → Set X) (tau : Nat → I → ENNReal)
    (L : Nat → I → I → ENNReal)
    (target_state proxy_state : Nat → X) (k : Nat)
    (hinitial : target_state 0 = proxy_state 0)
    (htarget_step : ∀ n : Nat, n < k →
      target_state (n + 1) = (target n).func (target_state n))
    (hproxy_step : ∀ n : Nat, n < k →
      proxy_state (n + 1) = (proxy n).func (proxy_state n))
    (hfit : ∀ n : Nat, n < k →
      InFullFittingBall d (target n) (proxy n) (U n) (tau n))
    (hL : ∀ n : Nat, n < k → IsLipMatrix d (target n) (U n) (L n))
    (htarget_mem : ∀ n : Nat, n < k → target_state n ∈ U n)
    (hproxy_mem : ∀ n : Nat, n < k → proxy_state n ∈ U n) :
    ∀ j : I,
      d j (target_state k) (proxy_state k) ≤
        ordered_suffix_error_sum L tau k j :=
  in_domain_chain_deviation_accumulation d hd target proxy U tau L
    target_state proxy_state k hinitial htarget_step hproxy_step hfit hL
    htarget_mem hproxy_mem

end formal_oet.vol_03.ch_12_residuals_and_substitution
