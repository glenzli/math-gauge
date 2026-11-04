import formal_oet.vol_01.ch_05_operator_networks.network_profiles
import formal_oet.vol_02.ch_07_fitting_foundations.fitting_ball

namespace formal_oet.vol_02.ch_08_network_fitting

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_05_operator_networks
open formal_oet.vol_02.ch_07_fitting_foundations

variable {X I Net ProfileValue : Type} {bot : X}

/--
OET path: vol-02-deterministic-fitting/08-network-fitting.md
**定义（读出受控代理）**
The readout preorder comparison induced by one ordered network profile.
-/
def profile_le (Γ : OrderedNetworkProfile Net ProfileValue)
    (proxy target : Net) : Prop :=
  Γ.le (Γ.read proxy) (Γ.read target)

/--
OET path: vol-02-deterministic-fitting/08-network-fitting.md
**定义（读出受控代理）**
The canonical strict part of the readout preorder.
-/
def profile_lt (Γ : OrderedNetworkProfile Net ProfileValue)
    (proxy target : Net) : Prop :=
  profile_le Γ proxy target ∧ ¬ profile_le Γ target proxy

/--
OET anchor: h-b48eeff85d89e7fb
**命题（外延拟合的读出不敏感性）**
If two proxy exterior operators are pointwise indistinguishable on the
evaluation domain in every gauge component, then they have the same
full-gauge error-band membership with respect to the same target.
-/
theorem full_fitting_ball_iff_of_pointwise_zero
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (target proxy₁ proxy₂ : Operator X bot) (U : Set X) (eps : I → ENNReal)
    (htarget_dom : U ⊆ dom target)
    (hproxy₁_dom : U ⊆ dom proxy₁)
    (hproxy₂_dom : U ⊆ dom proxy₂)
    (hzero : ∀ x ∈ U, ∀ i : I, d i (proxy₁.func x) (proxy₂.func x) = 0) :
    InFullFittingBall d target proxy₁ U eps ↔
      InFullFittingBall d target proxy₂ U eps := by
  constructor
  · intro hfit
    refine ⟨hfit.tolerance_finite, htarget_dom, hproxy₂_dom, ?_⟩
    intro x hx i _
    have htri := (hd i).triangle
      (target.func x) (proxy₁.func x) (proxy₂.func x)
    calc
      d i (target.func x) (proxy₂.func x)
          ≤ d i (target.func x) (proxy₁.func x) +
            d i (proxy₁.func x) (proxy₂.func x) := htri
      _ = d i (target.func x) (proxy₁.func x) := by
        rw [hzero x hx i, add_zero]
      _ ≤ eps i := hfit.error x hx i (Set.mem_univ i)
  · intro hfit
    refine ⟨hfit.tolerance_finite, htarget_dom, hproxy₁_dom, ?_⟩
    intro x hx i _
    have htri :=
      (hd i).triangle (target.func x) (proxy₂.func x) (proxy₁.func x)
    have hz : d i (proxy₂.func x) (proxy₁.func x) = 0 := by
      rw [(hd i).symm (proxy₂.func x) (proxy₁.func x)]
      exact hzero x hx i
    calc
      d i (target.func x) (proxy₁.func x)
          ≤ d i (target.func x) (proxy₂.func x) +
            d i (proxy₂.func x) (proxy₁.func x) := htri
      _ = d i (target.func x) (proxy₂.func x) := by
        rw [hz, add_zero]
      _ ≤ eps i := hfit.error x hx i (Set.mem_univ i)

/--
OET path: vol-02-deterministic-fitting/08-network-fitting.md
**定义（读出受控代理）**
A profile-controlled proxy combines a full-gauge exterior error bound with
one ordered readout comparison on the same two network representations.
-/
structure ProfileControlledProxy
    (d : I → X → X → ENNReal)
    (extensional : Net → Operator X bot)
    (U : Set X) (eps : I → ENNReal)
    (Γ : OrderedNetworkProfile Net ProfileValue) (target_net proxy_net : Net) :
    Prop where
  eps_ne_top : ∀ i : I, eps i ≠ ⊤
  target_dom : U ⊆ dom (extensional target_net)
  proxy_dom : U ⊆ dom (extensional proxy_net)
  error : ∀ x ∈ U, ∀ i : I,
    d i ((extensional proxy_net).func x) ((extensional target_net).func x) ≤ eps i
  profile_le : profile_le Γ proxy_net target_net

/--
OET path: vol-02-deterministic-fitting/08-network-fitting.md
**定义（读出受控代理）**
Strict profile control uses the canonical strict part of the selected readout
preorder.
-/
def StrictProfileControlledProxy
    (d : I → X → X → ENNReal)
    (extensional : Net → Operator X bot)
    (U : Set X) (eps : I → ENNReal)
    (Γ : OrderedNetworkProfile Net ProfileValue) (target_net proxy_net : Net) :
    Prop :=
  ProfileControlledProxy d extensional U eps Γ target_net proxy_net ∧
    profile_lt Γ proxy_net target_net

/--
OET support: definition consequence of a readout-controlled proxy
A profile-controlled proxy belongs to the full-component fitting ball of the
target exterior operator.
-/
theorem profile_controlled_proxy_in_full_fitting_ball
    (d : I → X → X → ENNReal)
    (hd_symm : ∀ i : I, ∀ x y : X, d i x y = d i y x)
    (extensional : Net → Operator X bot) (U : Set X) (eps : I → ENNReal)
    (Γ : OrderedNetworkProfile Net ProfileValue) (target_net proxy_net : Net)
    (hproxy : ProfileControlledProxy d extensional U eps Γ target_net proxy_net) :
    InFullFittingBall d (extensional target_net) (extensional proxy_net) U eps := by
  refine ⟨fun i _ => hproxy.eps_ne_top i, hproxy.target_dom, hproxy.proxy_dom, ?_⟩
  intro x hx i _
  simpa [hd_symm i ((extensional target_net).func x) ((extensional proxy_net).func x)]
    using hproxy.error x hx i

/--
OET support: definition consequence of a readout-controlled proxy
The representation-level conclusion is exactly the selected readout
comparison.
-/
theorem profile_controlled_proxy_profile_le
    (d : I → X → X → ENNReal)
    (extensional : Net → Operator X bot) (U : Set X) (eps : I → ENNReal)
    (Γ : OrderedNetworkProfile Net ProfileValue) (target_net proxy_net : Net)
    (hproxy : ProfileControlledProxy d extensional U eps Γ target_net proxy_net) :
    profile_le Γ proxy_net target_net :=
  hproxy.profile_le

end formal_oet.vol_02.ch_08_network_fitting
