import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.lip_matrix
import formal_oet.vol_01.ch_03_operator_local_degeneracy.annihilation_matrix
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Tactic

namespace formal_oet.vol_02.ch_07_fitting_foundations

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open formal_oet.vol_01.ch_03_operator_local_degeneracy

open scoped BigOperators

variable {X I : Type} {bot : X}
variable (d : I → X → X → ENNReal)

/--
OET anchor: h-70b110ccae52fc0b
**§ #h-70b110ccae52fc0b（分量误差向量）**
`component_error_vector d target proxy U j` is the `j`-component
supremum of the pointwise output error on `U`.
-/
noncomputable def component_error_vector
    (target proxy : Operator X bot) (U : Set X) (j : I) : ENNReal :=
  ⨆ x : {x // x ∈ U}, d j (target.func x.1) (proxy.func x.1)

/--
OET anchor: h-70b110ccae52fc0b
**定义（代理闭球）**
Pointwise form of membership in the proxy closed ball on a component set `J`.
-/
structure InFittingBall
    (target proxy : Operator X bot) (U : Set X) (J : Set I) (eps : I → ENNReal) :
    Prop where
  tolerance_finite : ∀ j : I, j ∈ J → eps j ≠ ⊤
  target_dom : U ⊆ dom target
  proxy_dom : U ⊆ dom proxy
  error : ∀ x ∈ U, ∀ j : I, j ∈ J → d j (target.func x) (proxy.func x) ≤ eps j

/--
OET anchor: h-70b110ccae52fc0b
**§ #h-70b110ccae52fc0b（全分量代理闭球）**
The all-component specialization of `InFittingBall`.
-/
abbrev InFullFittingBall
    (target proxy : Operator X bot) (U : Set X) (eps : I → ENNReal) : Prop :=
  InFittingBall d target proxy U Set.univ eps

/--
OET anchor: h-70b110ccae52fc0b
**定义（残差下界证书）**
A residual lower-bound certificate includes the same common-domain conditions
as the corresponding pointwise comparison.
-/
structure ResidualLowerCertificate
    (target proxy : Operator X bot) (U : Set X) (J : Set I)
    (eps_res : I → ENNReal) : Prop where
  target_dom : U ⊆ dom target
  proxy_dom : U ⊆ dom proxy
  component_nonempty : J.Nonempty
  lower : ∀ x ∈ U, ∀ j : I, j ∈ J → eps_res j ≤ d j (target.func x) (proxy.func x)

/--
OET anchor: h-70b110ccae52fc0b
**定义（残差下界证书，零证书）**
The zero vector is a residual lower-bound certificate on every common domain.
-/
theorem zero_residual_lower_certificate
    (target proxy : Operator X bot) (U : Set X) (J : Set I)
    (htarget : U ⊆ dom target) (hproxy : U ⊆ dom proxy)
    (hJ : J.Nonempty) :
    ResidualLowerCertificate d target proxy U J (fun _ => 0) := by
  refine ⟨htarget, hproxy, hJ, ?_⟩
  intro x hx j hj
  exact zero_le _

/--
OET anchor: h-70b110ccae52fc0b
**定义（残差下界证书，空域语义）**
On the empty domain every nonnegative extended vector satisfies the pointwise
lower inequality vacuously.
-/
theorem residual_lower_certificate_empty
    (target proxy : Operator X bot) (J : Set I) (eps_res : I → ENNReal)
    (hJ : J.Nonempty) :
    ResidualLowerCertificate d target proxy ∅ J eps_res := by
  refine ⟨Set.empty_subset _, Set.empty_subset _, hJ, ?_⟩
  intro x hx
  exact False.elim hx

/--
OET anchor: h-70b110ccae52fc0b
**定义（残差下界证书，正残差的非空域语义）**
A positive certificate component yields an attained positive residual only
when the measuring domain is nonempty.
-/
theorem positive_residual_witness_of_nonempty
    (target proxy : Operator X bot) (U : Set X) (J : Set I)
    (eps_res : I → ENNReal)
    (hcert : ResidualLowerCertificate d target proxy U J eps_res)
    (hU : U.Nonempty) (j : I) (hj : j ∈ J) (hpos : 0 < eps_res j) :
    ∃ x ∈ U, 0 < d j (target.func x) (proxy.func x) := by
  rcases hU with ⟨x, hx⟩
  exact ⟨x, hx, lt_of_lt_of_le hpos (hcert.lower x hx j hj)⟩

/--
OET anchor: h-70b110ccae52fc0b
**§ #h-70b110ccae52fc0b（分量误差向量与代理闭球）**
Proxy-ball membership bounds each component error vector entry.
-/
theorem component_error_vector_le_of_fitting
    (target proxy : Operator X bot) (U : Set X) (J : Set I) (eps : I → ENNReal)
    (hfit : InFittingBall d target proxy U J eps) :
    ∀ j : I, j ∈ J →
      component_error_vector d target proxy U j ≤ eps j := by
  intro j hj
  unfold component_error_vector
  apply iSup_le
  intro x
  exact hfit.error x.1 x.2 j hj

/--
OET anchor: h-70b110ccae52fc0b
**§ #h-70b110ccae52fc0b（分量误差向量与代理闭球）**
Conversely, componentwise supremum bounds give the pointwise proxy-ball
condition, once the common-domain requirements are supplied.
-/
theorem fitting_of_component_error_vector_le
    (target proxy : Operator X bot) (U : Set X) (J : Set I) (eps : I → ENNReal)
    (heps_finite : ∀ j : I, j ∈ J → eps j ≠ ⊤)
    (htarget : U ⊆ dom target) (hproxy : U ⊆ dom proxy)
    (hD : ∀ j : I, j ∈ J →
      component_error_vector d target proxy U j ≤ eps j) :
    InFittingBall d target proxy U J eps := by
  refine ⟨heps_finite, htarget, hproxy, ?_⟩
  intro x hx j hj
  have hx_le :
      d j (target.func x) (proxy.func x) ≤
        component_error_vector d target proxy U j := by
    unfold component_error_vector
    exact le_iSup (fun y : {x // x ∈ U} => d j (target.func y.1) (proxy.func y.1)) ⟨x, hx⟩
  exact le_trans hx_le (hD j hj)

/--
OET anchor: h-70b110ccae52fc0b
**§ #h-70b110ccae52fc0b（域单调性）**
Restricting the measuring domain preserves proxy-ball membership.
-/
theorem fitting_ball_mono_domain
    (target proxy : Operator X bot) (U₁ U₂ : Set X) (J : Set I) (eps : I → ENNReal)
    (hsub : U₁ ⊆ U₂)
    (hfit : InFittingBall d target proxy U₂ J eps) :
    InFittingBall d target proxy U₁ J eps := by
  refine ⟨hfit.tolerance_finite, fun x hx => hfit.target_dom (hsub hx),
    fun x hx => hfit.proxy_dom (hsub hx), ?_⟩
  intro x hx j hj
  exact hfit.error x (hsub hx) j hj

/--
OET anchor: h-a48c70147269828e
**命题 #h-a48c70147269828e（代理闭球传递律，二步形式）**
Two consecutive full-component proxy-ball certificates compose with additive
tolerance.
-/
theorem fitting_ball_transitive_two
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (phi₀ phi₁ phi₂ : Operator X bot) (U : Set X)
    (eps₁ eps₂ : I → ENNReal)
    (hfit₁ : InFullFittingBall d phi₀ phi₁ U eps₁)
    (hfit₂ : InFullFittingBall d phi₁ phi₂ U eps₂) :
    InFullFittingBall d phi₀ phi₂ U (fun j => eps₁ j + eps₂ j) := by
  refine ⟨?_, hfit₁.target_dom, hfit₂.proxy_dom, ?_⟩
  · intro j _
    exact ENNReal.add_ne_top.mpr
      ⟨hfit₁.tolerance_finite j (Set.mem_univ j),
        hfit₂.tolerance_finite j (Set.mem_univ j)⟩
  intro x hx j _
  have htri := (hd j).triangle (phi₀.func x) (phi₁.func x) (phi₂.func x)
  exact le_trans htri
    (add_le_add
      (hfit₁.error x hx j (Set.mem_univ j))
      (hfit₂.error x hx j (Set.mem_univ j)))

/--
OET anchor: h-a48c70147269828e
**命题 #h-a48c70147269828e（代理闭球传递律）**
This declaration formalizes the target-center-shift special case.
A full-component error-vector bound from a perturbed target to the original
target, followed by a fitting certificate from the original target to the
proxy, gives the sum-tolerance certificate from the perturbed target.
-/
theorem fitting_ball_target_center_shift
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (perturbed_target target proxy : Operator X bot) (U : Set X)
    (delta eps : I → ENNReal)
    (hdelta_finite : ∀ j : I, delta j ≠ ⊤)
    (hperturbed_dom : U ⊆ dom perturbed_target)
    (hfit : InFullFittingBall d target proxy U eps)
    (hdelta :
      ∀ j : I,
        component_error_vector d perturbed_target target U j ≤ delta j) :
    InFullFittingBall d perturbed_target proxy U (fun j => delta j + eps j) := by
  have hshift :
      InFullFittingBall d perturbed_target target U delta :=
    fitting_of_component_error_vector_le d perturbed_target target U Set.univ delta
      (fun j _ => hdelta_finite j) hperturbed_dom hfit.target_dom
      (fun j _ => hdelta j)
  exact fitting_ball_transitive_two d hd perturbed_target target proxy U delta eps
    hshift hfit

/--
OET anchor: h-a48c70147269828e
**命题 #h-a48c70147269828e（代理闭球传递律）**
Along a finite proxy chain indexed by `0, ..., m`, pointwise fitting errors
accumulate by the finite sum of the step tolerances.
-/
theorem fitting_ball_transitive_chain
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (phi : Nat → Operator X bot) (U : Set X) (eps : Nat → I → ENNReal)
    (m : Nat)
    (hdom : ∀ r : Nat, r ≤ m → U ⊆ dom (phi r))
    (heps_finite : ∀ r : Nat, r < m → ∀ j : I, eps r j ≠ ⊤)
    (hfit :
      ∀ r : Nat, r < m →
        ∀ x ∈ U, ∀ j : I,
          d j ((phi r).func x) ((phi (r + 1)).func x) ≤ eps r j) :
    InFullFittingBall d (phi 0) (phi m) U
      (fun j => (Finset.range m).sum (fun r => eps r j)) := by
  induction m with
  | zero =>
      refine ⟨?_, hdom 0 le_rfl, hdom 0 le_rfl, ?_⟩
      · intro j _
        simp
      intro x _ j _
      simpa using (hd j).dist_self ((phi 0).func x)
  | succ m ih =>
      have ihfit :
          InFullFittingBall d (phi 0) (phi m) U
            (fun j => (Finset.range m).sum (fun r => eps r j)) := by
        apply ih
        · intro r hr
          exact hdom r (Nat.le_trans hr (Nat.le_succ m))
        · intro r hr j
          exact heps_finite r (Nat.lt_trans hr (Nat.lt_succ_self m)) j
        · intro r hr
          exact hfit r (Nat.lt_trans hr (Nat.lt_succ_self m))
      refine ⟨?_, hdom 0 (Nat.zero_le _), hdom (m + 1) le_rfl, ?_⟩
      · intro j _
        exact ENNReal.sum_ne_top.mpr fun r hr =>
          heps_finite r (Finset.mem_range.mp hr) j
      intro x hx j _
      have htri :=
        (hd j).triangle ((phi 0).func x) ((phi m).func x) ((phi (m + 1)).func x)
      have hstep := hfit m (Nat.lt_succ_self m) x hx j
      calc
        d j ((phi 0).func x) ((phi (m + 1)).func x)
            ≤ d j ((phi 0).func x) ((phi m).func x) +
              d j ((phi m).func x) ((phi (m + 1)).func x) := htri
        _ ≤ (Finset.range m).sum (fun r => eps r j) + eps m j :=
            add_le_add (ihfit.error x hx j (Set.mem_univ j)) hstep
        _ = (Finset.range (m + 1)).sum (fun r => eps r j) := by
            rw [Finset.sum_range_succ]

/--
OET anchor: h-a48c70147269828e
**命题 #h-a48c70147269828e（代理闭球传递律，任意子链）**
Text-faithful interval form.  Here `eps r` records the text's tolerance
`ε⁽ʳ⁺¹⁾` for the step from `phi r` to `phi (r + 1)`.
-/
theorem fitting_ball_transitive_subchain_text
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (phi : Nat → Operator X bot) (U : Set X) (eps : Nat → I → ENNReal)
    (m : Nat) (hm_pos : 1 ≤ m) (hU_nonempty : U.Nonempty)
    (hdom : ∀ r : Nat, r ≤ m → U ⊆ dom (phi r))
    (heps_finite : ∀ r : Nat, r < m → ∀ j : I, eps r j ≠ ⊤)
    (hfit :
      ∀ r : Nat, r < m →
        ∀ x ∈ U, ∀ j : I,
          d j ((phi r).func x) ((phi (r + 1)).func x) ≤ eps r j)
    (a b : Nat) (ha : a < b) (hb : b ≤ m) :
    InFullFittingBall d (phi a) (phi b) U
      (fun j => (Finset.range (b - a)).sum (fun r => eps (a + r) j)) := by
  have _ := hm_pos
  have _ := hU_nonempty
  let shifted_phi : Nat → Operator X bot := fun r => phi (a + r)
  let shifted_eps : Nat → I → ENNReal := fun r => eps (a + r)
  have hchain := fitting_ball_transitive_chain d hd shifted_phi U shifted_eps (b - a)
    (by
      intro r hr
      apply hdom (a + r)
      omega)
    (by
      intro r hr j
      apply heps_finite (a + r)
      omega)
    (by
      intro r hr x hx j
      simpa [shifted_phi, shifted_eps, Nat.add_assoc] using
        hfit (a + r) (by omega) x hx j)
  simpa [shifted_phi, shifted_eps, Nat.add_sub_of_le (Nat.le_of_lt ha)] using hchain

/--
A fitting certificate with a componentwise smaller tolerance is also a fitting
certificate for any larger tolerance vector on the same domain and target.
-/
theorem fitting_ball_mono_tolerance
    (target proxy : Operator X bot) (U : Set X) (eps eta : I → ENNReal)
    (heta_finite : ∀ j : I, eta j ≠ ⊤)
    (hle : ∀ j : I, eps j ≤ eta j)
    (hfit : InFullFittingBall d target proxy U eps) :
    InFullFittingBall d target proxy U eta := by
  refine ⟨fun j _ => heta_finite j, hfit.target_dom, hfit.proxy_dom, ?_⟩
  intro x hx j hj
  exact le_trans (hfit.error x hx j hj) (hle j)

/--
OET anchor: h-96c357f03b81261a
**命题 #h-96c357f03b81261a（同目标代理对的域内外距离与补域自由）**
Two proxies fitting the same target on `U` differ by at most the sum of their
component tolerances on `U`.
-/
theorem proxy_pair_cross_consistency
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy_a proxy_b : Operator X bot) (U : Set X)
    (eps_a eps_b : I → ENNReal)
    (hfit_a : InFullFittingBall d target proxy_a U eps_a)
    (hfit_b : InFullFittingBall d target proxy_b U eps_b) :
    ∀ x ∈ U, ∀ j : I,
      d j (proxy_a.func x) (proxy_b.func x) ≤ eps_a j + eps_b j := by
  intro x hx j
  have htri :=
    (hd j).triangle (proxy_a.func x) (target.func x) (proxy_b.func x)
  have ha : d j (proxy_a.func x) (target.func x) ≤ eps_a j := by
    rw [(hd j).symm (proxy_a.func x) (target.func x)]
    exact hfit_a.error x hx j (Set.mem_univ j)
  have hb : d j (target.func x) (proxy_b.func x) ≤ eps_b j :=
    hfit_b.error x hx j (Set.mem_univ j)
  exact le_trans htri (add_le_add ha hb)

/--
OET anchor: h-96c357f03b81261a
**命题 #h-96c357f03b81261a（同目标代理对的域内外距离与补域自由，正文前提版本）**
Text-faithful wrapper retaining the nonempty fitting domain and finite
nonnegative tolerance assumptions from the text.  Nonnegativity is built into
`ENNReal`; finiteness is kept as an explicit text-level hypothesis.
-/
theorem proxy_pair_cross_consistency_text
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy_a proxy_b : Operator X bot) (U : Set X)
    (eps_a eps_b : I → ENNReal)
    (hU_nonempty : U.Nonempty)
    (heps_a_finite : ∀ j : I, eps_a j ≠ ⊤)
    (heps_b_finite : ∀ j : I, eps_b j ≠ ⊤)
    (hfit_a : InFullFittingBall d target proxy_a U eps_a)
    (hfit_b : InFullFittingBall d target proxy_b U eps_b) :
    ∀ x ∈ U, ∀ j : I,
      d j (proxy_a.func x) (proxy_b.func x) ≤ eps_a j + eps_b j := by
  have _ := hU_nonempty
  have _ := heps_a_finite
  have _ := heps_b_finite
  exact proxy_pair_cross_consistency d hd target proxy_a proxy_b U eps_a eps_b hfit_a hfit_b

/--
OET anchor: h-09f81de53176a55d
**命题 #h-09f81de53176a55d（零容限拟合的受限规范数据一致）**
Zero-tolerance fitting on `U` makes the target and proxy pairwise output
distances identical on `U`, without requiring pointwise equality.
-/
theorem zero_error_fitting_pairwise_distance_eq
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U : Set X)
    (hfit : InFullFittingBall d target proxy U (fun _ => 0)) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (target.func x) (target.func y) =
        d j (proxy.func x) (proxy.func y) := by
  intro x hx y hy j
  have hx_zero : d j (target.func x) (proxy.func x) = 0 :=
    le_antisymm (hfit.error x hx j (Set.mem_univ j)) (zero_le _)
  have hy_zero : d j (target.func y) (proxy.func y) = 0 :=
    le_antisymm (hfit.error y hy j (Set.mem_univ j)) (zero_le _)
  have hx_zero_symm : d j (proxy.func x) (target.func x) = 0 := by
    simpa [(hd j).symm (proxy.func x) (target.func x)] using hx_zero
  have hy_zero_symm : d j (proxy.func y) (target.func y) = 0 := by
    simpa [(hd j).symm (proxy.func y) (target.func y)] using hy_zero
  apply le_antisymm
  · have htri₁ :=
      (hd j).triangle (target.func x) (proxy.func x) (target.func y)
    have htri₂ :=
      (hd j).triangle (proxy.func x) (proxy.func y) (target.func y)
    have hmid :
        d j (proxy.func x) (target.func y) ≤
          d j (proxy.func x) (proxy.func y) := by
      have hle :
          d j (proxy.func x) (target.func y) ≤
            d j (proxy.func x) (proxy.func y) + 0 :=
        le_trans htri₂ (add_le_add le_rfl (le_of_eq hy_zero_symm))
      simpa using hle
    have hle :
        d j (target.func x) (target.func y) ≤
          0 + d j (proxy.func x) (proxy.func y) :=
      le_trans htri₁ (add_le_add (le_of_eq hx_zero) hmid)
    simpa using hle
  · have htri₁ :=
      (hd j).triangle (proxy.func x) (target.func x) (proxy.func y)
    have htri₂ :=
      (hd j).triangle (target.func x) (target.func y) (proxy.func y)
    have hmid :
        d j (target.func x) (proxy.func y) ≤
          d j (target.func x) (target.func y) := by
      have hle :
          d j (target.func x) (proxy.func y) ≤
            d j (target.func x) (target.func y) + 0 :=
        le_trans htri₂ (add_le_add le_rfl (le_of_eq hy_zero))
      simpa using hle
    have hle :
        d j (proxy.func x) (proxy.func y) ≤
          0 + d j (target.func x) (target.func y) :=
      le_trans htri₁ (add_le_add (le_of_eq hx_zero_symm) hmid)
    simpa using hle

/--
OET anchor: h-09f81de53176a55d
**命题 #h-09f81de53176a55d（零容限拟合的受限规范数据一致）**
Zero pointwise fitting error preserves all restricted Lip matrix predicates.
-/
theorem zero_error_lip_matrix_iff [Fintype I]
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U : Set X) (L : I → I → ENNReal)
    (htarget_dom : U ⊆ dom target) (hproxy_dom : U ⊆ dom proxy)
    (hfit : InFullFittingBall d target proxy U (fun _ => 0)) :
    IsLipMatrix d target U L ↔ IsLipMatrix d proxy U L := by
  constructor
  · intro hL
    refine ⟨hproxy_dom, ?_⟩
    intro x hx y hy j
    have hdist := zero_error_fitting_pairwise_distance_eq d hd target proxy U hfit x hx y hy j
    rw [← hdist]
    exact hL.2 x hx y hy j
  · intro hL
    refine ⟨htarget_dom, ?_⟩
    intro x hx y hy j
    have hdist := zero_error_fitting_pairwise_distance_eq d hd target proxy U hfit x hx y hy j
    rw [hdist]
    exact hL.2 x hx y hy j

/-- Internal helper: zero pointwise fitting error preserves restricted co-Lip
matrix predicates, including the vacuous equivalence on an empty domain. -/
theorem zero_error_colip_matrix_iff [Fintype I]
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U : Set X) (K : I → I → ENNReal)
    (htarget_dom : U ⊆ dom target) (hproxy_dom : U ⊆ dom proxy)
    (hfit : InFullFittingBall d target proxy U (fun _ => 0)) :
    IsCoLipMatrix d target U K ↔ IsCoLipMatrix d proxy U K := by
  constructor
  · intro hK
    refine ⟨hK.1, hproxy_dom, ?_⟩
    intro x hx y hy j
    have hdist := zero_error_fitting_pairwise_distance_eq d hd target proxy U hfit x hx y hy j
    rw [← hdist]
    exact hK.2.2 x hx y hy j
  · intro hK
    refine ⟨hK.1, htarget_dom, ?_⟩
    intro x hx y hy j
    have hdist := zero_error_fitting_pairwise_distance_eq d hd target proxy U hfit x hx y hy j
    rw [hdist]
    exact hK.2.2 x hx y hy j

/--
OET anchor: h-09f81de53176a55d
**命题 #h-09f81de53176a55d（零容限拟合的受限规范数据一致，非空域 co-Lip）**
Text-faithful co-Lip equality on a nonempty restricted domain.
-/
theorem zero_error_colip_matrix_iff_on_nonempty [Fintype I]
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U : Set X) (K : I → I → ENNReal)
    (hfit : InFullFittingBall d target proxy U (fun _ => 0))
    (hU_nonempty : U.Nonempty) :
    IsCoLipMatrix d target U K ↔ IsCoLipMatrix d proxy U K := by
  have _ := hU_nonempty
  exact zero_error_colip_matrix_iff d hd target proxy U K
    hfit.target_dom hfit.proxy_dom hfit

/--
OET anchor: h-09f81de53176a55d
**命题 #h-09f81de53176a55d（零容限拟合的受限规范数据一致）**
Zero pointwise fitting error gives identical computational fibers on `U`.
-/
theorem zero_error_computational_fiber_iff
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U : Set X)
    (hfit : InFullFittingBall d target proxy U (fun _ => 0))
    (J : NonemptyFinset I) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    x ∈ ComputationalFiber d target J U (target.func y) ↔
      x ∈ ComputationalFiber d proxy J U (proxy.func y) := by
  classical
  constructor
  · intro hfib
    constructor
    · exact hfib.1
    · have hzero_target :
        ∀ j ∈ J.val, d j (target.func x) (target.func y) = 0 :=
        (comp_pseudo_metric_eq_zero_iff d J (target.func x) (target.func y)).mp hfib.2
      apply (comp_pseudo_metric_eq_zero_iff d J (proxy.func x) (proxy.func y)).mpr
      intro j hj
      have hdist := zero_error_fitting_pairwise_distance_eq d hd target proxy U hfit x hx y hy j
      rw [← hdist]
      exact hzero_target j hj
  · intro hfib
    constructor
    · exact hfib.1
    · have hzero_proxy :
        ∀ j ∈ J.val, d j (proxy.func x) (proxy.func y) = 0 :=
        (comp_pseudo_metric_eq_zero_iff d J (proxy.func x) (proxy.func y)).mp hfib.2
      apply (comp_pseudo_metric_eq_zero_iff d J (target.func x) (target.func y)).mpr
      intro j hj
      have hdist := zero_error_fitting_pairwise_distance_eq d hd target proxy U hfit x hx y hy j
      rw [hdist]
      exact hzero_proxy j hj

/-- Internal helper: zero pointwise fitting error preserves pointwise
restricted annihilation radii, including the vacuous empty-domain case. -/
theorem zero_error_annihilation_radius_eq
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U : Set X)
    (hfit : InFullFittingBall d target proxy U (fun _ => 0))
    (i : I) (J : NonemptyFinset I) {y : X} (hy : y ∈ U) :
    annihilation_radius d target i J U y =
      annihilation_radius d proxy i J U y := by
  apply le_antisymm
  · dsimp [annihilation_radius]
    apply iSup_le
    intro r
    apply iSup_le
    intro hr
    apply iSup_le
    intro hsub
    apply le_iSup_of_le r
    apply le_iSup_of_le hr
    have hsub_proxy :
        OpenBall d i y r ∩ U ⊆
          ComputationalFiber d proxy J U (proxy.func y) := by
      intro x hx
      exact (zero_error_computational_fiber_iff d hd target proxy U hfit J
        hx.2 hy).mp (hsub hx)
    exact le_iSup_of_le hsub_proxy le_rfl
  · dsimp [annihilation_radius]
    apply iSup_le
    intro r
    apply iSup_le
    intro hr
    apply iSup_le
    intro hsub
    apply le_iSup_of_le r
    apply le_iSup_of_le hr
    have hsub_target :
        OpenBall d i y r ∩ U ⊆
          ComputationalFiber d target J U (target.func y) := by
      intro x hx
      exact (zero_error_computational_fiber_iff d hd target proxy U hfit J
        hx.2 hy).mpr (hsub hx)
    exact le_iSup_of_le hsub_target le_rfl

/--
OET anchor: h-09f81de53176a55d
**命题 #h-09f81de53176a55d（零容限拟合的受限规范数据一致，非空域零化半径）**
Text-faithful pointwise annihilation-radius equality on a nonempty domain.
-/
theorem zero_error_annihilation_radius_eq_on_nonempty
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U : Set X)
    (hfit : InFullFittingBall d target proxy U (fun _ => 0))
    (hU_nonempty : U.Nonempty)
    (i : I) (J : NonemptyFinset I) {y : X} (hy : y ∈ U) :
    annihilation_radius d target i J U y =
      annihilation_radius d proxy i J U y := by
  have _ := hU_nonempty
  exact zero_error_annihilation_radius_eq d hd target proxy U hfit i J hy

/-- Internal helper: zero error preserves restricted minimal annihilation
radii, including the empty-domain lattice value. -/
theorem zero_error_min_annihilation_radius_eq
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U : Set X)
    (hfit : InFullFittingBall d target proxy U (fun _ => 0))
    (i : I) (J : NonemptyFinset I) :
    min_annihilation_radius d target i J U =
      min_annihilation_radius d proxy i J U := by
  apply le_antisymm
  · dsimp [min_annihilation_radius]
    apply le_iInf
    intro y
    apply le_iInf
    intro hy
    exact le_trans (iInf₂_le y hy)
      (le_of_eq (zero_error_annihilation_radius_eq d hd target proxy U hfit i J hy))
  · dsimp [min_annihilation_radius]
    apply le_iInf
    intro y
    apply le_iInf
    intro hy
    exact le_trans (iInf₂_le y hy)
      (ge_of_eq (zero_error_annihilation_radius_eq d hd target proxy U hfit i J hy))

/--
OET anchor: h-09f81de53176a55d
**命题 #h-09f81de53176a55d（零容限拟合的受限规范数据一致，非空域极小零化半径）**
Text-faithful minimal annihilation-radius equality on a nonempty domain.
-/
theorem zero_error_min_annihilation_radius_eq_on_nonempty
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U : Set X)
    (hfit : InFullFittingBall d target proxy U (fun _ => 0))
    (hU_nonempty : U.Nonempty)
    (i : I) (J : NonemptyFinset I) :
    min_annihilation_radius d target i J U =
      min_annihilation_radius d proxy i J U := by
  have _ := hU_nonempty
  exact zero_error_min_annihilation_radius_eq d hd target proxy U hfit i J

/-- Internal helper: zero error preserves restricted annihilation matrices,
including the empty-domain lattice value. -/
theorem zero_error_annihilation_matrix_eq
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U : Set X)
    (hfit : InFullFittingBall d target proxy U (fun _ => 0)) :
    ∀ i j : I, AnnihilationMatrix d target U i j =
      AnnihilationMatrix d proxy U i j := by
  intro i j
  dsimp [AnnihilationMatrix]
  exact zero_error_min_annihilation_radius_eq d hd target proxy U hfit j
    (singleton_nonempty_finset i)

/--
OET anchor: h-09f81de53176a55d
**命题 #h-09f81de53176a55d（零容限拟合的受限规范数据一致，非空域零化矩阵）**
Text-faithful annihilation-matrix equality on a nonempty domain.
-/
theorem zero_error_annihilation_matrix_eq_on_nonempty
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U : Set X)
    (hfit : InFullFittingBall d target proxy U (fun _ => 0))
    (hU_nonempty : U.Nonempty) :
    ∀ i j : I, AnnihilationMatrix d target U i j =
      AnnihilationMatrix d proxy U i j := by
  have _ := hU_nonempty
  exact zero_error_annihilation_matrix_eq d hd target proxy U hfit

/--
OET anchor: h-09f81de53176a55d
**命题 #h-09f81de53176a55d（零容限拟合的受限规范数据一致）**
Full zero-radius fitting-ball membership yields equality of restricted L/K/N
data on the common evaluation domain.
-/
theorem zero_error_restricted_data
    [Fintype I]
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U : Set X)
    (hfit : InFullFittingBall d target proxy U (fun _ => 0))
    (hU_nonempty : U.Nonempty) :
    (∀ L : I → I → ENNReal,
      IsLipMatrix d target U L ↔ IsLipMatrix d proxy U L) ∧
    (∀ K : I → I → ENNReal,
      IsCoLipMatrix d target U K ↔ IsCoLipMatrix d proxy U K) ∧
    (∀ i j : I,
      AnnihilationMatrix d target U i j =
        AnnihilationMatrix d proxy U i j) := by
  have _ := hU_nonempty
  exact ⟨
    fun L =>
      zero_error_lip_matrix_iff d hd target proxy U L
        hfit.target_dom hfit.proxy_dom hfit,
    fun K =>
      zero_error_colip_matrix_iff_on_nonempty d hd target proxy U K
        hfit hU_nonempty,
    zero_error_annihilation_matrix_eq_on_nonempty d hd target proxy U
      hfit hU_nonempty⟩

end formal_oet.vol_02.ch_07_fitting_foundations
