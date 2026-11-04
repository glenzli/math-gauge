import formal_oet.vol_02.ch_07_fitting_foundations.single_step_bounds
import formal_oet.vol_02.ch_09_family_fitting.joint_fitting
import formal_oet.vol_01.ch_04_operator_chain_calculus.spectral_regimes
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace formal_oet.vol_02.ch_10_composition_fitting

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open formal_oet.vol_01.ch_04_operator_chain_calculus
open formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_02.ch_07_fitting_foundations
open formal_oet.vol_02.ch_09_family_fitting

open scoped BigOperators

variable {X I β : Type} {bot : X} [Fintype I] [Nonempty I]
variable (d : I → X → X → ENNReal)

/--
Internal single-target common pre/post data used to formalize the target-family
common external context. The corresponding single-target fitting certificate is
handled in §7, not as a separate §10 item.
-/
structure CommonPrePostData
    (psi phi eta chi : Operator X bot) (A U V : Set X) : Prop where
  eta_dom : A ⊆ dom eta
  eta_mem : ∀ x ∈ A, eta.func x ∈ U
  psi_dom : U ⊆ dom psi
  phi_dom : U ⊆ dom phi
  psi_image_mem : ∀ x ∈ A, psi.func (eta.func x) ∈ V
  phi_image_mem : ∀ x ∈ A, phi.func (eta.func x) ∈ V
  chi_dom : V ⊆ dom chi

/--
Internal helper: a single-target fitting bound propagates through a common
pre-composition and a common post-composition with a valid Lip matrix.
-/
theorem common_external_composition_upper_certificate
    (psi phi eta chi : Operator X bot) (A U V : Set X)
    (eps : I → ENNReal) (Lχ : I → I → ENNReal)
    (ctx : CommonPrePostData psi phi eta chi A U V)
    (hfit : InFullFittingBall d psi phi U eps)
    (hLχ : IsLipMatrix d chi V Lχ) :
    ∀ x ∈ A, ∀ j : I,
      d j (chi.func (psi.func (eta.func x)))
          (chi.func (phi.func (eta.func x))) ≤
        matrix_vector_bound Lχ eps j := by
  intro x hx j
  exact common_pre_post_composition_local_upper_bound d eta chi psi phi A U V
    eps Lχ ctx.eta_dom ctx.eta_mem
    (fun u hu i => hfit.error u hu i (Set.mem_univ i))
    (fun y hy => ⟨ctx.psi_image_mem y hy, ctx.phi_image_mem y hy⟩)
    hLχ x hx j

/--
Internal helper: a post-composition co-Lip lower bound exceeding twice the
requested tolerance prevents one proxy from fitting two post-composed targets
at the same point.
-/
private theorem common_external_composition_separation_incompatible
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (psi₁ psi₂ phi eta chi : Operator X bot) (A U V : Set X)
    (Kχ : I → I → ENNReal)
    (ctx₁ : CommonPrePostData psi₁ phi eta chi A U V)
    (ctx₂ : CommonPrePostData psi₂ phi eta chi A U V)
    (hKχ : IsCoLipMatrix d chi V Kχ)
    {x : X} (hx : x ∈ A) (j : I) (tau : ENNReal)
    (hstrict :
      tau + tau <
        matrix_vector_bound Kχ
          (fun i => d i (psi₁.func (eta.func x)) (psi₂.func (eta.func x))) j) :
    ¬ (d j (chi.func (psi₁.func (eta.func x)))
          (chi.func (phi.func (eta.func x))) ≤ tau ∧
        d j (chi.func (psi₂.func (eta.func x)))
          (chi.func (phi.func (eta.func x))) ≤ tau) := by
  intro hboth
  have hright :
      d j (chi.func (phi.func (eta.func x)))
          (chi.func (psi₂.func (eta.func x))) ≤ tau := by
    simpa [(hd j).symm
      (chi.func (phi.func (eta.func x)))
      (chi.func (psi₂.func (eta.func x)))] using hboth.2
  have htri :
      d j (chi.func (psi₁.func (eta.func x)))
          (chi.func (psi₂.func (eta.func x))) ≤ tau + tau := by
    exact le_trans
      ((hd j).triangle
        (chi.func (psi₁.func (eta.func x)))
        (chi.func (phi.func (eta.func x)))
        (chi.func (psi₂.func (eta.func x))))
      (add_le_add hboth.1 hright)
  have hlower :
      matrix_vector_bound Kχ
          (fun i => d i (psi₁.func (eta.func x)) (psi₂.func (eta.func x))) j ≤
        d j (chi.func (psi₁.func (eta.func x)))
          (chi.func (psi₂.func (eta.func x))) := by
    simpa [matrix_vector_bound] using
      hKχ.2.2
        (psi₁.func (eta.func x)) (ctx₁.psi_image_mem x hx)
        (psi₂.func (eta.func x)) (ctx₂.psi_image_mem x hx) j
  exact (not_lt_of_ge (le_trans hlower htri)) hstrict

/--
OET anchor: h-f0b77b4693ca1b12
**定义（目标族的共同外部复合语境）**
Common pre/post data for every target in a target family.
-/
structure FamilyCommonExternalContext
    (target : β → Operator X bot) (phi eta chi : Operator X bot)
    (A U V : Set X) : Prop where
  data : ∀ b : β, CommonPrePostData (target b) phi eta chi A U V

/--
OET anchor: h-006158670576669f
**推论 #h-006158670576669f（目标族共同外部复合的上界证书）**
Joint fitting of a target family propagates through a common external
composition by the post-composition Lip matrix.
-/
theorem family_common_external_upper_certificate
    [Fintype β] [Nonempty β]
    (target : β → Operator X bot) (phi eta chi : Operator X bot)
    (A U V : Set X) (eps : I → ENNReal) (Lχ : I → I → ENNReal)
    (ctx : FamilyCommonExternalContext target phi eta chi A U V)
    (hfit : JointFitting d target phi U eps)
    (hLχ : IsLipMatrix d chi V Lχ) :
    ∀ b : β, ∀ x ∈ A, ∀ j : I,
      d j (chi.func ((target b).func (eta.func x)))
          (chi.func (phi.func (eta.func x))) ≤
        matrix_vector_bound Lχ eps j := by
  intro b x hx j
  have hsingle : InFullFittingBall d (target b) phi U eps := by
    refine ⟨fun i _ => hfit.tolerance_finite i, ?_, ?_, ?_⟩
    · intro y hy
      exact (ctx.data b).psi_dom hy
    · intro y hy
      exact (ctx.data b).phi_dom hy
    · intro y hy i _
      exact hfit.error y ⟨hy, b, (ctx.data b).psi_dom hy⟩ b
        ⟨hy, (ctx.data b).psi_dom hy⟩ i
  exact common_external_composition_upper_certificate d
    (target b) phi eta chi A U V eps Lχ (ctx.data b) hsingle hLχ x hx j

/--
OET anchor: h-fbfa3512b4c1ffb9
**推论 #h-fbfa3512b4c1ffb9（目标族共同外部复合的分离不相容）**
The two-target incompatibility certificate applies to any two selected
targets in the family context.
-/
theorem family_common_external_separation_incompatible
    [Fintype β] [Nonempty β]
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target : β → Operator X bot) (phi eta chi : Operator X bot)
    (A U V : Set X) (Kχ : I → I → ENNReal)
    (ctx : FamilyCommonExternalContext target phi eta chi A U V)
    (hKχ : IsCoLipMatrix d chi V Kχ)
    {a b : β} (hne : a ≠ b) {x : X} (hx : x ∈ A)
    (j : I) (tau : ENNReal)
    (hstrict :
      tau + tau <
        matrix_vector_bound Kχ
          (fun i => d i ((target a).func (eta.func x))
            ((target b).func (eta.func x))) j) :
    ¬ (d j (chi.func ((target a).func (eta.func x)))
          (chi.func (phi.func (eta.func x))) ≤ tau ∧
        d j (chi.func ((target b).func (eta.func x)))
          (chi.func (phi.func (eta.func x))) ≤ tau) := by
  have _ := hne
  exact common_external_composition_separation_incompatible d hd
    (target a) (target b) phi eta chi A U V Kχ
    (ctx.data a) (ctx.data b) hKχ hx j tau hstrict

/--
OET anchor: h-006158670576669f
**推论 #h-006158670576669f（目标族共同外部复合的代理闭球形式）**
The pointwise upper certificate assembles into the exact jointly fitted
post-composed target family when its propagated tolerance is finite.
-/
theorem family_common_external_joint_fitting
    [Fintype β] [Nonempty β]
    (target : β → Operator X bot) (phi eta chi : Operator X bot)
    (A U V : Set X) (eps : I → ENNReal) (Lchi : I → I → ENNReal)
    (ctx : FamilyCommonExternalContext target phi eta chi A U V)
    (hfit : JointFitting d target phi U eps)
    (hLchi : IsLipMatrix d chi V Lchi)
    (hfinite : ∀ j : I, matrix_vector_bound Lchi eps j ≠ ⊤) :
    JointFitting d
      (fun b => OperatorChain [chi, target b, eta])
      (OperatorChain [chi, phi, eta]) A
      (matrix_vector_bound Lchi eps) := by
  refine ⟨hfinite, ?_, ?_⟩
  · intro x hx
    rcases hx.2 with ⟨b, _⟩
    have hnonbot := (ctx.data b).chi_dom ((ctx.data b).phi_image_mem x hx.1)
    simpa [dom, OperatorChain, Function.comp_apply] using hnonbot
  · intro x hx b hb j
    have hbound := family_common_external_upper_certificate d
      target phi eta chi A U V eps Lchi ctx hfit hLchi b x hx.1 j
    simpa [OperatorChain, Function.comp_apply] using hbound

/--
OET anchor: h-fbfa3512b4c1ffb9
**推论 #h-fbfa3512b4c1ffb9（共同外部复合后的联合拟合不相容）**
The strict post-composed pair separation excludes the corresponding joint
fitting certificate on `A`.
-/
theorem family_common_external_not_joint_fitting
    [Fintype β] [Nonempty β]
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target : β → Operator X bot) (phi eta chi : Operator X bot)
    (A U V : Set X) (Kchi : I → I → ENNReal)
    (ctx : FamilyCommonExternalContext target phi eta chi A U V)
    (hKchi : IsCoLipMatrix d chi V Kchi)
    {a b : β} (hne : a ≠ b) {x : X} (hx : x ∈ A)
    (j : I) (tau : I → ENNReal)
    (hstrict : tau j + tau j <
      matrix_vector_bound Kchi
        (fun i => d i ((target a).func (eta.func x))
          ((target b).func (eta.func x))) j) :
    ¬ JointFitting d
      (fun c => OperatorChain [chi, target c, eta])
      (OperatorChain [chi, phi, eta]) A tau := by
  intro hall
  have hpair := family_common_external_separation_incompatible d hd
    target phi eta chi A U V Kchi ctx hKchi hne hx j (tau j) hstrict
  apply hpair
  constructor
  · have hdom_a : x ∈ dom (OperatorChain [chi, target a, eta]) := by
      have hnonbot := (ctx.data a).chi_dom ((ctx.data a).psi_image_mem x hx)
      simpa [dom, OperatorChain, Function.comp_apply] using hnonbot
    have heff : x ∈ effective_family_domain
        (fun c => OperatorChain [chi, target c, eta]) A := ⟨hx, a, hdom_a⟩
    have hactive : a ∈ active_indices
        (fun c => OperatorChain [chi, target c, eta]) A x := by
      exact ⟨hx, hdom_a⟩
    simpa [OperatorChain, Function.comp_apply] using hall.error x heff a hactive j
  · have hdom_b : x ∈ dom (OperatorChain [chi, target b, eta]) := by
      have hnonbot := (ctx.data b).chi_dom ((ctx.data b).psi_image_mem x hx)
      simpa [dom, OperatorChain, Function.comp_apply] using hnonbot
    have heff : x ∈ effective_family_domain
        (fun c => OperatorChain [chi, target c, eta]) A := ⟨hx, b, hdom_b⟩
    have hactive : b ∈ active_indices
        (fun c => OperatorChain [chi, target c, eta]) A x := by
      exact ⟨hx, hdom_b⟩
    simpa [OperatorChain, Function.comp_apply] using hall.error x heff b hactive j

/--
OET anchor: h-f09503fad2aac2e8
**推论 #h-f09503fad2aac2e8（后接零化半径对成对分歧的截断）**
A pair below the uniform annihilation radius is identified in the requested
output component after post-composition.
-/
theorem postcomposition_annihilation_radius_pair_zero
    [DecidableEq I]
    (chi : Operator X bot) (V : Set X) (y₁ y₂ : X) (i j : I)
    (hy₁ : y₁ ∈ V) (hy₂ : y₂ ∈ V)
    (hbelow : d i y₁ y₂ <
      min_annihilation_radius d chi i (singleton_nonempty_finset j) V) :
    d j (chi.func y₁) (chi.func y₂) = 0 := by
  exact zeroing_step_of_min_annihilation_radius d chi V i j
    (min_annihilation_radius d chi i (singleton_nonempty_finset j) V)
    le_rfl hy₁ hy₂ hbelow

/--
OET source: vol-02-deterministic-fitting/10-composition-fitting.md
**定义（共同前后接链数据）**
The terminal chain values after the common pre-composition lie in the common
post-composition domain.
-/
structure CommonPrePostChainData
    (target_chain proxy_chain eta chi : Operator X bot) (A V : Set X) :
    Prop where
  eta_dom : A ⊆ dom eta
  target_chain_dom : ∀ x ∈ A, eta.func x ∈ dom target_chain
  proxy_chain_dom : ∀ x ∈ A, eta.func x ∈ dom proxy_chain
  target_terminal_mem : ∀ x ∈ A, target_chain.func (eta.func x) ∈ V
  proxy_terminal_mem : ∀ x ∈ A, proxy_chain.func (eta.func x) ∈ V
  chi_dom : V ⊆ dom chi

/--
OET anchor: h-f17dd88fcbe2e116
**命题 #h-f17dd88fcbe2e116（共同前后接链的上界证书）**
The composed operators represent the nonempty target and proxy chains fixed in
the text.  The propagated conclusion is explicit for every `x ∈ A` and every
output component `j`.
-/
theorem common_pre_post_chain_upper_certificate
    (target_chain proxy_chain eta chi : Operator X bot) (A V : Set X)
    (Theta : I → ENNReal) (Lχ : I → I → ENNReal)
    (ctx : CommonPrePostChainData target_chain proxy_chain eta chi A V)
    (hTheta :
      ∀ x ∈ A, ∀ i : I,
        d i (target_chain.func (eta.func x))
          (proxy_chain.func (eta.func x)) ≤ Theta i)
    (hLχ : IsLipMatrix d chi V Lχ) :
    ∀ x ∈ A, ∀ j : I,
      d j (chi.func (target_chain.func (eta.func x)))
          (chi.func (proxy_chain.func (eta.func x))) ≤
        matrix_vector_bound Lχ Theta j := by
  intro x hx j
  have hraw :
      d j (chi.func (target_chain.func (eta.func x)))
          (chi.func (proxy_chain.func (eta.func x))) ≤
        ∑ i : I, Lχ i j *
          d i (target_chain.func (eta.func x))
            (proxy_chain.func (eta.func x)) := by
    exact hLχ.2 (target_chain.func (eta.func x))
      (ctx.target_terminal_mem x hx)
      (proxy_chain.func (eta.func x)) (ctx.proxy_terminal_mem x hx) j
  have hsum :
      (∑ i : I, Lχ i j *
          d i (target_chain.func (eta.func x))
            (proxy_chain.func (eta.func x))) ≤
        matrix_vector_bound Lχ Theta j := by
    unfold matrix_vector_bound
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_right (hTheta x hx i) (Lχ i j)
  exact le_trans hraw hsum

/--
OET anchor: h-f17dd88fcbe2e116
**命题 #h-f17dd88fcbe2e116（共同前后接链的代理闭球形式）**
The propagated finite terminal vector gives the exact full-component fitting
certificate for the two commonly pre/post-composed chains.
-/
theorem common_pre_post_chain_fitting_certificate
    (target_chain proxy_chain eta chi : Operator X bot) (A V : Set X)
    (Theta : I → ENNReal) (Lchi : I → I → ENNReal)
    (ctx : CommonPrePostChainData target_chain proxy_chain eta chi A V)
    (hTheta : ∀ x ∈ A, ∀ i : I,
      d i (target_chain.func (eta.func x))
        (proxy_chain.func (eta.func x)) ≤ Theta i)
    (hLchi : IsLipMatrix d chi V Lchi)
    (hfinite : ∀ j : I, matrix_vector_bound Lchi Theta j ≠ ⊤) :
    InFullFittingBall d
      (OperatorChain [chi, target_chain, eta])
      (OperatorChain [chi, proxy_chain, eta]) A
      (matrix_vector_bound Lchi Theta) := by
  refine ⟨fun j _ => hfinite j, ?_, ?_, ?_⟩
  · intro x hx
    have hnonbot := ctx.chi_dom (ctx.target_terminal_mem x hx)
    simpa [dom, OperatorChain, Function.comp_apply] using hnonbot
  · intro x hx
    have hnonbot := ctx.chi_dom (ctx.proxy_terminal_mem x hx)
    simpa [dom, OperatorChain, Function.comp_apply] using hnonbot
  · intro x hx j _
    have _ := hfinite j
    simpa [OperatorChain, Function.comp_apply] using
      common_pre_post_chain_upper_certificate d target_chain proxy_chain eta chi
        A V Theta Lchi ctx hTheta hLchi x hx j

/--
OET anchor: h-75e01a5ca682be45
**定义（局部误差预算集）**
The local error budgets whose propagated componentwise sum is bounded by the
terminal tolerance vector.
-/
def LocalErrorBudget
    {k : Nat} (tau : I → ENNReal)
    (A : Fin k → I → I → ENNReal)
    (eps : Fin k → I → ENNReal) : Prop :=
  ∀ j : I, (∑ m : Fin k, matrix_vector_bound (A m) (eps m) j) ≤ tau j

/--
OET anchor: h-28ceee0bc7dbdab0
**命题 #h-28ceee0bc7dbdab0（局部误差预算集的基本性质，向下封闭）**
Lowering every local error vector preserves membership in the budget set.
-/
theorem local_error_budget_antitone_error
    {k : Nat} (tau : I → ENNReal)
    (A : Fin k → I → I → ENNReal)
    (hk : 1 ≤ k)
    {eps eps' : Fin k → I → ENNReal}
    (hbudget : LocalErrorBudget tau A eps)
    (heps : ∀ m : Fin k, ∀ i : I, eps' m i ≤ eps m i) :
    LocalErrorBudget tau A eps' := by
  have _ := hk
  intro j
  exact le_trans
    (Finset.sum_le_sum (fun m _ =>
      by
        unfold matrix_vector_bound
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_right (heps m i) (A m i j)))
    (hbudget j)

/--
OET anchor: h-28ceee0bc7dbdab0
**命题 #h-28ceee0bc7dbdab0（局部误差预算集的基本性质，传播矩阵单调性）**
If every propagation matrix is decreased componentwise, every budget valid for
the larger matrices remains valid for the smaller matrices.
-/
theorem local_error_budget_antitone_matrix
    {k : Nat} (tau : I → ENNReal)
    {A B : Fin k → I → I → ENNReal}
    (eps : Fin k → I → ENNReal)
    (hk : 1 ≤ k)
    (hbudget : LocalErrorBudget tau B eps)
    (hAB : ∀ m : Fin k, ∀ i j : I, A m i j ≤ B m i j) :
    LocalErrorBudget tau A eps := by
  have _ := hk
  intro j
  have hterm :
      ∀ m : Fin k,
        matrix_vector_bound (A m) (eps m) j ≤
          matrix_vector_bound (B m) (eps m) j := by
    intro m
    unfold matrix_vector_bound
    apply Finset.sum_le_sum
    intro i _
    simpa [mul_comm] using mul_le_mul_right (hAB m i j) (eps m i)
  exact le_trans (Finset.sum_le_sum (fun m _ => hterm m)) (hbudget j)

/--
OET anchor: h-28ceee0bc7dbdab0
**命题 #h-28ceee0bc7dbdab0（无穷传播系数强制对应局部误差归零）**
If one local channel has coefficient `⊤` into a finite terminal budget, its
source local tolerance must vanish.
-/
theorem local_error_budget_top_coefficient_forces_zero
    {k : Nat} (tau : I → ENNReal)
    (A : Fin k → I → I → ENNReal)
    (eps : Fin k → I → ENNReal)
    (hk : 1 ≤ k)
    (hbudget : LocalErrorBudget tau A eps)
    (m : Fin k) (i j : I)
    (htau : tau j ≠ ⊤)
    (hA : A m i j = ⊤) :
    eps m i = 0 := by
  have _ := hk
  by_contra heps
  have hentry_top : A m i j * eps m i = ⊤ := by
    simp [hA, heps]
  have hentry_le_matrix :
      A m i j * eps m i ≤ matrix_vector_bound (A m) (eps m) j := by
    unfold matrix_vector_bound
    exact Finset.single_le_sum
      (s := Finset.univ) (a := i)
      (f := fun q : I => A m q j * eps m q)
      (fun _ _ => zero_le _) (Finset.mem_univ i)
  have hmatrix_le_total :
      matrix_vector_bound (A m) (eps m) j ≤
        ∑ q : Fin k, matrix_vector_bound (A q) (eps q) j := by
    exact Finset.single_le_sum
      (s := Finset.univ) (a := m)
      (f := fun q : Fin k => matrix_vector_bound (A q) (eps q) j)
      (fun _ _ => zero_le _) (Finset.mem_univ m)
  have htop_le : ⊤ ≤ tau j := by
    rw [← hentry_top]
    exact le_trans hentry_le_matrix (le_trans hmatrix_le_total (hbudget j))
  exact htau (top_unique htop_le)

end formal_oet.vol_02.ch_10_composition_fitting
