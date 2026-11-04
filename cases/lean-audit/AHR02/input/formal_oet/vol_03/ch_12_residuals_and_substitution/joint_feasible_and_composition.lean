import formal_oet.vol_03.ch_12_residuals_and_substitution.substitution_inheritance
import formal_oet.vol_02.ch_10_composition_fitting.external_composition
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
open formal_oet.vol_02.ch_10_composition_fitting

variable {X I β : Type} {bot : X} [Fintype I] [Nonempty I]

/--
OET anchor: h-336b0edda7ebdcc6
**定义（采样点的分量受限联合可行胞）**
The pointwise feasible cell at a sample point for all targets active on the
ambient domain and for a selected component subfamily.
-/
def sample_joint_feasible_cell
    (d : I → X → X → ENNReal) (target : β → Operator X bot)
    (U : Set X) (xₛ : X) (J : Set I) (tau : I → ENNReal) : Set X :=
  {z | ∀ beta : β, beta ∈ active_indices target U xₛ →
      ∀ j : I, j ∈ J → d j ((target beta).func xₛ) z ≤ tau j}

/--
OET anchor: h-336b0edda7ebdcc6
**定义（采样点的分量受限联合可行胞，全分量特例）**
On the full component family, the sample cell is exactly the local joint
feasible cell from target-family fitting.
-/
theorem sample_joint_feasible_cell_eq_local
    (d : I → X → X → ENNReal) (target : β → Operator X bot)
    (U : Set X) (xₛ : X) (tau : I → ENNReal) :
    sample_joint_feasible_cell d target U xₛ Set.univ tau =
      local_joint_feasible_cell d target U tau xₛ := by
  ext z
  simp [sample_joint_feasible_cell, local_joint_feasible_cell]

/--
OET anchor: h-336b0edda7ebdcc6
**命题（采样点联合可行胞判据）**
Pointwise simultaneous fitting at the sample point is exactly membership of
the proxy output in the component-restricted joint feasible cell.
-/
theorem sample_joint_feasible_cell_iff
    [Fintype β] [Nonempty β]
    (d : I → X → X → ENNReal) (target : β → Operator X bot)
    (proxy : Operator X bot) (U : Set X) (xₛ : X) (J : Set I)
    (tau : I → ENNReal)
    (hxₛ : xₛ ∈ effective_family_domain target U)
    (hJ : J.Nonempty)
    (htau_finite : ∀ j : I, j ∈ J → finite_ennreal (tau j))
    (hproxy_dom : xₛ ∈ dom proxy) :
    (∀ beta : β, beta ∈ active_indices target U xₛ →
        ∀ j : I, j ∈ J →
          d j ((target beta).func xₛ) (proxy.func xₛ) ≤ tau j) ↔
      proxy.func xₛ ∈ sample_joint_feasible_cell d target U xₛ J tau := by
  have _ := hxₛ
  have _ := hJ
  have _ := htau_finite
  have _ := hproxy_dom
  rfl

/--
OET anchor: h-336b0edda7ebdcc6
**命题（采样点联合可行胞判据，空胞）**
If the sample joint feasible cell is empty, no pointwise proxy output can
satisfy all active target inequalities at that sample point.
-/
theorem no_sample_joint_fitting_of_cell_empty
    [Fintype β] [Nonempty β]
    (d : I → X → X → ENNReal) (target : β → Operator X bot)
    (proxy : Operator X bot) (U : Set X) (xₛ : X) (J : Set I)
    (tau : I → ENNReal)
    (hxₛ : xₛ ∈ effective_family_domain target U)
    (hJ : J.Nonempty)
    (htau_finite : ∀ j : I, j ∈ J → finite_ennreal (tau j))
    (hproxy_dom : xₛ ∈ dom proxy)
    (hempty : sample_joint_feasible_cell d target U xₛ J tau = ∅) :
    ¬ (∀ beta : β, beta ∈ active_indices target U xₛ →
        ∀ j : I, j ∈ J →
          d j ((target beta).func xₛ) (proxy.func xₛ) ≤ tau j) := by
  intro hfit
  have hmem :
      proxy.func xₛ ∈ sample_joint_feasible_cell d target U xₛ J tau :=
    (sample_joint_feasible_cell_iff d target proxy U xₛ J tau
      hxₛ hJ htau_finite hproxy_dom).mp hfit
  simp [hempty] at hmem

/--
OET anchor: h-336b0edda7ebdcc6
**命题（采样点联合可行胞判据，不存在可行点值）**
An empty component-restricted joint feasible cell contains no point value
satisfying all active target constraints.
-/
theorem no_sample_joint_output_of_cell_empty
    [Fintype β] [Nonempty β]
    (d : I → X → X → ENNReal) (target : β → Operator X bot)
    (U : Set X) (xₛ : X) (J : Set I) (tau : I → ENNReal)
    (hxₛ : xₛ ∈ effective_family_domain target U)
    (hJ : J.Nonempty)
    (htau_finite : ∀ j : I, j ∈ J → finite_ennreal (tau j))
    (hempty : sample_joint_feasible_cell d target U xₛ J tau = ∅) :
    ¬ ∃ z : X, ∀ beta : β, beta ∈ active_indices target U xₛ →
        ∀ j : I, j ∈ J →
          d j ((target beta).func xₛ) z ≤ tau j := by
  have _ := hxₛ
  have _ := hJ
  have _ := htau_finite
  intro h
  rcases h with ⟨z, hz⟩
  have hzmem : z ∈ sample_joint_feasible_cell d target U xₛ J tau := hz
  simp [hempty] at hzmem

/--
OET anchor: h-236b99a83c3780af
**推论（共享中间目标的经验复合证书）**
If the target is close to an intermediate target chain and the proxy chain is
close to that intermediate target chain on the same domain, then the proxy
chain fits the target with the summed tolerance.
-/
theorem shared_intermediate_target_empirical_composition_certificate
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target_task target_chain proxy_chain : Operator X bot) (A : Set X)
    (Theta alpha : I → ENNReal)
    (hTheta_finite : ∀ j : I, finite_ennreal (Theta j))
    (halpha_finite : ∀ j : I, finite_ennreal (alpha j))
    (htask_dom : A ⊆ dom target_task)
    (htarget_chain_dom : A ⊆ dom target_chain)
    (hproxy_dom : A ⊆ dom proxy_chain)
    (htask_chain :
      ∀ x ∈ A, ∀ j : I,
        d j (target_task.func x) (target_chain.func x) ≤ alpha j)
    (hchain_proxy :
      ∀ x ∈ A, ∀ j : I,
        d j (target_chain.func x) (proxy_chain.func x) ≤ Theta j) :
    InFullFittingBall d target_task proxy_chain A
      (fun j => alpha j + Theta j) := by
  have _ := htarget_chain_dom
  refine ⟨?_, htask_dom, hproxy_dom, ?_⟩
  · intro j _
    exact ENNReal.add_ne_top.mpr ⟨halpha_finite j, hTheta_finite j⟩
  intro x hx j _
  exact le_trans
    ((hd j).triangle (target_task.func x) (target_chain.func x)
      (proxy_chain.func x))
    (add_le_add (htask_chain x hx j) (hchain_proxy x hx j))

/--
OET anchor: h-236b99a83c3780af
**推论（共享中间目标的经验复合证书，目标等同特例）**
When the intermediate target chain equals the task target on the analysis
domain, the intermediate-alignment tolerance is zero.
-/
theorem shared_intermediate_target_exact_specialization
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target_task target_chain proxy_chain : Operator X bot) (A : Set X)
    (Theta : I → ENNReal)
    (hTheta_finite : ∀ j : I, finite_ennreal (Theta j))
    (htask_dom : A ⊆ dom target_task)
    (htarget_chain_dom : A ⊆ dom target_chain)
    (hproxy_dom : A ⊆ dom proxy_chain)
    (heq : ∀ x ∈ A, target_chain.func x = target_task.func x)
    (hchain_proxy :
      ∀ x ∈ A, ∀ j : I,
        d j (target_chain.func x) (proxy_chain.func x) ≤ Theta j) :
    InFullFittingBall d target_task proxy_chain A Theta := by
  have _ := hd
  have _ := htarget_chain_dom
  refine ⟨fun j _ => hTheta_finite j, htask_dom, hproxy_dom, ?_⟩
  intro x hx j _
  simpa [heq x hx] using hchain_proxy x hx j

/--
OET anchor: h-7db372adecc0221f
**推论（经验链上界的共同前后接传递）**
An empirical terminal chain-error vector is exactly the vector consumed by the
common pre/post chain upper certificate.
-/
theorem empirical_common_pre_post_chain_inheritance
    (d : I → X → X → ENNReal)
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
        matrix_vector_bound Lχ Theta j :=
  common_pre_post_chain_upper_certificate d
    target_chain proxy_chain eta chi A V Theta Lχ ctx hTheta hLχ

end formal_oet.vol_03.ch_12_residuals_and_substitution
