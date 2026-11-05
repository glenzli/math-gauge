import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv

namespace OperatorLocalDegeneracy

set_option linter.unusedVariables false

open formal_oet.vol_01.ch_01_foundations

variable {X : Type} {bot : X}

noncomputable def r_null (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (y : X) (U : Set X) : ENNReal :=
  sSup { r : ENNReal | 0 < r ∧ r < ⊤ ∧ ∀ x ∈ U, d_in x y < r → d_out (ϕ.func x) (ϕ.func y) = 0 }

noncomputable def r_null_uniform (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : ENNReal :=
  ⨅ y ∈ U, r_null d_in d_out ϕ y U

theorem prop_3_12_i (d_in d_mid d_out : X → X → ENNReal)
    (ϕ ψ : Operator X bot) (U : Set X)
    (hψ : ∀ u ∈ ϕ.func '' U, ∀ v ∈ ϕ.func '' U, d_mid u v = 0 → d_out (ψ.func u) (ψ.func v) = 0) :
    r_null_uniform d_in d_mid ϕ U ≤ r_null_uniform d_in d_out (ψ * ϕ) U := by
  dsimp [r_null_uniform]
  apply le_iInf; intro y
  apply le_iInf; intro hy
  refine le_trans (biInf_le (fun y => r_null d_in d_mid ϕ y U) hy) ?_
  dsimp [r_null]
  apply sSup_le_sSup
  intro r hr
  rcases hr with ⟨hr0, hrt, hball⟩
  refine ⟨hr0, hrt, ?_⟩
  intro x hx hdist
  have hmid := hball x hx hdist
  change d_out (ψ.func (ϕ.func x)) (ψ.func (ϕ.func y)) = 0
  exact hψ (ϕ.func x) ⟨x, hx, rfl⟩ (ϕ.func y) ⟨y, hy, rfl⟩ hmid
