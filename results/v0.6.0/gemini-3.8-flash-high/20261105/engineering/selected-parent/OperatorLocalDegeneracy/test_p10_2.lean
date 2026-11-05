import Mathlib.Data.Real.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_01_foundations.gauge_space

open formal_oet.vol_01.ch_01_foundations

noncomputable def d_real_bot (x y : Option ℝ) : ENNReal :=
  match x, y with
  | none, none => 0
  | some a, some b => ENNReal.ofReal (|a - b|)
  | _, _ => ⊤

noncomputable def step_func (x : Option ℝ) : Option ℝ :=
  match x with
  | none => none
  | some r => if r > 0 then some 1 else some 0

noncomputable def step_op : Operator (Option ℝ) none where
  func := step_func
  preserves_bot := rfl

def U_step : Set (Option ℝ) :=
  { y | ∃ r : ℝ, y = some r ∧ ((-1 ≤ r ∧ r < 0) ∨ (0 < r ∧ r ≤ 1)) }

noncomputable def r_null (d_in d_out : Option ℝ → Option ℝ → ENNReal) (ϕ : Operator (Option ℝ) none) (y : Option ℝ) (U : Set (Option ℝ)) : ENNReal :=
  sSup { r : ENNReal | 0 < r ∧ r < ⊤ ∧ ∀ x ∈ U, d_in x y < r → d_out (ϕ.func x) (ϕ.func y) = 0 }

noncomputable def r_null_uniform (d_in d_out : Option ℝ → Option ℝ → ENNReal) (ϕ : Operator (Option ℝ) none) (U : Set (Option ℝ)) : ENNReal :=
  ⨅ y ∈ U, r_null d_in d_out ϕ y U

def step_admissible (y : Option ℝ) : Set ENNReal :=
  { r : ENNReal | 0 < r ∧ r < ⊤ ∧ ∀ x ∈ U_step, d_real_bot x y < r → d_real_bot (step_op.func x) (step_op.func y) = 0 }

lemma sSup_Ioc_eq (c : ENNReal) (hc0 : 0 < c) (hct : c < ⊤) :
    sSup { r : ENNReal | 0 < r ∧ r ≤ c } = c := by
  apply le_antisymm
  · apply sSup_le
    intro x hx
    exact hx.2
  · apply le_sSup
    exact ⟨hc0, le_refl c⟩

#check sSup_Ioc_eq
