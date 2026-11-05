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

lemma d_real_bot_self (x : Option ℝ) : d_real_bot x x = 0 := by
  cases x <;> simp [d_real_bot]

lemma d_real_bot_symm (x y : Option ℝ) : d_real_bot x y = d_real_bot y x := by
  cases x <;> cases y <;> simp [d_real_bot, abs_sub_comm]

lemma d_real_bot_triangle (x y z : Option ℝ) : d_real_bot x z ≤ d_real_bot x y + d_real_bot y z := by
  cases x <;> cases y <;> cases z <;> simp [d_real_bot]
  rename_i a b c
  have h := abs_sub_le a b c
  have h2 : ENNReal.ofReal (|a - c|) ≤ ENNReal.ofReal (|a - b| + |b - c|) :=
    ENNReal.ofReal_le_ofReal h
  exact le_trans h2 (ENNReal.ofReal_add_le)

lemma d_real_bot_isolate_bot (x : Option ℝ) (hx : x ≠ none) : d_real_bot x none = ⊤ := by
  cases x
  · contradiction
  · rfl

instance instExtendedPseudoMetricRealBot : ExtendedPseudoMetric (Option ℝ) none d_real_bot where
  nonabsorbing := ⟨some 0, by simp⟩
  dist_self := d_real_bot_self
  symm := d_real_bot_symm
  triangle := d_real_bot_triangle
  isolate_bot := d_real_bot_isolate_bot

theorem prop_3_10_01 :
    (none : Option ℝ) ∉ U_step ∧
    U_step.Nonempty ∧
    step_op.func none = none ∧
    ExtendedPseudoMetric (Option ℝ) none d_real_bot := by
  refine ⟨?_, ?_, rfl, instExtendedPseudoMetricRealBot⟩
  · intro ⟨r, hr, _⟩; contradiction
  · exact ⟨some 1, ⟨1, rfl, Or.inr ⟨by norm_num, by norm_num⟩⟩⟩
