import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Real.Basic
import Mathlib.Data.ENNReal.Basic

open formal_oet.vol_01.ch_01_foundations

noncomputable def d_real_bot (x y : Option ℝ) : ENNReal :=
  match x, y with
  | none, none => 0
  | some a, some b => ENNReal.ofReal (|a - b|)
  | _, _ => ⊤

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

#check instExtendedPseudoMetricRealBot
