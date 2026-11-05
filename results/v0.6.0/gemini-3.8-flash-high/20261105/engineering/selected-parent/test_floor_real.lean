import Mathlib.Data.Real.Basic
import Mathlib.Data.ENNReal.Basic
import formal_oet.vol_01.ch_01_foundations.operator_space

open formal_oet.vol_01.ch_01_foundations

noncomputable def floor_op : Operator (Option ℝ) none where
  func := fun x => match x with | none => none | some r => some (↑⌊r⌋ : ℝ)
  preserves_bot := rfl

lemma floor_of_lt_one (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) : floor_op.func (some r) = some 0 := by
  dsimp [floor_op]
  congr 1
  have : ⌊r⌋ = 0 := by
    rw [Int.floor_eq_iff]
    constructor
    · norm_cast
    · push_cast; linarith
  norm_cast
