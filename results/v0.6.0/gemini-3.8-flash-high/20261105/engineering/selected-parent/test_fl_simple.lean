
import Mathlib.Data.Real.Basic
lemma test_floor (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2) : ⌊r⌋ = (0 : ℤ) := by
  rw [Int.floor_eq_iff]
  constructor
  · norm_cast
  · norm_cast
