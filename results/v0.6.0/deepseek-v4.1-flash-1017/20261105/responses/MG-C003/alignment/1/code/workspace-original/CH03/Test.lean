import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic
example : (1:ENNReal) ≤ 2 := by norm_num
example : ¬ ((2:ENNReal) < 1) := by norm_num
example : ENNReal.ofReal (1/2:ℝ) < 1 := by
  rw [show (1:ENNReal) = ENNReal.ofReal (1:ℝ) by simp]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ)<1)).mpr (by norm_num)
