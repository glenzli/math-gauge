import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic
def d4 (x y : Fin 4) : ENNReal :=
  ((if x.val ≤ y.val then y.val - x.val else x.val - y.val : ℕ) : ENNReal)
example : d4 0 1 = 1 := by norm_num [d4]
example : d4 0 3 = 3 := by norm_num [d4]
example : ¬ d4 3 0 < (2:ENNReal) := by norm_num [d4]
