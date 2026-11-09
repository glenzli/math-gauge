import Mathlib.Data.Nat.Dist
example : Nat.dist 0 1 = 1 := by native_decide
example : Nat.dist 0 1 = 1 := by decide
example : Nat.dist 0 1 = 1 := by rfl
example : Nat.dist 3 0 = 3 := by native_decide
example : (Nat.dist 0 3 : ENNReal) = 3 := by native_decide
