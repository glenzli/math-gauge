import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
example : (0:ENNReal) < 1 := by decide
example : ¬ ((0:ENNReal) < 1) := by decide
