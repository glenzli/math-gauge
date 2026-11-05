import Mathlib.Data.Real.Basic
import Mathlib.Data.ENNReal.Basic

#check fun (a b : ℝ) => ENNReal.ofReal (abs (abs a - abs b))
