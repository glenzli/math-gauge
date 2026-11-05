import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Real.Basic

example : ENNReal.ofReal |0 - 3| ≤ 3 * ENNReal.ofReal |0 - 1| := by
  norm_num
