import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Inv

noncomputable def eps74 : ENNReal := ENNReal.ofReal (7 / 4)

theorem ex_div_one : eps74 / 1 = eps74 := by
  rw [ENNReal.div_eq_inv_mul, inv_one, one_mul]

theorem ex_div_three : eps74 / 3 ≤ 1 := by
  rw [ENNReal.div_le_iff (by norm_num) (by norm_num), one_mul]
  dsimp [eps74]
  have h3 : (3 : ENNReal) = ENNReal.ofReal 3 := by norm_num
  rw [h3]
  exact ENNReal.ofReal_le_ofReal (by norm_num)
