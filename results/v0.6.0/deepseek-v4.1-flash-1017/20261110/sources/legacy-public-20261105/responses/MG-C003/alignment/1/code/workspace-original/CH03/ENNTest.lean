import Mathlib
example : ENNReal.ofReal (1/2:ℝ) = (2⁻¹ : ENNReal) := by norm_num [ENNReal.ofReal, ENNReal.coe_div]
example : ENNReal.ofReal (1/5:ℝ) = (5⁻¹ : ENNReal) := by norm_num [ENNReal.ofReal, ENNReal.coe_div]
