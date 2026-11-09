import Mathlib
#check div_le_iff₀
#check div_le_iff
#check div_le_iff_of_pos
#check NNReal.div_le_iff
#check le_div_iff₀
example : (3/2 : NNReal) ≤ 2 := by
  rw [div_le_iff₀ (by norm_num : (0:NNReal)<2)]
  norm_num
example : ((3/2 : NNReal) : ENNReal) ≤ ((2 : NNReal) : ENNReal) := by
  exact_mod_cast (by
    rw [div_le_iff₀ (by norm_num : (0:NNReal)<2)]
    norm_num : (3/2 : NNReal) ≤ 2)
