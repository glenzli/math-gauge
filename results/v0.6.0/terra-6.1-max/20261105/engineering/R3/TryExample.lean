import formal_oet.vol_01.ch_01_foundations.metric_entropy
import formal_oet.vol_01.ch_02_operator_bounds.decoupling
open formal_oet.vol_01.ch_01_foundations

#check edist_dist
#check Real.edist_eq
#check Real.dist_eq
#check edist_triangle
#check edist_comm
#check edist_self
#check Real.norm_eq_abs
#check ENNReal.ofReal_inj
#check ENNReal.ofReal_ne_zero

example : edist |(-1 : ℝ)| |(1 : ℝ)| = 0 := by norm_num
example : edist |(-3 : ℝ)| |(1 : ℝ)| = 2 := by
  rw [edist_dist, Real.dist_eq]
  norm_num
