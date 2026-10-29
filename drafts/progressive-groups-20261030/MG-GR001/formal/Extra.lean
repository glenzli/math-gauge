import Limits
import Obstructions
import Weighted
import Mathlib.Topology.UniformSpace.Compact

noncomputable section
open scoped BigOperators ENNReal NNReal
namespace MathGauge.RecursiveClosure
namespace Obstructions
local instance zeroPseudoMetric : PseudoMetricSpace Bool :=
  PseudoMetricSpace.induced (fun _ : Bool => (0 : ℝ)) inferInstance

theorem zero_pseudo_complete : CompleteSpace Bool := inferInstance

theorem zero_pseudo_matches (x y : Bool) : edist x y = zeroGauge.d () x y := by
  change edist (0:ℝ) 0 = 0
  norm_num
end Obstructions
namespace Counterexample

theorem different_fixed_distance_top (c d : ℝ) (hcd : c ≠ d) :
    sys.delta (solution c) (solution d) (false,0) = ⊤ := by
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro C
  have ha : 0 < |c-d| := abs_pos.mpr (sub_ne_zero.mpr hcd)
  obtain ⟨k,hk⟩ := exists_nat_gt (max 1 ((C:ℝ)/|c-d|))
  have hk0 : 0 < k := by have := lt_of_le_of_lt (le_max_left _ _) hk; exact_mod_cast (lt_trans (by norm_num : (0:ℝ)<1) this)
  have hkZ : (0:ℤ) < k := by exact_mod_cast hk0
  have hp : (k:ℝ) ≤ 4^k := by
    have hb := one_add_mul_le_pow (by norm_num : (-2:ℝ) ≤ 3) k
    norm_num at hb
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hC : (C:ℝ) ≤ |c-d| * 4^k := by
    have hc := (div_lt_iff₀ ha).1 (lt_of_le_of_lt (le_max_right _ _) hk)
    nlinarith
  apply le_trans _ (sys.point_le_delta _ _ false 0 (k:ℤ))
  have hd : gauge.d 0 (solution c false k) (solution d false k) = ENNReal.ofReal (|c-d| * 4^k) := by
    simp [gauge,coordinate,solution,hk0.ne',not_le.mpr hkZ,← sub_mul,abs_mul,abs_of_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤4) k)]
  rw [hd]
  simpa using ENNReal.ofReal_le_ofReal hC

end Counterexample
end MathGauge.RecursiveClosure
