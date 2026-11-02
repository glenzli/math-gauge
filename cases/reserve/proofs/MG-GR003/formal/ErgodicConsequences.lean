import ErgodicQuotient

noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
open Filter Topology

namespace MathGauge.ErgodicRecovery
open ErgodicOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (T S : E →L[ℝ] E) (h : Commute T S) {KT KS : ℝ}
    (hT : ∀ n : ℕ, ‖T^n‖ ≤ KT) (hS : ∀ n : ℕ, ‖S^n‖ ≤ KS)
include h hT hS

theorem recovery_norm : ‖recovery T S h hT hS‖ ≤ KT*KS := by
  apply (recovery T S h hT hS).opNorm_le_bound
    (mul_nonneg ((norm_nonneg (T^0)).trans (hT 0)) ((norm_nonneg (S^0)).trans (hS 0)))
  exact recovered_norm T S h hT hS

theorem full_iteration_convergence_domain (x : E) :
    (∃ z, Tendsto (fun n => (iteration T S ^ n) x) atTop (𝓝 z)) ↔ x ∈ domain T S := by
  rw [← full_convergence_domain T S h hT hS x]
  exact exists_congr fun z => (equal_convergence_and_limits T S h hT hS x z).symm

theorem quotient_recovery_agrees (x : domain T S)
    (a : LinearMap.range (quotient_fixed T S))
    (ha : a.val = (differences T S).mkQ x.val) :
    record_recovery T S h hT hS a = recovery T S h hT hS x := by
  apply quotient_fixed_injective T S h hT hS
  change quotient_fixed T S ((quotient_equiv T S h hT hS).symm a) =
    (differences T S).mkQ (recovered T S x).val
  rw [quotient_inverse_property, ha]
  have hm := (Submodule.Quotient.mk_eq_zero (differences T S)).2 (recovered_difference T S x)
  change (differences T S).mkQ (x.val-(recovered T S x).val) = 0 at hm
  rwa [map_sub, sub_eq_zero] at hm

omit h hT hS in
theorem avg_difference_sharp (U : E →L[ℝ] E) {K : ℝ}
    (hU : ∀ n : ℕ, ‖U^n‖ ≤ K) (n : ℕ) :
    ‖avg U n * (1-U)‖ ≤ (1+K) * ((n:ℝ)+1)⁻¹ := by
  rw [avg_difference, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (show 0 < (n:ℝ)+1 by positivity))]
  have hb : ‖(1:E →L[ℝ] E)-U^(n+1)‖ ≤ 1+K :=
    (norm_sub_le _ _).trans (add_le_add (ContinuousLinearMap.norm_id_le) (hU (n+1)))
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hb
    (show 0 ≤ ((n:ℝ)+1)⁻¹ by positivity)

omit hT hS in
theorem rectangle_telescope_T (nm : ℕ×ℕ) :
    rectangle T S nm * (1-T) =
      (((nm.1:ℝ)+1)⁻¹ • (1-T^(nm.1+1))) * avg S nm.2 := by
  have hc : Commute (avg S nm.2) (1-T) :=
    (Commute.one_right _).sub_right (avg_commute h.symm _)
  rw [rectangle, mul_assoc, hc.eq, ← mul_assoc, avg_difference]

omit h hT hS in
theorem rectangle_telescope_S (nm : ℕ×ℕ) :
    rectangle T S nm * (1-S) =
      avg T nm.1 * (((nm.2:ℝ)+1)⁻¹ • (1-S^(nm.2+1))) := by
  rw [rectangle, mul_assoc, avg_difference]

theorem rectangle_defect_sharp_T (nm : ℕ×ℕ) :
    ‖rectangle T S nm * (1-T)‖ ≤ ((1+KT)*KS) * ((nm.1:ℝ)+1)⁻¹ := by
  have hc : Commute (avg S nm.2) (1-T) :=
    (Commute.one_right _).sub_right (avg_commute h.symm _)
  rw [rectangle, mul_assoc, hc.eq, ← mul_assoc]
  have ht0 : 0 ≤ KT := (norm_nonneg (T^0)).trans (hT 0)
  apply (norm_mul_le _ _).trans
  calc
    _ ≤ ((1+KT)*((nm.1:ℝ)+1)⁻¹)*KS :=
      mul_le_mul (avg_difference_sharp T hT _) (avg_bound S hS _) (norm_nonneg _) (by positivity)
    _ = _ := by ring

omit h in
theorem rectangle_defect_sharp_S (nm : ℕ×ℕ) :
    ‖rectangle T S nm * (1-S)‖ ≤ (KT*(1+KS)) * ((nm.2:ℝ)+1)⁻¹ := by
  rw [rectangle, mul_assoc]
  have ht0 : 0 ≤ KT := (norm_nonneg (T^0)).trans (hT 0)
  apply (norm_mul_le _ _).trans
  calc
    _ ≤ KT*((1+KS)*((nm.2:ℝ)+1)⁻¹) :=
      mul_le_mul (avg_bound T hT _) (avg_difference_sharp S hS _) (norm_nonneg _) ht0
    _ = _ := by ring

end MathGauge.ErgodicRecovery
