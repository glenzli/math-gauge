import ErgodicRecoveryCore

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
open Filter Topology Finset
open scoped BigOperators

namespace MathGauge.ErgodicRecovery
open ErgodicOperators BinomialSmoothing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (T S : E →L[ℝ] E)

theorem mem_fixed_iff (x : E) : x ∈ fixed T S ↔ T x = x ∧ S x = x := by
  change (x-T x = 0 ∧ x-S x = 0) ↔ (T x = x ∧ S x = x)
  simp only [sub_eq_zero]
  tauto

theorem lazy_commute_base {U V : E →L[ℝ] E} (h : Commute U V) : Commute (lazy U) V :=
  ((Commute.one_left V).add_left h).smul_left _

theorem rectangle_commute_T (h : Commute T S) (nm : ℕ×ℕ) :
    Commute (rectangle T S nm) T :=
  (avg_commute (Commute.refl T) _).mul_left (avg_commute h.symm _)

theorem rectangle_commute_S (h : Commute T S) (nm : ℕ×ℕ) :
    Commute (rectangle T S nm) S :=
  (avg_commute h _).mul_left (avg_commute (Commute.refl S) _)

theorem iteration_commute_T (h : Commute T S) (n : ℕ) :
    Commute (iteration T S ^ n) T := by
  rw [iteration_eq_lazy]
  exact ((lazy_commute_base (Commute.refl T)).mul_left (lazy_commute_base h.symm)).pow_left n

theorem iteration_commute_S (h : Commute T S) (n : ℕ) :
    Commute (iteration T S ^ n) S := by
  rw [iteration_eq_lazy]
  exact ((lazy_commute_base h).mul_left (lazy_commute_base (Commute.refl S))).pow_left n

theorem rectangle_defects (h : Commute T S) {KT KS : ℝ}
    (hT : ∀ n : ℕ, ‖T^n‖ ≤ KT) (hS : ∀ n : ℕ, ‖S^n‖ ≤ KS) :
    Tendsto (fun nm => rectangle T S nm * (1-T)) atTop (𝓝 0) ∧
    Tendsto (fun nm => rectangle T S nm * (1-S)) atTop (𝓝 0) := by
  have hf : Tendsto (Prod.fst : ℕ×ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]; exact tendsto_fst
  have hs : Tendsto (Prod.snd : ℕ×ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]; exact tendsto_snd
  have hi : Tendsto (fun n : ℕ => ((n:ℝ)+1)⁻¹) atTop (𝓝 0) := by
    simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => (1:ℝ)/(n+1)) atTop (𝓝 0))
  constructor
  · apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (rectangle_difference_T_bound T S h hT hS)
    simpa using (hi.comp hf).const_mul (2*KT*KS)
  · apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (rectangle_difference_S_bound T S hT hS)
    simpa using (hi.comp hs).const_mul (2*KT*KS)

theorem iteration_defects (h : Commute T S) {KT KS : ℝ}
    (hT : ∀ n : ℕ, ‖T^n‖ ≤ KT) (hS : ∀ n : ℕ, ‖S^n‖ ≤ KS) :
    Tendsto (fun n => iteration T S ^ n * (1-T)) atTop (𝓝 0) ∧
    Tendsto (fun n => iteration T S ^ n * (1-S)) atTop (𝓝 0) := by
  constructor
  · apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (iteration_difference_T_bound T S h hT hS)
    simpa using b_tendsto_zero.const_mul (2*(KT*KS))
  · apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (iteration_difference_S_bound T S h hT hS)
    simpa using b_tendsto_zero.const_mul (2*(KT*KS))

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

theorem power_record (U : E →L[ℝ] E) (q : E →ₗ[ℝ] W)
    (hq : ∀ x, q (U x) = q x) (n : ℕ) (x : E) : q ((U^n) x) = q x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', ContinuousLinearMap.mul_apply, hq, ih]

theorem avg_record (U : E →L[ℝ] E) (q : E →ₗ[ℝ] W)
    (hq : ∀ x, q (U x) = q x) (n : ℕ) (x : E) : q (avg U n x) = q x := by
  simp only [avg, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    map_smul, map_sum, power_record U q hq]
  simp only [sum_const, card_range]
  rw [← Nat.cast_smul_eq_nsmul ℝ (n+1) (q x), smul_smul]
  push_cast
  rw [inv_mul_cancel₀ (show (n:ℝ)+1 ≠ 0 by positivity), one_smul]

theorem lazy_record (U : E →L[ℝ] E) (q : E →ₗ[ℝ] W)
    (hq : ∀ x, q (U x) = q x) (x : E) : q (lazy U x) = q x := by
  simp only [lazy, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.one_apply, map_smul, map_add, hq]
  module

theorem quotient_T (x : E) : (differences T S).mkQ (T x) = (differences T S).mkQ x := by
  have hm : x-T x ∈ differences T S := by
    apply Submodule.le_topologicalClosure
    exact Submodule.mem_sup.mpr ⟨(1-T) x, ⟨x,rfl⟩, 0, Submodule.zero_mem _, by simp⟩
  have hh := (Submodule.Quotient.mk_eq_zero (differences T S)).2 hm
  change (differences T S).mkQ (x-T x) = 0 at hh
  rw [map_sub, sub_eq_zero] at hh
  exact hh.symm

theorem quotient_S (x : E) : (differences T S).mkQ (S x) = (differences T S).mkQ x := by
  have hm : x-S x ∈ differences T S := by
    apply Submodule.le_topologicalClosure
    exact Submodule.mem_sup.mpr ⟨0, Submodule.zero_mem _, (1-S) x, ⟨x,rfl⟩, by simp⟩
  have hh := (Submodule.Quotient.mk_eq_zero (differences T S)).2 hm
  change (differences T S).mkQ (x-S x) = 0 at hh
  rw [map_sub, sub_eq_zero] at hh
  exact hh.symm

theorem rectangle_record (x : E) (nm : ℕ×ℕ) : x - rectangle T S nm x ∈ differences T S := by
  apply (Submodule.Quotient.mk_eq_zero (differences T S)).mp
  change (differences T S).mkQ (x - rectangle T S nm x) = 0
  rw [map_sub]
  simp only [rectangle, ContinuousLinearMap.mul_apply]
  rw [avg_record T _ (quotient_T T S), avg_record S _ (quotient_S T S), sub_self]

theorem iteration_record (x : E) (n : ℕ) : x - (iteration T S ^ n) x ∈ differences T S := by
  have hq : ∀ y, (differences T S).mkQ (iteration T S y) = (differences T S).mkQ y := by
    intro y
    rw [iteration_eq_lazy, ContinuousLinearMap.mul_apply,
      lazy_record T _ (quotient_T T S), lazy_record S _ (quotient_S T S)]
  apply (Submodule.Quotient.mk_eq_zero (differences T S)).mp
  change (differences T S).mkQ (x - (iteration T S ^ n) x) = 0
  rw [map_sub, power_record _ _ hq, sub_self]

theorem power_fixed (U : E →L[ℝ] E) {z : E} (h : U z = z) (n : ℕ) : (U^n) z = z := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', ContinuousLinearMap.mul_apply, ih, h]

theorem avg_fixed (U : E →L[ℝ] E) {z : E} (h : U z = z) (n : ℕ) : avg U n z = z := by
  simp only [avg, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, power_fixed U h]
  simp only [sum_const, card_range]
  rw [← Nat.cast_smul_eq_nsmul ℝ (n+1) z, smul_smul]
  push_cast
  rw [inv_mul_cancel₀ (show (n:ℝ)+1 ≠ 0 by positivity), one_smul]

theorem lazy_fixed (U : E →L[ℝ] E) {z : E} (h : U z = z) : lazy U z = z := by
  simp only [lazy, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.one_apply, h]
  module

theorem rectangle_fixed (z : E) (hz : z ∈ fixed T S) (nm : ℕ×ℕ) : rectangle T S nm z = z := by
  have hz := (mem_fixed_iff T S z).1 hz
  rw [rectangle, ContinuousLinearMap.mul_apply, avg_fixed S hz.2, avg_fixed T hz.1]

theorem iteration_fixed (z : E) (hz : z ∈ fixed T S) (n : ℕ) : (iteration T S ^ n) z = z := by
  apply power_fixed
  have hz := (mem_fixed_iff T S z).1 hz
  rw [iteration_eq_lazy, ContinuousLinearMap.mul_apply, lazy_fixed S hz.2, lazy_fixed T hz.1]

/-- Full comparison of the actual rectangular averages and the task's actual iteration.
The pair filter is the coordinatewise atTop filter, equivalently min(N,M)→∞.
Our indices n,m represent the positive lengths N=n+1, M=m+1. -/
theorem comparison (h : Commute T S) {KT KS : ℝ}
    (hT : ∀ n : ℕ, ‖T^n‖ ≤ KT) (hS : ∀ n : ℕ, ‖S^n‖ ≤ KS) (x z : E) :
    (Tendsto (fun nm => rectangle T S nm x) atTop (𝓝 z) ↔
      z ∈ fixed T S ∧ x-z ∈ differences T S) ∧
    (Tendsto (fun n => (iteration T S ^ n) x) atTop (𝓝 z) ↔
      z ∈ fixed T S ∧ x-z ∈ differences T S) := by
  have ht0 : 0 ≤ KT := (norm_nonneg (T^0)).trans (hT 0)
  have hs0 : 0 ≤ KS := (norm_nonneg (S^0)).trans (hS 0)
  constructor
  · exact convergence_criterion atTop (rectangle T S) T S (mul_nonneg ht0 hs0)
      (rectangle_bound T S hT hS) (rectangle_commute_T T S h) (rectangle_commute_S T S h)
      (rectangle_defects T S h hT hS).1 (rectangle_defects T S h hT hS).2
      (rectangle_fixed T S) (rectangle_record T S) x z
  · exact convergence_criterion atTop (fun n => iteration T S ^ n) T S (mul_nonneg ht0 hs0)
      (iteration_bound T S h hT hS) (iteration_commute_T T S h) (iteration_commute_S T S h)
      (iteration_defects T S h hT hS).1 (iteration_defects T S h hT hS).2
      (iteration_fixed T S) (iteration_record T S) x z

theorem equal_convergence_and_limits (h : Commute T S) {KT KS : ℝ}
    (hT : ∀ n : ℕ, ‖T^n‖ ≤ KT) (hS : ∀ n : ℕ, ‖S^n‖ ≤ KS) (x z : E) :
    Tendsto (fun nm => rectangle T S nm x) atTop (𝓝 z) ↔
    Tendsto (fun n => (iteration T S ^ n) x) atTop (𝓝 z) :=
  (comparison T S h hT hS x z).1.trans (comparison T S h hT hS x z).2.symm

end MathGauge.ErgodicRecovery
