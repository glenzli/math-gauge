import BinomialSmoothing
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Order.Filter.AtTopBot.Prod

noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
open Filter Topology Finset
open scoped BigOperators

namespace MathGauge.ErgodicOperators
open BinomialSmoothing

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def avg (U : A) (n : ℕ) : A := ((n:ℝ)+1)⁻¹ • ∑ i ∈ range (n+1), U^i
def rectangle (T S : A) (nm : ℕ × ℕ) : A := avg T nm.1 * avg S nm.2
def iteration (T S : A) : A := (1/4 : ℝ) • ((1+T)*(1+S))

/-- The product definition is exactly the rectangular double sum in the task. -/
theorem rectangle_formula (T S : A) (n m : ℕ) :
    rectangle T S (n,m) = (((n:ℝ)+1)*((m:ℝ)+1))⁻¹ •
      ∑ i ∈ range (n+1), ∑ j ∈ range (m+1), T^i*S^j := by
  simp only [rectangle, avg, smul_mul_assoc, mul_smul_comm, smul_smul,
    Finset.sum_mul_sum, mul_inv_rev]

theorem iteration_eq_lazy (T S : A) : iteration T S = lazy T * lazy S := by
  simp only [iteration, lazy, smul_mul_assoc, mul_smul_comm, smul_smul]
  norm_num

theorem lazy_commute {T S : A} (h : Commute T S) : Commute (lazy T) (lazy S) := by
  have h1 : Commute (1+T) S := (Commute.one_left S).add_left h
  have h2 : Commute (1+T) (1+S) := (Commute.one_right _).add_right h1
  exact (h2.smul_left (1/2:ℝ)).smul_right (1/2:ℝ)

theorem avg_commute {T S : A} (h : Commute T S) (n : ℕ) : Commute (avg T n) S := by
  apply Commute.smul_left
  exact Commute.sum_left _ _ _ fun i hi => h.pow_left i

theorem avg_bound (U : A) {K : ℝ} (hK : ∀ n : ℕ, ‖U^n‖ ≤ K) (n : ℕ) :
    ‖avg U n‖ ≤ K := by
  have hpos : 0 < (n:ℝ)+1 := by positivity
  rw [avg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
  calc
    _ ≤ ((n:ℝ)+1)⁻¹ * ∑ i ∈ range (n+1), ‖U^i‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ ((n:ℝ)+1)⁻¹ * ∑ _i ∈ range (n+1), K := by
      gcongr with i hi
      exact hK i
    _ = K := by simp; field_simp

theorem avg_difference (U : A) (n : ℕ) :
    avg U n * (1-U) = ((n:ℝ)+1)⁻¹ • (1-U^(n+1)) := by
  rw [avg, smul_mul_assoc, geom_sum_mul_neg]

theorem avg_difference_bound (U : A) {K : ℝ} (hK : ∀ n : ℕ, ‖U^n‖ ≤ K) (n : ℕ) :
    ‖avg U n * (1-U)‖ ≤ (2*K) * ((n:ℝ)+1)⁻¹ := by
  rw [avg_difference, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (show 0 < (n:ℝ)+1 by positivity))]
  have h0 : ‖(1:A)‖ ≤ K := by simpa using hK 0
  have h1 : ‖(1:A)-U^(n+1)‖ ≤ 2*K := by
    apply (norm_sub_le _ _).trans
    linarith [hK (n+1)]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left h1 (show 0 ≤ ((n:ℝ)+1)⁻¹ by positivity)

theorem rectangle_bound (T S : A) {KT KS : ℝ}
    (hT : ∀ n : ℕ, ‖T^n‖ ≤ KT) (hS : ∀ n : ℕ, ‖S^n‖ ≤ KS) (nm : ℕ × ℕ) :
    ‖rectangle T S nm‖ ≤ KT*KS := by
  apply (norm_mul_le _ _).trans
  exact mul_le_mul (avg_bound T hT _) (avg_bound S hS _)
    (norm_nonneg _) ((norm_nonneg (T^0)).trans (hT 0))

theorem iteration_power (T S : A) (h : Commute T S) (n : ℕ) :
    iteration T S ^ n = lazy T ^ n * lazy S ^ n := by
  rw [iteration_eq_lazy, (lazy_commute h).mul_pow]

theorem iteration_bound (T S : A) (h : Commute T S) {KT KS : ℝ}
    (hT : ∀ n : ℕ, ‖T^n‖ ≤ KT) (hS : ∀ n : ℕ, ‖S^n‖ ≤ KS) (n : ℕ) :
    ‖iteration T S ^ n‖ ≤ KT*KS := by
  rw [iteration_power T S h]
  apply (norm_mul_le _ _).trans
  exact mul_le_mul (lazy_power_bound T hT _) (lazy_power_bound S hS _)
    (norm_nonneg _) ((norm_nonneg (T^0)).trans (hT 0))

theorem rectangle_difference_T_bound (T S : A) (h : Commute T S) {KT KS : ℝ}
    (hT : ∀ n : ℕ, ‖T^n‖ ≤ KT) (hS : ∀ n : ℕ, ‖S^n‖ ≤ KS) (nm : ℕ × ℕ) :
    ‖rectangle T S nm * (1-T)‖ ≤ (2*KT*KS) * ((nm.1:ℝ)+1)⁻¹ := by
  have hc : Commute (avg S nm.2) (1-T) :=
    (Commute.one_right _).sub_right (avg_commute h.symm _)
  rw [rectangle, mul_assoc, hc.eq, ← mul_assoc]
  apply (norm_mul_le _ _).trans
  have hs0 : 0 ≤ KS := (norm_nonneg (S^0)).trans (hS 0)
  have ht0 : 0 ≤ KT := (norm_nonneg (T^0)).trans (hT 0)
  calc
    _ ≤ ((2*KT)*((nm.1:ℝ)+1)⁻¹)*KS :=
      mul_le_mul (avg_difference_bound T hT _) (avg_bound S hS _) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem rectangle_difference_S_bound (T S : A) {KT KS : ℝ}
    (hT : ∀ n : ℕ, ‖T^n‖ ≤ KT) (hS : ∀ n : ℕ, ‖S^n‖ ≤ KS) (nm : ℕ × ℕ) :
    ‖rectangle T S nm * (1-S)‖ ≤ (2*KT*KS) * ((nm.2:ℝ)+1)⁻¹ := by
  rw [rectangle, mul_assoc]
  apply (norm_mul_le _ _).trans
  have ht0 : 0 ≤ KT := (norm_nonneg (T^0)).trans (hT 0)
  calc
    _ ≤ KT*((2*KS)*((nm.2:ℝ)+1)⁻¹) :=
      mul_le_mul (avg_bound T hT _) (avg_difference_bound S hS _) (norm_nonneg _) ht0
    _ = _ := by ring

theorem iteration_difference_T_bound (T S : A) (h : Commute T S) {KT KS : ℝ}
    (hT : ∀ n : ℕ, ‖T^n‖ ≤ KT) (hS : ∀ n : ℕ, ‖S^n‖ ≤ KS) (n : ℕ) :
    ‖iteration T S ^ n * (1-T)‖ ≤ 2*(KT*KS)*b n := by
  have hc : Commute (lazy S) (1-T) := by
    apply Commute.smul_left
    exact (Commute.one_left _).add_left ((Commute.one_right S).sub_right h.symm)
  rw [iteration_power T S h, mul_assoc, (hc.pow_left n).eq, ← mul_assoc]
  apply (norm_mul_le _ _).trans
  have ht0 : 0 ≤ KT := (norm_nonneg (T^0)).trans (hT 0)
  calc
    _ ≤ (2*KT*b n)*KS :=
      mul_le_mul (smoothing_bound T hT n) (lazy_power_bound S hS n)
        (norm_nonneg _) (mul_nonneg (by positivity) (p_nonneg n (n/2)))
    _ = _ := by ring

theorem iteration_difference_S_bound (T S : A) (h : Commute T S) {KT KS : ℝ}
    (hT : ∀ n : ℕ, ‖T^n‖ ≤ KT) (hS : ∀ n : ℕ, ‖S^n‖ ≤ KS) (n : ℕ) :
    ‖iteration T S ^ n * (1-S)‖ ≤ 2*(KT*KS)*b n := by
  rw [iteration_power T S h, mul_assoc]
  apply (norm_mul_le _ _).trans
  have ht0 : 0 ≤ KT := (norm_nonneg (T^0)).trans (hT 0)
  calc
    _ ≤ KT*(2*KS*b n) :=
      mul_le_mul (lazy_power_bound T hT n) (smoothing_bound S hS n) (norm_nonneg _) ht0
    _ = _ := by ring

end MathGauge.ErgodicOperators
