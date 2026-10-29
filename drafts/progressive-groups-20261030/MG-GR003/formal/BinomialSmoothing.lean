import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
open Filter Topology Finset
open scoped BigOperators

namespace MathGauge.BinomialSmoothing

def p (n k : ℕ) : ℝ := (n.choose k : ℝ) / 2^n
def b (n : ℕ) : ℝ := p n (n/2)
def c (m : ℕ) : ℝ := (Nat.centralBinom m : ℝ) / 4^m

theorem p_nonneg (n k : ℕ) : 0 ≤ p n k := by unfold p; positivity
theorem c_nonneg (m : ℕ) : 0 ≤ c m := by unfold c; positivity
theorem p_zero (n : ℕ) : p n 0 = (2 : ℝ)⁻¹^n := by simp [p, inv_pow]
theorem p_last_zero (n : ℕ) : p n (n+1) = 0 := by simp [p]

theorem choose_decreasing {n k : ℕ} (hk : n/2 ≤ k) : n.choose (k+1) ≤ n.choose k := by
  apply Nat.le_of_mul_le_mul_right (c := k+1)
  · rw [Nat.choose_succ_right_eq]
    apply Nat.mul_le_mul_left
    omega
  · omega

theorem p_increasing {n k : ℕ} (hk : k < n/2) : p n k ≤ p n (k+1) := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.choose_le_succ_of_lt_half_left hk

theorem p_decreasing {n k : ℕ} (hk : n/2 ≤ k) : p n (k+1) ≤ p n k := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast choose_decreasing hk

/-- The discrete total variation, including both zero exterior coefficients. -/
theorem variation (n : ℕ) :
    p n 0 + ∑ k ∈ range (n+1), |p n (k+1) - p n k| = 2 * b n := by
  have hsplit := sum_range_add_sum_Ico (fun k => |p n (k+1) - p n k|)
    (show n/2 ≤ n+1 by omega)
  rw [← hsplit]
  have hleft : ∑ k ∈ range (n/2), |p n (k+1) - p n k| = p n (n/2) - p n 0 := by
    calc
      _ = ∑ k ∈ range (n/2), (p n (k+1) - p n k) := by
        apply sum_congr rfl
        intro k hk
        rw [abs_of_nonneg (sub_nonneg.mpr (p_increasing (mem_range.mp hk)))]
      _ = _ := sum_range_sub (p n) (n/2)
  have hright : ∑ k ∈ Ico (n/2) (n+1), |p n (k+1) - p n k| = p n (n/2) := by
    calc
      _ = -(∑ k ∈ Ico (n/2) (n+1), (p n (k+1) - p n k)) := by
        rw [← sum_neg_distrib]
        apply sum_congr rfl
        intro k hk
        rw [abs_of_nonpos (sub_nonpos.mpr (p_decreasing (mem_Ico.mp hk).1))]
      _ = _ := by
        rw [sum_Ico_eq_sub _ (by omega), sum_range_sub, sum_range_sub, p_last_zero]
        ring
  rw [hleft, hright]
  dsimp [b]
  ring

theorem c_recurrence (m : ℕ) :
    c (m+1) = ((2*(m:ℝ)+1)/(2*(m+1))) * c m := by
  have h : ((m:ℝ)+1) * (Nat.centralBinom (m+1) : ℝ) =
      2*(2*(m:ℝ)+1)*(Nat.centralBinom m : ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ m
  unfold c
  rw [pow_succ]
  field_simp
  nlinarith

/-- A direct induction gives the reference decay bound without a logarithmic detour. -/
theorem c_square_bound (m : ℕ) : ((m:ℝ)+1) * (c m)^2 ≤ 1 := by
  induction m with
  | zero => norm_num [c]
  | succ m ih =>
    rw [c_recurrence]
    push_cast
    have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
    have hc : 0 ≤ (c m)^2 := sq_nonneg _
    have hf : ((m:ℝ)+2)*(2*m+1)^2 ≤ 4*(m+1)^3 := by nlinarith
    have hp : 0 < 4*((m:ℝ)+1)^2 := by positivity
    have he : ((m:ℝ)+1+1)*(((2*m+1)/(2*(m+1)))*c m)^2 =
        (((m:ℝ)+2)*(2*m+1)^2*(c m)^2)/(4*(m+1)^2) := by
      field_simp
      ring
    rw [he]
    apply (div_le_iff₀ hp).2
    calc
      _ ≤ 4*((m:ℝ)+1)^3 * (c m)^2 := mul_le_mul_of_nonneg_right hf hc
      _ = 4*((m:ℝ)+1)^2 * (((m:ℝ)+1)*(c m)^2) := by ring
      _ ≤ 4*((m:ℝ)+1)^2 * 1 := mul_le_mul_of_nonneg_left ih hp.le
      _ = _ := by ring

theorem b_even (m : ℕ) : b (2*m) = c m := by
  simp [b, p, c, Nat.centralBinom, pow_mul]
  ring

theorem b_odd_le (m : ℕ) : b (2*m+1) ≤ c m := by
  have hchoose : (2*m+1).choose m ≤ 2*Nat.centralBinom m := by
    rw [← Nat.choose_symm_half m, Nat.choose_succ_succ]
    have h := Nat.choose_le_centralBinom (m+1) m
    simpa [Nat.centralBinom, two_mul, add_comm] using Nat.add_le_add_left h ((2*m).choose m)
  have hc : ((2*m+1).choose m : ℝ) ≤ 2*(Nat.centralBinom m : ℝ) := by exact_mod_cast hchoose
  unfold b p c
  rw [show (2*m+1)/2 = m by omega, pow_succ, pow_mul]
  norm_num
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith [mul_le_mul_of_nonneg_right hc (show 0 ≤ (4:ℝ)^m by positivity)]

theorem c_tendsto_zero : Tendsto c atTop (𝓝 0) := by
  have hinv : Tendsto (fun m : ℕ => ((m:ℝ)+1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hs : Tendsto (fun m => (c m)^2) atTop (𝓝 0) := by
    apply squeeze_zero (fun m => sq_nonneg (c m)) _ hinv
    intro m
    rw [← one_div]
    apply (le_div_iff₀ (show 0 < (m:ℝ)+1 by positivity)).2
    simpa [mul_comm, one_div] using c_square_bound m
  simpa [Real.sqrt_sq (c_nonneg _)] using hs.sqrt

theorem b_le_c_half (n : ℕ) : b n ≤ c (n/2) := by
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · have h : n = 2*(n/2) := by omega
    nth_rw 1 [h]
    exact (b_even _).le
  · have h : n = 2*(n/2)+1 := by omega
    nth_rw 1 [h]
    exact b_odd_le _

theorem p_le_b (n k : ℕ) : p n k ≤ b n := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.choose_le_middle k n

theorem c_product (m : ℕ) :
    c m = ∏ j ∈ range m, (1 - 1/(2*((j:ℝ)+1))) := by
  induction m with
  | zero => simp [c]
  | succ m ih =>
    rw [prod_range_succ, c_recurrence, ← ih]
    have he : (2*(m:ℝ)+1)/(2*(m+1)) = 1-1/(2*((m:ℝ)+1)) := by field_simp; ring
    rw [he, mul_comm]

theorem b_sqrt_bound (n : ℕ) : b n ≤ 1 / Real.sqrt ((n/2:ℕ)+1) := by
  apply (b_le_c_half n).trans
  have hm : (0:ℝ) < (n/2:ℕ)+1 := by positivity
  have hs := c_square_bound (n/2)
  have he : Real.sqrt ((n/2:ℕ)+1)^2 = (n/2:ℕ)+1 := Real.sq_sqrt hm.le
  apply (le_div_iff₀ (Real.sqrt_pos.2 hm)).2
  nlinarith [c_nonneg (n/2), Real.sqrt_nonneg ((n/2:ℕ)+1)]

theorem b_tendsto_zero : Tendsto b atTop (𝓝 0) := by
  apply squeeze_zero (fun n => p_nonneg n (n/2)) b_le_c_half
  apply c_tendsto_zero.comp
  apply tendsto_atTop.2
  intro m
  filter_upwards [eventually_ge_atTop (2*m)] with n hn
  omega

theorem p_sum (n : ℕ) : ∑ k ∈ range (n+1), p n k = 1 := by
  simp only [p, ← sum_div]
  rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
  exact div_self (by positivity)

section Algebra
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def lazy (U : A) : A := (1/2 : ℝ) • (1+U)

theorem lazy_expansion (U : A) (n : ℕ) :
    lazy U ^ n = ∑ k ∈ range (n+1), p n k • U^k := by
  rw [lazy, smul_pow, add_comm, (Commute.one_right U).add_pow, smul_sum]
  apply sum_congr rfl
  intro k hk
  simp only [one_pow, mul_one]
  have hp : p n k = (1/2:ℝ)^n * (n.choose k : ℝ) := by
    simp [p, div_eq_mul_inv, mul_comm]
  rw [hp, mul_smul]
  congr 1
  simp [Algebra.smul_def, Nat.cast_comm]

theorem polynomial_difference (U : A) (a : ℕ → ℝ) (n : ℕ) (ha : a (n+1) = 0) :
    (∑ k ∈ range (n+1), a k • U^k) * (1-U) =
      a 0 • (1:A) + ∑ k ∈ range (n+1), (a (k+1)-a k) • U^(k+1) := by
  have ht := sum_range_sub (fun k => a k • U^k) (n+1)
  simp only [sum_sub_distrib, ha, zero_smul, pow_zero, zero_sub] at ht
  simp only [mul_sub, mul_one, sum_mul, smul_mul_assoc, ← pow_succ,
    sub_smul, sum_sub_distrib]
  rw [sub_eq_iff_eq_add] at ht
  rw [ht]
  abel

theorem lazy_power_bound (U : A) {K : ℝ} (hK : ∀ n : ℕ, ‖U^n‖ ≤ K) (n : ℕ) :
    ‖lazy U ^ n‖ ≤ K := by
  rw [lazy_expansion]
  calc
    _ ≤ ∑ k ∈ range (n+1), ‖p n k • U^k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ range (n+1), p n k * K := by
      apply sum_le_sum
      intro k hk
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (p_nonneg n k)]
      exact mul_le_mul_of_nonneg_left (hK k) (p_nonneg n k)
    _ = K := by rw [← sum_mul, p_sum, one_mul]

/-- This is the actual power-bounded operator smoothing estimate used by R003. -/
theorem smoothing_bound (U : A) {K : ℝ} (hK : ∀ n : ℕ, ‖U^n‖ ≤ K) (n : ℕ) :
    ‖lazy U ^ n * (1-U)‖ ≤ 2*K*b n := by
  rw [lazy_expansion, polynomial_difference U (p n) n (p_last_zero n)]
  calc
    _ ≤ ‖p n 0 • (1:A)‖ + ‖∑ k ∈ range (n+1), (p n (k+1)-p n k) • U^(k+1)‖ := norm_add_le _ _
    _ ≤ p n 0 * K + ∑ k ∈ range (n+1), |p n (k+1)-p n k| * K := by
      apply add_le_add
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (p_nonneg n 0)]
        exact mul_le_mul_of_nonneg_left (by simpa using hK 0) (p_nonneg n 0)
      · apply (norm_sum_le _ _).trans
        apply sum_le_sum
        intro k hk
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hK (k+1)) (abs_nonneg _)
    _ = 2*K*b n := by
      rw [← sum_mul, ← add_mul, variation]
      ring

theorem smoothing_tendsto_zero (U : A) {K : ℝ} (hK : ∀ n : ℕ, ‖U^n‖ ≤ K) :
    Tendsto (fun n => lazy U ^ n * (1-U)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (smoothing_bound U hK)
  simpa using b_tendsto_zero.const_mul (2*K)

end Algebra

end MathGauge.BinomialSmoothing
