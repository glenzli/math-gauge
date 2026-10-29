import ErgodicCounterexample

noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
open Filter Topology Finset
open scoped BigOperators

namespace MathGauge.ErgodicCounterexample
open ErgodicOperators BinomialSmoothing

theorem iteration_coordinate (n k : ℕ) : (iteration shift 1^n) e₀ k = p n k := by
  rw [iteration_shift, lazy_expansion]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    shift_power_e₀, lp.coeFn_sum, lp.coeFn_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [lp.single_apply, Pi.single_apply]
  by_cases hk : k < n+1
  · rw [sum_eq_single k]
    · simp
    · intro j hj hjk
      simp [Ne.symm hjk]
    · intro hk'
      exact (hk' (mem_range.mpr hk)).elim
  · have hkn : n < k := by omega
    have hp : p n k = 0 := by simp [p, Nat.choose_eq_zero_of_lt hkn]
    rw [hp]
    apply sum_eq_zero
    intro j hj
    have hjk : j ≠ k := by have := mem_range.mp hj; omega
    simp [Ne.symm hjk]

theorem iteration_coordinate_nonneg (n k : ℕ) : 0 ≤ (iteration shift 1^n) e₀ k := by
  rw [iteration_coordinate]
  exact p_nonneg n k

theorem iteration_coordinate_decay (k : ℕ) :
    Tendsto (fun n => (iteration shift 1^n) e₀ k) atTop (𝓝 0) := by
  simp only [iteration_coordinate]
  exact squeeze_zero (fun n => p_nonneg n k) (fun n => p_le_b n k) b_tendsto_zero

theorem rectangle_coordinate (nm : ℕ×ℕ) (k : ℕ) :
    rectangle shift 1 nm e₀ k = if k < nm.1+1 then ((nm.1:ℝ)+1)⁻¹ else 0 := by
  rw [rectangle, ContinuousLinearMap.mul_apply, ErgodicRecovery.avg_fixed 1 (by simp)]
  simp only [avg, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    shift_power_e₀, lp.coeFn_smul, lp.coeFn_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [lp.single_apply, Pi.single_apply]
  by_cases hk : k < nm.1+1
  · rw [if_pos hk, sum_eq_single k]
    · simp
    · intro j hj hjk
      simp [Ne.symm hjk]
    · intro hk'
      exact (hk' (mem_range.mpr hk)).elim
  · rw [if_neg hk]
    have he : ∑ j ∈ range (nm.1+1), (if k = j then (1:ℝ) else 0) = 0 := by
      apply sum_eq_zero
      intro j hj
      have hjk : j ≠ k := by have := mem_range.mp hj; omega
      simp [Ne.symm hjk]
    rw [he,mul_zero]

theorem rectangle_coordinate_decay (k : ℕ) :
    Tendsto (fun nm => rectangle shift 1 nm e₀ k) atTop (𝓝 0) := by
  have hf : Tendsto (Prod.fst : ℕ×ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hi : Tendsto (fun n : ℕ => ((n:ℝ)+1)⁻¹) atTop (𝓝 0) := by
    simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => (1:ℝ)/(n+1)) atTop (𝓝 0))
  apply (hi.comp hf).congr'
  filter_upwards [hf.eventually (eventually_ge_atTop k)] with nm hnm
  rw [rectangle_coordinate, if_pos (by omega)]
  rfl

end MathGauge.ErgodicCounterexample
