import NoisyProjection

noncomputable section
open Filter Topology
namespace MathGauge.SharpNoise
open ErgodicOperators ErgodicRecovery OrthogonalComponents
abbrev T : ℝ →L[ℝ] ℝ := 1
abbrev S : ℝ →L[ℝ] ℝ := 0

theorem legal : IsStarProjection T ∧ IsStarProjection S ∧ Commute T S :=
  ⟨IsStarProjection.one _,IsStarProjection.zero _,Commute.zero_right _⟩

theorem iteration_apply (x : ℝ) : iteration T S x = x/2 := by
  simp only [iteration,T,S,mul_one,add_zero,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.one_apply,smul_eq_mul]
  ring

def state (ε : ℝ) (n : ℕ) : ℝ := 2*ε*(1-(1/2:ℝ)^n)

theorem state_zero (ε : ℝ) : state ε 0 = 0 := by simp [state]

theorem state_recurrence (ε : ℝ) (n : ℕ) :
    state ε (n+1) = iteration T S (state ε n)+ε := by
  rw [iteration_apply]
  simp only [state,pow_succ]
  ring

theorem errors_in_difference (ε : ℝ) : ε ∈ differences T S := by
  rw [differences_eq_kernel legal.1 legal.2.1 legal.2.2]
  simp [T,S]

theorem exact_error {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    ‖state ε n-(T*S) (state ε 0)‖ = 2*ε*(1-(1/2:ℝ)^n) := by
  have hp : (1/2:ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  simp only [T,S,mul_zero,ContinuousLinearMap.zero_apply,sub_zero,state,Real.norm_eq_abs]
  rw [abs_of_nonneg (mul_nonneg (by positivity) (by linarith))]

theorem constant_two_minimal (c : ℝ)
    (hc : ∀ n, ‖state 1 n-(T*S) (state 1 0)‖ ≤ c*(1-(1/2:ℝ)^n)) : 2 ≤ c := by
  have h := hc 1
  rw [exact_error (by norm_num)] at h
  norm_num at h
  linarith

theorem state_limit (ε : ℝ) : Tendsto (state ε) atTop (𝓝 (2*ε)) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num : (1/2:ℝ)<1)
  unfold state
  simpa using (hp.const_sub 1).const_mul (2*ε)

theorem no_smaller_uniform_noise_constant (c : ℝ) (hc : c < 2) :
    ∃ n, ‖state 1 n‖ > c := by
  have ht : Tendsto (fun n => ‖state 1 n‖) atTop (𝓝 (2:ℝ)) := by
    simpa using (state_limit 1).norm
  obtain ⟨n,hn⟩ := (ht.eventually (lt_mem_nhds hc)).exists
  exact ⟨n,hn⟩

end MathGauge.SharpNoise
