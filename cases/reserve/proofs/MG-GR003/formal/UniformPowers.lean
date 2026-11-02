import FullRecovery

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Filter Topology
namespace MathGauge.ErgodicUniform
open ErgodicOperators ErgodicRecovery
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem operator_power_bound (U : E →L[ℝ] E) {r : ℝ} (hr : 0 ≤ r) (hU : ‖U‖ ≤ r) (n : ℕ) :
    ‖U^n‖ ≤ r^n := by
  induction n with
  | zero => simpa using (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E))
  | succ n ih =>
    rw [pow_succ,pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul ih hU (norm_nonneg _) (pow_nonneg hr n))

theorem powers_tendsto_of_some_contraction (U : E →L[ℝ] E) {K : ℝ}
    (hU : ∀ n, ‖U^n‖ ≤ K) {m : ℕ} (hm : 0 < m) (hsmall : ‖U^m‖ < 1) :
    Tendsto (fun n => U^n) atTop (𝓝 0) := by
  have hdiv : Tendsto (fun n : ℕ => n/m) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    refine eventually_atTop.mpr ⟨b*m,?_⟩
    intro n hn
    exact (Nat.le_div_iff_mul_le hm).mpr hn
  have hn (n : ℕ) : ‖U^n‖ ≤ K*‖U^m‖^(n/m) := by
    conv_lhs => rw [← Nat.mod_add_div n m]
    rw [pow_add,pow_mul]
    exact (norm_mul_le _ _).trans
      (mul_le_mul (hU (n%m)) (operator_power_bound (U^m) (norm_nonneg _) le_rfl _)
        (norm_nonneg _) ((norm_nonneg (U^0)).trans (hU 0)))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) hn
  simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (U^m)) hsmall).comp hdiv).const_mul K

variable (T S : E →L[ℝ] E) (h : Commute T S) {KT KS : ℝ}
  (hT : ∀ n : ℕ, ‖T^n‖ ≤ KT) (hS : ∀ n : ℕ, ‖S^n‖ ≤ KS)
  (hfull : domain T S = ⊤)

local instance restricted_normed : NormedAddCommGroup (differences T S) := inferInstance
local instance restricted_space : NormedSpace ℝ (differences T S) := inferInstance
local instance restricted_end_normed : NormedAddCommGroup
    (differences T S →L[ℝ] differences T S) := inferInstance

theorem iteration_geometric_bound {r : ℝ} (hr : 0 ≤ r)
    (hR : ‖restrictedIteration T S‖ ≤ r) (n : ℕ) :
    ‖iteration T S^n-fullProjection T S h hT hS hfull‖ ≤ (1+KT*KS)*r^n := by
  apply (iteration_error_bound T S h hT hS hfull n).trans
  apply mul_le_mul_of_nonneg_left (operator_power_bound _ hr hR n)
  have hk := mul_nonneg ((norm_nonneg (T^0)).trans (hT 0)) ((norm_nonneg (S^0)).trans (hS 0))
  linarith

theorem uniform_iteration_iff_restricted :
    Tendsto (fun n => iteration T S^n) atTop (𝓝 (fullProjection T S h hT hS hfull)) ↔
      Tendsto (fun n => restrictedIteration T S^n) atTop (𝓝 0) := by
  constructor
  · intro ht
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (restricted_error_bound T S h hT hS hfull)
    exact tendsto_iff_norm_sub_tendsto_zero.mp ht
  · intro ht
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (iteration_error_bound T S h hT hS hfull)
    simpa only [norm_zero,mul_zero] using ht.norm.const_mul (1+KT*KS)

theorem uniform_iteration_iff_some_power :
    Tendsto (fun n => iteration T S^n) atTop (𝓝 (fullProjection T S h hT hS hfull)) ↔
      ∃ m : ℕ, 1 ≤ m ∧ ‖restrictedIteration T S^m‖ < 1 := by
  rw [uniform_iteration_iff_restricted T S h hT hS hfull]
  constructor
  · intro ht
    have hn : Tendsto (fun n => ‖restrictedIteration T S^n‖) atTop (𝓝 0) := by
      simpa only [norm_zero] using ht.norm
    obtain ⟨m,hm,hnm⟩ := ((eventually_ge_atTop 1).and
      (hn.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)))).exists
    exact ⟨m,hm,hnm⟩
  · rintro ⟨m,hm,hsmall⟩
    exact powers_tendsto_of_some_contraction _ (restricted_power_bound T S h hT hS)
      (by omega) hsmall

end MathGauge.ErgodicUniform
