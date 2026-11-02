import ErgodicQuotient
import Mathlib.Analysis.Normed.Lp.lpSpace

noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
open Filter Topology
open scoped ENNReal BigOperators

namespace MathGauge.ErgodicCounterexample
open ErgodicOperators ErgodicRecovery

abbrev E := lp (fun _ : ℕ => ℝ) 1

theorem norm_formula (x : E) : ‖x‖ = ∑' n, ‖x n‖ := by
  simpa using lp.norm_eq_tsum_rpow (show 0 < (1:ℝ≥0∞).toReal by norm_num) x

theorem norm_summable (x : E) : Summable (fun n => ‖x n‖) := by
  simpa using (lp.memℓp x).summable (show 0 < (1:ℝ≥0∞).toReal by norm_num)

def shift_linear : E →ₗ[ℝ] E where
  toFun x := ⟨fun n => match n with | 0 => 0 | k+1 => x k, by
    apply memℓp_gen
    simp only [ENNReal.toReal_one, Real.rpow_one]
    apply (summable_nat_add_iff 1).mp
    exact norm_summable x⟩
  map_add' x y := by ext n; cases n <;> simp
  map_smul' c x := by ext n; cases n <;> simp

theorem shift_norm (x : E) : ‖shift_linear x‖ = ‖x‖ := by
  rw [norm_formula, (norm_summable (shift_linear x)).tsum_eq_zero_add, norm_formula]
  change ‖(0:ℝ)‖ + ∑' n, ‖x n‖ = _
  simp

def shift : E →L[ℝ] E := shift_linear.mkContinuous 1 (by intro x; simp [shift_norm])

@[simp] theorem shift_zero (x : E) : shift x 0 = 0 := rfl
@[simp] theorem shift_succ (x : E) (n : ℕ) : shift x (n+1) = x n := rfl

theorem shift_power_norm (x : E) (n : ℕ) : ‖(shift^n) x‖ = ‖x‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    exact (shift_norm _).trans ih

theorem shift_power_bound (n : ℕ) : ‖shift^n‖ ≤ 1 := by
  apply (shift^n).opNorm_le_bound (by norm_num)
  intro x
  change ‖(shift^n) x‖ ≤ 1 * ‖x‖
  rw [shift_power_norm, one_mul]

theorem identity_power_bound (n : ℕ) : ‖(1 : E →L[ℝ] E)^n‖ ≤ 1 := by
  simpa using (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E))

theorem shift_fixed_zero {x : E} (h : shift x = x) : x = 0 := by
  have hx : ∀ n, x n = 0 := by
    intro n
    induction n with
    | zero => exact (congrArg (fun y : E => y 0) h).symm
    | succ n ih =>
      have hn := congrArg (fun y : E => y (n+1)) h
      simpa [ih] using hn.symm
  ext n
  exact hx n

def mass_linear : E →ₗ[ℝ] ℝ where
  toFun x := ∑' n, x n
  map_add' x y := by
    change (∑' n, (x n + y n)) = _
    exact (norm_summable x).of_norm.tsum_add (norm_summable y).of_norm
  map_smul' c x := by simp [tsum_mul_left]

theorem mass_bound (x : E) : ‖mass_linear x‖ ≤ ‖x‖ := by
  rw [norm_formula]
  exact norm_tsum_le_tsum_norm (norm_summable x)

def mass : E →L[ℝ] ℝ := mass_linear.mkContinuous 1 (by intro x; simpa using mass_bound x)

theorem mass_shift (x : E) : mass (shift x) = mass x := by
  change (∑' n, shift x n) = ∑' n, x n
  rw [((norm_summable (shift x)).of_norm).tsum_eq_zero_add]
  simp

theorem differences_in_mass_kernel : differences shift 1 ≤ LinearMap.ker mass.toLinearMap := by
  apply Submodule.topologicalClosure_minimal
  · apply sup_le
    · rintro y ⟨x,rfl⟩
      change mass ((1-shift) x) = 0
      simp [mass_shift]
    · rintro y ⟨x,rfl⟩
      simp
  · exact mass.isClosed_ker

def e₀ : E := lp.single 1 0 1

theorem mass_e₀ : mass e₀ = 1 := by
  change (∑' n, lp.single 1 0 (1:ℝ) n) = 1
  simp [lp.single_apply]

theorem e₀_norm : ‖e₀‖ = 1 := by simp [e₀, lp.norm_single (show (0:ℝ≥0∞) < 1 by norm_num)]

theorem e₀_not_zero_record : e₀ ∉ differences shift 1 := by
  intro he
  have hm := differences_in_mass_kernel he
  change mass e₀ = 0 at hm
  rw [mass_e₀] at hm
  norm_num at hm

theorem no_recovery_e₀ :
    (¬ ∃ z, Tendsto (fun nm => rectangle shift 1 nm e₀) atTop (𝓝 z)) ∧
    (¬ ∃ z, Tendsto (fun n => (iteration shift 1 ^ n) e₀) atTop (𝓝 z)) := by
  have hnone : ¬ ∃ z, z ∈ fixed shift 1 ∧ e₀-z ∈ differences shift 1 := by
    rintro ⟨z,hz,hy⟩
    have hz0 := shift_fixed_zero ((mem_fixed_iff shift 1 z).mp hz).1
    exact e₀_not_zero_record (by simpa [hz0] using hy)
  constructor
  · rintro ⟨z,hz⟩
    exact hnone ⟨z,(comparison shift 1 (Commute.one_right shift) shift_power_bound identity_power_bound e₀ z).1.mp hz⟩
  · rintro ⟨z,hz⟩
    exact hnone ⟨z,(comparison shift 1 (Commute.one_right shift) shift_power_bound identity_power_bound e₀ z).2.mp hz⟩

theorem rectangle_e₀_norm (nm : ℕ×ℕ) : ‖rectangle shift 1 nm e₀‖ = 1 := by
  apply le_antisymm
  · have hb := (rectangle shift 1 nm).le_opNorm e₀
    have ho := rectangle_bound shift 1 shift_power_bound identity_power_bound nm
    rw [e₀_norm, mul_one] at hb
    norm_num at ho
    exact hb.trans ho
  · have hm : mass (rectangle shift 1 nm e₀) = 1 := by
      change mass.toLinearMap (rectangle shift 1 nm e₀) = 1
      rw [rectangle, ContinuousLinearMap.mul_apply,
        avg_record shift mass.toLinearMap mass_shift,
        avg_record 1 mass.toLinearMap (by intro x; simp)]
      exact mass_e₀
    have hb := mass_bound (rectangle shift 1 nm e₀)
    change ‖mass (rectangle shift 1 nm e₀)‖ ≤ _ at hb
    rw [hm] at hb
    simpa using hb

theorem iteration_e₀_norm (n : ℕ) : ‖(iteration shift 1^n) e₀‖ = 1 := by
  apply le_antisymm
  · have hb := (iteration shift 1^n).le_opNorm e₀
    have ho := iteration_bound shift 1 (Commute.one_right shift) shift_power_bound identity_power_bound n
    rw [e₀_norm, mul_one] at hb
    norm_num at ho
    exact hb.trans ho
  · have hm : mass ((iteration shift 1^n) e₀) = 1 := by
      change mass.toLinearMap ((iteration shift 1^n) e₀) = 1
      rw [power_record (iteration shift 1) mass.toLinearMap (by
        intro x
        rw [iteration_eq_lazy, ContinuousLinearMap.mul_apply,
          lazy_record shift mass.toLinearMap mass_shift,
          lazy_record 1 mass.toLinearMap (by intro y; simp)])]
      exact mass_e₀
    have hb := mass_bound ((iteration shift 1^n) e₀)
    change ‖mass ((iteration shift 1^n) e₀)‖ ≤ _ at hb
    rw [hm] at hb
    simpa using hb

theorem shift_single (n : ℕ) : shift (lp.single 1 n (1:ℝ)) = lp.single 1 (n+1) 1 := by
  ext k
  cases k <;> simp [lp.single_apply, Pi.single_apply]

theorem shift_power_e₀ (n : ℕ) : (shift^n) e₀ = lp.single 1 n 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', ContinuousLinearMap.mul_apply, ih, shift_single]

theorem shift_power_norm_one (n : ℕ) : ‖shift^n‖ = 1 := by
  apply le_antisymm (shift_power_bound n)
  have hb := (shift^n).le_opNorm e₀
  rwa [shift_power_norm, e₀_norm, mul_one] at hb

theorem identity_power_norm_one (n : ℕ) : ‖(1:E →L[ℝ] E)^n‖ = 1 := by
  apply le_antisymm (identity_power_bound n)
  have hb := ((1:E →L[ℝ] E)^n).le_opNorm e₀
  simpa [e₀_norm] using hb

theorem iteration_shift : iteration shift 1 = BinomialSmoothing.lazy shift := by
  rw [iteration_eq_lazy]
  have he : BinomialSmoothing.lazy (1:E →L[ℝ] E) = 1 := by
    simp only [BinomialSmoothing.lazy]
    module
  rw [he, mul_one]

end MathGauge.ErgodicCounterexample
