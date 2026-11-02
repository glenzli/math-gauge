import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.Tactic

noncomputable section
open Filter Topology
open scoped ZeroAtInfty
namespace MathGauge.SpectralApproximation
abbrev E := C₀(ℕ,ℂ)

theorem norm_le_of_coords {x : E} {C : ℝ} (hC : 0≤C) (h : ∀ k, ‖x k‖≤C) : ‖x‖≤C := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact (BoundedContinuousFunction.norm_le hC).2 h

theorem coord_le (x : E) (k : ℕ) : ‖x k‖≤‖x‖ :=
  BoundedContinuousFunction.norm_coe_le_norm x.toBCF k

theorem zero_limit (x : E) : Tendsto (fun k => x k) atTop (𝓝 0) := by
  simpa only [cocompact_eq_atTop] using x.zero_at_infty'

def shift_value (x : E) : E where
  toFun k := match k with | 0 => 0 | n+1 => x n
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [cocompact_eq_atTop]
    apply (tendsto_add_atTop_iff_nat 1).1
    simpa using zero_limit x

@[simp] theorem shift_zero (x : E) : shift_value x 0=0 := rfl
@[simp] theorem shift_succ (x : E) (k : ℕ) : shift_value x (k+1)=x k := rfl

theorem shift_value_bound (x : E) : ‖shift_value x‖≤‖x‖ := by
  apply norm_le_of_coords (norm_nonneg _)
  intro k
  cases k with
  | zero => simp
  | succ k => exact coord_le x k

def shift : E →L[ℂ] E :=
  (show E →ₗ[ℂ] E from {
    toFun := shift_value
    map_add' := by intro x y; ext k; cases k <;> simp [shift_value]
    map_smul' := by intro a x; ext k; cases k <;> simp [shift_value] }).mkContinuous 1
    (by intro x; simpa using shift_value_bound x)

@[simp] theorem shift_apply_zero (x : E) : shift x 0=0 := rfl
@[simp] theorem shift_apply_succ (x : E) (k : ℕ) : shift x (k+1)=x k := rfl

def truncated_value (n : ℕ) (x : E) : E where
  toFun k := match k with | 0 => 0 | j+1 => if j+1<n then x j else 0
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [cocompact_eq_atTop]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n] with k hk
    cases k with
    | zero => rfl
    | succ j => simp [show ¬j+1<n by omega]

@[simp] theorem truncated_zero (n : ℕ) (x : E) : truncated_value n x 0=0 := rfl
@[simp] theorem truncated_succ (n : ℕ) (x : E) (j : ℕ) :
    truncated_value n x (j+1) = if j+1<n then x j else 0 := rfl

theorem truncated_value_bound (n : ℕ) (x : E) : ‖truncated_value n x‖≤‖x‖ := by
  apply norm_le_of_coords (norm_nonneg _)
  intro k
  cases k with
  | zero => simp
  | succ j => simp only [truncated_succ]; split_ifs <;> simp [coord_le]

def truncated (n : ℕ) : E →L[ℂ] E :=
  (show E →ₗ[ℂ] E from {
    toFun := truncated_value n
    map_add' := by
      intro x y; ext k; cases k with
      | zero => simp [truncated_value]
      | succ j =>
        change (if j+1<n then x j+y j else 0) =
          (if j+1<n then x j else 0)+(if j+1<n then y j else 0)
        split_ifs <;> simp
    map_smul' := by
      intro a x; ext k; cases k with
      | zero => simp [truncated_value]
      | succ j =>
        change (if j+1<n then a*x j else 0) = a*(if j+1<n then x j else 0)
        split_ifs <;> simp }).mkContinuous 1
    (by intro x; simpa using truncated_value_bound n x)

@[simp] theorem truncated_apply_zero (n : ℕ) (x : E) : truncated n x 0=0 := rfl
@[simp] theorem truncated_apply_succ (n : ℕ) (x : E) (j : ℕ) :
    truncated n x (j+1) = if j+1<n then x j else 0 := rfl

theorem shift_norm_le : ‖shift‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simpa using shift_value_bound x

theorem truncated_norm_le (n : ℕ) : ‖truncated n‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simpa using truncated_value_bound n x

theorem truncated_strong (x : E) : Tendsto (fun n => truncated n x) atTop (𝓝 (shift x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N,hN⟩ := (Metric.tendsto_atTop.1 (zero_limit x)) (ε/2) (half_pos hε)
  refine ⟨N+1,?_⟩
  intro n hn
  rw [dist_eq_norm]
  have hb : ‖truncated n x-shift x‖≤ε/2 := by
    apply norm_le_of_coords (by positivity)
    intro k
    cases k with
    | zero => simp; positivity
    | succ j =>
      change ‖(if j+1<n then x j else 0)-x j‖≤ε/2
      split_ifs with hj
      · simp; positivity
      · have hjN : N≤j := by omega
        simpa [dist_eq_norm] using (hN j hjN).le
  linarith

end MathGauge.SpectralApproximation
