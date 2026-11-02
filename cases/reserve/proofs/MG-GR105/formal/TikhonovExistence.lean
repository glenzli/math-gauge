import ObservationRecovery
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section
open Topology Filter
open scoped InnerProductSpace
namespace MathGauge.GR105
open MathGauge.R105
variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def normalOperator (A : E →L[ℝ] H) (lam : ℝ) : E →L[ℝ] E :=
  A.adjoint.comp A + lam • ContinuousLinearMap.id ℝ E

def normalBilin (A : E →L[ℝ] H) (lam : ℝ) : E →L[ℝ] E →L[ℝ] ℝ :=
  (innerSL ℝ).comp (normalOperator A lam)

theorem normal_inner (A : E →L[ℝ] H) (lam : ℝ) (x v : E) :
    ⟪normalOperator A lam x, v⟫_ℝ = ⟪A x, A v⟫_ℝ + lam * ⟪x, v⟫_ℝ := by
  simp only [normalOperator, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, inner_add_left,
    real_inner_smul_left, A.adjoint_inner_left]

theorem normal_coercive (A : E →L[ℝ] H) {lam : ℝ} (hlam : 0 < lam) :
    IsCoercive (normalBilin A lam) := by
  refine ⟨lam, hlam, ?_⟩
  intro x
  change lam * ‖x‖ * ‖x‖ ≤ ⟪normalOperator A lam x, x⟫_ℝ
  rw [normal_inner, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  nlinarith [sq_nonneg ‖A x‖]

def regularEquiv (A : E →L[ℝ] H) {lam : ℝ} (hlam : 0 < lam) : E ≃L[ℝ] E :=
  (normal_coercive A hlam).continuousLinearEquivOfBilin

theorem regularEquiv_apply (A : E →L[ℝ] H) {lam : ℝ} (hlam : 0 < lam) (x : E) :
    regularEquiv A hlam x = normalOperator A lam x := by
  apply ext_inner_right ℝ
  intro v
  exact (normal_coercive A hlam).continuousLinearEquivOfBilin_apply x v

def regularized (A : E →L[ℝ] H) (y : H) (lam : ℝ) : E :=
  if hlam : 0 < lam then (regularEquiv A hlam).symm (A.adjoint y) else 0

theorem regularized_normal (A : E →L[ℝ] H) (y : H) {lam : ℝ} (hlam : 0 < lam) :
    normalOperator A lam (regularized A y lam) = A.adjoint y := by
  rw [regularized, dif_pos hlam, ← regularEquiv_apply A hlam]
  exact (regularEquiv A hlam).apply_symm_apply _

def objective (A : E →L[ℝ] H) (y : H) (lam : ℝ) (x : E) : ℝ :=
  ‖y - A x‖ ^ 2 + lam * ‖x‖ ^ 2

theorem regularized_variation (A : E →L[ℝ] H) (y : H) {lam : ℝ} (hlam : 0 < lam) (d : E) :
    ⟪A (regularized A y lam), A d⟫_ℝ + lam * ⟪regularized A y lam, d⟫_ℝ = ⟪y, A d⟫_ℝ := by
  rw [← normal_inner, regularized_normal A y hlam, A.adjoint_inner_left]

theorem objective_decomposition (A : E →L[ℝ] H) (y : H) {lam : ℝ}
    (hlam : 0 < lam) (x : E) :
    objective A y lam x = objective A y lam (regularized A y lam) +
      ‖A (x - regularized A y lam)‖ ^ 2 + lam * ‖x - regularized A y lam‖ ^ 2 := by
  let u := regularized A y lam
  have h := regularized_variation A y hlam (x-u)
  change ⟪A u, A (x-u)⟫_ℝ + lam * ⟪u,x-u⟫_ℝ = ⟪y,A (x-u)⟫_ℝ at h
  simp only [map_sub, inner_sub_right, real_inner_self_eq_norm_sq] at h
  simp only [objective, map_sub, norm_sub_sq_real]
  rw [real_inner_comm u x, real_inner_comm (A u) (A x)]
  nlinarith

theorem regularized_minimal (A : E →L[ℝ] H) (y : H) {lam : ℝ} (hlam : 0 < lam) (x : E) :
    objective A y lam (regularized A y lam) ≤ objective A y lam x := by
  rw [objective_decomposition A y hlam x]
  nlinarith [sq_nonneg ‖A (x - regularized A y lam)‖, mul_nonneg hlam.le (sq_nonneg ‖x - regularized A y lam‖)]

theorem regularized_unique (A : E →L[ℝ] H) (y : H) {lam : ℝ} (hlam : 0 < lam) (x : E)
    (hx : ∀ z, objective A y lam x ≤ objective A y lam z) : x = regularized A y lam := by
  have he := hx (regularized A y lam)
  rw [objective_decomposition A y hlam x] at he
  have hs : lam * ‖x - regularized A y lam‖ ^ 2 ≤ lam * 0 := by
    nlinarith [sq_nonneg ‖A (x - regularized A y lam)‖]
  have hs' : ‖x - regularized A y lam‖ ^ 2 ≤ 0 := (mul_le_mul_iff_right₀ hlam).mp hs
  have hz : ‖x - regularized A y lam‖ = 0 := by
    nlinarith [norm_nonneg (x - regularized A y lam)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

theorem observation_error_comparison (A : E →L[ℝ] H) (y : H) {lam : ℝ}
    (hlam : 0 < lam) (x : E) :
    ‖predicted A.toLinearMap y - A (regularized A y lam)‖ ^ 2 ≤
      ‖predicted A.toLinearMap y - A x‖ ^ 2 + lam * ‖x‖ ^ 2 := by
  have hm := regularized_minimal A y hlam x
  have hu := residual_decomposition A.toLinearMap y
    ⟨A (regularized A y lam), A.range.le_topologicalClosure ⟨_, rfl⟩⟩
  have hx := residual_decomposition A.toLinearMap y ⟨A x, A.range.le_topologicalClosure ⟨x,rfl⟩⟩
  change ‖y - A (regularized A y lam)‖ ^ 2 = _ at hu
  change ‖y - A x‖ ^ 2 = _ at hx
  dsimp only [objective] at hm
  nlinarith [mul_nonneg hlam.le (sq_nonneg ‖regularized A y lam‖)]

theorem regularized_norm_le_solution (A : E →L[ℝ] H) (y : H) {lam : ℝ}
    (hlam : 0 < lam) (z : E) (hz : A z = predicted A.toLinearMap y) :
    ‖regularized A y lam‖ ≤ ‖z‖ := by
  have hm := regularized_minimal A y hlam z
  have hu := residual_decomposition A.toLinearMap y
    ⟨A (regularized A y lam), A.range.le_topologicalClosure ⟨_, rfl⟩⟩
  change ‖y - A (regularized A y lam)‖ ^ 2 = _ at hu
  dsimp only [objective] at hm
  rw [hz] at hm
  have hs : lam * ‖regularized A y lam‖ ^ 2 ≤ lam * ‖z‖ ^ 2 := by
    nlinarith [sq_nonneg ‖predicted A.toLinearMap y - A (regularized A y lam)‖]
  have hs' := (mul_le_mul_iff_right₀ hlam).mp hs
  nlinarith [norm_nonneg (regularized A y lam), norm_nonneg z]
end MathGauge.GR105
