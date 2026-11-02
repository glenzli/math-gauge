import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

noncomputable section

open UniformSpace Topology Filter Set

namespace MathGauge.R105

variable {E H : Type*} [AddCommGroup E] [Module ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The algebraic quotient; its norm below is the observation norm, not a quotient of a prior norm. -/
def ObservationQuotient (A : E →ₗ[ℝ] H) := E ⧸ A.ker

instance (A : E →ₗ[ℝ] H) : AddCommGroup (ObservationQuotient A) :=
  inferInstanceAs (AddCommGroup (E ⧸ A.ker))

instance (A : E →ₗ[ℝ] H) : Module ℝ (ObservationQuotient A) :=
  inferInstanceAs (Module ℝ (E ⧸ A.ker))

def quotient_range (A : E →ₗ[ℝ] H) : ObservationQuotient A ≃ₗ[ℝ] A.range :=
  A.quotKerEquivRange

instance (A : E →ₗ[ℝ] H) : NormedAddCommGroup (ObservationQuotient A) :=
  NormedAddCommGroup.induced _ _ (quotient_range A) (quotient_range A).injective

instance (A : E →ₗ[ℝ] H) : NormedSpace ℝ (ObservationQuotient A) :=
  NormedSpace.induced ℝ _ _ (quotient_range A)

def quotient_map (A : E →ₗ[ℝ] H) : E →ₗ[ℝ] ObservationQuotient A := A.ker.mkQ

@[simp] theorem quotient_range_mk (A : E →ₗ[ℝ] H) (x : E) :
    (quotient_range A (quotient_map A x) : H) = A x := by
  rfl

@[simp] theorem norm_quotient_map (A : E →ₗ[ℝ] H) (x : E) :
    ‖quotient_map A x‖ = ‖A x‖ := rfl

def observation_closure (A : E →ₗ[ℝ] H) : Submodule ℝ H := A.range.topologicalClosure

instance closure_complete (A : E →ₗ[ℝ] H) : CompleteSpace (observation_closure A) :=
  inferInstanceAs (CompleteSpace A.range.topologicalClosure)

def range_inclusion (A : E →ₗ[ℝ] H) : A.range →ₗ[ℝ] observation_closure A :=
  Submodule.inclusion A.range.le_topologicalClosure

theorem range_inclusion_dense (A : E →ₗ[ℝ] H) : DenseRange (range_inclusion A) := by
  exact (denseRange_inclusion_iff A.range.le_topologicalClosure).2 (by
    intro x hx
    exact hx)

/-- The canonical completion isometry is constructed from the algebraic quotient map. -/
def completion_equiv (A : E →ₗ[ℝ] H) [CompleteSpace H] :
    Completion (ObservationQuotient A) ≃ₗᵢ[ℝ] observation_closure A := by
  letI : CompleteSpace (observation_closure A) := closure_complete A
  exact (quotient_range A).extendOfIsometry (Eₗ := Completion (ObservationQuotient A))
    (Fₗ := observation_closure A)
    (Completion.toComplₗᵢ.toLinearMap) (range_inclusion A)
    Completion.denseRange_coe (range_inclusion_dense A)
    (by intro x; exact (Completion.norm_coe x).symm)

def realization (A : E →ₗ[ℝ] H) : Completion (ObservationQuotient A) →ₗᵢ[ℝ] H :=
  (observation_closure A).subtypeₗᵢ.comp (completion_equiv A).toLinearIsometry

theorem realization_range (A : E →ₗ[ℝ] H) :
    Set.range (realization A) = (observation_closure A : Set H) := by
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    exact (completion_equiv A q).property
  · intro hy
    obtain ⟨q, hq⟩ := (completion_equiv A).surjective ⟨y, hy⟩
    exact ⟨q, congrArg Subtype.val hq⟩

@[simp] theorem completion_equiv_mk (A : E →ₗ[ℝ] H) (x : E) :
    (completion_equiv A (quotient_map A x) : H) = A x := by
  exact congrArg Subtype.val ((quotient_range A).extendOfIsometry_eq
    Completion.toComplₗᵢ.toLinearMap (range_inclusion A)
    Completion.denseRange_coe (range_inclusion_dense A)
    (by intro q; exact (Completion.norm_coe q).symm) (quotient_map A x))

/-- Its values on original observations uniquely determine the realization. -/
theorem realization_unique (A : E →ₗ[ℝ] H)
    (g : Completion (ObservationQuotient A) → H) (hg : Continuous g)
    (h : ∀ x, g (quotient_map A x) = A x) :
    g = fun q => (completion_equiv A q : H) := by
  apply Completion.ext hg (continuous_subtype_val.comp (completion_equiv A).continuous)
  intro q
  obtain ⟨x, hx⟩ := A.ker.mkQ_surjective q
  change quotient_map A x = q at hx
  simp only [← hx, Function.comp_apply, h, completion_equiv_mk]

def recovered (A : E →ₗ[ℝ] H) : H →L[ℝ] Completion (ObservationQuotient A) :=
  (completion_equiv A).symm.toLinearIsometry.toContinuousLinearMap.comp
    (observation_closure A).orthogonalProjection

def predicted (A : E →ₗ[ℝ] H) : H →L[ℝ] H :=
  (observation_closure A).starProjection

@[simp] theorem recovery_observation (A : E →ₗ[ℝ] H) (y : H) :
    (completion_equiv A (recovered A y) : H) = predicted A y := by
  simp [recovered, predicted]

theorem predicted_mem (A : E →ₗ[ℝ] H) (y : H) :
    predicted A y ∈ observation_closure A :=
  Submodule.starProjection_apply_mem _ _

theorem residual_orthogonal (A : E →ₗ[ℝ] H) (y : H) (z : observation_closure A) :
    inner ℝ (y - predicted A y) (z : H) = 0 :=
  Submodule.starProjection_inner_eq_zero y z z.property

theorem prediction_lipschitz (A : E →ₗ[ℝ] H) : LipschitzWith 1 (predicted A) :=
  Submodule.lipschitzWith_starProjection _

theorem recovery_lipschitz (A : E →ₗ[ℝ] H) : LipschitzWith 1 (recovered A) := by
  simpa [recovered] using (completion_equiv A).symm.lipschitz.comp
    (Submodule.lipschitzWith_orthogonalProjection (observation_closure A))

/-- Pythagoras holds in the closed observation carrier. -/
theorem residual_decomposition (A : E →ₗ[ℝ] H) (y : H) (z : observation_closure A) :
    ‖y - (z : H)‖ ^ 2 = ‖y - predicted A y‖ ^ 2 + ‖predicted A y - z‖ ^ 2 := by
  have hz : predicted A y - z ∈ observation_closure A :=
    (observation_closure A).sub_mem (predicted_mem A y) z.property
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (𝕜 := ℝ) (y - predicted A y) (predicted A y - z)
    (residual_orthogonal A y ⟨_, hz⟩)
  simpa only [sub_add_sub_cancel, pow_two] using h

theorem completed_residual_decomposition (A : E →ₗ[ℝ] H) (y : H)
    (q : Completion (ObservationQuotient A)) :
    ‖y - (completion_equiv A q : H)‖ ^ 2 =
      ‖y - predicted A y‖ ^ 2 + ‖recovered A y - q‖ ^ 2 := by
  have heq : ‖predicted A y - (completion_equiv A q : H)‖ = ‖recovered A y - q‖ := by
    rw [← recovery_observation]
    simpa only [map_sub, Submodule.coe_sub, Submodule.norm_coe] using
      (completion_equiv A).norm_map (recovered A y - q)
  rw [residual_decomposition, heq]

theorem completed_minimal (A : E →ₗ[ℝ] H) (y : H)
    (q : Completion (ObservationQuotient A)) :
    ‖y - (completion_equiv A (recovered A y) : H)‖ ≤
      ‖y - (completion_equiv A q : H)‖ := by
  rw [recovery_observation]
  have h := completed_residual_decomposition A y q
  nlinarith [sq_nonneg ‖recovered A y - q‖, norm_nonneg (y - predicted A y),
    norm_nonneg (y - (completion_equiv A q : H))]

theorem completed_minimizer_unique (A : E →ₗ[ℝ] H) (y : H)
    (q : Completion (ObservationQuotient A))
    (h : ∀ r, ‖y - (completion_equiv A q : H)‖ ≤
      ‖y - (completion_equiv A r : H)‖) : q = recovered A y := by
  have hm := h (recovered A y)
  rw [recovery_observation] at hm
  have hd := completed_residual_decomposition A y q
  have hn : ‖recovered A y - q‖ = 0 := by
    nlinarith [norm_nonneg (y - predicted A y), norm_nonneg (y - (completion_equiv A q : H)),
      norm_nonneg (recovered A y - q)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm

theorem original_infimum (A : E →ₗ[ℝ] H) (y : H) :
    Metric.infDist y (Set.range A) = ‖y - predicted A y‖ := by
  rw [← Metric.infDist_closure]
  change Metric.infDist y (observation_closure A : Set H) = _
  rw [Metric.infDist_eq_iInf]
  simpa only [dist_eq_norm, predicted] using
    (Submodule.starProjection_minimal (U := observation_closure A) y).symm

theorem original_iInf (A : E →ₗ[ℝ] H) (y : H) :
    (⨅ x : E, ‖y - A x‖) = ‖y - predicted A y‖ := by
  have hg : IsGLB (Set.range fun x : E => ‖y - A x‖)
      (Metric.infDist y (Set.range A)) := by
    simpa only [← Set.range_comp, Function.comp_def, dist_eq_norm] using
      (Metric.isGLB_infDist (x := y) (s := Set.range A) ⟨A 0, ⟨0, rfl⟩⟩)
  exact hg.ciInf_eq.trans (original_infimum A y)

def OriginalMinimizer (A : E →ₗ[ℝ] H) (y : H) (x : E) : Prop :=
  ∀ z : E, ‖y - A x‖ ≤ ‖y - A z‖

theorem original_minimizer_iff (A : E →ₗ[ℝ] H) (y : H) (x : E) :
    OriginalMinimizer A y x ↔ A x = predicted A y := by
  constructor
  · intro h
    have hl : ‖y - A x‖ ≤ Metric.infDist y (Set.range A) := by
      apply (Metric.le_infDist (s := Set.range A) (x := y) ⟨A 0, ⟨0, rfl⟩⟩).mpr
      rintro z ⟨w, rfl⟩
      simpa only [dist_eq_norm] using h w
    rw [original_infimum] at hl
    have hd := residual_decomposition A y
      ⟨A x, A.range.le_topologicalClosure ⟨x, rfl⟩⟩
    have hz : ‖predicted A y - A x‖ = 0 := by
      nlinarith [norm_nonneg (y - A x), norm_nonneg (y - predicted A y),
        norm_nonneg (predicted A y - A x)]
    exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm
  · intro hx z
    rw [hx, ← original_infimum]
    simpa only [dist_eq_norm] using
      (Metric.infDist_le_dist_of_mem (s := Set.range A) (x := y) (y := A z) ⟨z, rfl⟩)

theorem original_attainment_iff (A : E →ₗ[ℝ] H) (y : H) :
    (∃ x, OriginalMinimizer A y x) ↔ predicted A y ∈ A.range := by
  simp only [original_minimizer_iff, LinearMap.mem_range]

theorem original_fiber (A : E →ₗ[ℝ] H) (y : H) {x₀ : E}
    (hx₀ : OriginalMinimizer A y x₀) (x : E) :
    OriginalMinimizer A y x ↔ x - x₀ ∈ A.ker := by
  rw [original_minimizer_iff] at hx₀ ⊢
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero, hx₀]

/-- The exact infimum-equality formulation used in the task. -/
theorem original_infimum_attained_iff (A : E →ₗ[ℝ] H) (y : H) (x : E) :
    ‖y - A x‖ = (⨅ z : E, ‖y - A z‖) ↔ A x = predicted A y := by
  constructor
  · intro h
    apply (original_minimizer_iff A y x).mp
    intro z
    rw [h]
    exact ciInf_le ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩ z
  · intro h
    rw [h, original_iInf]

theorem original_solution_set (A : E →ₗ[ℝ] H) (y : H) {x₀ : E}
    (hx₀ : A x₀ = predicted A y) :
    {x : E | ‖y - A x‖ = (⨅ z : E, ‖y - A z‖)} =
      {x : E | x - x₀ ∈ A.ker} := by
  ext x
  simp only [Set.mem_setOf_eq, original_infimum_attained_iff,
    LinearMap.mem_ker, map_sub, sub_eq_zero, hx₀]

end MathGauge.R105
