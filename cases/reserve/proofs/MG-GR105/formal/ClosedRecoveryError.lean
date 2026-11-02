import ObservationRecovery

noncomputable section
open UniformSpace Topology Filter Set
namespace MathGauge.GR105
open MathGauge.R105
variable {E H : Type*} [AddCommGroup E] [Module ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def quotientRangeIso (A : E →ₗ[ℝ] H) : ObservationQuotient A ≃ₗᵢ[ℝ] A.range :=
  { quotient_range A with norm_map' := fun _ => rfl }

section ClosedRange
variable (A : E →ₗ[ℝ] H) (hclosed : IsClosed (A.range : Set H))
include hclosed
local instance : CompleteSpace A.range := hclosed.completeSpace_coe

def closedRecovery : H →L[ℝ] ObservationQuotient A :=
  (quotientRangeIso A).symm.toLinearIsometry.toContinuousLinearMap.comp A.range.orthogonalProjection

theorem closed_recovery_observation (y : H) :
    (quotientRangeIso A (closedRecovery A hclosed y) : H) = A.range.starProjection y := by
  simp only [closedRecovery, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem closed_recovery_lipschitz : LipschitzWith 1 (closedRecovery A hclosed) := by
  simpa [closedRecovery] using (quotientRangeIso A).symm.lipschitz.comp
    (Submodule.lipschitzWith_orthogonalProjection A.range)

theorem closed_residual_decomposition (y : H) (v : ObservationQuotient A) :
    ‖y - (quotientRangeIso A v : H)‖ ^ 2 =
      ‖y - A.range.starProjection y‖ ^ 2 + ‖closedRecovery A hclosed y - v‖ ^ 2 := by
  have hv : A.range.starProjection y - (quotientRangeIso A v : H) ∈ A.range :=
    A.range.sub_mem (Submodule.starProjection_apply_mem _ _) (quotientRangeIso A v).property
  have hi : inner ℝ (y - A.range.starProjection y)
      (A.range.starProjection y - (quotientRangeIso A v : H)) = 0 :=
    Submodule.starProjection_inner_eq_zero y _ hv
  have he := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℝ) _ _ hi
  have hn : ‖A.range.starProjection y - (quotientRangeIso A v : H)‖ =
      ‖closedRecovery A hclosed y - v‖ := by
    rw [← closed_recovery_observation A hclosed y]
    simpa only [map_sub, Submodule.coe_sub, Submodule.norm_coe] using
      (quotientRangeIso A).norm_map (closedRecovery A hclosed y - v)
  simpa only [sub_add_sub_cancel, hn, pow_two] using he

theorem closed_optimum_unique (y : H) :
    ∀ v, (∀ w : ObservationQuotient A,
      ‖y - (quotientRangeIso A v : H)‖ ≤ ‖y - (quotientRangeIso A w : H)‖) ↔
      v = closedRecovery A hclosed y := by
  intro v
  constructor
  · intro h
    have hm := h (closedRecovery A hclosed y)
    rw [closed_recovery_observation] at hm
    have hd := closed_residual_decomposition A hclosed y v
    have hz : ‖closedRecovery A hclosed y - v‖ = 0 := by
      nlinarith [norm_nonneg (y - (quotientRangeIso A v : H)),
        norm_nonneg (y - A.range.starProjection y), norm_nonneg (closedRecovery A hclosed y - v)]
    exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm
  · rintro rfl w
    rw [closed_recovery_observation]
    have hd := closed_residual_decomposition A hclosed y w
    nlinarith [sq_nonneg ‖closedRecovery A hclosed y - w‖,
      norm_nonneg (y - (quotientRangeIso A w : H)), norm_nonneg (y - A.range.starProjection y)]

theorem closed_original_attainment (y : H) : ∃ x, OriginalMinimizer A y x := by
  rw [original_attainment_iff]
  have he : observation_closure A = A.range := hclosed.submodule_topologicalClosure_eq
  simpa [he] using predicted_mem A y

theorem closed_squared_infimum (y : H) :
    (⨅ w : ObservationQuotient A, ‖y - (quotientRangeIso A w : H)‖ ^ 2) =
      ‖y - A.range.starProjection y‖ ^ 2 := by
  apply le_antisymm
  · have h := ciInf_le (f := fun w : ObservationQuotient A => ‖y - (quotientRangeIso A w : H)‖ ^ 2)
      ⟨0, by rintro _ ⟨w, rfl⟩; positivity⟩ (closedRecovery A hclosed y)
    simpa [closed_recovery_observation] using h
  · apply le_ciInf
    intro w
    rw [closed_residual_decomposition A hclosed]
    exact le_add_of_nonneg_right (sq_nonneg _)

theorem closed_error_bound (y yt : H) (v : ObservationQuotient A) (δ ε : ℝ)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hdata : ‖y - yt‖ ≤ δ)
    (hsub : ‖yt - (quotientRangeIso A v : H)‖ ^ 2 ≤
      (⨅ w : ObservationQuotient A, ‖yt - (quotientRangeIso A w : H)‖ ^ 2) + ε ^ 2) :
    ‖v - closedRecovery A hclosed y‖ ≤ ε + δ := by
  rw [closed_squared_infimum A hclosed, closed_residual_decomposition A hclosed] at hsub
  have hv : ‖v - closedRecovery A hclosed yt‖ ≤ ε := by
    rw [norm_sub_rev]
    nlinarith [norm_nonneg (closedRecovery A hclosed yt - v)]
  have hy : ‖closedRecovery A hclosed yt - closedRecovery A hclosed y‖ ≤ δ := by
    have hl := (closed_recovery_lipschitz A hclosed).dist_le_mul yt y
    simp only [dist_eq_norm, NNReal.coe_one, one_mul] at hl
    exact hl.trans (by simpa only [norm_sub_rev] using hdata)
  calc
    _ ≤ ‖v - closedRecovery A hclosed yt‖ +
      ‖closedRecovery A hclosed yt - closedRecovery A hclosed y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ε + δ := add_le_add hv hy
end ClosedRange

theorem completed_squared_infimum (A : E →ₗ[ℝ] H) (y : H) :
    (⨅ w : Completion (ObservationQuotient A), ‖y - (completion_equiv A w : H)‖ ^ 2) =
      ‖y - predicted A y‖ ^ 2 := by
  apply le_antisymm
  · have h := ciInf_le (f := fun w : Completion (ObservationQuotient A) =>
        ‖y - (completion_equiv A w : H)‖ ^ 2)
      ⟨0, by rintro _ ⟨w, rfl⟩; positivity⟩ (recovered A y)
    simpa only [recovery_observation] using h
  · apply le_ciInf
    intro w
    rw [completed_residual_decomposition]
    exact le_add_of_nonneg_right (sq_nonneg _)

theorem completed_error_bound (A : E →ₗ[ℝ] H) (y yt : H)
    (v : Completion (ObservationQuotient A)) (δ ε : ℝ)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hdata : ‖y - yt‖ ≤ δ)
    (hsub : ‖yt - (completion_equiv A v : H)‖ ^ 2 ≤
      (⨅ w : Completion (ObservationQuotient A), ‖yt - (completion_equiv A w : H)‖ ^ 2) + ε ^ 2) :
    ‖v - recovered A y‖ ≤ ε + δ := by
  rw [completed_squared_infimum, completed_residual_decomposition] at hsub
  have hv : ‖v - recovered A yt‖ ≤ ε := by
    rw [norm_sub_rev]
    nlinarith [norm_nonneg (recovered A yt - v)]
  have hy : ‖recovered A yt - recovered A y‖ ≤ δ := by
    have hl := (recovery_lipschitz A).dist_le_mul yt y
    simp only [dist_eq_norm, NNReal.coe_one, one_mul] at hl
    exact hl.trans (by simpa only [norm_sub_rev] using hdata)
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hv hy)

/-- With E=H=ℝ and A=id the exact formula is attained for all δ,ε≥0. -/
theorem both_error_constants_sharp (δ ε : ℝ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε) :
    ‖(0 : ℝ) - δ‖ = δ ∧ ‖δ - (δ + ε)‖ ^ 2 = ε ^ 2 ∧
    (⨅ w : ℝ, ‖δ - w‖ ^ 2) = 0 ∧ ‖(δ + ε) - 0‖ = ε + δ := by
  have hinf : (⨅ w : ℝ, ‖δ - w‖ ^ 2) = 0 := by
    apply le_antisymm
    · have h := ciInf_le (f := fun w : ℝ => ‖δ - w‖ ^ 2)
        ⟨0, by rintro _ ⟨w, rfl⟩; positivity⟩ δ
      simpa using h
    · apply le_ciInf; intro w; positivity
  refine ⟨?_, ?_, hinf, ?_⟩
  · simp [Real.norm_eq_abs, abs_of_nonneg hδ]
  · have : δ - (δ+ε) = -ε := by ring
    simp [this, Real.norm_eq_abs, abs_of_nonneg hε]
  · simp [Real.norm_eq_abs, abs_of_nonneg (add_nonneg hδ hε), add_comm]
end MathGauge.GR105
