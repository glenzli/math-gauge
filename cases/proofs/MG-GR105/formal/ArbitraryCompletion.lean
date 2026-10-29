import ClosedRecoveryError

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Topology UniformSpace
namespace MathGauge.GR105
open MathGauge.R105
variable {E H : Type*} [AddCommGroup E] [Module ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {Qhat : Type*} [NormedAddCommGroup Qhat] [NormedSpace ℝ Qhat] [CompleteSpace Qhat]

local instance (A : E →ₗ[ℝ] H) : CompleteSpace (observation_closure A) :=
  closure_complete A

/-- The construction also works for any supplied completion and its dense linear isometry. -/
def arbitraryCompletionEquiv (A : E →ₗ[ℝ] H)
    (i : ObservationQuotient A →ₗᵢ[ℝ] Qhat) (hi : DenseRange i) :
    Qhat ≃ₗᵢ[ℝ] observation_closure A := by
  letI : CompleteSpace (observation_closure A) := closure_complete A
  exact (quotient_range A).extendOfIsometry (Eₗ := Qhat) (Fₗ := observation_closure A)
    i.toLinearMap (range_inclusion A)
    hi (range_inclusion_dense A) (by intro q; exact (i.norm_map q).symm)

theorem arbitraryCompletion_mk (A : E →ₗ[ℝ] H)
    (i : ObservationQuotient A →ₗᵢ[ℝ] Qhat) (hi : DenseRange i) (x : E) :
    (arbitraryCompletionEquiv A i hi (i (quotient_map A x)) : H) = A x := by
  letI : CompleteSpace (observation_closure A) := closure_complete A
  exact congrArg Subtype.val ((quotient_range A).extendOfIsometry_eq
    (Eₗ := Qhat) (Fₗ := observation_closure A)
    i.toLinearMap (range_inclusion A) hi (range_inclusion_dense A)
    (by intro q; exact (i.norm_map q).symm) (quotient_map A x))

theorem arbitraryCompletion_unique (A : E →ₗ[ℝ] H)
    (i : ObservationQuotient A →ₗᵢ[ℝ] Qhat) (hi : DenseRange i)
    (g : Qhat → H) (hg : Continuous g) (h : ∀ x, g (i (quotient_map A x)) = A x) :
    g = fun q => (arbitraryCompletionEquiv A i hi q : H) := by
  apply hi.equalizer hg (continuous_subtype_val.comp (arbitraryCompletionEquiv A i hi).continuous)
  funext q
  obtain ⟨x, rfl⟩ := A.ker.mkQ_surjective q
  exact (h x).trans (arbitraryCompletion_mk A i hi x).symm

theorem identity_closedRecovery (hclosed : IsClosed ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).range : Set ℝ)) (y : ℝ) :
    closedRecovery (LinearMap.id : ℝ →ₗ[ℝ] ℝ) hclosed y = quotient_map LinearMap.id y := by
  apply (quotientRangeIso (LinearMap.id : ℝ →ₗ[ℝ] ℝ)).injective
  apply Subtype.ext
  rw [closed_recovery_observation]
  exact Submodule.starProjection_eq_self_iff.mpr ⟨y, rfl⟩

/-- The scalar sharpness calculation is literally the identity observation problem
    after its canonical quotient isometry, not an unrelated scalar inequality. -/
theorem identity_sharp_error (δ ε : ℝ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hclosed : IsClosed ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).range : Set ℝ)) :
    ‖quotient_map (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (δ+ε) - closedRecovery LinearMap.id hclosed 0‖ = ε+δ := by
  rw [identity_closedRecovery, ← map_sub, norm_quotient_map]
  simpa using (both_error_constants_sharp δ ε hδ hε).2.2.2
end MathGauge.GR105
