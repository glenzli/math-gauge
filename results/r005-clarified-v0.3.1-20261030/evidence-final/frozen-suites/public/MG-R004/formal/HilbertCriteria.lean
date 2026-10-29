import HilbertComplex

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped ComplexConjugate

namespace MathGauge.HilbertCriteria

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- At an actual degree of a complex, a chain contraction removes the closure bar. -/
theorem range_eq_kernel_of_contraction (A : E →L[ℂ] F) (B : F →L[ℂ] G)
    (hBA : B.comp A = 0) (s : F →L[ℂ] E) (t : G →L[ℂ] F)
    (h : A.comp s + t.comp B = ContinuousLinearMap.id ℂ F) :
    LinearMap.range A.toLinearMap = LinearMap.ker B.toLinearMap := by
  apply le_antisymm
  · rintro x ⟨u, rfl⟩
    exact congrArg (fun C : E →L[ℂ] G => C u) hBA
  · intro x hx
    refine ⟨s x, ?_⟩
    have he := congrArg (fun C : F →L[ℂ] F => C x) h
    have hb : B x = 0 := hx
    simpa [hb] using he

theorem contraction_implies_closed_range (A : E →L[ℂ] F) (B : F →L[ℂ] G)
    (hBA : B.comp A = 0) (s : F →L[ℂ] E) (t : G →L[ℂ] F)
    (h : A.comp s + t.comp B = ContinuousLinearMap.id ℂ F) :
    IsClosed (Set.range A) := by
  change IsClosed (LinearMap.range A.toLinearMap : Set F)
  rw [range_eq_kernel_of_contraction A B hBA s t h]
  exact B.isClosed_ker

def laplacian (A : E →L[ℂ] F) (B : F →L[ℂ] G) : F →L[ℂ] F :=
  A.comp A.adjoint + B.adjoint.comp B

theorem laplacian_energy (A : E →L[ℂ] F) (B : F →L[ℂ] G) (x : F) :
    Complex.re (inner ℂ ((laplacian A B) x) x) =
      ‖A.adjoint x‖^2 + ‖B x‖^2 := by
  simp only [laplacian, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    inner_add_left, map_add]
  rw [← A.adjoint_inner_right, B.adjoint_inner_left]
  simp [← Complex.ofReal_pow]

/-- The zero kernel in the reference uses reduced exactness, with its norm closure intact. -/
theorem laplacian_injective_of_reduced_exactness (A : E →L[ℂ] F) (B : F →L[ℂ] G)
    (hex : (LinearMap.range A.toLinearMap).topologicalClosure =
      LinearMap.ker B.toLinearMap) : Function.Injective (laplacian A B) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm
  · intro x hx
    have he := laplacian_energy A B x
    have hz : laplacian A B x = 0 := hx
    rw [hz, inner_zero_left, Complex.zero_re] at he
    have hA : A.adjoint x = 0 := by
      apply norm_eq_zero.mp
      nlinarith [sq_nonneg ‖A.adjoint x‖, sq_nonneg ‖B x‖, norm_nonneg (A.adjoint x)]
    have hB : B x = 0 := by
      apply norm_eq_zero.mp
      nlinarith [sq_nonneg ‖A.adjoint x‖, sq_nonneg ‖B x‖, norm_nonneg (B x)]
    have hx1 : x ∈ (LinearMap.range A.toLinearMap).topologicalClosure := by
      rw [hex]
      exact hB
    have hx2 : x ∈ (LinearMap.range A.toLinearMap).topologicalClosureᗮ := by
      rw [Submodule.orthogonal_closure, A.orthogonal_range]
      exact hA
    have hx3 : x ∈ (LinearMap.range A.toLinearMap).topologicalClosure ⊓
        (LinearMap.range A.toLinearMap).topologicalClosureᗮ := ⟨hx1, hx2⟩
    simpa only [Submodule.inf_orthogonal_eq_bot] using hx3
  · exact bot_le

theorem right_inverse_is_inverse (A : E →L[ℂ] F) (B : F →L[ℂ] G)
    (hex : (LinearMap.range A.toLinearMap).topologicalClosure =
      LinearMap.ker B.toLinearMap)
    (U : F →L[ℂ] F) (hu : (laplacian A B).comp U = ContinuousLinearMap.id ℂ F) :
    U.comp (laplacian A B) = ContinuousLinearMap.id ℂ F := by
  apply ContinuousLinearMap.ext
  intro x
  apply laplacian_injective_of_reduced_exactness A B hex
  exact congrArg (fun C : F →L[ℂ] F => C (laplacian A B x)) hu

end MathGauge.HilbertCriteria
