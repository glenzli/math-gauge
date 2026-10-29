import ProjectionEnergy

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open scoped ComplexConjugate
namespace MathGauge.HilbertCriteria
variable {E F G H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The degreewise inverse is built from the original differentials and their closed ranges. -/
def laplacianEquiv (A : E →L[ℂ] F) (B : F →L[ℂ] G)
    (hA : IsClosed (Set.range A)) (hB : IsClosed (Set.range B)) (hex : A.range=B.ker) :
    F ≃L[ℂ] F :=
  coerciveEquiv (laplacian A B) ((degreeBound A B hA hB)^2)⁻¹
    (inv_pos.mpr (sq_pos_of_pos (degreeBound_pos A B hA hB)))
    (degree_coercive A B hA hB hex)

theorem laplacian_inverse_bound (A : E →L[ℂ] F) (B : F →L[ℂ] G)
    (hA : IsClosed (Set.range A)) (hB : IsClosed (Set.range B)) (hex : A.range=B.ker) :
    ‖(laplacianEquiv A B hA hB hex).symm.toContinuousLinearMap‖ ≤ (degreeBound A B hA hB)^2 := by
  simpa only [inv_inv] using coercive_inverse_bound (laplacian A B) ((degreeBound A B hA hB)^2)⁻¹
    (inv_pos.mpr (sq_pos_of_pos (degreeBound_pos A B hA hB)))
    (degree_coercive A B hA hB hex)

theorem closed_reduced_exact (A : E →L[ℂ] F) (B : F →L[ℂ] G)
    (hA : IsClosed (Set.range A)) (hex : A.range.topologicalClosure=B.ker) : A.range=B.ker := by
  have he : A.range.topologicalClosure=A.range := by
    apply SetLike.coe_injective
    exact hA.closure_eq
  rwa [he] at hex

/-- Differential-Laplacian commutation is derived from the actual zero compositions. -/
theorem laplacian_commutes (A : E →L[ℂ] F) (B : F →L[ℂ] G) (C : G →L[ℂ] H)
    (hBA : B.comp A=0) (hCB : C.comp B=0) :
    B.comp (laplacian A B)=(laplacian B C).comp B := by
  ext x
  have h1 : B (A (A.adjoint x))=0 := congrArg (fun m : E →L[ℂ] G => m (A.adjoint x)) hBA
  have h2 : C (B x)=0 := congrArg (fun m : F →L[ℂ] H => m x) hCB
  simp only [laplacian,ContinuousLinearMap.comp_apply,ContinuousLinearMap.add_apply,map_add,h1,h2,map_zero,zero_add,add_zero]

/-- Every actual inverse transports the preceding commutation equation. -/
theorem inverse_commutes (A : E →L[ℂ] F) (B : F →L[ℂ] G) (C : G →L[ℂ] H)
    (hBA : B.comp A=0) (hCB : C.comp B=0)
    (U : F →L[ℂ] F) (V : G →L[ℂ] G)
    (hU : (laplacian A B).comp U=ContinuousLinearMap.id ℂ F)
    (hV : V.comp (laplacian B C)=ContinuousLinearMap.id ℂ G) : B.comp U=V.comp B := by
  ext x
  have he := congrArg (fun m : F →L[ℂ] G => V (m (U x))) (laplacian_commutes A B C hBA hCB)
  have hu : laplacian A B (U x)=x := congrArg (fun m : F →L[ℂ] F => m x) hU
  have hv : V (laplacian B C (B (U x)))=B (U x) := congrArg (fun m : G →L[ℂ] G => m (B (U x))) hV
  change V (B (laplacian A B (U x)))=V (laplacian B C (B (U x))) at he
  rw [hu,hv] at he
  exact he.symm

/-- The reference's uniform adjoint-times-inverse formula. It also applies to zero end maps. -/
theorem adjoint_inverse_contraction (A : E →L[ℂ] F) (B : F →L[ℂ] G) (C : G →L[ℂ] H)
    (hBA : B.comp A=0) (hCB : C.comp B=0)
    (U : F →L[ℂ] F) (V : G →L[ℂ] G)
    (hU : (laplacian A B).comp U=ContinuousLinearMap.id ℂ F)
    (hV : V.comp (laplacian B C)=ContinuousLinearMap.id ℂ G) :
    A.comp (A.adjoint.comp U)+(B.adjoint.comp V).comp B=ContinuousLinearMap.id ℂ F := by
  have hc := inverse_commutes A B C hBA hCB U V hU hV
  ext x
  have hx := congrArg (fun m : F →L[ℂ] G => m x) hc
  change B (U x)=V (B x) at hx
  change A (A.adjoint (U x))+B.adjoint (V (B x))=x
  rw [← hx]
  exact congrArg (fun m : F →L[ℂ] F => m x) hU

end MathGauge.HilbertCriteria
