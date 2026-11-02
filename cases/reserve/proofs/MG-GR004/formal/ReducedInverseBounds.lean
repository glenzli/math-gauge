import FiniteComplexTarget

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace MathGauge.HilbertCriteria
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem partialInverse_norm_le_reduced (A : E →L[ℂ] F) (hc : IsClosed (Set.range A)) :
    ‖partialInverse A hc‖ ≤ ‖(reducedEquiv A hc).symm.toContinuousLinearMap‖ := by
  letI : CompleteSpace A.range := hc.completeSpace_coe
  refine ContinuousLinearMap.opNorm_le_bound _ ?_ ?_
  · exact norm_nonneg ((reducedEquiv A hc).symm.toContinuousLinearMap)
  intro y
  change ‖(reducedEquiv A hc).symm (A.range.orthogonalProjection y)‖ ≤ _
  exact ((reducedEquiv A hc).symm.toContinuousLinearMap.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (A.range.norm_orthogonalProjection_apply_le y) (norm_nonneg _))

def reducedDegreeBound (A : E →L[ℂ] F) (B : F →L[ℂ] G)
    (hA : IsClosed (Set.range A)) (hB : IsClosed (Set.range B)) : ℝ :=
  max 1 (max ‖(reducedEquiv A hA).symm.toContinuousLinearMap‖
    ‖(reducedEquiv B hB).symm.toContinuousLinearMap‖)

theorem degreeBound_le_reduced (A : E →L[ℂ] F) (B : F →L[ℂ] G)
    (hA : IsClosed (Set.range A)) (hB : IsClosed (Set.range B)) :
    degreeBound A B hA hB ≤ reducedDegreeBound A B hA hB := by
  exact max_le_max le_rfl (max_le_max (partialInverse_norm_le_reduced A hA)
    (partialInverse_norm_le_reduced B hB))

theorem degree_coercive_reduced (A : E →L[ℂ] F) (B : F →L[ℂ] G)
    (hA : IsClosed (Set.range A)) (hB : IsClosed (Set.range B)) (hex : A.range=B.ker)
    (x : F) :
    ((reducedDegreeBound A B hA hB)^2)⁻¹*‖x‖^2 ≤ Complex.re (inner ℂ (laplacian A B x) x) := by
  apply le_trans _ (degree_coercive A B hA hB hex x)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hc : 0 < reducedDegreeBound A B hA hB :=
    lt_of_lt_of_le (degreeBound_pos A B hA hB) (degreeBound_le_reduced A B hA hB)
  apply (inv_le_inv₀ (sq_pos_of_pos hc) (sq_pos_of_pos (degreeBound_pos A B hA hB))).mpr
  nlinarith [degreeBound_le_reduced A B hA hB,degreeBound_pos A B hA hB]

theorem laplacian_inverse_reduced_bound (A : E →L[ℂ] F) (B : F →L[ℂ] G)
    (hA : IsClosed (Set.range A)) (hB : IsClosed (Set.range B)) (hex : A.range=B.ker) :
    ‖(laplacianEquiv A B hA hB hex).symm.toContinuousLinearMap‖ ≤ (reducedDegreeBound A B hA hB)^2 := by
  apply (laplacian_inverse_bound A B hA hB hex).trans
  nlinarith [degreeBound_le_reduced A B hA hB,degreeBound_pos A B hA hB]

end MathGauge.HilbertCriteria
