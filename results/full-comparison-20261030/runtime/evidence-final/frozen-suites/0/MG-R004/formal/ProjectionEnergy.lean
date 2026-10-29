import CoerciveInverse

noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
open scoped ComplexConjugate
namespace MathGauge.HilbertCriteria
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

def degreeBound (A : E →L[ℂ] F) (B : F →L[ℂ] G)
    (hA : IsClosed (Set.range A)) (hB : IsClosed (Set.range B)) : ℝ :=
  max 1 (max ‖partialInverse A hA‖ ‖partialInverse B hB‖)

theorem degreeBound_pos (A : E →L[ℂ] F) (B : F →L[ℂ] G)
    (hA : IsClosed (Set.range A)) (hB : IsClosed (Set.range B)) :
    0<degreeBound A B hA hB := lt_of_lt_of_le zero_lt_one (le_max_left _ _)

/-- The lower bound in the reference, on the actual Hilbert complex at a degree. -/
theorem degree_coercive (A : E →L[ℂ] F) (B : F →L[ℂ] G)
    (hA : IsClosed (Set.range A)) (hB : IsClosed (Set.range B)) (hex : A.range=B.ker)
    (x : F) :
    ((degreeBound A B hA hB)^2)⁻¹*‖x‖^2 ≤ Complex.re (inner ℂ (laplacian A B x) x) := by
  letI : CompleteSpace A.range := hA.completeSpace_coe
  let z := B.ker.starProjection x
  let u := x-z
  let M := degreeBound A B hA hB
  have hM : 0<M := degreeBound_pos A B hA hB
  have hsM : ‖partialInverse A hA‖ ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have htM : ‖partialInverse B hB‖ ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have hzker : z ∈ B.ker := (B.ker.orthogonalProjection x).property
  have hurange : u ∈ A.rangeᗮ := by
    rw [hex]
    exact Submodule.sub_starProjection_mem_orthogonal x
  have hau : A.adjoint u=0 := by
    rw [A.orthogonal_range] at hurange
    exact hurange
  have haz : A.adjoint z=A.adjoint x := by
    have h : x=z+u := by dsimp [u]; abel
    rw [h,map_add,hau,add_zero]
  have hs : A (partialInverse A hA z)=z := by
    rw [partialInverse_right]
    apply Submodule.starProjection_eq_self_iff.mpr
    rwa [hex]
  have hnz : ‖z‖ ≤ ‖partialInverse A hA‖*‖A.adjoint x‖ := by
    have he : ‖z‖^2 ≤ ‖partialInverse A hA‖*‖z‖*‖A.adjoint x‖ := by
      calc
        ‖z‖^2 = ‖inner ℂ z z‖ := by simp
        _ = ‖inner ℂ (partialInverse A hA z) (A.adjoint z)‖ := by rw [← hs,← A.adjoint_inner_right]; rw [hs]
        _ ≤ ‖partialInverse A hA z‖*‖A.adjoint z‖ := norm_inner_le_norm _ _
        _ ≤ (‖partialInverse A hA‖*‖z‖)*‖A.adjoint x‖ := by rw [haz]; gcongr; exact (partialInverse A hA).le_opNorm z
    by_cases hz : ‖z‖=0
    · rw [hz]; positivity
    · have hp : 0<‖z‖ := lt_of_le_of_ne (norm_nonneg z) (Ne.symm hz)
      nlinarith
  have hnu : ‖u‖ ≤ ‖partialInverse B hB‖*‖B x‖ := by
    rw [show u=partialInverse B hB (B x) from (partialInverse_left B hB x).symm]
    exact (partialInverse B hB).le_opNorm _
  have hnz' : ‖z‖ ≤ M*‖A.adjoint x‖ := hnz.trans (mul_le_mul_of_nonneg_right hsM (norm_nonneg _))
  have hnu' : ‖u‖ ≤ M*‖B x‖ := hnu.trans (mul_le_mul_of_nonneg_right htM (norm_nonneg _))
  have hnorm : ‖x‖^2=‖z‖^2+‖u‖^2 := by
    have h := Submodule.norm_sq_eq_add_norm_sq_starProjection x B.ker
    simpa only [Submodule.starProjection_orthogonal,ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply] using h
  rw [laplacian_energy]
  have he : ‖x‖^2 ≤ M^2*(‖A.adjoint x‖^2+‖B x‖^2) := by
    have hz2 : ‖z‖^2 ≤ (M*‖A.adjoint x‖)^2 := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr hnz'
    have hu2 : ‖u‖^2 ≤ (M*‖B x‖)^2 := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr hnu'
    nlinarith
  exact (inv_mul_le_iff₀ (sq_pos_of_pos hM)).mpr he

end MathGauge.HilbertCriteria
