import HilbertCriteria
import Mathlib.Analysis.Normed.Operator.Banach

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open scoped ComplexConjugate
namespace MathGauge.HilbertCriteria
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- The original operator, restricted off its kernel and into its actual range. -/
def reducedMap (A : E →L[ℂ] F) : A.kerᗮ →L[ℂ] A.range :=
  (A.comp A.kerᗮ.subtypeL).codRestrict A.range (fun x => ⟨x.val,rfl⟩)

theorem reducedMap_bijective (A : E →L[ℂ] F) : Function.Bijective (reducedMap A) := by
  constructor
  · intro x y h
    apply sub_eq_zero.mp
    apply Subtype.ext
    have hz : (x-y).val ∈ A.ker ⊓ A.kerᗮ := by
      constructor
      · change A (x.val-y.val)=0
        rw [map_sub,sub_eq_zero]
        exact congrArg Subtype.val h
      · exact (x-y).property
    simpa only [Submodule.inf_orthogonal_eq_bot] using hz
  · intro y
    obtain ⟨x,hx⟩ := y.property
    refine ⟨⟨x-A.ker.starProjection x,Submodule.sub_starProjection_mem_orthogonal x⟩, ?_⟩
    apply Subtype.ext
    change A (x-A.ker.starProjection x)=y.val
    rw [map_sub]
    have hz : A (A.ker.starProjection x)=0 := (A.ker.orthogonalProjection x).property
    rw [hz,sub_zero]
    exact hx

/-- Closedness makes this actual bijection continuously invertible by the Banach inverse theorem. -/
def reducedEquiv (A : E →L[ℂ] F) (hc : IsClosed (Set.range A)) : A.kerᗮ ≃L[ℂ] A.range := by
  letI : CompleteSpace A.range := hc.completeSpace_coe
  exact ContinuousLinearEquiv.ofBijective (reducedMap A)
    (LinearMap.ker_eq_bot.mpr (reducedMap_bijective A).1)
    (LinearMap.range_eq_top.mpr (reducedMap_bijective A).2)

def partialInverse (A : E →L[ℂ] F) (hc : IsClosed (Set.range A)) : F →L[ℂ] E := by
  letI : CompleteSpace A.range := hc.completeSpace_coe
  exact A.kerᗮ.subtypeL.comp ((reducedEquiv A hc).symm.toContinuousLinearMap.comp A.range.orthogonalProjection)

theorem partialInverse_right (A : E →L[ℂ] F) (hc : IsClosed (Set.range A)) (y : F) :
    A (partialInverse A hc y) =
      @Submodule.starProjection ℂ F _ _ _ A.range (by
        letI : CompleteSpace A.range := hc.completeSpace_coe
        infer_instance) y := by
  letI : CompleteSpace A.range := hc.completeSpace_coe
  exact congrArg Subtype.val ((reducedEquiv A hc).apply_symm_apply (A.range.orthogonalProjection y))

theorem partialInverse_left (A : E →L[ℂ] F) (hc : IsClosed (Set.range A)) (x : E) :
    partialInverse A hc (A x)=x-A.ker.starProjection x := by
  letI : CompleteSpace A.range := hc.completeSpace_coe
  let y : A.kerᗮ := ⟨x-A.ker.starProjection x,Submodule.sub_starProjection_mem_orthogonal x⟩
  have hy : reducedEquiv A hc y = A.range.orthogonalProjection (A x) := by
    apply Subtype.ext
    change A (x-A.ker.starProjection x)=A.range.starProjection (A x)
    rw [map_sub,Submodule.starProjection_eq_self_iff.mpr (show A x ∈ A.range from ⟨x,rfl⟩)]
    have hz : A (A.ker.starProjection x)=0 := (A.ker.orthogonalProjection x).property
    rw [hz,sub_zero]
  have h := congrArg (reducedEquiv A hc).symm hy
  exact (congrArg Subtype.val ((reducedEquiv A hc).symm_apply_apply y)).symm.trans
    (congrArg Subtype.val h) |>.symm

/-- Actual closed range and exactness give a bounded chain contraction at each degree. -/
theorem closed_range_contraction (A : E →L[ℂ] F) (B : F →L[ℂ] G)
    (hA : IsClosed (Set.range A)) (hB : IsClosed (Set.range B))
    (hex : A.range=B.ker) :
    A.comp (partialInverse A hA)+(partialInverse B hB).comp B=ContinuousLinearMap.id ℂ F := by
  letI : CompleteSpace A.range := hA.completeSpace_coe
  apply ContinuousLinearMap.ext
  intro x
  change A (partialInverse A hA x)+partialInverse B hB (B x)=x
  rw [partialInverse_right,partialInverse_left]
  have hp : A.range.starProjection=B.ker.starProjection := by congr 1
  rw [hp]
  abel

end MathGauge.HilbertCriteria
