import LaplacianInverse
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
open scoped ComplexConjugate
namespace MathGauge.HilbertCriteria
universe u
variable (H : ℕ → Type u)
variable [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)] [∀ n, CompleteSpace (H n)]
variable (d : ∀ n, H n →L[ℂ] H (n+1))
variable (hd : ∀ n, (d (n+1)).comp (d n)=0)
variable (hex : ∀ n, (d n).range.topologicalClosure=(d (n+1)).ker)

/-- Padding the finite chain by zero spaces makes s_n uniformly typed H_(n+1)→H_n.
No new exactness, inverse or convergence field is used. -/
def chainSolution (hc : ∀ n, IsClosed (Set.range (d n))) (n : ℕ) : H (n+1) →L[ℂ] H n :=
  partialInverse (d n) (hc n)

include hex in
theorem chainSolution_identity (hc : ∀ n, IsClosed (Set.range (d n))) (n : ℕ) :
    (d n).comp (chainSolution H d hc n)+(chainSolution H d hc (n+1)).comp (d (n+1))=
      ContinuousLinearMap.id ℂ (H (n+1)) :=
  closed_range_contraction (d n) (d (n+1)) (hc n) (hc (n+1))
    (closed_reduced_exact (d n) (d (n+1)) (hc n) (hex n))

def chainInverse (hc : ∀ n, IsClosed (Set.range (d n))) (n : ℕ) : H (n+1) →L[ℂ] H (n+1) :=
  (laplacianEquiv (d n) (d (n+1)) (hc n) (hc (n+1))
    (closed_reduced_exact (d n) (d (n+1)) (hc n) (hex n))).symm.toContinuousLinearMap

@[simp] theorem chainInverse_right (hc : ∀ n, IsClosed (Set.range (d n))) (n : ℕ) :
    (laplacian (d n) (d (n+1))).comp (chainInverse H d hex hc n)=ContinuousLinearMap.id ℂ (H (n+1)) := by
  ext x
  exact (laplacianEquiv (d n) (d (n+1)) (hc n) (hc (n+1))
    (closed_reduced_exact (d n) (d (n+1)) (hc n) (hex n))).apply_symm_apply x

@[simp] theorem chainInverse_left (hc : ∀ n, IsClosed (Set.range (d n))) (n : ℕ) :
    (chainInverse H d hex hc n).comp (laplacian (d n) (d (n+1)))=ContinuousLinearMap.id ℂ (H (n+1)) := by
  ext x
  exact (laplacianEquiv (d n) (d (n+1)) (hc n) (hc (n+1))
    (closed_reduced_exact (d n) (d (n+1)) (hc n) (hex n))).symm_apply_apply x

include hd in
/-- Any bounded chain contraction forces the original ranges to be closed. -/
theorem all_ranges_closed_of_contraction
    (s : ∀ n, H (n+1) →L[ℂ] H n)
    (hs : ∀ n, (d n).comp (s n)+(s (n+1)).comp (d (n+1))=ContinuousLinearMap.id ℂ (H (n+1))) :
    ∀ n, IsClosed (Set.range (d n)) := by
  intro n
  exact contraction_implies_closed_range (d n) (d (n+1)) (hd n) (s n) (s (n+1)) (hs n)

/-- A right inverse gives coercivity of the outgoing differential off its kernel, hence closed range.
This proof avoids requiring a predecessor inverse at a zero endpoint. -/
theorem closed_range_of_degree_inverse {E F G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : E →L[ℂ] F) (B : F →L[ℂ] G)
    (hBA : B.comp A=0) (U : F →L[ℂ] F)
    (hU : U.comp (laplacian A B)=ContinuousLinearMap.id ℂ F) :
    IsClosed (Set.range B) := by
  have hh : (LinearMap.range A.toLinearMap) ≤ B.ker := by
    rintro _ ⟨x,rfl⟩
    exact congrArg (fun f : E →L[ℂ] G => f x) hBA
  let L : B.kerᗮ →L[ℂ] G := B.comp B.kerᗮ.subtypeL
  have hb : ∀ x : B.kerᗮ, ‖x‖ ≤ (‖U‖*‖B.adjoint‖)*‖L x‖ := by
    intro x
    have hz : A.adjoint x.val=0 := by
      have ho : x.val ∈ A.rangeᗮ := Submodule.orthogonal_le hh x.property
      rw [A.orthogonal_range] at ho
      exact ho
    have he : U (B.adjoint (B x.val))=x.val := by
      have h := congrArg (fun f : F →L[ℂ] F => f x.val) hU
      simpa [laplacian,hz] using h
    calc
      ‖x‖ = ‖U (B.adjoint (B x.val))‖ := congrArg norm he.symm
      _ ≤ ‖U‖*‖B.adjoint (B x.val)‖ := U.le_opNorm _
      _ ≤ ‖U‖*(‖B.adjoint‖*‖B x.val‖) := mul_le_mul_of_nonneg_left (B.adjoint.le_opNorm _) (norm_nonneg _)
      _ = (‖U‖*‖B.adjoint‖)*‖L x‖ := by dsimp [L]; ring
  have hc := (L.antilipschitz_of_bound (K := ⟨‖U‖*‖B.adjoint‖,mul_nonneg (norm_nonneg _) (norm_nonneg _)⟩) hb).isClosed_range L.uniformContinuous
  have he : Set.range L=Set.range B := by
    ext y; constructor
    · rintro ⟨x,rfl⟩; exact ⟨x.val,rfl⟩
    · rintro ⟨x,rfl⟩
      refine ⟨⟨x-B.ker.starProjection x,Submodule.sub_starProjection_mem_orthogonal x⟩, ?_⟩
      change B (x-B.ker.starProjection x)=B x
      rw [map_sub,show B (B.ker.starProjection x)=0 from (B.ker.orthogonalProjection x).property,sub_zero]
  rwa [he] at hc

end MathGauge.HilbertCriteria
