import FiniteGreen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace MathGauge.HilbertFinite
open HilbertCriteria
universe u
variable (H : ℕ → Type u)
variable [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)] [∀ n, CompleteSpace (H n)]
variable (d : ∀ n, H n →L[ℂ] H (n+1)) (r : ℕ)
variable [Subsingleton (H 0)] [Subsingleton (H (r+2))]

/-- This single construction ties the exact contraction and the Green inverse to
bounds by the true inverse of d on its kernel orthogonal complement. -/
theorem finite_reduced_control
    (hc : ∀ n≤r+1, IsClosed (Set.range (d n)))
    (hex : ∀ n≤r, (d n).range.topologicalClosure=(d (n+1)).ker) :
    ∃ (s : ∀ n, H (n+1) →L[ℂ] H n) (U : ∀ n, H (n+1) →L[ℂ] H (n+1)),
      s 0=0 ∧ s (r+1)=0 ∧
      (∀ n≤r, (d n).comp (s n)+(s (n+1)).comp (d (n+1))=1) ∧
      (∀ n≤r, (laplacian (d n) (d (n+1))).comp (U n)=1) ∧
      (∀ n≤r, (U n).comp (laplacian (d n) (d (n+1)))=1) ∧
      (∀ n (hn : n≤r+1), ‖s n‖≤‖(reducedEquiv (d n) (hc n hn)).symm.toContinuousLinearMap‖) ∧
      (∀ n (hn : n≤r), ‖U n‖≤(reducedDegreeBound (d n) (d (n+1))
        (hc n (by omega)) (hc (n+1) (by omega)))^2) ∧
      (∀ n (hn : n≤r), ∀ x, ((reducedDegreeBound (d n) (d (n+1))
        (hc n (by omega)) (hc (n+1) (by omega)))^2)⁻¹*‖x‖^2≤
          Complex.re (inner ℂ (laplacian (d n) (d (n+1)) x) x)) := by
  classical
  let s : ∀ n, H (n+1) →L[ℂ] H n := fun n =>
    if hn : n≤r+1 then partialInverse (d n) (hc n hn) else 0
  let U : ∀ n, H (n+1) →L[ℂ] H (n+1) := fun n =>
    if hn : n≤r then (laplacianEquiv (d n) (d (n+1)) (hc n (by omega)) (hc (n+1) (by omega))
      (closed_reduced_exact _ _ (hc n (by omega)) (hex n hn))).symm.toContinuousLinearMap else 0
  refine ⟨s,U,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · ext x; exact Subsingleton.elim _ _
  · ext x; rw [Subsingleton.elim x 0,map_zero]; rfl
  · intro n hn
    simp only [s,dif_pos (show n≤r+1 by omega),dif_pos (show n+1≤r+1 by omega)]
    exact closed_range_contraction _ _ (hc n (by omega)) (hc (n+1) (by omega))
      (closed_reduced_exact _ _ (hc n (by omega)) (hex n hn))
  · intro n hn
    simp only [U,dif_pos hn]
    apply ContinuousLinearMap.ext
    exact (laplacianEquiv (d n) (d (n+1)) (hc n (by omega)) (hc (n+1) (by omega))
      (closed_reduced_exact _ _ (hc n (by omega)) (hex n hn))).apply_symm_apply
  · intro n hn
    simp only [U,dif_pos hn]
    apply ContinuousLinearMap.ext
    exact (laplacianEquiv (d n) (d (n+1)) (hc n (by omega)) (hc (n+1) (by omega))
      (closed_reduced_exact _ _ (hc n (by omega)) (hex n hn))).symm_apply_apply
  · intro n hn
    simp only [s,dif_pos hn]
    exact partialInverse_norm_le_reduced _ _
  · intro n hn
    simp only [U,dif_pos hn]
    exact laplacian_inverse_reduced_bound _ _ _ _ _
  · intro n hn x
    exact degree_coercive_reduced _ _ _ _ (closed_reduced_exact _ _ (hc n (by omega)) (hex n hn)) x

end MathGauge.HilbertFinite
