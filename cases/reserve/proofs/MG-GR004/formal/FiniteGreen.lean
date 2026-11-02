import RegularLaplacian
import ReducedInverseBounds

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
open Filter Topology
namespace MathGauge.HilbertFinite
open HilbertCriteria HilbertPerturbation HilbertRegular
universe u
variable (H : ℕ → Type u)
variable [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)] [∀ n, CompleteSpace (H n)]
variable (d : ∀ n, H n →L[ℂ] H (n+1)) (r : ℕ)
variable [Subsingleton (H 0)] [Subsingleton (H (r+2))]

def adjointSolution (U : ∀ n, H (n+1) →L[ℂ] H (n+1)) (n : ℕ) : H (n+1) →L[ℂ] H n :=
  (d n).adjoint.comp (U n)

theorem adjoint_endpoints (U : ∀ n, H (n+1) →L[ℂ] H (n+1)) :
    adjointSolution H d U 0=0 ∧ adjointSolution H d U (r+1)=0 := by
  constructor
  · ext x; exact Subsingleton.elim _ _
  · ext x; rw [Subsingleton.elim x 0,map_zero]; rfl

theorem finite_adjoint_formula
    (hd : ∀ n≤r, (d (n+1)).comp (d n)=0)
    (U : ∀ n, H (n+1) →L[ℂ] H (n+1))
    (hr : ∀ n≤r, (laplacian (d n) (d (n+1))).comp (U n)=1)
    (hl : ∀ n≤r, (U n).comp (laplacian (d n) (d (n+1)))=1) :
    ∀ n≤r, (d n).comp (adjointSolution H d U n)+
      (adjointSolution H d U (n+1)).comp (d (n+1))=1 := by
  intro n hn
  apply adjoint_inverse_contraction _ _ (d (n+1+1)) (hd n hn)
  · by_cases hnr : n+1≤r
    · exact hd (n+1) hnr
    · have he : n+1+1=r+2 := by omega
      have hz : d (n+1)=0 := by
        haveI : Subsingleton (H (n+1+1)) := he ▸ inferInstance
        ext x; exact Subsingleton.elim _ _
      rw [hz,ContinuousLinearMap.comp_zero]
  · exact hr n hn
  · by_cases hnr : n+1≤r
    · exact hl (n+1) hnr
    · have he : n+1+1=r+2 := by omega
      haveI : Subsingleton (H (n+1+1)) := he ▸ inferInstance
      ext x; exact Subsingleton.elim _ _

def finiteGreen (c : ℕ → ℝ) (hc : ∀ n≤r, 0<c n)
    (hL : ∀ n≤r, ∀ x, c n*‖x‖^2≤Complex.re (inner ℂ (laplacian (d n) (d (n+1)) x) x))
    (n : ℕ) : H (n+1) →L[ℂ] H (n+1) :=
  if hn : n≤r then Green (laplacian (d n) (d (n+1))) (hc n hn) (hL n hn) else 0

omit [Subsingleton (H 0)] [Subsingleton (H (r+2))] in
theorem finiteGreen_right (c : ℕ → ℝ) (hc : ∀ n≤r, 0<c n)
    (hL : ∀ n≤r, ∀ x, c n*‖x‖^2≤Complex.re (inner ℂ (laplacian (d n) (d (n+1)) x) x))
    (n : ℕ) (hn : n≤r) :
    (laplacian (d n) (d (n+1))).comp (finiteGreen H d r c hc hL n)=1 := by
  rw [finiteGreen,dif_pos hn]
  exact Green_right _ _ _

omit [Subsingleton (H 0)] [Subsingleton (H (r+2))] in
theorem finiteGreen_left (c : ℕ → ℝ) (hc : ∀ n≤r, 0<c n)
    (hL : ∀ n≤r, ∀ x, c n*‖x‖^2≤Complex.re (inner ℂ (laplacian (d n) (d (n+1)) x) x))
    (n : ℕ) (hn : n≤r) :
    (finiteGreen H d r c hc hL n).comp (laplacian (d n) (d (n+1)))=1 := by
  rw [finiteGreen,dif_pos hn]
  exact Green_left _ _ _

omit [Subsingleton (H 0)] [Subsingleton (H (r+2))] in
theorem finiteGreen_norm (c : ℕ → ℝ) (hc : ∀ n≤r, 0<c n)
    (hL : ∀ n≤r, ∀ x, c n*‖x‖^2≤Complex.re (inner ℂ (laplacian (d n) (d (n+1)) x) x))
    (n : ℕ) (hn : n≤r) : ‖finiteGreen H d r c hc hL n‖≤(c n)⁻¹ := by
  rw [finiteGreen,dif_pos hn]
  exact Green_norm _ _ _

theorem finiteGreen_contraction
    (hd : ∀ n≤r, (d (n+1)).comp (d n)=0)
    (c : ℕ → ℝ) (hc : ∀ n≤r, 0<c n)
    (hL : ∀ n≤r, ∀ x, c n*‖x‖^2≤Complex.re (inner ℂ (laplacian (d n) (d (n+1)) x) x)) :
    ∀ n≤r, (d n).comp (adjointSolution H d (finiteGreen H d r c hc hL) n)+
      (adjointSolution H d (finiteGreen H d r c hc hL) (n+1)).comp (d (n+1))=1 :=
  finite_adjoint_formula H d r hd _ (finiteGreen_right H d r c hc hL)
    (finiteGreen_left H d r c hc hL)

omit [Subsingleton (H 0)] [Subsingleton (H (r+2))] in
theorem finite_dimensional_closed
    (hfd : ∀ n≤r+1, FiniteDimensional ℂ (H n)) :
    ∀ n≤r+1, IsClosed (Set.range (d n)) := by
  intro n hn
  letI := hfd n hn
  exact (d n).range.closed_of_finiteDimensional

/-- The finite-dimensional target is obtained without any condition on an unused tail.
The explicit inverse-norm bounds are supplied by reducedDegreeBound in the same closure. -/
theorem finite_dimensional_target
    (hfd : ∀ n≤r+1, FiniteDimensional ℂ (H n))
    (hex : ∀ n≤r, (d n).range.topologicalClosure=(d (n+1)).ker) :
    ∃ (s : ∀ n, H (n+1) →L[ℂ] H n) (U : ∀ n, H (n+1) →L[ℂ] H (n+1)),
      s 0=0 ∧ s (r+1)=0 ∧
      (∀ n≤r, (d n).comp (s n)+(s (n+1)).comp (d (n+1))=1) ∧
      (∀ n≤r, (laplacian (d n) (d (n+1))).comp (U n)=1) ∧
      (∀ n≤r, (U n).comp (laplacian (d n) (d (n+1)))=1) := by
  obtain ⟨s,U,h0,hr,hs,hu,hv,_⟩ := finite_closed_range_target H d r
    (finite_dimensional_closed H d r hfd) hex
  exact ⟨s,U,h0,hr,hs,hu,hv⟩

end MathGauge.HilbertFinite
