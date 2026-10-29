import ComplexAssembly

noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace MathGauge.HilbertCriteria
universe u
 theorem zero_range_closed {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] :
    IsClosed (Set.range (0 : E →L[ℂ] F)) := by
  have he : Set.range (0 : E →L[ℂ] F)=({0} : Set F) := by
    ext y
    constructor
    · rintro ⟨x,hx⟩
      change y=0
      exact hx.symm
    · intro hy
      change y=0 at hy
      exact ⟨0,hy.symm⟩
  rw [he]
  exact isClosed_singleton
variable (H : ℕ → Type u)
variable [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)] [∀ n, CompleteSpace (H n)]
variable (d : ∀ n, H n →L[ℂ] H (n+1))
variable (hd : ∀ n, (d (n+1)).comp (d n)=0)
variable (hex : ∀ n, (d n).range.topologicalClosure=(d (n+1)).ker)

include hd hex in
/-- In a zero-padded complex the three reference criteria are equivalent. -/
theorem full_criteria [Subsingleton (H 0)] :
    ((∃ s : ∀ n, H (n+1) →L[ℂ] H n,
      ∀ n, (d n).comp (s n)+(s (n+1)).comp (d (n+1))=ContinuousLinearMap.id ℂ (H (n+1))) ↔
      ∀ n, IsClosed (Set.range (d n))) ∧
    ((∀ n, IsClosed (Set.range (d n))) ↔
      ∀ n, ∃ U : H (n+1) →L[ℂ] H (n+1),
        (laplacian (d n) (d (n+1))).comp U=ContinuousLinearMap.id ℂ (H (n+1))) := by
  constructor
  · constructor
    · rintro ⟨s,hs⟩; exact all_ranges_closed_of_contraction H d hd s hs
    · intro hc; exact ⟨chainSolution H d hc,chainSolution_identity H d hex hc⟩
  · constructor
    · intro hc n; exact ⟨chainInverse H d hex hc n,chainInverse_right H d hex hc n⟩
    · intro hu n
      cases n with
      | zero =>
        have hz : d 0=0 := by ext x; rw [Subsingleton.elim x 0,map_zero]; rfl
        rw [hz]
        exact zero_range_closed
      | succ n =>
        obtain ⟨U,hU⟩ := hu n
        exact closed_range_of_degree_inverse (d n) (d (n+1)) (hd n) U
          (right_inverse_is_inverse (d n) (d (n+1)) (hex n) U hU)

/-- Endpoint conventions are literal zero maps, including zero-dimensional layers. -/
theorem chainSolution_endpoints (r : ℕ) [Subsingleton (H 0)] [Subsingleton (H (r+2))]
    (hc : ∀ n, IsClosed (Set.range (d n))) :
    chainSolution H d hc 0=0 ∧ chainSolution H d hc (r+1)=0 := by
  constructor
  · ext x; exact Subsingleton.elim _ _
  · ext x; rw [Subsingleton.elim x 0,map_zero]; rfl

/-- Finite length yields finite uniform bounds without requiring a uniform bound on an infinite chain. -/
theorem finite_stability (r : ℕ)
    (s : ∀ n, H (n+1) →L[ℂ] H n)
    (U : ∀ n, H (n+1) →L[ℂ] H (n+1)) :
    ∃ Cs CG : ℝ, 0≤Cs ∧ 0≤CG ∧
      (∀ n≤r+1, ∀ x y, ‖s n x-s n y‖≤Cs*‖x-y‖) ∧
      (∀ n≤r, ∀ x y, ‖U n x-U n y‖≤CG*‖x-y‖) := by
  let Cs := ∑ n ∈ Finset.range (r+2), ‖s n‖
  let CG := ∑ n ∈ Finset.range (r+1), ‖U n‖
  refine ⟨Cs,CG,Finset.sum_nonneg (fun n _ => norm_nonneg _),
    Finset.sum_nonneg (fun n _ => norm_nonneg _), ?_, ?_⟩
  · intro n hn x y
    have hs : ‖s n‖≤Cs := Finset.single_le_sum (fun i _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
    rw [← map_sub]
    exact (s n).le_opNorm (x-y) |>.trans (mul_le_mul_of_nonneg_right hs (norm_nonneg _))
  · intro n hn x y
    have hs : ‖U n‖≤CG := Finset.single_le_sum (fun i _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
    rw [← map_sub]
    exact (U n).le_opNorm (x-y) |>.trans (mul_le_mul_of_nonneg_right hs (norm_nonneg _))

/-- Finite-dimensional layers are an explicitly sufficient subclass. -/
theorem finite_dimensional_ranges [∀ n, FiniteDimensional ℂ (H n)] :
    ∀ n, IsClosed (Set.range (d n)) := by
  intro n
  exact (d n).range.closed_of_finiteDimensional

end MathGauge.HilbertCriteria
