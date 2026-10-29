import FiniteCriteria

noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace MathGauge.HilbertCriteria
universe u
variable (H : ℕ → Type u)
variable [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)] [∀ n, CompleteSpace (H n)]
variable (d : ∀ n, H n →L[ℂ] H (n+1)) (r : ℕ)
variable [Subsingleton (H 0)] [Subsingleton (H (r+2))]

/-- The finite task directly: H_(j+1) denotes its H_j; H_0 and H_(r+2) are the
stated zero endpoint spaces. No hypotheses about the unused tail are imposed. -/
theorem finite_closed_range_target
    (hc : ∀ n≤r+1, IsClosed (Set.range (d n)))
    (hex : ∀ n≤r, (d n).range.topologicalClosure=(d (n+1)).ker) :
    ∃ (s : ∀ n, H (n+1) →L[ℂ] H n) (U : ∀ n, H (n+1) →L[ℂ] H (n+1)),
      s 0=0 ∧ s (r+1)=0 ∧
      (∀ n≤r, (d n).comp (s n)+(s (n+1)).comp (d (n+1))=ContinuousLinearMap.id ℂ (H (n+1))) ∧
      (∀ n≤r, (laplacian (d n) (d (n+1))).comp (U n)=ContinuousLinearMap.id ℂ (H (n+1))) ∧
      (∀ n≤r, (U n).comp (laplacian (d n) (d (n+1)))=ContinuousLinearMap.id ℂ (H (n+1))) ∧
      (∃ Cs CG : ℝ, 0≤Cs ∧ 0≤CG ∧
        (∀ n≤r+1, ∀ x y, ‖s n x-s n y‖≤Cs*‖x-y‖) ∧
        (∀ n≤r, ∀ x y, ‖U n x-U n y‖≤CG*‖x-y‖)) := by
  classical
  let s : ∀ n, H (n+1) →L[ℂ] H n := fun n =>
    if hn : n≤r+1 then partialInverse (d n) (hc n hn) else 0
  let U : ∀ n, H (n+1) →L[ℂ] H (n+1) := fun n =>
    if hn : n≤r then (laplacianEquiv (d n) (d (n+1)) (hc n (by omega)) (hc (n+1) (by omega))
      (closed_reduced_exact _ _ (hc n (by omega)) (hex n hn))).symm.toContinuousLinearMap else 0
  refine ⟨s,U, ?_, ?_, ?_, ?_, ?_,finite_stability H r s U⟩
  · ext x; exact Subsingleton.elim _ _
  · ext x; rw [Subsingleton.elim x 0,map_zero]; rfl
  · intro n hn
    simp only [s,dif_pos (show n≤r+1 by omega),dif_pos (show n+1≤r+1 by omega)]
    exact closed_range_contraction _ _ (hc n (by omega)) (hc (n+1) (by omega))
      (closed_reduced_exact _ _ (hc n (by omega)) (hex n hn))
  · intro n hn
    simp only [U,dif_pos hn]
    ext x
    exact (laplacianEquiv (d n) (d (n+1)) (hc n (by omega)) (hc (n+1) (by omega))
      (closed_reduced_exact _ _ (hc n (by omega)) (hex n hn))).apply_symm_apply x
  · intro n hn
    simp only [U,dif_pos hn]
    ext x
    exact (laplacianEquiv (d n) (d (n+1)) (hc n (by omega)) (hc (n+1) (by omega))
      (closed_reduced_exact _ _ (hc n (by omega)) (hex n hn))).symm_apply_apply x

/-- The exact three-way criterion is also local to the finite chain. -/
theorem finite_criteria
    (hd : ∀ n≤r, (d (n+1)).comp (d n)=0)
    (hex : ∀ n≤r, (d n).range.topologicalClosure=(d (n+1)).ker) :
    ((∃ s : ∀ n, H (n+1) →L[ℂ] H n,
       ∀ n≤r, (d n).comp (s n)+(s (n+1)).comp (d (n+1))=ContinuousLinearMap.id ℂ (H (n+1))) ↔
      ∀ n≤r+1, IsClosed (Set.range (d n))) ∧
    ((∀ n≤r+1, IsClosed (Set.range (d n))) ↔
      ∀ n≤r, ∃ U : H (n+1) →L[ℂ] H (n+1),
        (laplacian (d n) (d (n+1))).comp U=ContinuousLinearMap.id ℂ (H (n+1))) := by
  constructor
  · constructor
    · rintro ⟨s,hs⟩ n hn
      by_cases hnr : n≤r
      · exact contraction_implies_closed_range _ _ (hd n hnr) (s n) (s (n+1)) (hs n hnr)
      · have he : n=r+1 := by omega
        subst n
        have hz : d (r+1)=0 := by ext x; exact Subsingleton.elim _ _
        rw [hz]
        exact zero_range_closed
    · intro hc
      obtain ⟨s,U,_,_,hs,_⟩ := finite_closed_range_target H d r hc hex
      exact ⟨s,hs⟩
  · constructor
    · intro hc n hn
      obtain ⟨s,U,_,_,_,hU,_⟩ := finite_closed_range_target H d r hc hex
      exact ⟨U n,hU n hn⟩
    · intro hU n hn
      cases n with
      | zero =>
        have hz : d 0=0 := by ext x; rw [Subsingleton.elim x 0,map_zero]; rfl
        rw [hz]
        exact zero_range_closed
      | succ n =>
        obtain ⟨U,hu⟩ := hU n (by omega)
        exact closed_range_of_degree_inverse _ _ (hd n (by omega)) U
          (right_inverse_is_inverse _ _ (hex n (by omega)) U hu)

end MathGauge.HilbertCriteria
