import FiniteGreen

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

def chainRegularGreen (ε : ℝ) (n : ℕ) : H (n+1) →L[ℂ] H (n+1) :=
  regularGreen (laplacian (d n) (d (n+1))) (laplacian_positive _ _) ε

theorem finite_regular_identity
    (hd : ∀ n≤r, (d (n+1)).comp (d n)=0) {ε : ℝ} (hε : 0<ε) :
    ∀ n≤r, (d n).comp (adjointSolution H d (chainRegularGreen H d ε) n)+
      (adjointSolution H d (chainRegularGreen H d ε) (n+1)).comp (d (n+1))=
        1-(ε:ℂ) • chainRegularGreen H d ε n := by
  intro n hn
  apply regular_contraction_identity _ _ (d (n+1+1)) (hd n hn) _ hε
  by_cases hnr : n+1≤r
  · exact hd (n+1) hnr
  · have he : n+1+1=r+2 := by omega
    have hz : d (n+1)=0 := by
      haveI : Subsingleton (H (n+1+1)) := he ▸ inferInstance
      ext x; exact Subsingleton.elim _ _
    rw [hz,ContinuousLinearMap.comp_zero]

theorem finite_regular_strong
    (hex : ∀ n≤r, (d n).range.topologicalClosure=(d (n+1)).ker)
    (n : ℕ) (hn : n≤r) (x : H (n+1)) :
    Tendsto (fun ε : ℝ => (1-(ε:ℂ) • chainRegularGreen H d ε n) x)
      (𝓝[>] (0:ℝ)) (𝓝 x) :=
  laplacian_regular_strong _ _ (hex n hn) x

/-- Four exact conditions on the finite chain; no exactness, spectral gap, or
closed-range condition is smuggled into the regularization condition. -/
theorem finite_four_way
    (hd : ∀ n≤r, (d (n+1)).comp (d n)=0)
    (hex : ∀ n≤r, (d n).range.topologicalClosure=(d (n+1)).ker) :
    ((∀ n≤r+1, IsClosed (Set.range (d n))) ↔
      ∃ s : ∀ n, H (n+1) →L[ℂ] H n,
        ∀ n≤r, (d n).comp (s n)+(s (n+1)).comp (d (n+1))=1) ∧
    ((∀ n≤r+1, IsClosed (Set.range (d n))) ↔
      ∀ n≤r, ∃ U : H (n+1) →L[ℂ] H (n+1),
        (laplacian (d n) (d (n+1))).comp U=1) ∧
    ((∀ n≤r, ∃ U : H (n+1) →L[ℂ] H (n+1),
        (laplacian (d n) (d (n+1))).comp U=1) ↔
      ∀ n≤r, Tendsto (fun ε : ℝ => ‖(ε:ℂ) • chainRegularGreen H d ε n‖)
        (𝓝[>] (0:ℝ)) (𝓝 0)) := by
  have hc := finite_criteria H d r hd hex
  refine ⟨hc.1.symm,hc.2,?_⟩
  constructor
  · intro hU n hn
    exact (regularError_norm_iff_right_inverse _ (laplacian_positive (d n) (d (n+1)))).mpr (hU n hn)
  · intro hnorm n hn
    exact (regularError_norm_iff_right_inverse _ (laplacian_positive (d n) (d (n+1)))).mp (hnorm n hn)

theorem finite_uniform_formula
    (hd : ∀ n≤r, (d (n+1)).comp (d n)=0)
    (hex : ∀ n≤r, (d n).range.topologicalClosure=(d (n+1)).ker)
    (hc : ∀ n≤r+1, IsClosed (Set.range (d n))) :
    ∃ U : ∀ n, H (n+1) →L[ℂ] H (n+1),
      (∀ n≤r, (laplacian (d n) (d (n+1))).comp (U n)=1) ∧
      (∀ n≤r, (U n).comp (laplacian (d n) (d (n+1)))=1) ∧
      adjointSolution H d U 0=0 ∧ adjointSolution H d U (r+1)=0 ∧
      (∀ n≤r, (d n).comp (adjointSolution H d U n)+
        (adjointSolution H d U (n+1)).comp (d (n+1))=1) ∧
      (∀ n, ‖adjointSolution H d U n‖≤‖d n‖*‖U n‖) ∧
      (∃ Cs CG : ℝ, 0≤Cs ∧ 0≤CG ∧
        (∀ n≤r+1, ∀ x y, ‖adjointSolution H d U n x-adjointSolution H d U n y‖≤Cs*‖x-y‖) ∧
        (∀ n≤r, ∀ x y, ‖U n x-U n y‖≤CG*‖x-y‖)) := by
  obtain ⟨s,U,_,_,_,hU,hV,_⟩ := finite_closed_range_target H d r hc hex
  refine ⟨U,hU,hV,(adjoint_endpoints H d r U).1,(adjoint_endpoints H d r U).2,
    finite_adjoint_formula H d r hd U hU hV,?_,finite_stability H r (adjointSolution H d U) U⟩
  intro n
  simpa only [adjointSolution,ContinuousLinearMap.adjoint.norm_map] using (d n).adjoint.opNorm_comp_le (U n)

end MathGauge.HilbertFinite

namespace MathGauge.HilbertRegular
open HilbertComplex HilbertCriteria

theorem diagonal_positive_zero : Positive L₀ := by
  have h := laplacian_positive (0 : H →L[ℂ] H) d
  simpa only [laplacian,ContinuousLinearMap.adjoint.map_zero,ContinuousLinearMap.zero_comp,zero_add,L₀] using h

theorem diagonal_positive_one : Positive L₁ := by
  have h := laplacian_positive d (0 : H →L[ℂ] H)
  simpa only [laplacian,ContinuousLinearMap.adjoint.map_zero,ContinuousLinearMap.zero_comp,add_zero,L₁] using h

/-- The actual complex diagonal counterexample rules out norm convergence at both
degrees. This uses the proved Neumann-series implication, without assuming a spectral theorem. -/
theorem diagonal_regular_norm_failure :
    ¬ Tendsto (fun ε => ‖regularError L₀ diagonal_positive_zero ε‖) (𝓝[>] (0:ℝ)) (𝓝 0) ∧
    ¬ Tendsto (fun ε => ‖regularError L₁ diagonal_positive_one ε‖) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  constructor
  · intro h
    exact no_laplacian_right_inverse.1 ((regularError_norm_iff_right_inverse L₀ diagonal_positive_zero).mp h)
  · intro h
    exact no_laplacian_right_inverse.2 ((regularError_norm_iff_right_inverse L₁ diagonal_positive_one).mp h)

/-- Restatement in the operator topology of the exact right side of the task. -/
theorem diagonal_regular_operator_failure :
    ¬ Tendsto (fun ε => (1 : H →L[ℂ] H)-regularError L₀ diagonal_positive_zero ε)
      (𝓝[>] (0:ℝ)) (𝓝 1) ∧
    ¬ Tendsto (fun ε => (1 : H →L[ℂ] H)-regularError L₁ diagonal_positive_one ε)
      (𝓝[>] (0:ℝ)) (𝓝 1) := by
  constructor
  · intro ht
    apply diagonal_regular_norm_failure.1
    have h1 : Tendsto (fun _ : ℝ => (1 : H →L[ℂ] H)) (𝓝[>] (0:ℝ)) (𝓝 1) := tendsto_const_nhds
    have he := (h1.sub ht).norm
    simpa only [sub_sub_cancel,sub_self,norm_zero] using he
  · intro ht
    apply diagonal_regular_norm_failure.2
    have h1 : Tendsto (fun _ : ℝ => (1 : H →L[ℂ] H)) (𝓝[>] (0:ℝ)) (𝓝 1) := tendsto_const_nhds
    have he := (h1.sub ht).norm
    simpa only [sub_sub_cancel,sub_self,norm_zero] using he

end MathGauge.HilbertRegular
