import FiniteObservation
import Mathlib.Topology.Instances.EReal.Lemmas

noncomputable section
open Set
open scoped ENNReal

namespace MathGauge.ConvexCost

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

/-- Every minorant with a closed real-height epigraph lies below the reconstruction. -/
theorem reconstruct_maximal_ereal_of_isClosed_real_epigraph
    {f : E → ℝ≥0∞} (hf : ConvexCost f) (hp : ∃ x, f x ≠ ⊤)
    (h : E → EReal)
    (hclosed : IsClosed {p : E × ℝ | h p.1 ≤ (p.2 : EReal)})
    (hle : ∀ x, h x ≤ (f x : EReal)) :
    ∀ x, h x ≤ (reconstruct f x : EReal) := by
  have hsub : closure (epigraph f) ⊆ {p : E × ℝ | h p.1 ≤ (p.2 : EReal)} := by
    apply closure_minimal _ hclosed
    intro p hp'
    have he : ((ENNReal.ofReal p.2 : ℝ≥0∞) : EReal) = (p.2 : EReal) := by
      rw [EReal.coe_ennreal_ofReal, max_eq_left hp'.1]
    exact (hle p.1).trans (he ▸ EReal.coe_ennreal_le_coe_ennreal_iff.mpr hp'.2)
  intro x
  rw [reconstruct_eq_affineHull]
  by_cases hx : affineHull f x = ⊤
  · simp [hx]
  have hm : (x, (affineHull f x).toReal) ∈ epigraph (affineHull f) :=
    ⟨ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hx).ge⟩
  rw [epigraph_affineHull_eq_closure hf hp] at hm
  simpa only [Set.mem_setOf_eq, EReal.coe_ennreal_toReal hx] using hsub hm

/-- The existing lower-semicontinuity interface follows from the direct epigraph theorem. -/
theorem reconstruct_maximal_ereal {f : E → ℝ≥0∞} (hf : JensenConvex f)
    (hp : ∃ x, f x ≠ ⊤) (h : E → EReal) (hc : LowerSemicontinuous h)
    (hle : ∀ x, h x ≤ (f x : EReal)) : ∀ x, h x ≤ (reconstruct f x : EReal) := by
  have hclosed : IsClosed {p : E × ℝ | h p.1 ≤ (p.2 : EReal)} :=
    hc.isClosed_epigraph.preimage
      (continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd))
  exact reconstruct_maximal_ereal_of_isClosed_real_epigraph
    (convexCost_of_jensen hf) hp h hclosed hle

end MathGauge.ConvexCost
