import Construction
open scoped Topology
namespace MathGauge.F103
universe u v w z
variable {ι : Type u} {X : Type v} {Y : ι → Type w}
theorem candidate_realizes (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i) :
    Realizes t f (assembled t f) := by
  intro i
  exact continuous_iff_le_induced.2 (iInf_le _ i)
theorem candidate_coarsest (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    (s : TopologicalSpace X) (h : Realizes t f s) : s ≤ assembled t f := by
  exact le_iInf fun i => continuous_iff_le_induced.1 (h i)
theorem candidate_inbound (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    {Z : Type z} (s : TopologicalSpace Z) (g : Z → X) :
    Continuous[s, assembled t f] g ↔ ∀ i, Continuous[s, t i] (f i ∘ g) := by
  simp only [continuous_iInf_rng, continuous_induced_rng]
theorem candidate_unique (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    (s : TopologicalSpace X) (h : Realizes t f s)
    (hs : ∀ r : TopologicalSpace X, Realizes t f r → r ≤ s) : s = assembled t f := by
  exact le_antisymm (candidate_coarsest t f s h) (hs _ (candidate_realizes t f))
#print axioms candidate_realizes
#print axioms candidate_coarsest
#print axioms candidate_inbound
#print axioms candidate_unique
end MathGauge.F103
