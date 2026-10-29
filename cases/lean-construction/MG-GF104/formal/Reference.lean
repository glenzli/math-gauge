import Core
open scoped Topology
namespace MathGauge.F104
@[reducible] def repaired {ι : Type*} {X : Type*} {Y : ι → Type*}
    (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i) : TopologicalSpace X :=
  ⨅ i, TopologicalSpace.induced (f i) (t i)
universe u v w z
variable {ι : Type u} {X : Type v} {Y : ι → Type w}
theorem repaired_realizes (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i) :
    Realizes t f (repaired t f) := by
  intro i
  exact continuous_iff_le_induced.2 (iInf_le _ i)
theorem repaired_coarsest (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    (s : TopologicalSpace X) (h : Realizes t f s) : s ≤ repaired t f := by
  exact le_iInf fun i => continuous_iff_le_induced.1 (h i)
theorem repaired_inbound (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    {Z : Type z} (s : TopologicalSpace Z) (g : Z → X) :
    Continuous[s, repaired t f] g ↔ ∀ i, Continuous[s, t i] (f i ∘ g) := by
  simp only [continuous_iInf_rng, continuous_induced_rng]
theorem repaired_unique (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    (s : TopologicalSpace X) (h : Realizes t f s)
    (hs : ∀ r : TopologicalSpace X, Realizes t f r → r ≤ s) : s = repaired t f := by
  exact le_antisymm (repaired_coarsest t f s h) (hs _ (repaired_realizes t f))
#print axioms repaired_realizes
#print axioms repaired_coarsest
#print axioms repaired_inbound
#print axioms repaired_unique
end MathGauge.F104
