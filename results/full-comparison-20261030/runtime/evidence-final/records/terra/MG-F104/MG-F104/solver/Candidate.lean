import Construction
open scoped Topology
namespace MathGauge.F104
universe u v w z
variable {ι : Type u} {X : Type v} {Y : ι → Type w}
theorem candidate_realizes (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i) :
    Realizes t f (assembled t f) := by
  intro i
  have hb : Realizes t f (⊥ : TopologicalSpace X) := fun _ => continuous_bot
  exact continuous_le_dom (construction_bound t f ⊥ hb) continuous_bot
theorem candidate_inbound (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    {Z : Type z} (s : TopologicalSpace Z) (g : Z → X)
    (hg : Continuous[s, assembled t f] g) :
    ∀ i, Continuous[s, t i] (f i ∘ g) := by
  intro i
  letI : TopologicalSpace Z := s
  letI : TopologicalSpace X := assembled t f
  letI : TopologicalSpace (Y i) := t i
  exact (candidate_realizes t f i).comp hg
#print axioms candidate_realizes
#print axioms candidate_inbound
end MathGauge.F104
