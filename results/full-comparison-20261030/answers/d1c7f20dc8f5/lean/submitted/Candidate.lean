import Construction

open scoped Topology

namespace MathGauge.F104

universe u v w z

variable {ι : Type u} {X : Type v} {Y : ι → Type w}

/-- Continuity into the constructed topology implies continuity of composites. -/
theorem candidate_inbound
    (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    {Z : Type z} (s : TopologicalSpace Z) (g : Z → X)
    (hg : Continuous[s, assembled t f] g) :
    ∀ i, Continuous[s, t i] (f i ∘ g) := by
  intro i
  letI : TopologicalSpace Z := s
  letI : TopologicalSpace X := assembled t f
  letI : TopologicalSpace (Y i) := t i
  exact (candidate_realizes t f i).comp hg

/-- Continuity of all composites implies continuity into the construction. -/
theorem candidate_outbound
    (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    {Z : Type z} (s : TopologicalSpace Z) (g : Z → X)
    (hcomp : ∀ i, Continuous[s, t i] (f i ∘ g)) :
    Continuous[s, assembled t f] g := by
  let q : TopologicalSpace X := TopologicalSpace.coinduced g s
  have hq : Realizes t f q := by
    intro i
    letI : TopologicalSpace Z := s
    letI : TopologicalSpace X := q
    letI : TopologicalSpace (Y i) := t i
    apply continuous_def.mpr
    intro U hU
    change s.IsOpen ((f i ∘ g) ⁻¹' U)
    exact (continuous_def.mp (hcomp i)) U hU
  letI : TopologicalSpace Z := s
  letI : TopologicalSpace X := assembled t f
  apply continuous_def.mpr
  intro U hU
  change ∀ r : TopologicalSpace X, Realizes t f r → r.IsOpen U at hU
  have hqU : q.IsOpen U := hU q hq
  change s.IsOpen (g ⁻¹' U) at hqU
  exact hqU

/-- The mapping property of the constructed topology. -/
theorem candidate_mapping
    (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    {Z : Type z} (s : TopologicalSpace Z) (g : Z → X) :
    Continuous[s, assembled t f] g ↔
      ∀ i, Continuous[s, t i] (f i ∘ g) := by
  exact ⟨candidate_inbound t f s g, candidate_outbound t f s g⟩

#print axioms existsUnique_coarsest
#print axioms candidate_mapping

end MathGauge.F104
