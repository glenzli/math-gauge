import Core
open scoped Topology
namespace MathGauge.F104
universe u v w
variable {ι : Type u} {X : Type v} {Y : ι → Type w}
@[reducible] def legacyAssembled (t : ∀ i, TopologicalSpace (Y i))
    (f : ∀ i, X → Y i) : TopologicalSpace X :=
  sInf {s | Realizes t f s}
theorem legacyConstructionBound (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    (s : TopologicalSpace X) (hs : Realizes t f s) : legacyAssembled t f ≤ s := by
  exact sInf_le hs
end MathGauge.F104
