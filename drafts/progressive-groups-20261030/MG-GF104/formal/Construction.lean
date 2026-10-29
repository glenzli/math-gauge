import Core
open scoped Topology
namespace MathGauge.F104
universe u v w
variable {ι : Type u} {X : Type v} {Y : ι → Type w}
@[reducible] def assembled (t : ∀ i, TopologicalSpace (Y i))
    (f : ∀ i, X → Y i) : TopologicalSpace X :=
  ⨅ i, TopologicalSpace.induced (f i) (t i)
end MathGauge.F104
