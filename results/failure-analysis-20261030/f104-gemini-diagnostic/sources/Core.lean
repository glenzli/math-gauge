import Mathlib.Topology.Order

open scoped Topology

namespace MathGauge.F104

universe u v w

variable {ι : Type u} {X : Type v} {Y : ι → Type w}

/-- 拓扑 `s` 使得映射族中每一个 `f i : (X, s) → (Y i, t i)` 均连续。 -/
def Realizes (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    (s : TopologicalSpace X) : Prop := ∀ i, Continuous[s, t i] (f i)

end MathGauge.F104
