import Mathlib.Topology.Order
open scoped Topology
universe u
variable {X : Type u}
#synth OrderBot (TopologicalSpace X)
#synth CompleteLattice (TopologicalSpace X)
#check @bot_le
#check @TopologicalSpace.instCompleteLattice
example (s : TopologicalSpace X) : (⊥ : TopologicalSpace X) ≤ s := by
  exact bot_le
