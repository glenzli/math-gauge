import Candidate
open scoped Topology
namespace MathGauge.F104
theorem assembled_eq_bot {ι X : Type*} {Y : ι → Type*}
    (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i) : assembled t f = ⊥ := by
  apply le_antisymm
  · exact construction_bound t f ⊥ (fun _ => continuous_bot)
  · intro U hU
    trivial
theorem top_bool_not_le_bot : ¬ (⊤ : TopologicalSpace Bool) ≤ ⊥ := by
  intro h
  have ho : IsOpen[(⊤ : TopologicalSpace Bool)] ({true} : Set Bool) :=
    h ({true} : Set Bool) (by trivial)
  rcases (TopologicalSpace.isOpen_top_iff _).1 ho with he | hu
  · have : (true : Bool) ∈ (∅ : Set Bool) := he ▸ (by simp : (true : Bool) ∈ ({true} : Set Bool))
    exact this
  · have : (false : Bool) ∈ ({true} : Set Bool) := hu ▸ (by trivial : (false : Bool) ∈ (Set.univ : Set Bool))
    simpa using this
theorem discrete_fails_coarsest :
    Realizes (fun _ : Unit => (⊤ : TopologicalSpace Bool)) (fun _ : Unit => id)
      (⊤ : TopologicalSpace Bool) ∧
    ¬ (⊤ : TopologicalSpace Bool) ≤
      assembled (fun _ : Unit => (⊤ : TopologicalSpace Bool)) (fun _ : Unit => id) := by
  constructor
  · intro i
    exact continuous_top
  · simpa only [assembled_eq_bot] using top_bool_not_le_bot
theorem inbound_reverse_fails :
    (∀ i : Unit, Continuous[(⊤ : TopologicalSpace Bool), (⊤ : TopologicalSpace Bool)]
      ((fun _ : Unit => id) i ∘ (id : Bool → Bool))) ∧
    ¬ Continuous[(⊤ : TopologicalSpace Bool),
      assembled (fun _ : Unit => (⊤ : TopologicalSpace Bool)) (fun _ : Unit => id)]
      (id : Bool → Bool) := by
  constructor
  · intro i
    exact continuous_top
  · intro h
    have hh := continuous_id_iff_le.1 h
    rw [assembled_eq_bot] at hh
    exact top_bool_not_le_bot hh
#print axioms assembled_eq_bot
#print axioms top_bool_not_le_bot
#print axioms discrete_fails_coarsest
#print axioms inbound_reverse_fails
end MathGauge.F104
