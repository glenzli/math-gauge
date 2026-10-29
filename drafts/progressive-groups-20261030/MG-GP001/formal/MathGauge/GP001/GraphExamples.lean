import FiniteCones

/-! Two explicit finite graphs for suspension non-cancellation.  The first is
two triangular circles with a common vertex together with an isolated vertex;
the second is the disjoint union of two triangular circles. -/

open Finset Set
open MathGauge.PublicProof.Topology

namespace MathGauge.GP001

def graphAt (a : Fin 6) : PreAbstractSimplicialComplex (Fin 6) :=
  simplex_complex {0, 1} ⊔ simplex_complex {1, 2} ⊔ simplex_complex {2, 0} ⊔
    simplex_complex {a, 3} ⊔ simplex_complex {3, 4} ⊔ simplex_complex {4, a} ⊔
    simplex_complex {5}

abbrev graphOne := graphAt 0
abbrev graphTwo := graphAt 5

instance graphAt_decidable (a : Fin 6) (s : Finset (Fin 6)) :
    Decidable (s ∈ graphAt a) := by
  change Decidable (((((((s.Nonempty ∧ s ⊆ {0, 1}) ∨ (s.Nonempty ∧ s ⊆ {1, 2})) ∨
    (s.Nonempty ∧ s ⊆ {2, 0})) ∨ (s.Nonempty ∧ s ⊆ {a, 3})) ∨
    (s.Nonempty ∧ s ⊆ {3, 4})) ∨ (s.Nonempty ∧ s ⊆ {4, a})) ∨
    (s.Nonempty ∧ s ⊆ {5}))
  infer_instance

theorem graphAt_vertex_zero (a : Fin 6) : ({0} : Finset (Fin 6)) ∈ graphAt a := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
    ⟨singleton_nonempty 0, by simp⟩)))))

theorem graphAt_nonempty (a : Fin 6) : Nonempty (Realization (graphAt a)) :=
  ⟨vertex (graphAt a) 0 (graphAt_vertex_zero a)⟩

theorem graphOne_nonempty : Nonempty (Realization graphOne) := graphAt_nonempty 0
theorem graphTwo_nonempty : Nonempty (Realization graphTwo) := graphAt_nonempty 5

end MathGauge.GP001
