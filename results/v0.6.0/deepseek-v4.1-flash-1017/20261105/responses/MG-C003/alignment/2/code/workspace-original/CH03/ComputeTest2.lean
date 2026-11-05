import CH03.Core6
namespace test
def NetF {X : Type} [DecidableEq X] (d : X → X → ENNReal) (ε : ENNReal)
    (U centers : Finset X) : Prop :=
  centers ⊆ U ∧ ∀ x ∈ U, ∃ c ∈ centers, d x c < ε
def d2 (x y : Fin 2) : ENNReal := if x = y then 0 else 1
example (S U : Finset (Fin 2)) : Decidable (NetF d2 (1/2:ENNReal) U S) := by infer_instance
example : Decidable (∃ S : Finset (Fin 2), NetF d2 (1/2:ENNReal) Finset.univ S ∧ S.card = 2) := by infer_instance
example : Decidable (∀ S : Finset (Fin 2), NetF d2 (1/2:ENNReal) Finset.univ S → 2 ≤ S.card) := by infer_instance
end test
