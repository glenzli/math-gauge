import CH03.Core6
open formal_oet.vol_01.ch_01_foundations
namespace test

def NetF {X : Type} [DecidableEq X] (d : X → X → ENNReal) (ε : ENNReal)
    (U centers : Finset X) : Prop :=
  centers ⊆ U ∧ ∀ x ∈ U, ∃ c ∈ centers, d x c < ε

def HasN {X : Type} [Fintype X] [DecidableEq X] (d : X → X → ENNReal) (ε : ENNReal)
    (U : Finset X) (n : ℕ) : Prop :=
  (∃ S : Finset X, NetF d ε U S ∧ S.card = n) ∧
    ∀ S : Finset X, NetF d ε U S → n ≤ S.card

def d2 (x y : Fin 2) : ENNReal := if x = y then 0 else 1
example : HasN d2 (1/2 : ENNReal) Finset.univ 2 := by
  native_decide
end test
