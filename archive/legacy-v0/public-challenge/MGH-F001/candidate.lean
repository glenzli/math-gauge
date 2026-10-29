import Std
namespace MGHF001
universe u
variable {α : Type u}
def step (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => step f n (f x)
def Stable (f : α → α) (S : α → α → Prop) : Prop :=
  ∀ x y, S x y → S (f x) (f y)
def Included (S R : α → α → Prop) : Prop := ∀ x y, S x y → R x y
def Trace (f : α → α) (R : α → α → Prop) (x y : α) : Prop :=
  ∀ n, R (step f n x) (step f n y)
theorem candidate (f : α → α) (R : α → α → Prop) (hR : Equivalence R) :
    ∃ E : α → α → Prop, Equivalence E ∧ Included E R ∧ Stable f E ∧
      (∀ S : α → α → Prop, Equivalence S → Included S R → Stable f S → Included S E) := by
  refine ⟨Trace f R, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro x n
      exact hR.refl (step f n x)
    · intro x y h n
      exact hR.symm (h n)
    · intro x y z hxy hyz n
      exact hR.trans (hxy n) (hyz n)
  · intro x y h
    exact h 0
  · intro x y h n
    exact h (n + 1)
  · intro S _hS hSR hSf x y hxy n
    apply hSR
    induction n generalizing x y with
    | zero => exact hxy
    | succ n ih => exact ih (f x) (f y) (hSf x y hxy)
#print axioms candidate
end MGHF001
