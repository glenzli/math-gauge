import Std
namespace F001
theorem candidate {α : Type} (R : α → α → Prop) (f : α → α)
    (_equiv : Equivalence R)
    (preserves : ∀ x y, R x y → R (f x) (f y))
    (separated : ∀ x y, R x y → x = y) :
    ∀ x y, R x y → f x = f y := by
  intro x y h
  exact separated (f x) (f y) (preserves x y h)
#print axioms candidate
end F001
