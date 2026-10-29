import Std
namespace F006
theorem candidate {α : Type} (U : α → Prop) (R : α → α → Prop) (f : α → α)
    (invariant : ∀ x, U x → U (f x))
    (localPreserves : ∀ x y, U x → U y → R x y → R (f x) (f y)) :
    ∀ x y, U x → U y → R x y → R (f (f x)) (f (f y)) := by
  intro x y hx hy hxy
  exact localPreserves (f x) (f y) (invariant x hx) (invariant y hy)
    (localPreserves x y hx hy hxy)
#print axioms candidate
end F006
