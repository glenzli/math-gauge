import Std
namespace F001Repair
theorem repaired {α : Type} (R : α → α → Prop) (f : α → α)
    (_equiv : Equivalence R)
    (preserves : ∀ x y, R x y → R (f x) (f y)) :
    ∀ x y, R x y → R (f x) (f y) := preserves
#print axioms repaired
end F001Repair
