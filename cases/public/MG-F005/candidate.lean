import Std
namespace F005
def E {α : Type} (R : α → α → Prop) (x y : α) : Prop := R x y ∧ R y x
theorem candidate {α : Type} (R : α → α → Prop)
    (reflR : ∀ x, R x x)
    (transR : ∀ x y z, R x y → R y z → R x z) :
    Equivalence (E R) := by
  constructor
  · intro x
    exact ⟨reflR x, reflR x⟩
  · intro x y h
    exact ⟨h.2, h.1⟩
  · intro x y z hxy hyz
    exact ⟨transR x y z hxy.1 hyz.1, transR z y x hyz.2 hxy.2⟩
#print axioms candidate
end F005
