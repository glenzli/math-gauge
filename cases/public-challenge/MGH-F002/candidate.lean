import Std
namespace MGHF002
universe u
variable {α : Type u}
def ImageGraph (s : Setoid α) (D : α → Prop) (f : α → α)
    (q r : Quotient s) : Prop :=
  ∃ x : α, D x ∧ Quotient.mk s x = q ∧ Quotient.mk s (f x) = r
def RightUnique {β : Type u} (G : β → β → Prop) : Prop :=
  ∀ q r₁ r₂, G q r₁ → G q r₂ → r₁ = r₂
theorem candidate (s : Setoid α) (D : α → Prop) (f : α → α)
    (h : ∀ x y, D x → D y → s.r x y → s.r (f x) (f y)) :
    RightUnique (ImageGraph s D f) := by
  intro q r₁ r₂ hx hy
  obtain ⟨x, hDx, hxq, hxr⟩ := hx
  obtain ⟨y, hDy, hyq, hyr⟩ := hy
  have hxy : s.r x y := Quotient.exact (hxq.trans hyq.symm)
  have hout : Quotient.mk s (f x) = Quotient.mk s (f y) :=
    Quotient.sound (h x y hDx hDy hxy)
  exact hxr.symm.trans (hout.trans hyr)
#print axioms candidate
end MGHF002
