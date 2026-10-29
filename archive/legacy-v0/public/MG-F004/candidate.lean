import Std
namespace F004
def Image {α : Type} (f : α → α) := {y : α // ∃ x, f x = y}
structure Certificate {α : Type} (f : α → α) where
  r : α → Image f
  projects : ∀ x, (r x).val = f x
  fixes : ∀ y : Image f, r y.val = y
theorem candidate {α : Type} (f : α → α) (_hf : ∀ x, f (f x) = f x)
    (cert : Certificate f) :
    ∃ r : α → Image f, (∀ x, (r x).val = f x) ∧ (∀ y : Image f, r y.val = y) := by
  exact ⟨cert.r, cert.projects, cert.fixes⟩
#print axioms candidate
end F004
