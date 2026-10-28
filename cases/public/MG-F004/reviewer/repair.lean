import Std
namespace F004Repair
def Image {α : Type} (f : α → α) := {y : α // ∃ x, f x = y}
theorem repaired {α : Type} (f : α → α) (hf : ∀ x, f (f x) = f x) :
    ∃ r : α → Image f, (∀ x, (r x).val = f x) ∧ (∀ y : Image f, r y.val = y) := by
  refine ⟨fun x => ⟨f x, x, rfl⟩, ?_, ?_⟩
  · intro x
    rfl
  · intro y
    apply Subtype.ext
    obtain ⟨x, hx⟩ := y.property
    change f y.val = y.val
    rw [← hx]
    exact hf x
#print axioms repaired
end F004Repair
