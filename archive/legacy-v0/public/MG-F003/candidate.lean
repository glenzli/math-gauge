import Std
namespace F003
theorem candidate {α β γ : Type} (f : α → β) (g : β → γ)
    (P : α → Prop) (Q : β → Prop) (S : γ → Prop)
    (first : ∀ a, P a → Q (f a)) (second : ∀ b, Q b → S (g b)) :
    ∀ a, P a → S (g (f a)) := by
  intro a ha
  exact second (f a) (first a ha)
#print axioms candidate
end F003
