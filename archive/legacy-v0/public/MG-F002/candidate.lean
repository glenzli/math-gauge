import Std
namespace F002
theorem candidate : ∀ n : Nat, ∃ N : Nat, n ≤ N := by
  intro n
  exact ⟨n, Nat.le_refl n⟩
#print axioms candidate
end F002
