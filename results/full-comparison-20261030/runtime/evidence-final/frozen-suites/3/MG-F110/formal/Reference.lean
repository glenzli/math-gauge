import Candidate

namespace MathGauge.F110

variable {X Y : Type*} [DecidableEq Y]

def Stutters (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y) : Prop :=
  ∀ x, q x ∈ B → q (f x) = q x ∨ q (f x) = g (q x)

theorem safe_subset (B : Finset Y) (q : X → Y) (f : X → X) {x : X}
    (hx : Safe B q f x) : q x ∈ B := hx 0

theorem safe_maximal (B : Finset Y) (q : X → Y) (f : X → X) (S : Set X)
    (hB : ∀ x ∈ S, q x ∈ B) (hS : ∀ x ∈ S, f x ∈ S) :
    ∀ x ∈ S, Safe B q f x := by
  intro x hx n
  apply hB
  induction n generalizing x with
  | zero => exact hx
  | succ n ih => exact ih (f x) (hS x hx)

theorem terminal_sound_for_stuttering (B : Finset Y) (q : X → Y) (f : X → X)
    (g : Y → Y) (h : Stutters B q f g) {x : X}
    (hx : q x ∈ terminal B g) : Safe B q f x := by
  intro n
  induction n generalizing x with
  | zero => exact ((terminal_mem B g (q x)).mp hx).1
  | succ n ih =>
    have hx' := (terminal_mem B g (q x)).mp hx
    have hf : q (f x) ∈ terminal B g := by
      rcases h x hx'.1 with hs | hs
      · rw [hs]; exact hx
      · rw [hs]; exact hx'.2
    exact ih hf

theorem stuttering_counterexample :
    Stutters ({false} : Finset Bool) id id (fun _ => true) ∧
    Safe ({false} : Finset Bool) id id false ∧
    false ∉ terminal ({false} : Finset Bool) (fun _ => true) ∧
    ¬ Realizes ({false} : Finset Bool) id id (fun _ => true) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx; exact Or.inl rfl
  · intro n
    have hi : orbit (id : Bool → Bool) n false = false := by
      induction n with
      | zero => rfl
      | succ n ih => exact ih
    simpa [hi]
  · simp [terminal, layers]
  · intro h
    have := h false (by simp)
    simp at this

#print axioms terminal_sound_for_stuttering
#print axioms stuttering_counterexample
#print axioms safe_maximal

end MathGauge.F110
