import OrbitModel

namespace MathGauge.F109

variable {X Y : Type*} [DecidableEq Y]

theorem terminal_implies_safe (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : Realizes B q f g) {x : X} (hx : q x ∈ terminal B g) : Safe B q f x := by
  intro n
  induction n generalizing x with
  | zero => exact ((terminal_mem B g (q x)).mp hx).1
  | succ n ih =>
    have hx' := (terminal_mem B g (q x)).mp hx
    have hf : q (f x) ∈ terminal B g := by rw [h x hx'.1]; exact hx'.2
    exact ih hf

theorem exact_realization (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : Realizes B q f g) (x : X) :
    Safe B q f x ↔ q x ∈ terminal B g :=
  ⟨safe_in_layers B q f g h B.card, terminal_implies_safe B q f g h⟩

theorem maximal_invariant (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : Realizes B q f g) (S : Set X)
    (hB : ∀ x ∈ S, q x ∈ B) (hS : ∀ x ∈ S, f x ∈ S) :
    ∀ x ∈ S, q x ∈ terminal B g := by
  intro x hx
  apply (exact_realization B q f g h x).mp
  intro n
  apply hB
  induction n generalizing x with
  | zero => exact hx
  | succ n ih => exact ih (f x) (hS x hx)

#print axioms exact_realization
#print axioms maximal_invariant

end MathGauge.F109
