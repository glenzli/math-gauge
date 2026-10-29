import RecordLayers

namespace MathGauge.F110

variable {X Y : Type*} [DecidableEq Y]

def orbit (f : X → X) : ℕ → X → X
  | 0, x => x
  | n + 1, x => orbit f n (f x)

def Safe (B : Finset Y) (q : X → Y) (f : X → X) (x : X) : Prop :=
  ∀ n, q (orbit f n x) ∈ B

def Realizes (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y) : Prop :=
  ∀ x, q x ∈ B → q (f x) = g (q x)

theorem safe_step (B : Finset Y) (q : X → Y) (f : X → X) {x : X}
    (hx : Safe B q f x) : Safe B q f (f x) := by
  intro n
  exact hx (n + 1)

theorem safe_in_layers (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : Realizes B q f g) (n : ℕ) {x : X} (hx : Safe B q f x) :
    q x ∈ layers B g n := by
  induction n generalizing x with
  | zero => exact hx 0
  | succ n ih =>
    apply Finset.mem_filter.mpr
    refine ⟨hx 0, ?_⟩
    rw [← h x (hx 0)]
    exact ih (safe_step B q f hx)

end MathGauge.F110
