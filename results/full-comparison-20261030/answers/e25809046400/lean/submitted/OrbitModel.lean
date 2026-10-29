import RecordLayers

namespace MathGauge.F110

variable {X Y : Type*} [DecidableEq Y]

def orbit (f : X → X) : ℕ → X → X
  | 0, x => x
  | n + 1, x => orbit f n (f x)

def Safe (B : Finset Y) (q : X → Y) (f : X → X) (x : X) : Prop :=
  ∀ n, q (orbit f n x) ∈ B

/-- The original evolution condition, only for states whose record is in B. -/
def OneStep (B : Finset Y) (q : X → Y) (f : X → X)
    (g : Y → Y) : Prop :=
  ∀ x, q x ∈ B → q (f x) = q x ∨ q (f x) = g (q x)

/-- A sufficient additional condition for the reverse inclusion. -/
def EventuallyProgress (B : Finset Y) (q : X → Y) (f : X → X)
    (g : Y → Y) : Prop :=
  ∀ x, q x ∈ B → ∃ k : ℕ, q (orbit f k x) = g (q x)

/-- The stronger condition used by the original attachment. -/
def Realizes (B : Finset Y) (q : X → Y) (f : X → X)
    (g : Y → Y) : Prop :=
  ∀ x, q x ∈ B → q (f x) = g (q x)

def admissibleSet (B : Finset Y) (q : X → Y) : Set X :=
  q ⁻¹' (B : Set Y)

def safeSet (B : Finset Y) (q : X → Y) (f : X → X) : Set X :=
  {x | Safe B q f x}

def candidateSet (B : Finset Y) (q : X → Y) (g : Y → Y) : Set X :=
  q ⁻¹' (terminal B g : Set Y)

theorem safe_step (B : Finset Y) (q : X → Y) (f : X → X) {x : X}
    (hx : Safe B q f x) : Safe B q f (f x) := by
  intro n
  exact hx (n + 1)

theorem safe_orbit (B : Finset Y) (q : X → Y) (f : X → X) {x : X}
    (hx : Safe B q f x) (n : ℕ) :
    Safe B q f (orbit f n x) := by
  induction n generalizing x with
  | zero =>
      exact hx
  | succ n ih =>
      change Safe B q f (orbit f n (f x))
      apply ih
      exact safe_step B q f hx

theorem orbit_mem_of_invariant (f : X → X) (S : Set X)
    (hS : ∀ x ∈ S, f x ∈ S) (n : ℕ) {x : X} (hx : x ∈ S) :
    orbit f n x ∈ S := by
  induction n generalizing x with
  | zero =>
      exact hx
  | succ n ih =>
      change orbit f n (f x) ∈ S
      apply ih
      exact hS x hx

theorem safeSet_subset_admissibleSet
    (B : Finset Y) (q : X → Y) (f : X → X) :
    safeSet B q f ⊆ admissibleSet B q := by
  intro x hx
  change Safe B q f x at hx
  change q x ∈ B
  exact hx 0

theorem safeSet_forward_invariant
    (B : Finset Y) (q : X → Y) (f : X → X) :
    ∀ x ∈ safeSet B q f, f x ∈ safeSet B q f := by
  intro x hx
  change Safe B q f x at hx
  change Safe B q f (f x)
  exact safe_step B q f hx

theorem safeSet_maximal
    (B : Finset Y) (q : X → Y) (f : X → X) (S : Set X)
    (hA : S ⊆ admissibleSet B q)
    (hS : ∀ x ∈ S, f x ∈ S) :
    S ⊆ safeSet B q f := by
  intro x hx
  change Safe B q f x
  intro n
  exact hA (orbit_mem_of_invariant f S hS n hx)

theorem realizes_oneStep
    (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : Realizes B q f g) :
    OneStep B q f g := by
  intro x hx
  exact Or.inr (h x hx)

theorem realizes_eventuallyProgress
    (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : Realizes B q f g) :
    EventuallyProgress B q f g := by
  intro x hx
  refine ⟨1, ?_⟩
  exact h x hx

/--
A safe state belongs to every layer if its record eventually reaches
the prescribed g-successor. The original OneStep condition is not needed
for this direction.
-/
theorem safe_in_layers_of_eventuallyProgress
    (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : EventuallyProgress B q f g) (n : ℕ) {x : X}
    (hx : Safe B q f x) :
    q x ∈ layers B g n := by
  induction n generalizing x with
  | zero =>
      exact hx 0
  | succ n ih =>
      change q x ∈ B.filter (fun y => g y ∈ layers B g n)
      apply Finset.mem_filter.mpr
      refine ⟨hx 0, ?_⟩
      obtain ⟨k, hk⟩ := h x (hx 0)
      rw [← hk]
      apply ih
      exact safe_orbit B q f hx k

/-- Compatibility with the valid lemma from the attachment. -/
theorem safe_in_layers
    (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : Realizes B q f g) (n : ℕ) {x : X}
    (hx : Safe B q f x) :
    q x ∈ layers B g n :=
  safe_in_layers_of_eventuallyProgress B q f g
    (realizes_eventuallyProgress B q f g h) n hx

end MathGauge.F110
