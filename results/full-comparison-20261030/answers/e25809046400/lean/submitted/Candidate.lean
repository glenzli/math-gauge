import OrbitModel

namespace MathGauge.F110

variable {X Y : Type*} [DecidableEq Y]

/-- Under the original condition, the candidate is forward invariant. -/
theorem terminal_step
    (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : OneStep B q f g) {x : X}
    (hx : q x ∈ terminal B g) :
    q (f x) ∈ terminal B g := by
  obtain ⟨hxB, hxg⟩ := (terminal_mem B g (q x)).mp hx
  rcases h x hxB with hs | hg
  · rw [hs]
    exact hx
  · rw [hg]
    exact hxg

theorem candidateSet_forward_invariant
    (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : OneStep B q f g) :
    ∀ x ∈ candidateSet B q g, f x ∈ candidateSet B q g := by
  intro x hx
  change q x ∈ terminal B g at hx
  change q (f x) ∈ terminal B g
  exact terminal_step B q f g h hx

/-- This implication uses precisely the original evolution condition. -/
theorem terminal_implies_safe
    (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : OneStep B q f g) {x : X}
    (hx : q x ∈ terminal B g) :
    Safe B q f x := by
  intro n
  induction n generalizing x with
  | zero =>
      exact ((terminal_mem B g (q x)).mp hx).1
  | succ n ih =>
      change q (orbit f n (f x)) ∈ B
      apply ih
      exact terminal_step B q f g h hx

theorem candidateSet_subset_safeSet
    (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : OneStep B q f g) :
    candidateSet B q g ⊆ safeSet B q f := by
  intro x hx
  change q x ∈ terminal B g at hx
  change Safe B q f x
  exact terminal_implies_safe B q f g h hx

/-- A concrete counterexample to the reverse inclusion. -/
theorem counterexample :
    ∃ (B : Finset Bool) (q : Bool → Bool) (f : Bool → Bool)
      (g : Bool → Bool) (x : Bool),
      OneStep B q f g ∧
      Safe B q f x ∧
      q x ∉ terminal B g := by
  refine ⟨({false} : Finset Bool), id, id, (fun _ => true), false,
    ?_, ?_, ?_⟩
  · intro x hx
    exact Or.inl rfl
  · intro n
    induction n with
    | zero =>
        decide
    | succ n ih =>
        exact ih
  · decide

/-- Even the Bool instance of the proposed set equality is false. -/
theorem original_set_claim_false :
    ¬ (∀ (B : Finset Bool) (q f g : Bool → Bool),
      OneStep B q f g →
      safeSet B q f = candidateSet B q g) := by
  intro claim
  rcases counterexample with ⟨B, q, f, g, x, hstep, hsafe, hnot⟩
  have heq := claim B q f g hstep
  have hx : x ∈ safeSet B q f := hsafe
  rw [heq] at hx
  exact hnot hx

/-- Equality is restored by the explicitly stated additional condition. -/
theorem safe_iff_terminal_of_eventuallyProgress
    (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : OneStep B q f g)
    (hp : EventuallyProgress B q f g) (x : X) :
    Safe B q f x ↔ q x ∈ terminal B g := by
  constructor
  · intro hx
    exact safe_in_layers_of_eventuallyProgress B q f g hp B.card hx
  · intro hx
    exact terminal_implies_safe B q f g h hx

theorem safeSet_eq_candidateSet_of_eventuallyProgress
    (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : OneStep B q f g)
    (hp : EventuallyProgress B q f g) :
    safeSet B q f = candidateSet B q g := by
  apply Set.ext
  intro x
  change Safe B q f x ↔ q x ∈ terminal B g
  exact safe_iff_terminal_of_eventuallyProgress B q f g h hp x

/--
The attachment's exact-realization theorem is valid with its stronger
Realizes hypothesis; it is not the original OneStep claim.
-/
theorem exact_realization
    (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : Realizes B q f g) (x : X) :
    Safe B q f x ↔ q x ∈ terminal B g :=
  safe_iff_terminal_of_eventuallyProgress B q f g
    (realizes_oneStep B q f g h)
    (realizes_eventuallyProgress B q f g h) x

/-- The attachment's maximality conclusion under its stronger hypothesis. -/
theorem maximal_invariant
    (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : Realizes B q f g) (S : Set X)
    (hB : ∀ x ∈ S, q x ∈ B)
    (hS : ∀ x ∈ S, f x ∈ S) :
    ∀ x ∈ S, q x ∈ terminal B g := by
  intro x hx
  apply (exact_realization B q f g h x).mp
  intro n
  exact hB (orbit f n x) (orbit_mem_of_invariant f S hS n hx)

end MathGauge.F110
