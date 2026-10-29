import Reference

namespace MathGauge.F110

variable {X Y : Type*} [DecidableEq Y]

theorem orbit_eq_iterate (f : X → X) (n : ℕ) (x : X) : orbit f n x = f^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simpa only [orbit, Function.iterate_succ_apply] using ih (f x)

theorem safe_orbit (B : Finset Y) (q : X → Y) (f : X → X) {x : X}
    (hx : Safe B q f x) (k : ℕ) : Safe B q f (orbit f k x) := by
  induction k generalizing x with
  | zero => exact hx
  | succ k ih => exact ih (safe_step B q f hx)

theorem all_layers_eq_of_closed (B : Finset Y) (g : Y → Y)
    (hB : ∀ y ∈ B, g y ∈ B) (n : ℕ) : layers B g n = B := by
  induction n with
  | zero => rfl
  | succ n ih =>
    ext y
    simp only [layers, ih, Finset.mem_filter]
    exact ⟨And.left, fun hy => ⟨hy, hB y hy⟩⟩

theorem stutters_closed_forward (B : Finset Y) (q : X → Y) (f : X → X)
    (g : Y → Y) (h : Stutters B q f g) (hB : ∀ y ∈ B, g y ∈ B)
    {x : X} (hx : q x ∈ B) : q (f x) ∈ B := by
  rcases h x hx with hstay | hgo
  · rw [hstay]; exact hx
  · rw [hgo]; exact hB (q x) hx

theorem exact_under_record_closed (B : Finset Y) (q : X → Y) (f : X → X)
    (g : Y → Y) (h : Stutters B q f g) (hB : ∀ y ∈ B, g y ∈ B) (x : X) :
    (Safe B q f x ↔ q x ∈ B) ∧ (q x ∈ B ↔ q x ∈ terminal B g) := by
  refine ⟨⟨safe_subset B q f, ?_⟩, ?_⟩
  · intro hx
    exact safe_maximal B q f {x | q x ∈ B} (fun _ hy => hy)
      (fun _ hy => stutters_closed_forward B q f g h hB hy) x hx
  · rw [terminal, all_layers_eq_of_closed B g hB]

theorem closed_counterexample :
    Stutters (Finset.univ : Finset Bool) id id Bool.not ∧
    (∀ y ∈ (Finset.univ : Finset Bool), Bool.not y ∈ (Finset.univ : Finset Bool)) ∧
    (∀ x : Bool, Safe Finset.univ id id x ↔ x ∈ terminal Finset.univ Bool.not) ∧
    ¬ Realizes (Finset.univ : Finset Bool) id id Bool.not := by
  have hw : Stutters (Finset.univ : Finset Bool) id id Bool.not := fun _ _ => Or.inl rfl
  have hb : ∀ y ∈ (Finset.univ : Finset Bool), Bool.not y ∈ (Finset.univ : Finset Bool) := by simp
  refine ⟨hw, hb, ?_, ?_⟩
  · intro x
    exact ((exact_under_record_closed Finset.univ id id Bool.not hw hb x).1).trans
      ((exact_under_record_closed Finset.univ id id Bool.not hw hb x).2)
  · intro he
    have hf := he false (by simp)
    simp at hf

theorem stuttering_counterexample_complete :
    (∀ x : Bool, Safe {false} id id x ↔ x = false) ∧
    terminal ({false} : Finset Bool) (fun _ => true) = ∅ := by
  constructor
  · intro x
    constructor
    · intro hx; simpa using hx 0
    · rintro rfl; exact stuttering_counterexample.2.1
  · simp [terminal, layers]

theorem exact_record_unfold (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y) :
    Realizes B q f g ↔ ∀ x, q x ∈ B → q (f x) = g (q x) := Iff.rfl

end MathGauge.F110
