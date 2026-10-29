import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace MathGauge.F102

variable {R : Type*} [CommRing R]

abbrev Level (I : Ideal R) (n : ℕ) := R ⧸ I ^ (n + 1)

def residual (I : Ideal R) (n : ℕ) : Ideal (Level I n) :=
  I.map (Ideal.Quotient.mk (I ^ (n + 1)))

def transition (I : Ideal R) {m n : ℕ} (h : m ≤ n) :
    Level I n →+* Level I m :=
  Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))

theorem residual_pow_eq_bot (I : Ideal R) (n : ℕ) :
    residual I n ^ (n + 1) = ⊥ := by
  change (I.map (Ideal.Quotient.mk (I ^ (n + 1)))) ^ (n + 1) = ⊥
  rw [← Ideal.map_pow]
  apply le_antisymm ?_ bot_le
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  simpa using (Ideal.Quotient.eq_zero_iff_mem.mpr ha)

theorem transition_residual (I : Ideal R) {m n : ℕ} (h : m ≤ n) :
    (residual I n).map (transition I h) = residual I m := by
  have hcomp :
      (transition I h).comp (Ideal.Quotient.mk (I ^ (n + 1))) =
        Ideal.Quotient.mk (I ^ (m + 1)) := by
    apply RingHom.ext
    intro a
    first
    | rfl
    | simp [transition]
  simpa only [residual, Ideal.map_map, hcomp]

theorem transition_comp (I : Ideal R) {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) :
    (transition I hlm).comp (transition I hmn) =
      transition I (le_trans hlm hmn) := by
  apply RingHom.ext
  intro x
  refine Quotient.inductionOn' x ?_
  intro a
  first
  | rfl
  | simp [transition]

end MathGauge.F102
