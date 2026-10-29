import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace MathGauge.F102

variable {R : Type*} [CommRing R]

abbrev Level (I : Ideal R) (n : ℕ) := R ⧸ I ^ (n + 1)

def residual (I : Ideal R) (n : ℕ) : Ideal (Level I n) :=
  I.map (Ideal.Quotient.mk (I ^ (n + 1)))

def transition (I : Ideal R) {m n : ℕ} (h : m ≤ n) : Level I n →+* Level I m :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))

end MathGauge.F102
