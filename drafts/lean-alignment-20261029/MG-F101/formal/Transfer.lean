import Core
namespace MathGauge.F101
variable {R : Type*} [CommRing R]
structure SourceData (I : Ideal R) where
  exponent : ℕ
  annihilates : I ^ exponent = ⊥
theorem mapped_power (I J : Ideal R) (n : ℕ) :
    (I.map (Ideal.Quotient.mk J)) ^ n = (I ^ n).map (Ideal.Quotient.mk J) := by
  exact (Ideal.map_pow _ _ _).symm
theorem transport (I J : Ideal R) (d : SourceData I) :
    IsNilpotent (I.map (Ideal.Quotient.mk J)) := by
  refine ⟨d.exponent, ?_⟩
  change (I.map (Ideal.Quotient.mk J)) ^ d.exponent = ⊥
  rw [mapped_power, d.annihilates, Ideal.map_bot]
theorem transition_image (I : Ideal R) {m n : ℕ} (h : m ≤ n) :
    (residual I n).map (transition I h) = residual I m := by
  simp only [residual, transition, Ideal.map_map, Ideal.Quotient.factor_comp_mk]
theorem transition_comp (I : Ideal R) {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) :
    (transition I h).comp (transition I k) = transition I (h.trans k) := by
  unfold transition
  exact Ideal.Quotient.factor_comp _ _
end MathGauge.F101
