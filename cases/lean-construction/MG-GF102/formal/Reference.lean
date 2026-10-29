import Core
namespace MathGauge.F102
variable {R : Type*} [CommRing R]
theorem residual_power_zero_iff (I J : Ideal R) (n : ℕ) :
    (I.map (Ideal.Quotient.mk J)) ^ n = ⊥ ↔ I ^ n ≤ J := by
  rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
theorem residual_power_zero (I : Ideal R) (n : ℕ) :
    residual I n ^ (n + 1) = ⊥ := by
  exact (residual_power_zero_iff I (I ^ (n + 1)) (n + 1)).2 le_rfl
theorem residual_nilpotent (I : Ideal R) (n : ℕ) : IsNilpotent (residual I n) := by
  exact ⟨n + 1, residual_power_zero I n⟩
theorem residual_transition (I : Ideal R) {m n : ℕ} (h : m ≤ n) :
    (residual I n).map (transition I h) = residual I m := by
  simp only [residual, transition, Ideal.map_map, Ideal.Quotient.factor_comp_mk]
theorem residual_composition (I : Ideal R) {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) :
    (transition I h).comp (transition I k) = transition I (h.trans k) := by
  unfold transition
  exact Ideal.Quotient.factor_comp _ _
theorem top_int_not_nilpotent : ¬ IsNilpotent (⊤ : Ideal ℤ) := by
  rintro ⟨n, hn⟩
  have h : (⊤ : Ideal ℤ) = ⊥ := by
    simpa only [← Ideal.one_eq_top, one_pow, Ideal.zero_eq_bot] using hn
  have hz : (1 : ℤ) ∈ (⊥ : Ideal ℤ) := h ▸ (show (1 : ℤ) ∈ (⊤ : Ideal ℤ) from trivial)
  simpa using hz
#print axioms residual_power_zero_iff
#print axioms residual_power_zero
#print axioms residual_nilpotent
#print axioms residual_transition
#print axioms residual_composition
#print axioms top_int_not_nilpotent
end MathGauge.F102
