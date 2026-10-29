import Reference
import Candidate
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.Tactic

namespace MathGauge.F101
variable {R : Type*} [CommRing R]

theorem zero_exponent_iff (A B : Ideal R) :
    (A.map (Ideal.Quotient.mk B)) ^ 0 = ⊥ ↔ B = ⊤ := by
  rw [residual_power_zero_iff, pow_zero, Ideal.one_eq_top, top_le_iff]

theorem transition_surjective (I : Ideal R) {m n : ℕ} (h : m ≤ n) :
    Function.Surjective (transition I h) := Ideal.Quotient.factor_surjective _

theorem transition_kernel (I : Ideal R) {m n : ℕ} (h : m ≤ n) :
    RingHom.ker (transition I h) = (I ^ (m + 1)).map (Ideal.Quotient.mk (I ^ (n + 1))) :=
  Ideal.Quotient.factor_ker _

theorem transition_bijective_iff (I : Ideal R) {m n : ℕ} (h : m ≤ n) :
    Function.Bijective (transition I h) ↔ I ^ (m + 1) = I ^ (n + 1) := by
  rw [Function.Bijective, RingHom.injective_iff_ker_eq_bot, transition_kernel,
    Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  exact ⟨fun hh => le_antisymm hh.1 (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)),
    fun he => ⟨he.le, transition_surjective I h⟩⟩

noncomputable def transition_equiv_of_powers_eq (I : Ideal R) {m n : ℕ} (h : m ≤ n)
    (he : I ^ (m + 1) = I ^ (n + 1)) : Level I n ≃+* Level I m :=
  RingEquiv.ofBijective (transition I h) ((transition_bijective_iff I h).mpr he)

theorem uniform_bound_iff_intersection (I : Ideal R) (N : ℕ) :
    (∀ n, residual I n ^ N = ⊥) ↔ I ^ N ≤ ⨅ n : ℕ, I ^ (n + 1) := by
  simp only [le_iInf_iff]
  exact forall_congr' fun n => residual_power_zero_iff I (I ^ (n + 1)) N

theorem uniform_top_int : (∀ n, residual (⊤ : Ideal ℤ) n ^ 1 = ⊥) ∧
    ¬ IsNilpotent (⊤ : Ideal ℤ) := by
  refine ⟨?_, top_int_not_nilpotent⟩
  intro n
  apply (residual_power_zero_iff ⊤ (⊤ ^ (n + 1)) 1).mpr
  simp only [← Ideal.one_eq_top, one_pow]
  exact le_rfl

theorem separated_uniform_iff (I : Ideal R) (hsep : (⨅ n : ℕ, I ^ (n + 1)) = ⊥) (N : ℕ) :
    (∀ n, residual I n ^ N = ⊥) ↔ I ^ N = ⊥ := by
  rw [uniform_bound_iff_intersection, hsep, le_bot_iff]

theorem no_source_data_top_int : IsEmpty (SourceData (⊤ : Ideal ℤ)) := by
  refine ⟨fun d => top_int_not_nilpotent ⟨d.exponent, d.annihilates⟩⟩

end MathGauge.F101
