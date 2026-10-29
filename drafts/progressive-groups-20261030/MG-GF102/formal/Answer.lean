import Reference
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Tactic

noncomputable section
namespace MathGauge.F102
variable {R : Type*} [CommRing R]

def sourceMap (I : Ideal R) (n : ℕ) : R →+* Level I n := Ideal.Quotient.mk _

theorem source_injective_iff (I : Ideal R) (n : ℕ) :
    Function.Injective (sourceMap I n) ↔ I ^ (n + 1) = ⊥ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  simp only [sourceMap, Ideal.mk_ker]

def level_zero_equiv (I : Ideal R) : Level I 0 ≃+* R ⧸ I :=
  Ideal.quotEquivOfEq (by simp)

theorem square_zero_higher_power (I : Ideal R) (hI : I ^ 2 = ⊥) {n : ℕ} (hn : 1 ≤ n) :
    I ^ (n + 1) = ⊥ := by
  apply le_antisymm _ bot_le
  exact (Ideal.pow_le_pow_right (show 2 ≤ n + 1 by omega)).trans hI.le

def square_zero_level_equiv (I : Ideal R) (hI : I ^ 2 = ⊥) {n : ℕ} (hn : 1 ≤ n) :
    R ≃+* Level I n := RingEquiv.ofBijective (sourceMap I n)
      ⟨(source_injective_iff I n).mpr (square_zero_higher_power I hI hn), Ideal.Quotient.mk_surjective⟩

theorem square_zero_residual (I : Ideal R) (hI : I ^ 2 = ⊥) {n : ℕ} (hn : 1 ≤ n) :
    I.map (square_zero_level_equiv I hI hn).toRingHom = residual I n := rfl

theorem transition_source (I : Ideal R) {m n : ℕ} (h : m ≤ n) :
    (transition I h).comp (sourceMap I n) = sourceMap I m := by
  exact Ideal.Quotient.factor_comp_mk _

theorem square_zero_transition (I : Ideal R) (hI : I ^ 2 = ⊥) {m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m ≤ n) :
    (transition I hmn).comp (square_zero_level_equiv I hI hn).toRingHom =
      (square_zero_level_equiv I hI hm).toRingHom := transition_source I hmn

theorem square_zero_to_zero (I : Ideal R) (hI : I ^ 2 = ⊥) {n : ℕ} (hn : 1 ≤ n) :
    (level_zero_equiv I).toRingHom.comp
      ((transition I (Nat.zero_le n)).comp (square_zero_level_equiv I hI hn).toRingHom) =
      Ideal.Quotient.mk I := by ext a; rfl

theorem nilpotent_iff_eventual_source_injective (I : Ideal R) :
    IsNilpotent I ↔ ∃ N : ℕ, ∀ n ≥ N, Function.Injective (sourceMap I n) := by
  constructor
  · rintro ⟨e,he⟩
    refine ⟨e,fun n hn => (source_injective_iff I n).mpr ?_⟩
    apply le_antisymm _ bot_le
    exact (Ideal.pow_le_pow_right (show e ≤ n + 1 by omega)).trans (by simpa using he.le)
  · rintro ⟨N,hN⟩
    exact ⟨N+1,(source_injective_iff I N).mp (hN N le_rfl)⟩

variable {S : Type*} [CommRing S]

def inducedLevel (I : Ideal R) (L : Ideal S) (φ : R →+* S) (hφ : I.map φ ≤ L) (n : ℕ) :
    Level I n →+* Level L n :=
  Ideal.quotientMap (L ^ (n+1)) φ (Ideal.map_le_iff_le_comap.mp (by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' hφ (n+1)))

theorem induced_source (I : Ideal R) (L : Ideal S) (φ : R →+* S) (hφ : I.map φ ≤ L) (n : ℕ) :
    (inducedLevel I L φ hφ n).comp (sourceMap I n) = (sourceMap L n).comp φ := by
  ext a; rfl

theorem induced_transition (I : Ideal R) (L : Ideal S) (φ : R →+* S) (hφ : I.map φ ≤ L)
    {m n : ℕ} (h : m ≤ n) :
    (transition L h).comp (inducedLevel I L φ hφ n) =
      (inducedLevel I L φ hφ m).comp (transition I h) := by
  apply RingHom.ext
  intro z
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

def twoIdeal : Ideal ℤ := Ideal.span {2}

def integer_level_zero_equiv : Level twoIdeal 0 ≃+* ZMod 2 :=
  (level_zero_equiv twoIdeal).trans (Int.quotientSpanNatEquivZMod 2)

theorem twoIdeal_square : twoIdeal ^ 2 = Ideal.span ({4} : Set ℤ) := by
  rw [twoIdeal, Ideal.span_singleton_pow]
  norm_num

def integer_level_one_equiv : Level twoIdeal 1 ≃+* ZMod 4 :=
  (Ideal.quotEquivOfEq twoIdeal_square).trans (Int.quotientSpanNatEquivZMod 4)

def zero_ideal_level_equiv (n : ℕ) : Level (⊥ : Ideal (ZMod 2)) n ≃+* ZMod 2 :=
  (Ideal.quotEquivOfEq (by simp)).trans (RingEquiv.quotientBot (ZMod 2))

def matching_zero_levels : Level twoIdeal 0 ≃+* Level (⊥ : Ideal (ZMod 2)) 0 :=
  integer_level_zero_equiv.trans (zero_ideal_level_equiv 0).symm

theorem zmod_four_two_not_isomorphic : ¬ Nonempty (ZMod 4 ≃+* ZMod 2) := by
  rintro ⟨e⟩
  have h := Nat.card_congr e.toEquiv
  norm_num [Nat.card_zmod] at h

theorem higher_levels_not_isomorphic :
    ¬ Nonempty (Level twoIdeal 1 ≃+* Level (⊥ : Ideal (ZMod 2)) 1) := by
  rintro ⟨e⟩
  exact zmod_four_two_not_isomorphic ⟨integer_level_one_equiv.symm.trans
    (e.trans (zero_ideal_level_equiv 1))⟩

theorem modulo_two_compatible : twoIdeal.map (Int.castRingHom (ZMod 2)) ≤ ⊥ := by
  rw [twoIdeal, Ideal.map_span, Set.image_singleton]
  have hz : (Int.castRingHom (ZMod 2)) (2 : ℤ) = 0 := by decide
  rw [hz]
  simp

theorem induced_example_not_injective :
    ¬ Function.Injective (inducedLevel twoIdeal (⊥ : Ideal (ZMod 2))
      (Int.castRingHom (ZMod 2)) modulo_two_compatible 1) := by
  intro hi
  have hz : sourceMap twoIdeal 1 2 = 0 := hi (by
    change Ideal.Quotient.mk _ ((Int.castRingHom (ZMod 2)) 2) = _
    have hz : (Int.castRingHom (ZMod 2)) (2 : ℤ) = 0 := by decide
    rw [hz]
    simp)
  have hm : (2 : ℤ) ∈ twoIdeal ^ 2 := Ideal.Quotient.eq_zero_iff_mem.mp hz
  rw [twoIdeal_square, Ideal.mem_span_singleton] at hm
  norm_num at hm

end MathGauge.F102
