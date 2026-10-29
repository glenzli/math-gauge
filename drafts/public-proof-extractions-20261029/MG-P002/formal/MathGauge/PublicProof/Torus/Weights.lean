import MathGauge.PublicProof.Torus.GeneralInverse
import MathGauge.PublicProof.Torus.ArithmeticSharp

noncomputable section
namespace MathGauge.PublicProof.Torus
open Borrowed.TorusInverse Borrowed.SmoothFourierData

def pairWeight (k : PairFrequency) : ℝ := weight ![k.1, k.2]

lemma pairWeight_pos (k : PairFrequency) : 0 < pairWeight k := weight_pos _
lemma one_le_pairWeight (k : PairFrequency) : 1 ≤ pairWeight k := one_le_weight _
lemma pairWeight_le_l1 (k : PairFrequency) : pairWeight k ≤ Borrowed.TorusInverse.weight k := by
  simpa [pairWeight, Borrowed.TorusInverse.weight] using weight_le_l1 ![k.1, k.2]
lemma l1_le_three_pairWeight (k : PairFrequency) : Borrowed.TorusInverse.weight k ≤ 3 * pairWeight k := by
  have h0 := abs_coord_le_weight ![k.1, k.2] 0
  have h1 := abs_coord_le_weight ![k.1, k.2] 1
  have hw := one_le_pairWeight k
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h0 h1
  dsimp [Borrowed.TorusInverse.weight, pairWeight] at *
  linarith

def PairHasDivisorBound (α s : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ k : PairFrequency, k ≠ 0 → c ≤ pairWeight k ^ s * |pairDivisor α k|

lemma pair_bound_iff_native (α s : ℝ) : PairHasDivisorBound α s ↔ HasDivisorBound α s := by
  constructor
  · rintro ⟨c, hc, hb⟩
    refine ⟨c, hc, ?_⟩
    intro k hk
    have hp : (k 0, k 1) ≠ (0 : PairFrequency) := by
      intro hz
      apply hk
      ext i
      fin_cases i
      · exact congrArg Prod.fst hz
      · exact congrArg Prod.snd hz
    have he : (![k 0, k 1] : Frequency) = k := by ext i; fin_cases i <;> rfl
    simpa only [pairWeight, pairDivisor, divisor, he] using hb (k 0, k 1) hp
  · rintro ⟨c, hc, hb⟩
    refine ⟨c, hc, ?_⟩
    intro k hk
    have hn : (![k.1, k.2] : Frequency) ≠ 0 := by
      intro hz
      apply hk
      apply Prod.ext
      · simpa using congrFun hz 0
      · simpa using congrFun hz 1
    exact hb ![k.1, k.2] hn

/-- The existence of a real nonnegative loss and of a natural polynomial
bound are equivalent; no endpoint is lost by this existence-only conversion. -/
theorem polynomial_bound_iff_exists_real (α : ℝ) :
    PolynomialDivisorBound α ↔ ∃ s : ℝ, 0 ≤ s ∧ PairHasDivisorBound α s := by
  constructor
  · rintro ⟨n, c, hc, hb⟩
    refine ⟨n, by positivity, c / 3 ^ n, by positivity, ?_⟩
    intro k hk
    rw [Real.rpow_natCast]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 3 ^ n)).mpr
    calc
      c ≤ Borrowed.TorusInverse.weight k ^ n * |pairDivisor α k| := hb k hk
      _ ≤ (3 * pairWeight k) ^ n * |pairDivisor α k| :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Borrowed.TorusInverse.weight_pos k).le
          (l1_le_three_pairWeight k) n) (abs_nonneg _)
      _ = _ := by rw [mul_pow]; ring
  · rintro ⟨s, hs, c, hc, hb⟩
    obtain ⟨n, hn⟩ := exists_nat_ge s
    refine ⟨n, c, hc, ?_⟩
    intro k hk
    apply (hb k hk).trans
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    calc
      pairWeight k ^ s ≤ pairWeight k ^ (n : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (one_le_pairWeight k) hn
      _ = pairWeight k ^ n := Real.rpow_natCast _ _
      _ ≤ Borrowed.TorusInverse.weight k ^ n := pow_le_pow_left₀ (pairWeight_pos k).le (pairWeight_le_l1 k) n

end MathGauge.PublicProof.Torus
