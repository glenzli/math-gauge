import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Arithmetic on the exact two-dimensional integer frequency lattice.
No smooth solvability or Fourier multiplier conclusion is assumed here. -/

noncomputable section

namespace MathGauge.PublicProof.Torus

abbrev Frequency := Fin 2 → ℤ

def weight (k : Frequency) : ℝ :=
  Real.sqrt (1 + (k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2)

def divisor (α : ℝ) (k : Frequency) : ℝ := α * (k 0 : ℝ) + (k 1 : ℝ)

def HasDivisorBound (α s : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ k : Frequency, k ≠ 0 → c ≤ weight k ^ s * |divisor α k|

lemma weight_sq (k : Frequency) :
    weight k ^ 2 = 1 + (k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2 := by
  exact Real.sq_sqrt (by positivity)

lemma one_le_weight (k : Frequency) : 1 ≤ weight k := by
  have h := weight_sq k
  have hnonneg : 0 ≤ weight k := Real.sqrt_nonneg _
  nlinarith [sq_nonneg (k 0 : ℝ), sq_nonneg (k 1 : ℝ)]

lemma weight_pos (k : Frequency) : 0 < weight k := lt_of_lt_of_le zero_lt_one (one_le_weight k)

lemma abs_coord_le_weight (k : Frequency) (i : Fin 2) : |(k i : ℝ)| ≤ weight k := by
  have h := weight_sq k
  have hw := (weight_pos k).le
  fin_cases i
  · change |(k 0 : ℝ)| ≤ weight k
    rw [← sq_le_sq₀ (abs_nonneg _) hw, sq_abs]
    nlinarith [sq_nonneg (k 1 : ℝ)]
  · change |(k 1 : ℝ)| ≤ weight k
    rw [← sq_le_sq₀ (abs_nonneg _) hw, sq_abs]
    nlinarith [sq_nonneg (k 0 : ℝ)]

lemma divisor_ne_zero (α : ℝ) (hα : Irrational α) (k : Frequency) (hk : k ≠ 0) :
    divisor α k ≠ 0 := by
  by_cases h0 : k 0 = 0
  · have h1 : k 1 ≠ 0 := by
      intro h1
      apply hk
      ext i
      fin_cases i <;> simp_all
    simpa [divisor, h0] using (Int.cast_ne_zero.mpr h1 : (k 1 : ℝ) ≠ 0)
  · simpa only [divisor, Int.cast_zero] using ((hα.mul_intCast h0).add_intCast (k 1)).ne_int 0

lemma divisor_bound_mono {α s t : ℝ} (h : HasDivisorBound α s) (hst : s ≤ t) :
    HasDivisorBound α t := by
  obtain ⟨c, hc, hbound⟩ := h
  refine ⟨c, hc, fun k hk => (hbound k hk).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (one_le_weight k) hst)
    (abs_nonneg _)

def quadraticDirection : ℝ := Real.sqrt 2 - 1

lemma quadraticDirection_irrational : Irrational quadraticDirection := by
  simpa [quadraticDirection] using irrational_sqrt_two.sub_intCast 1

lemma conjugateDirection_irrational : Irrational (-Real.sqrt 2 - 1) := by
  simpa using irrational_sqrt_two.neg.sub_intCast 1

lemma conjugate_product (k : Frequency) :
    divisor quadraticDirection k * divisor (-Real.sqrt 2 - 1) k =
      (((k 1 - k 0) ^ 2 - 2 * k 0 ^ 2 : ℤ) : ℝ) := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  push_cast
  dsimp [divisor, quadraticDirection]
  nlinarith

lemma one_le_abs_conjugate_product (k : Frequency) (hk : k ≠ 0) :
    1 ≤ |divisor quadraticDirection k| * |divisor (-Real.sqrt 2 - 1) k| := by
  have hn : (k 1 - k 0) ^ 2 - 2 * k 0 ^ 2 ≠ 0 := by
    intro hz
    have hp := conjugate_product k
    rw [hz, Int.cast_zero] at hp
    exact (mul_ne_zero (divisor_ne_zero _ quadraticDirection_irrational k hk)
      (divisor_ne_zero _ conjugateDirection_irrational k hk)) hp
  have hi : (1 : ℤ) ≤ |(k 1 - k 0) ^ 2 - 2 * k 0 ^ 2| := Int.one_le_abs hn
  have hr : (1 : ℝ) ≤ |(((k 1 - k 0) ^ 2 - 2 * k 0 ^ 2 : ℤ) : ℝ)| := by exact_mod_cast hi
  simpa only [← conjugate_product, abs_mul] using hr

lemma conjugate_upper_bound (k : Frequency) :
    |divisor (-Real.sqrt 2 - 1) k| ≤ (2 + Real.sqrt 2) * weight k := by
  have hident : divisor (-Real.sqrt 2 - 1) k = (k 1 : ℝ) - (1 + Real.sqrt 2) * (k 0 : ℝ) := by
    dsimp [divisor]
    ring
  rw [hident]
  calc
    |(k 1 : ℝ) - (1 + Real.sqrt 2) * (k 0 : ℝ)|
        ≤ |(k 1 : ℝ)| + |(1 + Real.sqrt 2) * (k 0 : ℝ)| := abs_sub _ _
    _ = |(k 1 : ℝ)| + (1 + Real.sqrt 2) * |(k 0 : ℝ)| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + Real.sqrt 2)]
    _ ≤ weight k + (1 + Real.sqrt 2) * weight k := by
      exact add_le_add (abs_coord_le_weight k 1)
        (mul_le_mul_of_nonneg_left (abs_coord_le_weight k 0) (by positivity))
    _ = (2 + Real.sqrt 2) * weight k := by ring

/-- An explicit attained arithmetic bound at loss one. -/
theorem quadratic_divisor_bound_one : HasDivisorBound quadraticDirection 1 := by
  refine ⟨1 / (2 + Real.sqrt 2), by positivity, ?_⟩
  intro k hk
  rw [Real.rpow_one]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 + Real.sqrt 2)).mpr
  have h := (one_le_abs_conjugate_product k hk).trans
    (mul_le_mul_of_nonneg_left (conjugate_upper_bound k) (abs_nonneg _))
  nlinarith

end MathGauge.PublicProof.Torus
