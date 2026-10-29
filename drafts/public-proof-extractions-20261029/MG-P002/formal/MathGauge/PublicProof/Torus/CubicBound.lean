import MathGauge.PublicProof.Torus.Borrowed.SmoothFourierData
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The missing one-derivative improvement: a cubic lattice majorant in dimension two,
then the actual `m+4` derivative-word estimate. This is new, not claimed to be upstream. -/

noncomputable section
namespace MathGauge.PublicProof.Torus

open Set
open scoped ContDiff Topology
open Borrowed.TorusInverse Borrowed.SmoothFourierData

lemma summable_integer_weight_neg_three_halves :
    Summable (fun n : ℤ => (1 + |(n : ℝ)|) ^ (-(3 / 2 : ℝ))) := by
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hNat : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ))) := by
    have h := (summable_nat_add_iff 1).mpr hbase
    simpa only [Nat.cast_add, Nat.cast_one] using h
  apply Summable.of_nat_of_neg
  · simpa only [Int.cast_natCast, Nat.abs_cast, add_comm] using hNat
  · simpa only [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast, add_comm] using hNat

lemma weight_inv_three_le_product (k : Borrowed.TorusInverse.Frequency) :
    (Borrowed.TorusInverse.weight k ^ 3)⁻¹ ≤
      (1 + |(k.1 : ℝ)|) ^ (-(3 / 2 : ℝ)) *
      (1 + |(k.2 : ℝ)|) ^ (-(3 / 2 : ℝ)) := by
  have hfirst : 1 + |(k.1 : ℝ)| ≤ Borrowed.TorusInverse.weight k := by
    unfold Borrowed.TorusInverse.weight
    linarith [abs_nonneg (k.2 : ℝ)]
  have hsecond : 1 + |(k.2 : ℝ)| ≤ Borrowed.TorusInverse.weight k := by
    unfold Borrowed.TorusInverse.weight
    linarith [abs_nonneg (k.1 : ℝ)]
  have hprod : (1 + |(k.1 : ℝ)|) ^ (3 / 2 : ℝ) * (1 + |(k.2 : ℝ)|) ^ (3 / 2 : ℝ)
      ≤ Borrowed.TorusInverse.weight k ^ 3 := by
    calc
      _ ≤ Borrowed.TorusInverse.weight k ^ (3 / 2 : ℝ) *
          Borrowed.TorusInverse.weight k ^ (3 / 2 : ℝ) :=
        mul_le_mul (Real.rpow_le_rpow (by positivity) hfirst (by norm_num))
          (Real.rpow_le_rpow (by positivity) hsecond (by norm_num))
          (by positivity) (Real.rpow_nonneg (Borrowed.TorusInverse.weight_pos k).le _)
      _ = _ := by rw [← Real.rpow_add (Borrowed.TorusInverse.weight_pos k)]; norm_num
  have h := one_div_le_one_div_of_le (by positivity : (0 : ℝ) <
    (1 + |(k.1 : ℝ)|) ^ (3 / 2 : ℝ) * (1 + |(k.2 : ℝ)|) ^ (3 / 2 : ℝ)) hprod
  simpa only [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + |(k.1 : ℝ)|),
    Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + |(k.2 : ℝ)|),
    one_div, mul_inv_rev, mul_comm] using h

/-- Dimension two admits cubic absolute decay. -/
theorem summable_weight_inv_three :
    Summable (fun k : Borrowed.TorusInverse.Frequency => (Borrowed.TorusInverse.weight k ^ 3)⁻¹) := by
  have hprod := summable_integer_weight_neg_three_halves.mul_of_nonneg
    summable_integer_weight_neg_three_halves (fun n => by positivity) (fun n => by positivity)
  exact Summable.of_nonneg_of_le (fun k => inv_nonneg.mpr
    (pow_nonneg (Borrowed.TorusInverse.weight_pos k).le _)) weight_inv_three_le_product hprod

/-- The quantitative Fourier moment needs only `p+3` actual input derivatives. -/
theorem coefficient_seminorm_bound_three {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) (p : ℕ) {C : ℝ}
    (hzero : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, ‖f (x, y)‖ ≤ C)
    (hfirst : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖xJet (p + 3) f (x, y)‖ ≤ C)
    (hsecond : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖xJet (p + 3) (swapFunction f) (x, y)‖ ≤ C) :
    coeffSeminorm p (coefficient f) ≤
      (3 ^ (p + 3) * C) * ∑' k : Borrowed.TorusInverse.Frequency, (Borrowed.TorusInverse.weight k ^ 3)⁻¹ := by
  have hb (k : Borrowed.TorusInverse.Frequency) :
      Borrowed.TorusInverse.weight k ^ p * ‖coefficient f k‖ ≤
      (3 ^ (p + 3) * C) * (Borrowed.TorusInverse.weight k ^ 3)⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos (Borrowed.TorusInverse.weight_pos k) 3)).mpr
    calc
      (Borrowed.TorusInverse.weight k ^ p * ‖coefficient f k‖) * Borrowed.TorusInverse.weight k ^ 3 =
          Borrowed.TorusInverse.weight k ^ (p + 3) * ‖coefficient f k‖ := by rw [pow_add]; ring
      _ ≤ 3 ^ (p + 3) * C := coefficient_polynomial_bound hf hp (p + 3) hzero hfirst hsecond k
  have h := (rapid_coefficient hf hp p).tsum_le_tsum hb
    (summable_weight_inv_three.mul_left (3 ^ (p + 3) * C))
  simpa only [coeffSeminorm, tsum_mul_left] using h

/-- A genuine `m+4` estimate for every actual mixed derivative word of the inverse.
The hypotheses bound the source and its two pure derivatives of order `m+4`.
They are weaker than the task's single `C^(m+4)` bound. -/
theorem inverse_derivativeWord_bound_four (d : Direction) {f : Plane → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : UnitPeriodic f) (w : List Bool) {C : ℝ}
    (hzero : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, ‖f (x, y)‖ ≤ C)
    (hfirst : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖xJet (w.length + 4) f (x, y)‖ ≤ C)
    (hsecond : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖xJet (w.length + 4) (swapFunction f) (x, y)‖ ≤ C) (x : Plane) :
    ‖derivativeWord w (directionalInverse d (coefficient f)) x‖ ≤
      (((6 * ‖omega⁻¹‖) * ‖omega‖ ^ w.length) * 3 ^ (w.length + 4) *
        ∑' k : Borrowed.TorusInverse.Frequency, (Borrowed.TorusInverse.weight k ^ 3)⁻¹) * C := by
  apply (inverse_derivativeWord_bound d (rapid_coefficient hf hp) w x).trans
  have hb := coefficient_seminorm_bound_three hf hp (w.length + 1) hzero hfirst hsecond
  have hm := mul_le_mul_of_nonneg_left hb
    (by positivity : 0 ≤ (6 * ‖omega⁻¹‖) * ‖omega‖ ^ w.length)
  convert hm using 1 <;> ring

end MathGauge.PublicProof.Torus
