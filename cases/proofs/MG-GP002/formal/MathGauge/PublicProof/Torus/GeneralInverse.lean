import MathGauge.PublicProof.Torus.GeneralTransport

noncomputable section
namespace MathGauge.PublicProof.Torus
open scoped ContDiff Topology
open Borrowed.TorusInverse Borrowed.SmoothFourierData

/-- A genuine arithmetic hypothesis, independent of the forcing and its solution. -/
def PolynomialDivisorBound (α : ℝ) : Prop :=
  ∃ n : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ k : PairFrequency, k ≠ 0 →
    c ≤ Borrowed.TorusInverse.weight k ^ n * |pairDivisor α k|

def generalMultiplier (α : ℝ) (k : PairFrequency) : ℂ :=
  (omega * (pairDivisor α k : ℂ))⁻¹

def generalInverseCoefficients (α : ℝ) (a : PairFrequency → ℂ) (k : PairFrequency) : ℂ :=
  generalMultiplier α k * a k

def generalInverse (α : ℝ) (f : Plane → ℂ) : Plane → ℂ :=
  series (generalInverseCoefficients α (coefficient f))

lemma rapid_mul_polynomial {a b : PairFrequency → ℂ} (ha : Rapid a) (C : ℝ) (n : ℕ)
    (hb : ∀ k, ‖b k‖ ≤ C * Borrowed.TorusInverse.weight k ^ n) : Rapid (fun k => b k * a k) := by
  intro p
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (Borrowed.TorusInverse.weight_pos k).le _) (norm_nonneg _)) _
    ((ha (p + n)).mul_left C)
  intro k
  calc
    Borrowed.TorusInverse.weight k ^ p * ‖b k * a k‖ =
        Borrowed.TorusInverse.weight k ^ p * (‖b k‖ * ‖a k‖) := by rw [norm_mul]
    _ ≤ Borrowed.TorusInverse.weight k ^ p * ((C * Borrowed.TorusInverse.weight k ^ n) * ‖a k‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hb k) (norm_nonneg _))
        (pow_nonneg (Borrowed.TorusInverse.weight_pos k).le _)
    _ = C * (Borrowed.TorusInverse.weight k ^ (p + n) * ‖a k‖) := by rw [pow_add]; ring

lemma multiplier_polynomial_bound {α c : ℝ} {n : ℕ} (hc : 0 < c)
    (hb : ∀ k : PairFrequency, k ≠ 0 → c ≤ Borrowed.TorusInverse.weight k ^ n * |pairDivisor α k|)
    (k : PairFrequency) :
    ‖generalMultiplier α k‖ ≤ (‖omega⁻¹‖ / c) * Borrowed.TorusInverse.weight k ^ n := by
  by_cases hk : k = 0
  · simp [hk, generalMultiplier, pairDivisor, Borrowed.TorusInverse.weight]
    positivity
  · have hd : 0 < |pairDivisor α k| := by
      have h := hb k hk
      have hw : 0 < Borrowed.TorusInverse.weight k ^ n := pow_pos (Borrowed.TorusInverse.weight_pos k) _
      nlinarith
    have hinv : |pairDivisor α k|⁻¹ ≤ Borrowed.TorusInverse.weight k ^ n / c := by
      rw [inv_eq_one_div]
      apply (div_le_div_iff₀ hd hc).mpr
      simpa only [one_mul] using hb k hk
    calc
      ‖generalMultiplier α k‖ = ‖omega⁻¹‖ * |pairDivisor α k|⁻¹ := by
        simp only [generalMultiplier, mul_inv_rev, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
        ring
      _ ≤ ‖omega⁻¹‖ * (Borrowed.TorusInverse.weight k ^ n / c) :=
        mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
      _ = _ := by ring

lemma rapid_generalInverseCoefficients {α : ℝ} (hb : PolynomialDivisorBound α)
    {a : PairFrequency → ℂ} (ha : Rapid a) : Rapid (generalInverseCoefficients α a) := by
  obtain ⟨n, c, hc, hbound⟩ := hb
  exact rapid_mul_polynomial ha (‖omega⁻¹‖ / c) n (multiplier_polynomial_bound hc hbound)

lemma generalInverse_zero_coefficient (α : ℝ) (a : PairFrequency → ℂ) :
    generalInverseCoefficients α a 0 = 0 := by
  simp [generalInverseCoefficients, generalMultiplier, pairDivisor]

lemma transport_generalInverseCoefficients {α : ℝ} (hα : Irrational α)
    {a : PairFrequency → ℂ} (ha0 : a 0 = 0) :
    transportCoefficients α (generalInverseCoefficients α a) = a := by
  funext k
  rw [transportCoefficients_formula]
  by_cases hk : k = 0
  · simp [hk, ha0, pairDivisor]
  · have hd := mul_ne_zero omega_ne_zero (Complex.ofReal_ne_zero.mpr (pairDivisor_ne_zero hα k hk))
    change (omega * (pairDivisor α k : ℂ)) * ((omega * (pairDivisor α k : ℂ))⁻¹ * a k) = a k
    rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]

/-- Explicit smooth zero-mean solution for every smooth forcing, from a finite
polynomial arithmetic lower bound. The Fourier assumptions are proved from `hf,hp`. -/
theorem generalInverse_properties {α : ℝ} (hα : Irrational α) (hb : PolynomialDivisorBound α)
    {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (hp : UnitPeriodic f) (hmean : coefficient f 0 = 0) :
    ContDiff ℝ ∞ (generalInverse α f) ∧ UnitPeriodic (generalInverse α f) ∧
    coefficient (generalInverse α f) 0 = 0 ∧ transportCover α (generalInverse α f) = f := by
  have ha := rapid_coefficient hf hp
  have hi := rapid_generalInverseCoefficients hb ha
  refine ⟨contDiff_series hi, ?_, ?_, ?_⟩
  · intro x k
    exact series_periodic _ x k.1 k.2
  · exact (coefficient_series_eq hi 0).trans (generalInverse_zero_coefficient α _)
  · unfold generalInverse
    rw [transportCover_series α hi, transport_generalInverseCoefficients hα hmean]
    exact funext (series_coefficient hf hp)

end MathGauge.PublicProof.Torus
