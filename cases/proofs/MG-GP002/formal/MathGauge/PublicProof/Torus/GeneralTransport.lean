import MathGauge.PublicProof.Torus.FourierBridge
import MathGauge.PublicProof.Torus.Arithmetic

noncomputable section
namespace MathGauge.PublicProof.Torus
open MeasureTheory
open scoped Topology ContDiff
open Borrowed.TorusInverse Borrowed.SmoothFourierData

abbrev PairFrequency := Borrowed.TorusInverse.Frequency
abbrev PairTorus := Borrowed.TorusInverse.Torus

def pairDivisor (α : ℝ) (k : PairFrequency) : ℝ := α * (k.1 : ℝ) + (k.2 : ℝ)

def transportCover (α : ℝ) (f : Plane → ℂ) (x : Plane) : ℂ :=
  fderiv ℝ f x (α, 1)

def transportCoefficients (α : ℝ) (a : PairFrequency → ℂ) (k : PairFrequency) : ℂ :=
  (α : ℂ) * derivX a k + derivY a k

lemma transportCoefficients_formula (α : ℝ) (a : PairFrequency → ℂ) (k : PairFrequency) :
    transportCoefficients α a k = omega * (pairDivisor α k : ℂ) * a k := by
  simp only [transportCoefficients, pairDivisor, derivX, derivY, freqX, freqY,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_intCast]
  ring

lemma rapid_transportCoefficients (α : ℝ) {a : PairFrequency → ℂ} (ha : Rapid a) :
    Rapid (transportCoefficients α a) := by
  have hb (k : PairFrequency) :
      ‖(α : ℂ) * freqX k + freqY k‖ ≤ ((|α| + 1) * ‖omega‖) * Borrowed.TorusInverse.weight k := by
    calc
      _ ≤ ‖(α : ℂ) * freqX k‖ + ‖freqY k‖ := norm_add_le _ _
      _ = |α| * ‖freqX k‖ + ‖freqY k‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |α| * (‖omega‖ * Borrowed.TorusInverse.weight k) + ‖omega‖ * Borrowed.TorusInverse.weight k :=
        add_le_add (mul_le_mul_of_nonneg_left (norm_freqX_le k) (abs_nonneg _)) (norm_freqY_le k)
      _ = _ := by ring
  have h := ha.mul_linear ((|α| + 1) * ‖omega‖) hb
  convert h using 1
  funext k
  simp only [transportCoefficients, derivX, derivY]
  ring

lemma transportCover_coordinate_formula (α : ℝ) (f : Plane → ℂ) (x : Plane) :
    transportCover α f x = (α : ℂ) * coordinatePartial false f x + coordinatePartial true f x := by
  have hv : (α, (1 : ℝ)) = α • ((1 : ℝ), (0 : ℝ)) + ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  simp only [transportCover, coordinatePartial, Bool.false_eq_true, ↓reduceIte]
  rw [hv, map_add, map_smul, Complex.real_smul]

lemma transportCover_series (α : ℝ) {a : PairFrequency → ℂ} (ha : Rapid a) :
    transportCover α (series a) = series (transportCoefficients α a) := by
  funext x
  rw [transportCover_coordinate_formula, coordinatePartial_series false ha,
    coordinatePartial_series true ha]
  simp only [coordinateCoeff, Bool.false_eq_true, ↓reduceIte]
  unfold series
  rw [← tsum_mul_left, ← (summable_terms ha.derivX x |>.mul_left (α : ℂ)).tsum_add (summable_terms ha.derivY x)]
  apply tsum_congr
  intro k
  simp only [transportCoefficients]
  ring

/-- The actual directional derivative has the required Fourier multiplier at every mode. -/
theorem coefficient_transportCover {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) (α : ℝ) (k : PairFrequency) :
    coefficient (transportCover α f) k = omega * (pairDivisor α k : ℂ) * coefficient f k := by
  have ha := rapid_coefficient hf hp
  have he : series (coefficient f) = f := funext (series_coefficient hf hp)
  have hd := transportCover_series α ha
  rw [he] at hd
  rw [hd, coefficient_series_eq (rapid_transportCoefficients α ha), transportCoefficients_formula]

lemma pairDivisor_ne_zero {α : ℝ} (hα : Irrational α) (k : PairFrequency) (hk : k ≠ 0) :
    pairDivisor α k ≠ 0 := by
  have h : (![k.1, k.2] : Frequency) ≠ 0 := by
    intro hz
    apply hk
    apply Prod.ext
    · simpa using congrFun hz 0
    · simpa using congrFun hz 1
  exact divisor_ne_zero α hα ![k.1, k.2] h

/-- Actual Fourier uniqueness on the universal cover. -/
theorem smoothPeriodic_ext {f g : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (hp : UnitPeriodic f)
    (hg : ContDiff ℝ ∞ g) (hgp : UnitPeriodic g) (hc : coefficient f = coefficient g) : f = g := by
  rw [← funext (series_coefficient hf hp), ← funext (series_coefficient hg hgp), hc]

/-- Irrationality gives uniqueness for the original smooth zero-mean equation. -/
theorem transportCover_injective_zeroMean {α : ℝ} (hα : Irrational α)
    {f g : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (hp : UnitPeriodic f)
    (hg : ContDiff ℝ ∞ g) (hgp : UnitPeriodic g)
    (hf0 : coefficient f 0 = 0) (hg0 : coefficient g 0 = 0)
    (he : transportCover α f = transportCover α g) : f = g := by
  apply smoothPeriodic_ext hf hp hg hgp
  funext k
  by_cases hk : k = 0
  · simpa [hk, hf0, hg0]
  · have hc := congrArg (fun h => coefficient h k) he
    dsimp only at hc
    rw [coefficient_transportCover hf hp, coefficient_transportCover hg hgp] at hc
    exact mul_left_cancel₀ (mul_ne_zero omega_ne_zero
      (Complex.ofReal_ne_zero.mpr (pairDivisor_ne_zero hα k hk))) hc

end MathGauge.PublicProof.Torus
