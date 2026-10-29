import MathGauge.PublicProof.Torus.Borrowed.SmoothFourierData

/-! Coefficient recovery for arbitrary rapidly decaying data and the actual
coordinate-derivative Fourier identity. These bridge the sequence calculations
back to real smooth periodic functions; no Fourier identity is assumed. -/

noncomputable section
namespace MathGauge.PublicProof.Torus
open MeasureTheory
open scoped Topology ContDiff
open Borrowed.TorusInverse Borrowed.SmoothFourierData

lemma torusMode_mul (j k : Borrowed.TorusInverse.Frequency) (z : Borrowed.TorusInverse.Torus) :
    torusMode j z * torusMode k z = torusMode (j + k) z := by
  simp only [torusMode, ContinuousMap.coe_mk, Prod.fst_add, Prod.snd_add, fourier_add]
  ring

lemma torusCoefficient_series {a : Borrowed.TorusInverse.Frequency → ℂ} (ha : Rapid a)
    (k : Borrowed.TorusInverse.Frequency) : torusCoefficient (torusSeries a) k = a k := by
  have hi' (j : Borrowed.TorusInverse.Frequency) :
      Integrable (fun z => a j * torusMode (-k + j) z) torusMeasure := by
    apply (integrable_const (‖a j‖ : ℝ)).mono'
      (continuous_const.mul (torusMode (-k + j)).continuous).aestronglyMeasurable
    filter_upwards with z
    change ‖a j * torusMode (-k + j) z‖ ≤ ‖a j‖
    rw [norm_mul, norm_torusMode, mul_one]
  have hs : Summable (fun j => ∫ z, ‖a j * torusMode (-k + j) z‖ ∂torusMeasure) := by
    simpa only [norm_mul, norm_torusMode, mul_one, integral_const, probReal_univ, one_smul]
      using ha.summable_norm
  have hfun (z : Borrowed.TorusInverse.Torus) :
      torusMode (-k) z * torusSeries a z = ∑' j, a j * torusMode (-k + j) z := by
    unfold torusSeries
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    rw [← torusMode_mul]
    ring
  unfold torusCoefficient
  simp_rw [hfun]
  rw [← integral_tsum_of_summable_integral_norm hi' hs]
  have hint (j : Borrowed.TorusInverse.Frequency) :
      (∫ z, a j * torusMode (-k + j) z ∂torusMeasure) = if j = k then a j else 0 := by
    calc
      _ = a j * (∫ z, torusMode (-k + j) z ∂torusMeasure) := integral_const_mul _ _
      _ = _ := by rw [integral_torusMode]; simp [neg_add_eq_zero, mul_ite, eq_comm]
  simp_rw [hint]
  simp

/-- Actual Fourier integrals recover every coefficient of the smooth series. -/
theorem coefficient_series_eq {a : Borrowed.TorusInverse.Frequency → ℂ} (ha : Rapid a)
    (k : Borrowed.TorusInverse.Frequency) : coefficient (series a) k = a k := by
  let f : C(Borrowed.TorusInverse.Torus, ℂ) := ⟨torusSeries a, continuous_torusSeries ha⟩
  have h : torusLift f = series a := by
    funext x
    exact (series_eq_torusSeries a x).symm
  rw [← h, coefficient_lift_eq_torus]
  exact torusCoefficient_series ha k

/-- The Fourier derivative identity is deduced for all frequencies, including zero,
from reconstruction and actual Fréchet differentiation of the series. -/
theorem coefficient_coordinatePartial {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) (j : Bool) (k : Borrowed.TorusInverse.Frequency) :
    coefficient (coordinatePartial j f) k = coordinateCoeff j (coefficient f) k := by
  have ha := rapid_coefficient hf hp
  have he : series (coefficient f) = f := funext (series_coefficient hf hp)
  have hd := coordinatePartial_series j ha
  rw [he] at hd
  rw [hd]
  exact coefficient_series_eq (ha.coordinateCoeff j) k

end MathGauge.PublicProof.Torus
