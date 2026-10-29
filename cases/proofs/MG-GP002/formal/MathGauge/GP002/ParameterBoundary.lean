import MathGauge.GP002.ArithmeticFailures

noncomputable section
namespace MathGauge.GP002
open MathGauge.PublicProof.Torus
open MathGauge.PublicProof.Torus.Borrowed.TorusInverse
open MathGauge.PublicProof.Torus.Borrowed.SmoothFourierData
open MeasureTheory
open scoped ContDiff Topology ENNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem divisor_bound_of_zero_order_estimate {α s C : ℝ}
    (hest : ∀ f : Plane → ℂ, ContDiff ℝ ∞ f → UnitPeriodic f → coefficient f 0 = 0 →
      hNorm 0 f ≤ C * hNorm s (transportCover α f)) :
    PairHasDivisorBound α s := by
  have hmode (k : PairFrequency) (hk : k ≠ 0) :
      1 ≤ C * (pairWeight k ^ s * (‖omega‖ * |pairDivisor α k|)) := by
    let f : Plane → ℂ := fun x => (1 : ℂ) * mode k x
    have hf : ContDiff ℝ ∞ f := by
      change ContDiff ℝ ∞ (fun x => (1 : ℂ) * mode k x)
      rw [← series_single]
      exact contDiff_series (rapid_single k 1)
    have hp : UnitPeriodic f := by
      change UnitPeriodic (fun x => (1 : ℂ) * mode k x)
      rw [← series_single]
      intro x l
      exact series_periodic _ x l.1 l.2
    have hf0 : coefficient f 0 = 0 := by
      rw [show f = (fun x => (1 : ℂ) * mode k x) from rfl, coefficient_mode_scaled]
      simp [Pi.single_apply, hk.symm]
    have ht : transportCover α f = fun x => (omega * (pairDivisor α k : ℂ)) * mode k x := by
      rw [show f = series (Pi.single k 1) by exact (series_single k 1).symm,
        transportCover_series α (rapid_single k 1)]
      have he : transportCoefficients α (Pi.single k 1) = Pi.single k (omega * (pairDivisor α k : ℂ)) := by
        funext j
        rw [transportCoefficients_formula]
        by_cases hj : j = k <;> simp [Pi.single_apply, hj]
      rw [he, series_single]
    have he := hest f hf hp hf0
    rw [ht] at he
    simpa only [f, hNorm_mode_scaled, zero_add, Real.rpow_zero, norm_one, mul_one,
      norm_mul, Complex.norm_real, Real.norm_eq_abs] using he
  have hCpos : 0 < C := by
    have hx := hmode (1, 0) (by simp)
    by_contra hn
    have hnonneg : 0 ≤ pairWeight (1,0) ^ s * (‖omega‖ * |pairDivisor α (1,0)|) :=
      mul_nonneg (Real.rpow_nonneg (pairWeight_pos _).le _) (by positivity)
    have hprod := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hnonneg
    linarith
  refine ⟨1 / (C * ‖omega‖), one_div_pos.mpr (mul_pos hCpos norm_omega_pos), ?_⟩
  intro k hk
  apply (div_le_iff₀ (mul_pos hCpos norm_omega_pos)).mpr
  nlinarith only [hmode k hk]


/-- The usual normalized L² integral norm, not an unproved Fourier-norm identification. -/
def nativeL2Norm (u : Torus2 → ℂ) : ℝ := Real.sqrt (∫ y, ‖u y‖^2)

theorem nativeL2Norm_eq_h0 (u : C(Torus2,ℂ)) : nativeL2Norm u = nativeHNorm 0 u := by
  have h := UnitAddTorus.hasSum_sq_mFourierCoeff (u.toLp 2 volume ℂ)
  simp only [UnitAddTorus.mFourierCoeff_toLp] at h
  have he : (∫ y, ‖u.toLp 2 volume ℂ y‖^2) = ∫ y, ‖u y‖^2 := by
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) volume u] with y hy
    rw [hy]
  rw [he] at h
  simp only [nativeL2Norm,nativeHNorm,mul_zero,Real.rpow_zero,one_mul,coeff]
  rw [h.tsum_eq]

/-- Every nonempty open set contains a direction defeating every finite-loss zero-order bound. -/
theorem no_uniform_estimate_on_open (J : Set ℝ) (hJ : IsOpen J) (hne : J.Nonempty)
    (s C : ℝ) (hs : 0 ≤ s) :
    ¬ ∀ α ∈ J, Irrational α → ∀ u : C(Torus2,ℂ), Smooth u → MeanZero u →
      nativeL2Norm u ≤ C * nativeHNorm s (transport α u) := by
  intro h
  obtain ⟨α,hmem,hα⟩ := dense_liouville.inter_open_nonempty J hJ hne
  have hb : PairHasDivisorBound α s := by
    apply divisor_bound_of_zero_order_estimate (C := C)
    intro f hf hp hf0
    let u := ofCover f hf hp
    have hu : Smooth u := ofCover_smooth f hf hp
    have hm : MeanZero u := by rw [native_meanZero_iff_cover,coverOf_ofCover]; exact hf0
    have hx := h α hmem hα.irrational u hu hm
    rw [nativeL2Norm_eq_h0,← nativeTransport_eq α u hu,nativeHNorm_eq_cover,
      nativeHNorm_eq_cover,cover_nativeTransport,coverOf_ofCover] at hx
    exact hx
  exact liouville_no_polynomial_bound hα ((polynomial_bound_iff_exists_real α).mpr ⟨s,hs,hb⟩)

end MathGauge.GP002
