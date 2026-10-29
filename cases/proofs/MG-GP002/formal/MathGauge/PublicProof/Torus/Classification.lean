import MathGauge.PublicProof.Torus.Necessity
import MathGauge.PublicProof.Torus.Sobolev

noncomputable section
namespace MathGauge.PublicProof.Torus
open scoped ContDiff Topology
open Borrowed.TorusInverse Borrowed.SmoothFourierData

/-- The full smooth-surjectivity quantifier, on actual periodic functions. -/
def SmoothSurjective (α : ℝ) : Prop :=
  ∀ f : Plane → ℂ, ContDiff ℝ ∞ f → UnitPeriodic f → coefficient f 0 = 0 →
    ∃ u : Plane → ℂ, ContDiff ℝ ∞ u ∧ UnitPeriodic u ∧ coefficient u 0 = 0 ∧ transportCover α u = f

/-- The absence of every finite bound gives one fixed actual smooth zero-mean forcing
with no smooth periodic zero-mean solution. -/
theorem exists_smooth_unsolvable {α : ℝ} (hα : Irrational α)
    (hbad : ¬ PolynomialDivisorBound α) :
    ∃ f : Plane → ℂ, ContDiff ℝ ∞ f ∧ UnitPeriodic f ∧ coefficient f 0 = 0 ∧
      ¬ ∃ u : Plane → ℂ, ContDiff ℝ ∞ u ∧ UnitPeriodic u ∧ coefficient u 0 = 0 ∧ transportCover α u = f := by
  obtain ⟨a, ha, ha0, hbadinv⟩ := exists_rapid_bad_inverse hα hbad
  let f := series a
  have hf : ContDiff ℝ ∞ f := contDiff_series ha
  have hp : UnitPeriodic f := fun x k => series_periodic a x k.1 k.2
  have hcf : coefficient f = a := funext (coefficient_series_eq ha)
  refine ⟨f, hf, hp, by rw [hcf, ha0], ?_⟩
  rintro ⟨u, hu, hup, hu0, hsol⟩
  have hcu : generalInverseCoefficients α a = coefficient u := by
    funext k
    have hc := congrArg (fun g => coefficient g k) hsol
    dsimp only at hc
    rw [coefficient_transportCover hu hup, hcf] at hc
    by_cases hk : k = 0
    · simp [hk, generalInverse_zero_coefficient, hu0]
    · have hd : omega * (pairDivisor α k : ℂ) ≠ 0 :=
        mul_ne_zero omega_ne_zero (Complex.ofReal_ne_zero.mpr (pairDivisor_ne_zero hα k hk))
      change (omega * (pairDivisor α k : ℂ))⁻¹ * a k = coefficient u k
      rw [← hc, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]
  have hur := (rapid_coefficient hu hup).summable_norm
  obtain ⟨k, hk⟩ := hbadinv (∑' j, ‖coefficient u j‖)
  rw [hcu] at hk
  exact (not_lt_of_ge (hur.le_tsum k (fun j _ => norm_nonneg _))) hk

/-- Exact general-irrational smooth solvability classification. -/
theorem smoothSurjective_iff_polynomialBound {α : ℝ} (hα : Irrational α) :
    SmoothSurjective α ↔ PolynomialDivisorBound α := by
  constructor
  · intro h
    by_contra hbad
    obtain ⟨f, hf, hp, hf0, hno⟩ := exists_smooth_unsolvable hα hbad
    exact hno (h f hf hp hf0)
  · intro hb f hf hp hf0
    exact ⟨generalInverse α f, generalInverse_properties hα hb hf hp hf0⟩

/-- Smooth solvability is equivalent to existence of a finite nonnegative Sobolev loss. -/
theorem smoothSurjective_iff_exists_sobolev {α : ℝ} (hα : Irrational α) :
    SmoothSurjective α ↔ ∃ s : ℝ, 0 ≤ s ∧ HasSobolevEstimates α s := by
  rw [smoothSurjective_iff_polynomialBound hα, polynomial_bound_iff_exists_real]
  simp_rw [sobolev_iff_divisor_bound]

/-- The fixed quadratic direction has a smooth inverse for every smooth zero-mean forcing. -/
theorem quadratic_smoothSurjective : SmoothSurjective quadraticDirection := by
  apply (smoothSurjective_iff_polynomialBound quadraticDirection_irrational).mpr
  apply (polynomial_bound_iff_exists_real _).mpr
  exact ⟨1, by norm_num, (pair_bound_iff_native _ _).mpr quadratic_divisor_bound_one⟩

end MathGauge.PublicProof.Torus
