import MathGauge.PublicProof.Torus.Weights

noncomputable section
namespace MathGauge.PublicProof.Torus
open scoped Topology ContDiff
open Borrowed.TorusInverse Borrowed.SmoothFourierData

/-- The exact Euclidean-frequency summand used in the task, for arbitrary real order. -/
def energyTerm (r : ℝ) (a : PairFrequency → ℂ) (k : PairFrequency) : ℝ :=
  pairWeight k ^ (2 * r) * ‖a k‖ ^ 2

def hNorm (r : ℝ) (f : Plane → ℂ) : ℝ := Real.sqrt (∑' k, energyTerm r (coefficient f) k)

lemma energyTerm_nonneg (r : ℝ) (a : PairFrequency → ℂ) (k : PairFrequency) : 0 ≤ energyTerm r a k :=
  mul_nonneg (Real.rpow_nonneg (pairWeight_pos k).le _) (sq_nonneg _)

lemma energyTerm_square (r : ℝ) (a : PairFrequency → ℂ) (k : PairFrequency) :
    energyTerm r a k = (pairWeight k ^ r * ‖a k‖) ^ 2 := by
  unfold energyTerm
  rw [show 2 * r = r + r by ring, Real.rpow_add (pairWeight_pos k)]
  ring

/-- Smoothness implies finiteness of every real-order Sobolev sum. -/
lemma summable_energyTerm (r : ℝ) {a : PairFrequency → ℂ} (ha : Rapid a) :
    Summable (energyTerm r a) := by
  obtain ⟨n, hn⟩ := exists_nat_ge (2 * r)
  let C : ℝ := ∑' k, ‖a k‖
  have hb (k : PairFrequency) : ‖a k‖ ≤ C := ha.summable_norm.le_tsum k (fun j _ => norm_nonneg _)
  have hC : 0 ≤ C := tsum_nonneg (fun k => norm_nonneg _)
  apply Summable.of_nonneg_of_le (energyTerm_nonneg r a) _ ((ha n).mul_left C)
  intro k
  have hw : pairWeight k ^ (2 * r) ≤ Borrowed.TorusInverse.weight k ^ n := by
    calc
      _ ≤ pairWeight k ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le (one_le_pairWeight k) hn
      _ = pairWeight k ^ n := Real.rpow_natCast _ _
      _ ≤ _ := pow_le_pow_left₀ (pairWeight_pos k).le (pairWeight_le_l1 k) n
  calc
    energyTerm r a k ≤ Borrowed.TorusInverse.weight k ^ n * (C * ‖a k‖) := by
      apply mul_le_mul hw
      · nlinarith [mul_le_mul_of_nonneg_right (hb k) (norm_nonneg (a k))]
      · exact sq_nonneg _
      · exact pow_nonneg (Borrowed.TorusInverse.weight_pos k).le _
    _ = C * (Borrowed.TorusInverse.weight k ^ n * ‖a k‖) := by ring

lemma hNorm_sq (r : ℝ) (f : Plane → ℂ) : hNorm r f ^ 2 = ∑' k, energyTerm r (coefficient f) k :=
  Real.sq_sqrt (tsum_nonneg (energyTerm_nonneg r _))

lemma norm_omega_pos : 0 < ‖omega‖ := norm_pos_iff.mpr omega_ne_zero

lemma weighted_norm_comparison {α s c : ℝ} (hc : 0 < c)
    (hb : ∀ k : PairFrequency, k ≠ 0 → c ≤ pairWeight k ^ s * |pairDivisor α k|)
    (r : ℝ) (a : PairFrequency → ℂ) (ha0 : a 0 = 0) (k : PairFrequency) :
    pairWeight k ^ r * ‖a k‖ ≤
      (1 / (‖omega‖ * c)) * (pairWeight k ^ (r + s) * ‖transportCoefficients α a k‖) := by
  by_cases hk : k = 0
  · simp [hk, ha0, transportCoefficients, derivX, derivY]
  · have hden : 0 < ‖omega‖ * c := mul_pos norm_omega_pos hc
    rw [one_div, ← div_eq_inv_mul]
    apply (le_div_iff₀ hden).mpr
    have hb' := mul_le_mul_of_nonneg_left (hb k hk) (norm_nonneg omega)
    calc
      (pairWeight k ^ r * ‖a k‖) * (‖omega‖ * c) ≤
          (pairWeight k ^ r * ‖a k‖) * (‖omega‖ * (pairWeight k ^ s * |pairDivisor α k|)) :=
        mul_le_mul_of_nonneg_left hb' (mul_nonneg (Real.rpow_nonneg (pairWeight_pos k).le _) (norm_nonneg _))
      _ = pairWeight k ^ (r + s) * ‖transportCoefficients α a k‖ := by
        rw [transportCoefficients_formula, norm_mul, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, Real.rpow_add (pairWeight_pos k)]
        ring

lemma energyTerm_comparison {α s c : ℝ} (hc : 0 < c)
    (hb : ∀ k : PairFrequency, k ≠ 0 → c ≤ pairWeight k ^ s * |pairDivisor α k|)
    (r : ℝ) (a : PairFrequency → ℂ) (ha0 : a 0 = 0) (k : PairFrequency) :
    energyTerm r a k ≤ (1 / (‖omega‖ * c)) ^ 2 * energyTerm (r + s) (transportCoefficients α a) k := by
  rw [energyTerm_square, energyTerm_square, ← mul_pow]
  exact pow_le_pow_left₀ (mul_nonneg (Real.rpow_nonneg (pairWeight_pos k).le _) (norm_nonneg _)) (weighted_norm_comparison hc hb r a ha0 k) 2

/-- Full actual-function estimate at every real order for precisely the stated
arithmetic bound. The same constant works for every `r`. -/
theorem hNorm_bound {α s : ℝ} (hb : PairHasDivisorBound α s) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, ∀ f : Plane → ℂ,
      ContDiff ℝ ∞ f → UnitPeriodic f → coefficient f 0 = 0 →
      hNorm r f ≤ C * hNorm (r + s) (transportCover α f) := by
  obtain ⟨c, hc, hbound⟩ := hb
  let C : ℝ := 1 / (‖omega‖ * c)
  have hC : 0 < C := one_div_pos.mpr (mul_pos norm_omega_pos hc)
  refine ⟨C, hC, ?_⟩
  intro r f hf hp hf0
  have ha := rapid_coefficient hf hp
  have hb' := rapid_transportCoefficients α ha
  have he : coefficient (transportCover α f) = transportCoefficients α (coefficient f) := by
    funext k
    rw [coefficient_transportCover hf hp, transportCoefficients_formula]
  have ht := (summable_energyTerm r ha).tsum_le_tsum
    (energyTerm_comparison hc hbound r (coefficient f) hf0)
    ((summable_energyTerm (r + s) hb').mul_left (C ^ 2))
  have hs : hNorm r f ^ 2 ≤ (C * hNorm (r + s) (transportCover α f)) ^ 2 := by
    rw [hNorm_sq, mul_pow, hNorm_sq, he]
    simpa only [tsum_mul_left] using ht
  exact (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hC.le (Real.sqrt_nonneg _))).mp hs

lemma rapid_single (k : PairFrequency) (z : ℂ) : Rapid (Pi.single k z) := by
  intro p
  exact (hasSum_single k (fun j hj => by simp [Pi.single_apply, hj])).summable

lemma series_single (k : PairFrequency) (z : ℂ) : series (Pi.single k z) = fun x => z * mode k x := by
  funext x
  unfold series
  simp [Pi.single_apply]

lemma coefficient_mode_scaled (k : PairFrequency) (z : ℂ) :
    coefficient (fun x => z * mode k x) = Pi.single k z := by
  rw [← series_single]
  funext j
  exact coefficient_series_eq (rapid_single k z) j

lemma hNorm_mode_scaled (r : ℝ) (k : PairFrequency) (z : ℂ) :
    hNorm r (fun x => z * mode k x) = pairWeight k ^ r * ‖z‖ := by
  unfold hNorm
  rw [coefficient_mode_scaled]
  have hsum : (∑' j, energyTerm r (Pi.single k z) j) = energyTerm r (Pi.single k z) k :=
    tsum_eq_single k (fun j hj => by simp [energyTerm, Pi.single_apply, hj])
  rw [hsum, energyTerm_square]
  simp only [Pi.single_eq_same]
  exact Real.sqrt_sq (mul_nonneg (Real.rpow_nonneg (pairWeight_pos k).le _) (norm_nonneg _))

/-- The quantifiers in the task, including all real orders and all smooth
zero-mean inputs, with finite real constants. -/
def HasSobolevEstimates (α s : ℝ) : Prop :=
  ∀ r : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Plane → ℂ,
    ContDiff ℝ ∞ f → UnitPeriodic f → coefficient f 0 = 0 →
    hNorm r f ≤ C * hNorm (r + s) (transportCover α f)

/-- Testing actual smooth Fourier monomials forces the exact endpoint arithmetic bound. -/
theorem divisor_bound_of_hNorm_bound {α s : ℝ} (h : HasSobolevEstimates α s) :
    PairHasDivisorBound α s := by
  obtain ⟨C, hC, hest⟩ := h 0
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
    have hz : C = 0 := le_antisymm (le_of_not_gt hn) hC
    rw [hz, zero_mul] at hx
    norm_num at hx
  refine ⟨1 / (C * ‖omega‖), one_div_pos.mpr (mul_pos hCpos norm_omega_pos), ?_⟩
  intro k hk
  apply (div_le_iff₀ (mul_pos hCpos norm_omega_pos)).mpr
  nlinarith only [hmode k hk]

/-- Exact Sobolev-loss criterion. No endpoint follows merely by taking an infimum. -/
theorem sobolev_iff_divisor_bound (α s : ℝ) :
    HasSobolevEstimates α s ↔ PairHasDivisorBound α s := by
  refine ⟨divisor_bound_of_hNorm_bound, ?_⟩
  intro h
  obtain ⟨C, hC, hb⟩ := hNorm_bound h
  exact fun r => ⟨C, hC.le, hb r⟩

/-- For the fixed quadratic irrational, every nonnegative loss is classified,
including the attained minimum `s = 1`. -/
theorem quadratic_sobolev_iff {s : ℝ} (hs : 0 ≤ s) :
    HasSobolevEstimates quadraticDirection s ↔ 1 ≤ s := by
  rw [sobolev_iff_divisor_bound, pair_bound_iff_native]
  exact quadratic_divisor_bound_iff hs

end MathGauge.PublicProof.Torus
