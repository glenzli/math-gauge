import MathGauge.GP002.ArithmeticFailures

noncomputable section
namespace MathGauge.GP002
open MathGauge.PublicProof.Torus
open MathGauge.PublicProof.Torus.Borrowed.TorusInverse
open MathGauge.PublicProof.Torus.Borrowed.SmoothFourierData
open scoped Topology ContDiff

def radius (k : PairFrequency) : ℝ := Real.sqrt ((k.1 : ℝ)^2 + (k.2 : ℝ)^2)

theorem radius_sq (k : PairFrequency) : radius k ^ 2 = (k.1 : ℝ)^2 + (k.2 : ℝ)^2 :=
  Real.sq_sqrt (by positivity)

theorem abs_coord_le_radius (k : PairFrequency) :
    |(k.1 : ℝ)| ≤ radius k ∧ |(k.2 : ℝ)| ≤ radius k := by
  have hr := radius_sq k
  have hn : 0 ≤ radius k := Real.sqrt_nonneg _
  constructor
  · apply (sq_le_sq₀ (abs_nonneg _) hn).mp
    rw [sq_abs]; nlinarith [sq_nonneg (k.2 : ℝ)]
  · apply (sq_le_sq₀ (abs_nonneg _) hn).mp
    rw [sq_abs]; nlinarith [sq_nonneg (k.1 : ℝ)]

def frequencyBand (N : ℝ) : Finset PairFrequency := by
  classical
  exact ((Finset.Icc (-⌈N⌉) ⌈N⌉) ×ˢ (Finset.Icc (-⌈N⌉) ⌈N⌉)).filter
    (fun k => k ≠ 0 ∧ radius k ≤ N)

theorem mem_frequencyBand (N : ℝ) (k : PairFrequency) :
    k ∈ frequencyBand N ↔ k ≠ 0 ∧ radius k ≤ N := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨?_,h⟩
    have hc : (N : ℝ) ≤ (⌈N⌉ : ℤ) := Int.le_ceil N
    have hp := (abs_coord_le_radius k).1.trans (h.2.trans hc)
    have hq := (abs_coord_le_radius k).2.trans (h.2.trans hc)
    rw [abs_le] at hp hq
    apply Finset.mem_product.mpr
    constructor <;> apply Finset.mem_Icc.mpr
    · constructor
      · exact_mod_cast hp.1
      · exact_mod_cast hp.2
    · constructor
      · exact_mod_cast hq.1
      · exact_mod_cast hq.2

theorem frequencyBand_nonempty {N : ℝ} (hN : 1 ≤ N) : (frequencyBand N).Nonempty := by
  refine ⟨(1,0),(mem_frequencyBand N (1,0)).mpr ⟨by simp,?_⟩⟩
  simpa [radius] using hN

def Supported (B : Finset PairFrequency) (a : PairFrequency → ℂ) : Prop :=
  ∀ k, k ∉ B → a k = 0

theorem rapid_of_supported {B : Finset PairFrequency} {a : PairFrequency → ℂ}
    (h : Supported B a) : Rapid a := by
  intro p
  apply summable_of_ne_finset_zero (s := B)
  intro k hk
  simp [h k hk]

theorem supported_series_eq_finite_sum {B : Finset PairFrequency} {a : PairFrequency → ℂ}
    (h : Supported B a) (x : Plane) : series a x = ∑ k ∈ B, a k * Borrowed.TorusInverse.mode k x := by
  unfold series
  apply tsum_eq_sum
  intro k hk
  simp [h k hk]

def truncate (N : ℝ) (a : PairFrequency → ℂ) (k : PairFrequency) : ℂ :=
  if k ∈ frequencyBand N then a k else 0

theorem truncate_supported (N : ℝ) (a : PairFrequency → ℂ) :
    Supported (frequencyBand N) (truncate N a) := by
  intro k hk; simp [truncate,hk]

theorem inverse_supported (α : ℝ) {B : Finset PairFrequency} {a : PairFrequency → ℂ}
    (h : Supported B a) : Supported B (generalInverseCoefficients α a) := by
  intro k hk
  simp [generalInverseCoefficients,h k hk]

def sequenceNorm (r : ℝ) (a : PairFrequency → ℂ) : ℝ :=
  Real.sqrt (∑' k,energyTerm r a k)

theorem sequenceNorm_series {a : PairFrequency → ℂ} (ha : Rapid a) (r : ℝ) :
    hNorm r (series a) = sequenceNorm r a := by
  have hc : coefficient (series a) = a := funext (coefficient_series_eq ha)
  simp only [hNorm,hc,sequenceNorm]

theorem sequenceNorm_bound {a b : PairFrequency → ℂ} (ha : Rapid a) (hb : Rapid b)
    (r t C : ℝ) (hC : 0 ≤ C)
    (h : ∀ k, pairWeight k ^ r * ‖b k‖ ≤ C * (pairWeight k ^ t * ‖a k‖)) :
    sequenceNorm r b ≤ C * sequenceNorm t a := by
  have ht := (summable_energyTerm r hb).tsum_le_tsum
    (fun k => show energyTerm r b k ≤ C^2 * energyTerm t a k from by
      rw [energyTerm_square,energyTerm_square,← mul_pow]
      exact pow_le_pow_left₀ (mul_nonneg (Real.rpow_nonneg (pairWeight_pos k).le _) (norm_nonneg _)) (h k) 2)
    ((summable_energyTerm t ha).mul_left (C^2))
  have hn (s : ℝ) (x : PairFrequency → ℂ) :
      sequenceNorm s x ^2 = ∑' k,energyTerm s x k :=
    Real.sq_sqrt (tsum_nonneg (energyTerm_nonneg s x))
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hC (Real.sqrt_nonneg _))).mp
  change sequenceNorm r b ^2 ≤ (C * sequenceNorm t a)^2
  rw [mul_pow,hn,hn]
  simpa only [tsum_mul_left] using ht

theorem sequenceNorm_single (r : ℝ) (k : PairFrequency) (z : ℂ) :
    sequenceNorm r (Pi.single k z) = pairWeight k ^ r * ‖z‖ := by
  rw [← sequenceNorm_series (rapid_single k z),series_single]
  exact hNorm_mode_scaled r k z

theorem omega_norm : ‖omega‖ = 2 * Real.pi := by
  simp [omega,norm_mul,Complex.norm_real,abs_of_pos Real.pi_pos]

theorem multiplier_norm (α : ℝ) (k : PairFrequency) :
    ‖generalMultiplier α k‖ = 1/(2*Real.pi*|pairDivisor α k|) := by
  simp [generalMultiplier,norm_inv,norm_mul,omega_norm,Complex.norm_real,Real.norm_eq_abs,one_div]

def bandConstant (α N : ℝ) (hN : 1 ≤ N) : ℝ :=
  (frequencyBand N).sup' (frequencyBand_nonempty hN) (fun k => ‖generalMultiplier α k‖)

theorem bandConstant_formula (α N : ℝ) (hN : 1 ≤ N) :
    bandConstant α N hN = (frequencyBand N).sup' (frequencyBand_nonempty hN)
      (fun k => 1/(2*Real.pi*|pairDivisor α k|)) := by
  unfold bandConstant
  congr 1
  funext k
  exact multiplier_norm α k

/-- The upper operator-norm bound, valid for every real Sobolev order. -/
theorem finite_inverse_bound (α N : ℝ) (hN : 1 ≤ N) (r : ℝ)
    (a : PairFrequency → ℂ) (ha : Supported (frequencyBand N) a) :
    sequenceNorm r (generalInverseCoefficients α a) ≤ bandConstant α N hN * sequenceNorm r a := by
  have hc : 0 ≤ bandConstant α N hN := by
    obtain ⟨k,hk⟩ := frequencyBand_nonempty hN
    exact (norm_nonneg _).trans (Finset.le_sup' (fun k => ‖generalMultiplier α k‖) hk)
  apply sequenceNorm_bound (rapid_of_supported ha) (rapid_of_supported (inverse_supported α ha)) r r _ hc
  intro k
  by_cases hk : k ∈ frequencyBand N
  · have hle := Finset.le_sup' (fun k => ‖generalMultiplier α k‖) hk
    change ‖generalMultiplier α k‖ ≤ bandConstant α N hN at hle
    change pairWeight k ^ r * ‖generalMultiplier α k * a k‖ ≤ _
    rw [norm_mul]
    nlinarith [Real.rpow_pos_of_pos (pairWeight_pos k) r,
      mul_le_mul_of_nonneg_right hle (norm_nonneg (a k))]
  · simp [generalInverseCoefficients,ha k hk]

theorem inverse_single (α : ℝ) (k : PairFrequency) (z : ℂ) :
    generalInverseCoefficients α (Pi.single k z) = Pi.single k (generalMultiplier α k * z) := by
  funext j
  by_cases h : j = k <;> simp [generalInverseCoefficients,Pi.single_apply,h]

/-- A single actual Fourier mode attains the upper bound, so the maximum is exact. -/
theorem finite_inverse_bound_attained (α N : ℝ) (hN : 1 ≤ N) (r : ℝ) :
    ∃ a : PairFrequency → ℂ, Supported (frequencyBand N) a ∧ 0 < sequenceNorm r a ∧
      sequenceNorm r (generalInverseCoefficients α a) = bandConstant α N hN * sequenceNorm r a := by
  obtain ⟨k,hk,he⟩ := Finset.exists_mem_eq_sup' (frequencyBand_nonempty hN)
    (fun k => ‖generalMultiplier α k‖)
  refine ⟨Pi.single k 1,?_,?_,?_⟩
  · intro j hj
    have hjk : j ≠ k := by intro h; subst j; exact hj hk
    simp [Pi.single_apply,hjk]
  · rw [sequenceNorm_single]; simpa using Real.rpow_pos_of_pos (pairWeight_pos k) r
  · rw [inverse_single,sequenceNorm_single,sequenceNorm_single]
    change _ = (frequencyBand N).sup' _ _ * _
    rw [he]
    simp [mul_comm]

/-- The finite inverse acts on actual smooth periodic functions and solves the equation. -/
theorem finite_inverse_solves {α : ℝ} (hα : Irrational α) (N : ℝ)
    (a : PairFrequency → ℂ) (ha : Supported (frequencyBand N) a) :
    ContDiff ℝ ∞ (series (generalInverseCoefficients α a)) ∧
    UnitPeriodic (series (generalInverseCoefficients α a)) ∧
    coefficient (series (generalInverseCoefficients α a)) 0 = 0 ∧
    transportCover α (series (generalInverseCoefficients α a)) = series a := by
  have hi := rapid_of_supported (inverse_supported α ha)
  have ha0 : a 0 = 0 := ha 0 (by simp [mem_frequencyBand])
  refine ⟨contDiff_series hi,?_,?_,?_⟩
  · intro x k; exact series_periodic _ x k.1 k.2
  · rw [coefficient_series_eq hi,generalInverse_zero_coefficient]
  · rw [transportCover_series α hi,transport_generalInverseCoefficients hα ha0]

end MathGauge.GP002
