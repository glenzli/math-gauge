import MathGauge.GP002.FunctionModels

noncomputable section
namespace MathGauge.GP002
open MathGauge.PublicProof.Torus
open MathGauge.PublicProof.Torus.Borrowed.TorusInverse
open MathGauge.PublicProof.Torus.Borrowed.SmoothFourierData

theorem multiplier_difference (α β : ℝ) (k : PairFrequency)
    (hα : pairDivisor α k ≠ 0) (hβ : pairDivisor β k ≠ 0) :
    generalMultiplier α k - generalMultiplier β k =
      (((β-α)*(k.1 : ℝ) : ℝ) : ℂ) /
        (omega * (pairDivisor α k : ℂ) * (pairDivisor β k : ℂ)) := by
  have ha := Complex.ofReal_ne_zero.mpr hα
  have hb := Complex.ofReal_ne_zero.mpr hβ
  unfold generalMultiplier
  field_simp [omega_ne_zero,ha,hb]
  simp only [pairDivisor,Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_mul]
  ring

theorem multiplier_difference_norm (α β : ℝ) (k : PairFrequency)
    (hα : pairDivisor α k ≠ 0) (hβ : pairDivisor β k ≠ 0) :
    ‖generalMultiplier α k - generalMultiplier β k‖ =
      |α-β| * |(k.1 : ℝ)| / (2*Real.pi*|pairDivisor α k| *|pairDivisor β k|) := by
  rw [multiplier_difference α β k hα hβ]
  simp only [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_mul,
    abs_sub_comm β α,omega_norm]

theorem multiplier_difference_bound {α β δ N : ℝ} (hδ : 0 < δ) (k : PairFrequency)
    (hk : k ∈ frequencyBand N) (ha : δ ≤ |pairDivisor α k|) (hb : δ ≤ |pairDivisor β k|) :
    ‖generalMultiplier α k - generalMultiplier β k‖ ≤ |α-β| *N/(2*Real.pi*δ^2) := by
  have hapos : 0 < |pairDivisor α k| := hδ.trans_le ha
  have hbpos : 0 < |pairDivisor β k| := hδ.trans_le hb
  rw [multiplier_difference_norm α β k (abs_pos.mp hapos) (abs_pos.mp hbpos)]
  have hr : |(k.1 : ℝ)| ≤ N :=
    (abs_coord_le_radius k).1.trans ((mem_frequencyBand N k).mp hk).2
  have hn : 0 ≤ N := (abs_nonneg _).trans hr
  have hnum : |α-β| *|(k.1 : ℝ)| ≤ |α-β| *N :=
    mul_le_mul_of_nonneg_left hr (abs_nonneg _)
  have hden : 2*Real.pi*δ^2 ≤ 2*Real.pi*|pairDivisor α k| *|pairDivisor β k| := by
    have hprod := mul_le_mul ha hb hδ.le hapos.le
    rw [pow_two]
    nlinarith [Real.pi_pos]
  apply (div_le_div_iff₀ (by positivity : 0 < 2*Real.pi*|pairDivisor α k| *|pairDivisor β k|)
    (by positivity : 0 < 2*Real.pi*δ^2)).mpr
  exact (mul_le_mul_of_nonneg_right hnum (by positivity)).trans
    (mul_le_mul_of_nonneg_left hden (mul_nonneg (abs_nonneg _) hn))

theorem finite_direction_difference {α β δ N : ℝ} (hδ : 0 < δ) (hN : 1 ≤ N)
    (ha : ∀ k ∈ frequencyBand N, δ ≤ |pairDivisor α k|)
    (hb : ∀ k ∈ frequencyBand N, δ ≤ |pairDivisor β k|)
    (r : ℝ) (a : PairFrequency → ℂ) (hs : Supported (frequencyBand N) a) :
    sequenceNorm r (generalInverseCoefficients α a - generalInverseCoefficients β a) ≤
      (|α-β| *N/(2*Real.pi*δ^2)) * sequenceNorm r a := by
  have hi := rapid_of_supported (inverse_supported α hs)
  have hj := rapid_of_supported (inverse_supported β hs)
  apply sequenceNorm_bound (rapid_of_supported hs) (rapid_sub hi hj) r r _ (by positivity)
  intro k
  by_cases hk : k ∈ frequencyBand N
  · have hm := multiplier_difference_bound hδ k hk (ha k hk) (hb k hk)
    change pairWeight k ^r * ‖generalMultiplier α k * a k - generalMultiplier β k * a k‖ ≤ _
    rw [← sub_mul,norm_mul]
    have h := mul_le_mul_of_nonneg_right hm (norm_nonneg (a k))
    have h' := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg (pairWeight_pos k).le r)
    nlinarith
  · simp [Pi.sub_apply,generalInverseCoefficients,hs k hk]

theorem native_direction_difference {α β δ N : ℝ} (hδ : 0 < δ) (hN : 1 ≤ N)
    (ha : ∀ k ∈ frequencyBand N, δ ≤ |pairDivisor α k|)
    (hb : ∀ k ∈ frequencyBand N, δ ≤ |pairDivisor β k|)
    (r : ℝ) (F : C(Torus2,ℂ)) (hF : NativeBand N F) :
    nativeHNorm r (finiteNativeInverse α N F - finiteNativeInverse β N F) ≤
      (|α-β| *N/(2*Real.pi*δ^2)) * nativeHNorm r F := by
  rcases hF with ⟨a,hs,rfl⟩
  rw [finiteNativeInverse_on_series α N a hs,finiteNativeInverse_on_series β N a hs]
  change nativeHNorm r (↑(nativeSeries (generalInverseCoefficients α a)
    (rapid_of_supported (inverse_supported α hs)) - nativeSeries (generalInverseCoefficients β a)
    (rapid_of_supported (inverse_supported β hs))) : Torus2 → ℂ) ≤ _
  rw [← nativeSeries_sub,nativeSeries_norm,nativeSeries_norm]
  exact finite_direction_difference hδ hN ha hb r a hs

end MathGauge.GP002
