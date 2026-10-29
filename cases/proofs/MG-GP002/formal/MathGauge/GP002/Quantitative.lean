import MathGauge.GP002.FunctionModels

noncomputable section
namespace MathGauge.GP002
open MathGauge.PublicProof.Torus
open MathGauge.PublicProof.Torus.Borrowed.TorusInverse
open MathGauge.PublicProof.Torus.Borrowed.SmoothFourierData
open scoped Topology ContDiff

theorem small_divisor_hypothesis_iff (α s c : ℝ) :
    (∀ k : PairFrequency, k ≠ 0 → c * pairWeight k ^(-s) ≤ |pairDivisor α k|) ↔
      (∀ k : PairFrequency, k ≠ 0 → c ≤ pairWeight k ^s * |pairDivisor α k|) := by
  have he (k : PairFrequency) : c * pairWeight k ^(-s) = c / pairWeight k ^s := by
    rw [Real.rpow_neg (pairWeight_pos k).le,div_eq_mul_inv]
  simp_rw [he,div_le_iff₀ (Real.rpow_pos_of_pos (pairWeight_pos _) s)]
  simp only [mul_comm]

def cutoffWeight (N : ℝ) : ℝ := Real.sqrt (1+N^2)

theorem cutoffWeight_pos (N : ℝ) : 0 < cutoffWeight N := by
  apply Real.sqrt_pos.mpr
  positivity

theorem cutoffWeight_le_pairWeight {N : ℝ} (hN : 0 ≤ N) (k : PairFrequency)
    (hk : N ≤ radius k) : cutoffWeight N ≤ pairWeight k := by
  apply (sq_le_sq₀ (cutoffWeight_pos N).le (pairWeight_pos k).le).mp
  have hw := MathGauge.PublicProof.Torus.weight_sq ![k.1,k.2]
  have hr := radius_sq k
  have hsq := pow_le_pow_left₀ hN hk 2
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] at hw
  rw [cutoffWeight,Real.sq_sqrt (by positivity)]
  change 1+N^2 ≤ MathGauge.PublicProof.Torus.weight ![k.1,k.2]^2
  linarith

theorem cutoffWeight_power (N q : ℝ) :
    cutoffWeight N ^ (-q) = (1+N^2)^(-q/2) := by
  rw [cutoffWeight,Real.sqrt_eq_rpow,← Real.rpow_mul (by positivity)]
  congr 1
  ring

theorem truncate_inverse_commute (α N : ℝ) (a : PairFrequency → ℂ) :
    truncate N (generalInverseCoefficients α a) = generalInverseCoefficients α (truncate N a) := by
  funext k
  by_cases hk : k ∈ frequencyBand N <;> simp [truncate,generalInverseCoefficients,hk]

/-- The exact cutoff power, including q=0 and all real r. -/
theorem inverse_tail_bound {α s c : ℝ} (hα : Irrational α) (hs : 0 ≤ s) (hc : 0 < c)
    (hbound : ∀ k : PairFrequency, k ≠ 0 → c ≤ pairWeight k ^s * |pairDivisor α k|)
    (a : PairFrequency → ℂ) (ha : Rapid a) (ha0 : a 0 = 0)
    (N r q : ℝ) (hN : 0 ≤ N) (hq : 0 ≤ q) :
    sequenceNorm r (generalInverseCoefficients α a - truncate N (generalInverseCoefficients α a)) ≤
      (1/(2*Real.pi*c)) * (1+N^2)^(-q/2) * sequenceNorm (r+s+q) a := by
  have hp : PolynomialDivisorBound α := (polynomial_bound_iff_exists_real α).mpr ⟨s,hs,c,hc,hbound⟩
  have hi := rapid_generalInverseCoefficients hp ha
  have hz := generalInverse_zero_coefficient α a
  have ht := rapid_of_supported (truncate_supported N (generalInverseCoefficients α a))
  have he : transportCoefficients α (generalInverseCoefficients α a) = a :=
    transport_generalInverseCoefficients hα ha0
  rw [← cutoffWeight_power N q]
  apply sequenceNorm_bound ha (rapid_sub hi ht) r (r+s+q) _ (by
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (cutoffWeight_pos N).le _))
  intro k
  by_cases hk : k ∈ frequencyBand N
  · simp only [Pi.sub_apply,truncate,if_pos hk,sub_self,norm_zero,mul_zero]
    exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (cutoffWeight_pos N).le _))
      (mul_nonneg (Real.rpow_nonneg (pairWeight_pos k).le _) (norm_nonneg _))
  by_cases hk0 : k = 0
  · subst k
    simp only [Pi.sub_apply,truncate,if_neg hk,hz,sub_zero,norm_zero,mul_zero]
    exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (cutoffWeight_pos N).le _))
      (mul_nonneg (Real.rpow_nonneg (pairWeight_pos _).le _) (norm_nonneg _))
  have hr : N < radius k := lt_of_not_ge (fun h => hk ((mem_frequencyBand N k).mpr ⟨hk0,h⟩))
  have hw : pairWeight k ^(-q) ≤ cutoffWeight N ^(-q) :=
    Real.rpow_le_rpow_of_nonpos (cutoffWeight_pos N) (cutoffWeight_le_pairWeight hN k hr.le) (by linarith)
  have hb := weighted_norm_comparison hc hbound r (generalInverseCoefficients α a) hz k
  rw [he,omega_norm] at hb
  simp only [Pi.sub_apply,truncate,if_neg hk,sub_zero]
  calc
    _ ≤ (1/(2*Real.pi*c)) * (pairWeight k ^(r+s) * ‖a k‖) := hb
    _ = (1/(2*Real.pi*c)) * pairWeight k ^(-q) * (pairWeight k ^(r+s+q) * ‖a k‖) := by
      have hpowe : pairWeight k ^(r+s) = pairWeight k ^(-q) * pairWeight k ^(r+s+q) := by
        rw [← Real.rpow_add (pairWeight_pos k)]
        congr 1
        ring
      rw [hpowe]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _
        (mul_nonneg (Real.rpow_nonneg (pairWeight_pos k).le _) (norm_nonneg _))
      exact mul_le_mul_of_nonneg_left hw (by positivity)

theorem truncation_estimate {α s c : ℝ} (hα : Irrational α) (hs : 0 ≤ s) (hc : 0 < c)
    (hbound : ∀ k : PairFrequency, k ≠ 0 → c ≤ pairWeight k ^s * |pairDivisor α k|)
    (F : C(Torus2,ℂ)) (hF : Smooth F) (hF0 : MeanZero F)
    (N r q : ℝ) (hN : 1 ≤ N) (hq : 0 ≤ q) :
    ∃ u : C(Torus2,ℂ), Smooth u ∧ MeanZero u ∧
      (∀ y, transport α u y = F y) ∧
      nativeHNorm r (u - finiteNativeInverse α N F) ≤
        (1/(2*Real.pi*c)) * (1+N^2)^(-q/2) * nativeHNorm (r+s+q) F := by
  let a := coefficient (coverOf F)
  have ha : Rapid a := rapid_coefficient ((smooth_iff_coverOf F).mp hF) (coverOf_periodic F)
  have ha0 : a 0 = 0 := (native_meanZero_iff_cover F).mp hF0
  have hp : PolynomialDivisorBound α := (polynomial_bound_iff_exists_real α).mpr ⟨s,hs,c,hc,hbound⟩
  have hi := rapid_generalInverseCoefficients hp ha
  let u := nativeSeries (generalInverseCoefficients α a) hi
  refine ⟨u,nativeSeries_smooth _ _,nativeSeries_meanZero hi (generalInverse_zero_coefficient α a),?_,?_⟩
  · intro y
    obtain ⟨x,rfl⟩ := pairProject_surjective y
    rw [transport_native_cover u (nativeSeries_smooth _ _),nativeSeries_cover,
      transportCover_series α hi,transport_generalInverseCoefficients hα ha0]
    exact series_coefficient ((smooth_iff_coverOf F).mp hF) (coverOf_periodic F) x
  · have ht := rapid_of_supported (truncate_supported N (generalInverseCoefficients α a))
    have hinv : finiteNativeInverse α N F =
        nativeSeries (truncate N (generalInverseCoefficients α a)) ht := by
      apply coverOf_injective
      simp only [finiteNativeInverse,nativeSeries_cover]
      rw [truncate_inverse_commute]
    have hn : nativeHNorm (r+s+q) F = sequenceNorm (r+s+q) a := by
      rw [nativeHNorm_eq_cover]
      rfl
    rw [hinv,hn]
    change nativeHNorm r (↑(nativeSeries (generalInverseCoefficients α a) hi -
      nativeSeries (truncate N (generalInverseCoefficients α a)) ht) : Torus2 → ℂ) ≤ _
    rw [← nativeSeries_sub hi ht,nativeSeries_norm]
    exact inverse_tail_bound hα hs hc hbound a ha ha0 N r q (by linarith) hq

/-- One fixed solution satisfies every cutoff and every real Sobolev estimate;
no solution is chosen after the norm indices or cutoff are specified. -/
theorem uniform_truncation_estimate {α s c : ℝ} (hα : Irrational α) (hs : 0 ≤ s) (hc : 0 < c)
    (hbound : ∀ k : PairFrequency, k ≠ 0 → c ≤ pairWeight k ^s * |pairDivisor α k|)
    (F : C(Torus2,ℂ)) (hF : Smooth F) (hF0 : MeanZero F) :
    ∃ u : C(Torus2,ℂ), Smooth u ∧ MeanZero u ∧
      (∀ y, transport α u y = F y) ∧
      ∀ N r q : ℝ, 1 ≤ N → 0 ≤ q →
        nativeHNorm r (u - finiteNativeInverse α N F) ≤
          (1/(2*Real.pi*c)) * (1+N^2)^(-q/2) * nativeHNorm (r+s+q) F := by
  obtain ⟨u, hu, hu0, hsol, _⟩ := truncation_estimate hα hs hc hbound F hF hF0
    1 0 0 (by norm_num) (by norm_num)
  refine ⟨u, hu, hu0, hsol, ?_⟩
  intro N r q hN hq
  obtain ⟨v, hv, hv0, hvsol, hvbound⟩ :=
    truncation_estimate hα hs hc hbound F hF hF0 N r q hN hq
  have hvu : v = u := native_solution_unique hα hv hu hv0 hu0
    (fun y => (hvsol y).trans (hsol y).symm)
  simpa only [hvu] using hvbound

end MathGauge.GP002
